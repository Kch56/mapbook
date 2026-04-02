from flask import Flask, after_this_request, jsonify, render_template, request, send_file
import json
import math
import os
import io
import time
import datetime
import tempfile
import re
import zipfile
import requests
import sys
import threading
import traceback
from pathlib import Path
from uuid import uuid4

from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

import geopandas as gpd
from shapely.geometry import shape, mapping, box
from shapely.ops import transform, unary_union
from pyproj import Transformer

from PIL import Image, ImageDraw, ImageFont

from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import letter
from reportlab.lib.utils import ImageReader

app = Flask(__name__)

DOWNLOAD_JOB_TTL_SECONDS = 60 * 60
_download_jobs = {}
_download_jobs_lock = threading.Lock()

def resource_path(*parts):
    """
    Returns an absolute path to a resource.
    Works for both:
      - normal python run (files next to app.py)
      - PyInstaller onefile (files extracted to sys._MEIPASS)
    """
    base = getattr(sys, "_MEIPASS", str(Path(__file__).resolve().parent))
    return str(Path(base, *parts))
# -----------------------------
# ArcGIS services (data layers)
# -----------------------------
LAYER_9_QUERY = (
    "https://services3.arcgis.com/t6ulOHDjzlBrOlof/ArcGIS/rest/services/"
    "FireStationAdministrativeAreas_New/FeatureServer/9/query"
)

HYDRANTS_QUERY = "https://services3.arcgis.com/t6ulOHDjzlBrOlof/arcgis/rest/services/Hydrants_GEO/FeatureServer/0/query"
SPEEDHUMPS_QUERY = "https://services.arcgis.com/9Nl857LBlQVyzq54/arcgis/rest/services/Speed_Humps/FeatureServer/0/query"
CENTERLINES_QUERY = "https://services3.arcgis.com/t6ulOHDjzlBrOlof/arcgis/rest/services/WebUpdate_Centerline/FeatureServer/1/query"
FIRE_STATIONS_QUERY = "https://services3.arcgis.com/t6ulOHDjzlBrOlof/arcgis/rest/services/Current_CFD_Fire_Stations/FeatureServer/0/query"

USER_AGENT = "CFD-MapBooks-MVP/OSM-Export (internal use)"

# -----------------------------
# Address Points from LOCAL FILE (GeoPackage)
# -----------------------------
ADDRESS_GPKG_PATH = os.path.join("data", "AddressPoints.gpkg")
ADDRESS_LAYER_NAME = None  # set exact layer name if needed; None uses first layer

_address_field_map = None
_address_source_crs = None
_address_bbox_transformer = None
_address_columns = None

STREET_SUFFIX_NORMALIZATION = {
    "STREET": "ST",
    "ST": "ST",
    "ROAD": "RD",
    "RD": "RD",
    "DRIVE": "DR",
    "DR": "DR",
    "AVENUE": "AVE",
    "AVE": "AVE",
    "BOULEVARD": "BLVD",
    "BLVD": "BLVD",
    "LANE": "LN",
    "LN": "LN",
    "COURT": "CT",
    "CT": "CT",
    "CIRCLE": "CIR",
    "CIR": "CIR",
    "PLACE": "PL",
    "PL": "PL",
    "PARKWAY": "PKWY",
    "PKWY": "PKWY",
    "TERRACE": "TER",
    "TER": "TER",
    "HIGHWAY": "HWY",
    "HWY": "HWY",
}


def load_address_points():
    """Load lightweight metadata for the address GeoPackage."""
    global _address_field_map, _address_source_crs, _address_bbox_transformer, _address_columns
    if _address_field_map is not None and _address_source_crs is not None and _address_columns is not None:
        return

    if not os.path.exists(ADDRESS_GPKG_PATH):
        raise FileNotFoundError(f"Missing {ADDRESS_GPKG_PATH}. Put exported GPKG in data/.")

    gdf = gpd.read_file(ADDRESS_GPKG_PATH, layer=ADDRESS_LAYER_NAME, rows=1)

    # If CRS missing, assume EPSG:4326 (adjust if your export CRS differs)
    if gdf.crs is None:
        gdf = gdf.set_crs("EPSG:4326")

    _address_source_crs = gdf.crs
    _address_bbox_transformer = None
    _address_columns = list(gdf.columns)
    if str(gdf.crs).upper() != "EPSG:4326":
        _address_bbox_transformer = Transformer.from_crs("EPSG:4326", gdf.crs, always_xy=True)

    _address_field_map = _build_address_field_map(gdf)


def _first_existing_col(gdf: gpd.GeoDataFrame, candidates):
    cols = set(gdf.columns)
    for c in candidates:
        if c in cols:
            return c
    # case-insensitive fallback
    lower = {c.lower(): c for c in gdf.columns}
    for c in candidates:
        if c.lower() in lower:
            return lower[c.lower()]
    return None


def _clean_text(value) -> str:
    if value is None:
        return ""
    text = str(value).strip()
    return "" if text.lower() == "nan" else text


def normalize_street_name(name) -> str:
    """
    Collapse common street naming differences so centerlines and address
    points can be matched without relying on geometry snapping.
    """
    text = _clean_text(name).upper()
    if not text:
        return ""

    text = re.sub(r"[.,;:]+", " ", text)
    text = re.sub(r"\s+", " ", text).strip(" -")
    if not text:
        return ""

    parts = text.split()
    if parts:
        parts[-1] = STREET_SUFFIX_NORMALIZATION.get(parts[-1], parts[-1])
    return " ".join(parts)


def _build_address_field_map(gdf: gpd.GeoDataFrame) -> dict:
    return {
        "address": _first_existing_col(gdf, ["Address", "ADDRESS", "FULLADDR", "FULL_ADDY", "SITEADDR", "ADDR"]),
        "street": _first_existing_col(gdf, ["StreetName", "STREETNAME", "Street", "STREET", "RoadName", "ROADNAME"]),
        "building": _first_existing_col(gdf, ["Building", "BUILDING"]),
        "unit": _first_existing_col(gdf, ["Apartment", "APT", "UNIT"]),
        "location": _first_existing_col(gdf, ["LocationName", "LOCATIONNAME", "FULLADDR", "FULL_ADDY", "SITEADDR"]),
    }


def _get_address_field_map() -> dict:
    load_address_points()
    return _address_field_map


def _get_address_column_by_name(*candidates):
    load_address_points()
    cols = set(_address_columns or [])
    for candidate in candidates:
        if candidate in cols:
            return candidate

    lowered = {c.lower(): c for c in (_address_columns or [])}
    for candidate in candidates:
        if candidate.lower() in lowered:
            return lowered[candidate.lower()]
    return None


def _address_bbox_in_source_crs(west, south, east, north):
    load_address_points()
    if _address_bbox_transformer is None:
        return (west, south, east, north)

    corners = [
        _address_bbox_transformer.transform(west, south),
        _address_bbox_transformer.transform(east, south),
        _address_bbox_transformer.transform(east, north),
        _address_bbox_transformer.transform(west, north),
    ]
    xs = [pt[0] for pt in corners]
    ys = [pt[1] for pt in corners]
    return (min(xs), min(ys), max(xs), max(ys))


def _normalize_address_subset(gdf: gpd.GeoDataFrame) -> gpd.GeoDataFrame:
    if gdf.empty:
        return gdf

    if gdf.crs is None:
        gdf = gdf.set_crs(_address_source_crs or "EPSG:4326")

    if str(gdf.crs).upper() != "EPSG:4326":
        gdf = gdf.to_crs("EPSG:4326")

    gdf = gdf[gdf.geometry.notnull()].copy()
    gdf = gdf[gdf.geometry.geom_type == "Point"].copy()
    return gdf


def _dedupe_columns(columns):
    out = []
    for col in columns or []:
        if col and col not in out:
            out.append(col)
    return out


def _get_address_subset_in_bbox(west, south, east, north, max_records=2500, columns=None):
    load_address_points()
    read_kwargs = {
        "layer": ADDRESS_LAYER_NAME,
        "bbox": _address_bbox_in_source_crs(west, south, east, north),
    }
    selected_columns = _dedupe_columns(columns)
    if selected_columns:
        read_kwargs["columns"] = selected_columns

    subset = gpd.read_file(ADDRESS_GPKG_PATH, **read_kwargs)
    subset = _normalize_address_subset(subset)
    if len(subset) > max_records:
        subset = subset.iloc[:max_records].copy()
    return subset


def _parse_house_number(value):
    text = _clean_text(value)
    if not text:
        return None
    m = re.match(r"^\s*(\d{1,8})\b", text)
    if not m:
        return None
    try:
        return int(m.group(1))
    except ValueError:
        return None


def _compose_full_address(row, field_map: dict) -> str:
    address = _clean_text(row.get(field_map.get("address"))) if field_map.get("address") else ""
    street = _clean_text(row.get(field_map.get("street"))) if field_map.get("street") else ""
    building = _clean_text(row.get(field_map.get("building"))) if field_map.get("building") else ""
    unit = _clean_text(row.get(field_map.get("unit"))) if field_map.get("unit") else ""
    location = _clean_text(row.get(field_map.get("location"))) if field_map.get("location") else ""

    if address and street:
        base = f"{address} {street}"
    else:
        base = address or location or street or building

    extras = []
    if building and building.upper() not in base.upper():
        extras.append(building)
    if unit:
        extras.append(unit)

    return " ".join([base] + extras).strip()


def get_address_records_in_bbox(west, south, east, north, max_records=5000):
    """
    Returns address points with the fields needed for street-index generation.
    Existing map rendering still uses get_address_points_with_labels_in_bbox().
    """
    field_map = _get_address_field_map()
    subset = _get_address_subset_in_bbox(
        west, south, east, north,
        max_records=max_records,
        columns=[
            field_map.get("address"),
            field_map.get("street"),
            field_map.get("building"),
            field_map.get("unit"),
            field_map.get("location"),
        ],
    )
    if subset.empty:
        return []

    out = []
    for _, row in subset.iterrows():
        g = row.geometry
        if g is None:
            continue

        street = _clean_text(row.get(field_map.get("street"))) if field_map.get("street") else ""
        full_address = _compose_full_address(row, field_map)
        house_number = _parse_house_number(row.get(field_map.get("address")))
        if house_number is None:
            house_number = _parse_house_number(full_address)

        out.append({
            "lon": float(g.x),
            "lat": float(g.y),
            "full_address": full_address,
            "street": street,
            "street_normalized": normalize_street_name(street),
            "house_number": house_number,
        })

    return out


def get_address_points_with_labels_in_bbox(west, south, east, north, max_records=2500):
    """
    Returns list of tuples: (lon, lat, label)
    label tries to be the house number or address string.
    """
    field_map = _get_address_field_map()
    subset = _get_address_subset_in_bbox(
        west, south, east, north,
        max_records=max_records,
        columns=[field_map.get("address"), field_map.get("building")],
    )
    if subset.empty:
        return []

    # Best label column for this dataset
    # (your uploaded schema includes "Address", "StreetName", "Building", "Apartment", etc.)
    addr_col = field_map.get("address")
    bldg_col = field_map.get("building")

    out = []
    for _, row in subset.iterrows():
        g = row.geometry
        if g is None:
            continue

        label = None
        if addr_col and row.get(addr_col) not in (None, ""):
            label = str(row.get(addr_col)).strip()
        # If Address is too long, try "Building"
        if label and len(label) > 10 and bldg_col and row.get(bldg_col) not in (None, ""):
            label = str(row.get(bldg_col)).strip()

        # Try to extract just the leading house number if present (keeps labels clean)
        if label:
            m = re.match(r"^\s*(\d{1,6})\b", label)
            if m:
                label = m.group(1)

        # If still nothing, skip labeling but still return point
        out.append((float(g.x), float(g.y), label))

    return out


def get_centerlines_in_bbox(west, south, east, north, max_records=4000):
    # you might need to adjust the out_fields once you confirm the street name field
    gj = arcgis_query_geojson_by_bbox(
        CENTERLINES_QUERY,
        west, south, east, north,
        out_fields="*",
        max_records=max_records
    )
    if isinstance(gj, dict) and gj.get("_arcgis_error"):
        return []

    out = []
    for f in gj.get("features", []):
        geom = f.get("geometry") or {}
        props = f.get("properties") or {}
        gtype = geom.get("type")

        # We only draw linework
        if gtype == "LineString":
            coords = geom.get("coordinates", [])
            out.append((coords, props))
        elif gtype == "MultiLineString":
            for part in geom.get("coordinates", []):
                out.append((part, props))

    return out


def _first_nonempty_prop(props: dict, candidates) -> str:
    if not props:
        return ""

    for key in candidates:
        value = props.get(key)
        if _clean_text(value):
            return _clean_text(value)

    lowered = {str(k).lower(): k for k in props.keys()}
    for key in candidates:
        actual = lowered.get(str(key).lower())
        if actual is None:
            continue
        value = props.get(actual)
        if _clean_text(value):
            return _clean_text(value)
    return ""


def get_centerline_street_name(props: dict) -> str:
    """
    Prefer the full centerline name field, then fall back to reconstructed
    directional/name/type pieces if the service response varies by format.
    """
    direct = _first_nonempty_prop(
        props,
        ["WholeStNam", "FULLNAME", "STREETNAME", "ST_NAME", "NAME", "RD_NAME", "FULL_NAME"],
    )
    if direct:
        return direct

    parts = [
        _first_nonempty_prop(props, ["PREFIXDIRE", "PREDIR", "PRE_DIR"]),
        _first_nonempty_prop(props, ["Streetname", "StreetName", "NAME", "ST_NAME"]),
        _first_nonempty_prop(props, ["StreetType", "STREETTYPE", "TYPE"]),
        _first_nonempty_prop(props, ["Suffix", "SUFFIX", "POSTDIR", "POST_DIR"]),
    ]
    return " ".join([p for p in parts if p and p != " "]).strip()




def get_fire_stations_in_bbox(west, south, east, north, max_records=200):
    gj = arcgis_query_geojson_by_bbox(
        FIRE_STATIONS_QUERY,
        west, south, east, north,
        out_fields="*",
        max_records=max_records
    )
    if isinstance(gj, dict) and gj.get("_arcgis_error"):
        return []

    out = []
    for f in gj.get("features", []):
        geom = f.get("geometry") or {}
        props = f.get("properties") or {}
        if geom.get("type") == "Point":
            lon, lat = geom.get("coordinates")
            out.append((float(lon), float(lat), props))
    return out







# Requests session w/ retries
SESSION = requests.Session()
retry = Retry(
    total=6,
    connect=6,
    read=6,
    backoff_factor=0.7,
    status_forcelist=[429, 500, 502, 503, 504],
    allowed_methods=["GET"],
)
adapter = HTTPAdapter(max_retries=retry, pool_connections=10, pool_maxsize=10)
SESSION.mount("https://", adapter)
SESSION.mount("http://", adapter)


def draw_legend_on_map(
    map_img: Image.Image,
    include_address: bool,
    include_hydrants: bool,
    include_speed: bool,
    include_centerlines: bool,
    include_firestations: bool,
    marker_scale: float = 1.0,
    position: str = "top_left",
):
    """
    Draw a compact legend directly on the map image.

    Why top-left by default?
    - Your map page has page info boxes at the bottom corners, so putting the legend
      up top avoids it getting covered.
    """
    img = map_img.convert("RGBA")
    d = ImageDraw.Draw(img)
    w, h = img.size

    pad = max(10, int(14 * marker_scale))
    line_h = max(16, int(18 * marker_scale))
    title_h = max(18, int(20 * marker_scale))

    f_title = try_font(max(12, int(14 * marker_scale)), bold=True)
    f_item = try_font(max(10, int(12 * marker_scale)), bold=False)

    items = []
    if include_centerlines:
        items.append(("Street centerline", "centerline"))
    if include_firestations:
        items.append(("Fire station", "station"))
    if include_address:
        items.append(("Address point", "address"))
    if include_hydrants:
        items.append(("Hydrant 0–500 gpm", ("hydrant", 400)))
        items.append(("Hydrant 501–999 gpm", ("hydrant", 800)))
        items.append(("Hydrant 1000+ gpm", ("hydrant", 1500)))
    if include_speed:
        items.append(("Speed hump", "speed"))

    if not items:
        return img.convert("RGB")

    # Legend sizing
    swatch = max(12, int(14 * marker_scale))
    icon = max(14, int(18 * marker_scale))
    inner_pad = max(8, int(10 * marker_scale))

    text_width = 0
    for label, _kind in items:
        text_width = max(text_width, int(d.textlength(label, font=f_item)))

    box_w = inner_pad * 3 + max(swatch, icon) + text_width
    box_h = inner_pad * 2 + title_h + len(items) * line_h

    # Position
    if position == "top_left":
        x1, y1 = pad, pad
    elif position == "top_right":
        x1, y1 = w - pad - box_w, pad
    elif position == "bottom_left":
        x1, y1 = pad, h - pad - box_h
    else:  # bottom_right
        x1, y1 = w - pad - box_w, h - pad - box_h

    x2, y2 = x1 + box_w, y1 + box_h

    # Background (slightly transparent) + border
    d.rounded_rectangle((x1, y1, x2, y2), radius=max(8, int(10 * marker_scale)),
                        fill=(255, 255, 255, 235), outline=(0, 0, 0, 230), width=max(2, int(2 * marker_scale)))

    # Title
    d.text((x1 + inner_pad, y1 + inner_pad - 2), "Legend", font=f_title, fill=(0, 0, 0, 255))

    y = y1 + inner_pad + title_h
    sx = x1 + inner_pad
    tx = x1 + inner_pad * 2 + max(swatch, icon)

    for label, kind in items:
        cy = y + line_h // 2

        if kind == "centerline":
            # sample road line
            d.line((sx, cy, sx + swatch, cy), fill=(70, 70, 70, 255), width=max(2, int(3 * marker_scale)))
        elif kind == "station":
            r = max(5, int(6 * marker_scale))
            d.ellipse((sx, cy - r, sx + 2 * r, cy + r), fill=(200, 0, 0, 255), outline=(0, 0, 0, 255), width=max(1, int(2 * marker_scale)))
        elif kind == "address":
            r = max(3, int(3 * marker_scale))
            d.ellipse((sx, cy - r, sx + 2 * r, cy + r), fill=(0, 0, 0, 255), outline=None)
        elif kind == "speed":
            s = max(5, int(6 * marker_scale))
            tri = [(sx + s, cy - s), (sx, cy + s), (sx + 2 * s, cy + s)]
            d.polygon(tri, fill=(145, 0, 255, 255), outline=(0, 0, 0, 255))
        elif isinstance(kind, tuple) and kind[0] == "hydrant":
            flow = kind[1]
            hs = icon
            hydr = _make_hydrant_icon(hs, fill_rgba=_hydrant_color(flow))
            img.alpha_composite(hydr, (sx, cy - hs // 2))

        d.text((tx, y), label, font=f_item, fill=(0, 0, 0, 255))
        y += line_h

    return img.convert("RGB")
def arcgis_query(url: str, params: dict) -> dict:
    try:
        r = SESSION.get(
            url,
            params=params,
            timeout=(10, 60),
            headers={"User-Agent": USER_AGENT},
        )
        r.raise_for_status()
        data = r.json()
        if isinstance(data, dict) and data.get("error"):
            return {"_arcgis_error": True, "kind": "arcgis", "error": data.get("error")}
        return data
    except requests.exceptions.SSLError as e:
        return {"_arcgis_error": True, "kind": "ssl", "message": str(e)}
    except requests.exceptions.RequestException as e:
        return {"_arcgis_error": True, "kind": "request", "message": str(e)}
    except Exception as e:
        return {"_arcgis_error": True, "kind": "unknown", "message": str(e)}


def get_all_station_areas_geojson() -> dict:
    params = {
        "where": "1=1",
        "outFields": "Station,Battalion,Ladder,Hazmat",
        "returnGeometry": "true",
        "f": "geojson",
        "outSR": "4326",
    }
    return arcgis_query(LAYER_9_QUERY, params)


def get_station_feature_geojson(station_id: int) -> dict:
    params = {
        "where": f"Station={station_id}",
        "outFields": "Station,Battalion,Ladder,Hazmat",
        "returnGeometry": "true",
        "f": "geojson",
        "outSR": "4326",
    }
    return arcgis_query(LAYER_9_QUERY, params)


def arcgis_query_geojson_by_bbox(
    url: str,
    west: float,
    south: float,
    east: float,
    north: float,
    out_fields: str = "*",
    max_records: int = 2000,
    result_offset: int = 0,
):
    envelope = {
        "xmin": west, "ymin": south,
        "xmax": east, "ymax": north,
        "spatialReference": {"wkid": 4326}
    }
    params = {
        "where": "1=1",
        "outFields": out_fields,
        "returnGeometry": "true",
        "f": "geojson",
        "outSR": "4326",
        "inSR": "4326",
        "geometry": json.dumps(envelope),
        "geometryType": "esriGeometryEnvelope",
        "spatialRel": "esriSpatialRelIntersects",
        "resultRecordCount": int(max_records),
        "resultOffset": int(result_offset),
    }
    return arcgis_query(url, params)


# -----------------------------
# City fishnet + station pages
# -----------------------------
to_3857 = Transformer.from_crs("EPSG:4326", "EPSG:3857", always_xy=True).transform
to_4326 = Transformer.from_crs("EPSG:3857", "EPSG:4326", always_xy=True).transform

fishnet_cache = {}


def get_city_union_polygon_wgs84():
    all_geo = get_all_station_areas_geojson()
    geoms = []
    for f in all_geo.get("features", []):
        g = f.get("geometry")
        if g:
            geoms.append(shape(g))
    if not geoms:
        raise ValueError("No station geometries found (ArcGIS returned 0 features or error).")
    return unary_union(geoms)


def snap_down(value: float, step: float) -> float:
    return math.floor(value / step) * step


def build_city_fishnet(cell_size_m: float = 800) -> dict:
    if cell_size_m in fishnet_cache:
        return fishnet_cache[cell_size_m]

    city_poly_wgs84 = get_city_union_polygon_wgs84()
    city_poly_m = transform(to_3857, city_poly_wgs84)
    minx, miny, maxx, maxy = city_poly_m.bounds

    origin_x = snap_down(minx, cell_size_m)
    origin_y = snap_down(miny, cell_size_m)

    cols = math.ceil((maxx - origin_x) / cell_size_m)
    rows = math.ceil((maxy - origin_y) / cell_size_m)

    cells = []
    for r in range(rows):
        for c in range(cols):
            x1 = origin_x + c * cell_size_m
            y1 = origin_y + r * cell_size_m
            x2 = x1 + cell_size_m
            y2 = y1 + cell_size_m
            cell_m = box(x1, y1, x2, y2)

            cell_wgs84 = transform(to_4326, cell_m)
            cells.append({
                "row": r,
                "col": c,
                "cell_m": cell_m,
                "bbox_wgs84": list(cell_wgs84.bounds),
            })

    fishnet_cache[cell_size_m] = {"cells": cells}
    return fishnet_cache[cell_size_m]


def station_pages_from_city_fishnet(station_geom_wgs84, cell_size_m: float, overlap_threshold: float = 0.10) -> dict:
    fishnet = build_city_fishnet(cell_size_m)
    station_m = transform(to_3857, station_geom_wgs84)

    features = []
    page = 1

    for cell in fishnet["cells"]:
        cell_m = cell["cell_m"]
        if not cell_m.intersects(station_m):
            continue

        inter = cell_m.intersection(station_m)
        if inter.is_empty:
            continue

        cell_area = cell_m.area
        inter_area = inter.area
        centroid_in = station_m.contains(cell_m.centroid)

        if (not centroid_in) and (inter_area / cell_area < overlap_threshold):
            continue

        full_cell_wgs84 = transform(to_4326, cell_m)
        features.append({
            "type": "Feature",
            "geometry": mapping(full_cell_wgs84),
            "properties": {
                "page": page,
                "row": cell["row"],
                "col": cell["col"],
                "full_bbox": list(full_cell_wgs84.bounds),
            }
        })
        page += 1

    return {"type": "FeatureCollection", "features": features}


# -----------------------------
# TILE STITCHING (OSM)
# -----------------------------
TILE_SIZE = 256

# You can swap tile host if you want a different cartography later.
# Example: "https://{s}.tile.openstreetmap.fr/hot/{z}/{x}/{y}.png"
OSM_TILE_TEMPLATE = "https://tile.openstreetmap.org/{z}/{x}/{y}.png"


def lonlat_to_global_pixels(lon, lat, zoom):
    siny = math.sin(lat * math.pi / 180.0)
    siny = min(max(siny, -0.9999), 0.9999)

    x = TILE_SIZE * (2 ** zoom) * (lon + 180.0) / 360.0
    y = TILE_SIZE * (2 ** zoom) * (0.5 - math.log((1 + siny) / (1 - siny)) / (4 * math.pi))
    return x, y


def tile_url(z, x, y):
    return OSM_TILE_TEMPLATE.format(z=z, x=x, y=y)


def fetch_tile(z, x, y):
    url = tile_url(z, x, y)
    r = SESSION.get(url, timeout=(10, 60), headers={"User-Agent": USER_AGENT})
    r.raise_for_status()
    return Image.open(io.BytesIO(r.content)).convert("RGBA")


def stitch_bbox_map(west, south, east, north, zoom=15, out_w=1400, out_h=900):
    """
    Fetch tiles that cover bbox, stitch, crop to bbox, then resize.
    """
    px_w, py_n = lonlat_to_global_pixels(west, north, zoom)
    px_e, py_s = lonlat_to_global_pixels(east, south, zoom)

    tile_x_min = int(math.floor(px_w / TILE_SIZE))
    tile_x_max = int(math.floor(px_e / TILE_SIZE))
    tile_y_min = int(math.floor(py_n / TILE_SIZE))
    tile_y_max = int(math.floor(py_s / TILE_SIZE))

    tiles_w = tile_x_max - tile_x_min + 1
    tiles_h = tile_y_max - tile_y_min + 1

    big = Image.new("RGBA", (tiles_w * TILE_SIZE, tiles_h * TILE_SIZE), (255, 255, 255, 255))

    for ty in range(tile_y_min, tile_y_max + 1):
        for tx in range(tile_x_min, tile_x_max + 1):
            try:
                im = fetch_tile(zoom, tx, ty)
            except Exception:
                im = Image.new("RGBA", (TILE_SIZE, TILE_SIZE), (240, 240, 240, 255))
            ox = (tx - tile_x_min) * TILE_SIZE
            oy = (ty - tile_y_min) * TILE_SIZE
            big.paste(im, (ox, oy))

    crop_left = int(px_w - tile_x_min * TILE_SIZE)
    crop_top = int(py_n - tile_y_min * TILE_SIZE)
    crop_right = int(px_e - tile_x_min * TILE_SIZE)
    crop_bottom = int(py_s - tile_y_min * TILE_SIZE)

    cropped = big.crop((crop_left, crop_top, crop_right, crop_bottom))
    return cropped.resize((out_w, out_h), Image.Resampling.LANCZOS)


def lonlat_to_image_xy(lon, lat, west, south, east, north, img_w, img_h, zoom=15):
    gx_w, gy_n = lonlat_to_global_pixels(west, north, zoom)
    gx_e, gy_s = lonlat_to_global_pixels(east, south, zoom)
    gx, gy = lonlat_to_global_pixels(lon, lat, zoom)

    if gx_e == gx_w or gy_s == gy_n:
        return None

    nx = (gx - gx_w) / (gx_e - gx_w)
    ny = (gy - gy_n) / (gy_s - gy_n)

    x = int(nx * img_w)
    y = int(ny * img_h)
    return x, y


# -----------------------------
# OVERLAYS (icons + labels)
# -----------------------------
def get_hydrants_in_bbox(west, south, east, north, max_records=2000):
    gj = arcgis_query_geojson_by_bbox(HYDRANTS_QUERY, west, south, east, north, out_fields="FLOW", max_records=max_records)
    if isinstance(gj, dict) and gj.get("_arcgis_error"):
        return []
    out = []
    for f in gj.get("features", []):
        geom = f.get("geometry") or {}
        if geom.get("type") == "Point":
            lon, lat = geom.get("coordinates")
            flow = (f.get("properties") or {}).get("FLOW")
            out.append((float(lon), float(lat), flow))
    return out


def get_speedhumps_in_bbox(west, south, east, north, max_records=2000):
    gj = arcgis_query_geojson_by_bbox(SPEEDHUMPS_QUERY, west, south, east, north, out_fields="*", max_records=max_records)
    if isinstance(gj, dict) and gj.get("_arcgis_error"):
        return []
    out = []
    for f in gj.get("features", []):
        geom = f.get("geometry") or {}
        if geom.get("type") == "Point":
            lon, lat = geom.get("coordinates")
            out.append((float(lon), float(lat)))
    return out


def _hydrant_color(flow):
    try:
        f = float(flow)
    except Exception:
        return (220, 220, 220, 255)
    if f <= 500:
        return (220, 0, 0, 255)
    if f <= 999:
        return (255, 140, 0, 255)
    if f <= 1499:
        return (0, 160, 0, 255)
    return (0, 90, 255, 255)


def _make_hydrant_icon(size_px: int, fill_rgba=(220, 0, 0, 255)):
    """
    Simple hydrant silhouette drawn with PIL. Cached by (size, fill).
    """
    key = (size_px, fill_rgba)
    if key in _make_hydrant_icon._cache:
        return _make_hydrant_icon._cache[key].copy()

    s = size_px
    img = Image.new("RGBA", (s, s), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)

    # proportions
    body_w = int(s * 0.42)
    body_h = int(s * 0.52)
    body_x1 = (s - body_w) // 2
    body_y1 = int(s * 0.30)
    body_x2 = body_x1 + body_w
    body_y2 = body_y1 + body_h

    # top dome
    dome_r = int(s * 0.18)
    cx = s // 2
    cy = int(s * 0.28)
    d.ellipse((cx - dome_r, cy - dome_r, cx + dome_r, cy + dome_r), fill=fill_rgba, outline=(0, 0, 0, 255), width=max(1, s // 18))

    # body
    d.rounded_rectangle((body_x1, body_y1, body_x2, body_y2), radius=max(2, s // 10), fill=fill_rgba, outline=(0, 0, 0, 255), width=max(1, s // 18))

    # side nozzles
    noz_w = int(s * 0.14)
    noz_h = int(s * 0.12)
    noz_y = int(s * 0.48)
    d.rounded_rectangle((body_x1 - noz_w + 1, noz_y, body_x1 + 1, noz_y + noz_h),
                        radius=max(2, s // 12), fill=fill_rgba, outline=(0, 0, 0, 255), width=max(1, s // 18))
    d.rounded_rectangle((body_x2 - 1, noz_y, body_x2 + noz_w - 1, noz_y + noz_h),
                        radius=max(2, s // 12), fill=fill_rgba, outline=(0, 0, 0, 255), width=max(1, s // 18))

    # base
    base_h = int(s * 0.10)
    d.rectangle((body_x1 - int(s * 0.04), body_y2 - int(base_h * 0.3), body_x2 + int(s * 0.04), body_y2 + base_h),
                fill=fill_rgba, outline=(0, 0, 0, 255), width=max(1, s // 18))

    _make_hydrant_icon._cache[key] = img
    return img.copy()
_make_hydrant_icon._cache = {}


def _boxes_overlap(a, b):
    ax1, ay1, ax2, ay2 = a
    bx1, by1, bx2, by2 = b
    return not (ax2 < bx1 or bx2 < ax1 or ay2 < by1 or by2 < ay1)


def try_font(size=14, bold=False):
    candidates = ["arial.ttf", "Arial.ttf", "DejaVuSans.ttf"]
    if bold:
        candidates = ["arialbd.ttf", "Arial Bold.ttf", "DejaVuSans-Bold.ttf"] + candidates
    for name in candidates:
        try:
            return ImageFont.truetype(name, size)
        except Exception:
            continue
    return ImageFont.load_default()


def draw_station_polygon_rgba(img_rgba: Image.Image, station_geom_wgs84, west, south, east, north, zoom=15):
    if station_geom_wgs84 is None:
        return
    draw = ImageDraw.Draw(img_rgba, "RGBA")
    w, h = img_rgba.size

    geom = station_geom_wgs84
    polys = []
    if geom.geom_type == "Polygon":
        polys = [geom]
    elif geom.geom_type == "MultiPolygon":
        polys = list(geom.geoms)

    for poly in polys:
        exterior = list(poly.exterior.coords)
        pts = []
        for lon, lat in exterior:
            xy = lonlat_to_image_xy(lon, lat, west, south, east, north, w, h, zoom=zoom)
            if xy:
                pts.append(xy)
        if len(pts) >= 3:
            draw.polygon(pts, fill=(255, 255, 0, 80), outline=(0, 0, 0, 180))

def draw_overlays(
    img: Image.Image,
    west, south, east, north,
    include_address=False, include_hydrants=False, include_speed=False,
    station_geom_wgs84=None, zoom=15,
    highlight_station=True,
    marker_scale: float = 1.0,
    label_address: bool = False,
    include_centerlines: bool = False,
    include_firestations: bool = False,
    label_streets: bool = False,
    hydrant_scale: float | None = None,
):
    """
    highlight_station:
      True  => draw yellow station area overlay (index page)
      False => do NOT draw yellow overlay (actual pages)

    marker_scale:
      Scale factor applied to point marker sizes.

    label_address:
      When True, draw address labels (tries to be house numbers).
    """
    base = img.convert("RGBA")

    if highlight_station and station_geom_wgs84 is not None:
        draw_station_polygon_rgba(base, station_geom_wgs84, west, south, east, north, zoom=zoom)

    draw = ImageDraw.Draw(base)
    w, h = base.size

    # hydrants can be scaled separately so they stay visible
    hydrant_scale = hydrant_scale if hydrant_scale is not None else marker_scale

    # -----------------------------
    # Centerlines (with optional street labels)
    # -----------------------------
    if include_centerlines:
        lines = get_centerlines_in_bbox(west, south, east, north, max_records=4000)

        # casing + inner stroke so lines stay readable on any basemap
        w_outer = max(2, int(4 * marker_scale))
        w_inner = max(1, int(2 * marker_scale))

        # street label controls
        street_font = try_font(max(11, int(14 * marker_scale)), bold=True)
        street_label_budget = 120 if zoom >= 16 else 70
        street_labeled = 0
        street_occupied = []

        for coords, props in lines:
            pts = []
            for lon, lat in coords:
                xy = lonlat_to_image_xy(lon, lat, west, south, east, north, w, h, zoom=zoom)
                if xy:
                    pts.append(xy)

            if len(pts) < 2:
                continue

            # draw the linework
            draw.line(pts, fill=(255, 255, 255, 210), width=w_outer)
            draw.line(pts, fill=(70, 70, 70, 235), width=w_inner)

            if not label_streets:
                continue
            if street_labeled >= street_label_budget:
                continue

            name = get_centerline_street_name(props)
            if not name:
                continue

            # label only if the line is "long enough" on the page
            # prevents tons of labels on tiny cul-de-sacs
            dx = pts[-1][0] - pts[0][0]
            dy = pts[-1][1] - pts[0][1]
            if (dx * dx + dy * dy) ** 0.5 < 140:
                continue

            mid = pts[len(pts) // 2]
            tx, ty = mid[0] + 6, mid[1] - 10

            tw = draw.textlength(name, font=street_font)
            th = street_font.size

            pad = max(3, int(4 * marker_scale))
            bb = (tx - pad, ty - pad, tx + int(tw) + pad, ty + th + pad)

            # keep inside image
            if bb[2] > w - 2:
                tx = max(2, w - 2 - int(tw) - pad)
                bb = (tx - pad, ty - pad, tx + int(tw) + pad, ty + th + pad)
            if bb[1] < 2:
                ty = 2 + pad
                bb = (tx - pad, ty - pad, tx + int(tw) + pad, ty + th + pad)

            # collision avoidance
            if any(_boxes_overlap(bb, other) for other in street_occupied):
                continue
            street_occupied.append(bb)

            # halo then text
            for ox, oy in [(-1, 0), (1, 0), (0, -1), (0, 1), (-1, -1), (1, 1), (-1, 1), (1, -1)]:
                draw.text((tx + ox, ty + oy), name, font=street_font, fill=(255, 255, 255, 235))
            draw.text((tx, ty), name, font=street_font, fill=(20, 20, 20, 255))
            street_labeled += 1

    # -----------------------------
    # Address points (bigger markers + optional numbers)
    # -----------------------------
    if include_address:
        pts = get_address_points_with_labels_in_bbox(west, south, east, north, max_records=2500)

        r = max(3, int(4 * marker_scale))
        halo_r = r + max(2, int(2 * marker_scale))

        label_budget = 220 if zoom >= 16 else 120
        font = try_font(max(10, int(12 * marker_scale)), bold=True)

        occupied = []
        labeled = 0

        for lon, lat, label in pts:
            xy = lonlat_to_image_xy(lon, lat, west, south, east, north, w, h, zoom=zoom)
            if not xy:
                continue
            x, y = xy

            draw.ellipse((x - halo_r, y - halo_r, x + halo_r, y + halo_r), fill=(255, 255, 255, 220), outline=None)
            draw.ellipse((x - r, y - r, x + r, y + r), fill=(0, 0, 0, 255), outline=None)

            if not label_address or not label:
                continue
            if labeled >= label_budget:
                continue

            pad = max(2, int(3 * marker_scale))
            text = str(label)
            tw = draw.textlength(text, font=font)
            th = font.size + pad * 2

            lx1 = x + r + 2
            ly1 = y - th - 2
            lx2 = lx1 + int(tw) + pad * 2
            ly2 = ly1 + th

            if lx2 > w - 2:
                lx1 = x - r - 2 - (int(tw) + pad * 2)
                lx2 = lx1 + int(tw) + pad * 2
            if ly1 < 2:
                ly1 = y + r + 2
                ly2 = ly1 + th

            box_bb = (lx1, ly1, lx2, ly2)
            if any(_boxes_overlap(box_bb, bb) for bb in occupied):
                continue
            occupied.append(box_bb)

            draw.rounded_rectangle(
                box_bb,
                radius=max(2, int(4 * marker_scale)),
                fill=(255, 255, 255, 225),
                outline=(0, 0, 0, 180),
                width=max(1, int(1 * marker_scale)),
            )
            draw.text((lx1 + pad, ly1 + pad - 1), text, font=font, fill=(0, 0, 0, 255))
            labeled += 1

    # -----------------------------
    # Hydrants (bigger + glow + icon)
    # -----------------------------
    if include_hydrants:
        hydrants = get_hydrants_in_bbox(west, south, east, north, max_records=2000)

        # make them noticeably larger than other points
        icon_size = max(18, int(26 * hydrant_scale))
        glow_pad = max(3, int(4 * hydrant_scale))

        for lon, lat, flow in hydrants:
            xy = lonlat_to_image_xy(lon, lat, west, south, east, north, w, h, zoom=zoom)
            if not xy:
                continue
            x, y = xy

            # soft white glow ring so hydrants pop over busy areas
            draw.ellipse(
                (x - icon_size // 2 - glow_pad, y - icon_size // 2 - glow_pad,
                 x + icon_size // 2 + glow_pad, y + icon_size // 2 + glow_pad),
                fill=(255, 255, 255, 210),
                outline=None,
            )

            icon = _make_hydrant_icon(icon_size, fill_rgba=_hydrant_color(flow))
            base.alpha_composite(icon, (x - icon_size // 2, y - icon_size // 2))

    # -----------------------------
    # Speed humps (triangle icon)
    # -----------------------------
    if include_speed:
        humps = get_speedhumps_in_bbox(west, south, east, north, max_records=2000)
        size = max(7, int(9 * marker_scale))
        for lon, lat in humps:
            xy = lonlat_to_image_xy(lon, lat, west, south, east, north, w, h, zoom=zoom)
            if not xy:
                continue
            x, y = xy
            tri = [(x, y - size), (x - size, y + size), (x + size, y + size)]
            draw.polygon(tri, fill=(145, 0, 255, 230), outline=(0, 0, 0, 255))

    # -----------------------------
    # Fire stations (marker + station number label)
    # -----------------------------
    if include_firestations:
        stations = get_fire_stations_in_bbox(west, south, east, north, max_records=200)

        r = max(9, int(12 * marker_scale))
        stroke = max(2, int(2 * marker_scale))
        font = try_font(max(11, int(14 * marker_scale)), bold=True)

        # avoid station labels colliding with address labels
        station_occupied = []

        def _pick_station_id(props: dict) -> str:
            for k in ("Station", "STATION", "STN", "STATION_NO", "STA"):
                v = props.get(k)
                if v is not None and str(v).strip():
                    return str(v).strip()
            return ""

        for lon, lat, props in stations:
            xy = lonlat_to_image_xy(lon, lat, west, south, east, north, w, h, zoom=zoom)
            if not xy:
                continue
            x, y = xy

            draw.ellipse((x - r, y - r, x + r, y + r), fill=(200, 0, 0, 245), outline=(0, 0, 0, 255), width=stroke)

            st_num = _pick_station_id(props)
            if not st_num:
                continue

            tw = draw.textlength(st_num, font=font)
            pad = max(3, int(4 * marker_scale))

            lx1 = x + r + 6
            ly1 = y - (font.size // 2) - pad
            lx2 = lx1 + int(tw) + pad * 2
            ly2 = ly1 + font.size + pad * 2

            # keep inside image
            if lx2 > w - 2:
                lx1 = x - r - 6 - (int(tw) + pad * 2)
                lx2 = lx1 + int(tw) + pad * 2
            if ly1 < 2:
                ly1 = 2
                ly2 = ly1 + font.size + pad * 2

            bb = (lx1, ly1, lx2, ly2)
            if any(_boxes_overlap(bb, other) for other in station_occupied):
                continue
            station_occupied.append(bb)

            draw.rounded_rectangle(bb, radius=max(2, int(5 * marker_scale)), fill=(255, 255, 255, 235),
                                   outline=(0, 0, 0, 255), width=stroke)
            draw.text((lx1 + pad, ly1 + pad - 1), st_num, font=font, fill=(0, 0, 0, 255))

    return base.convert("RGB")


# -----------------------------
# Mapbook page layout helpers
# -----------------------------
def _expand_bounds(bounds, pct=0.12):
    west, south, east, north = bounds
    dx = (east - west) * pct
    dy = (north - south) * pct
    return (west - dx, south - dy, east + dx, north + dy)


def _rowcol_label_maps(pages):
    rows = sorted({(f.get("properties") or {}).get("row") for f in pages})
    cols = sorted({(f.get("properties") or {}).get("col") for f in pages})

    row_to_letter = {r: chr(ord("A") + i) for i, r in enumerate([r for r in rows if r is not None])}
    col_to_num = {c: i + 1 for i, c in enumerate([c for c in cols if c is not None])}
    return row_to_letter, col_to_num


def make_cover_page_image(station_id: int, produced_by: str = "Produced by CFD Planning", date_text=None):
    page_w, page_h = 1650, 2200
    img = Image.new("RGB", (page_w, page_h), (255, 255, 255))
    draw = ImageDraw.Draw(img)

    draw.rectangle((40, 40, page_w - 40, page_h - 40), outline=(0, 0, 0), width=6)

    maroon = (120, 30, 30)
    box_w, box_h = 1100, 420
    bx1 = (page_w - box_w) // 2
    by1 = 260
    bx2 = bx1 + box_w
    by2 = by1 + box_h

    draw.rectangle((bx1, by1, bx2, by2), outline=maroon, width=10)
    draw.rectangle((bx1 + 16, by1 + 16, bx2 - 16, by2 - 16), outline=maroon, width=3)

    f_title = try_font(44, bold=False)
    f_sub = try_font(30, bold=False)
    f_small = try_font(22, bold=False)

    date_text = date_text or datetime.datetime.now().strftime("%B %Y")

    def center_text(y, text, font, fill=(0, 0, 0)):
        tw = draw.textlength(text, font=font)
        draw.text(((page_w - tw) / 2, y), text, font=font, fill=fill)

    center_text(by1 + 80, "Charlotte Fire Department", f_title)
    center_text(by1 + 145, f"Station {station_id} Map Book", f_title)
    center_text(by1 + 250, date_text, f_sub)
    center_text(by1 + 330, produced_by, f_small)

    logo_path = os.path.join(app.static_folder or "static", "cfd_seal.png")
    if os.path.exists(logo_path):
        try:
            logo = Image.open(logo_path).convert("RGBA")
            target_w = 420
            ratio = target_w / logo.size[0]
            logo = logo.resize((target_w, int(logo.size[1] * ratio)), Image.Resampling.LANCZOS)
            lx = (page_w - logo.size[0]) // 2
            ly = 1120
            img.paste(logo, (lx, ly), logo)
        except Exception:
            pass

    return img


def make_overview_page_image(station_geom_wgs84, pages, row_to_letter, col_to_num, zoom=12, station_id=None):
    page_w, page_h = 1650, 2200
    margin = 60
    footer_h = 140

    img = Image.new("RGB", (page_w, page_h), (255, 255, 255))
    draw = ImageDraw.Draw(img)

    draw.rectangle((40, 40, page_w - 40, page_h - 40), outline=(0, 0, 0), width=6)

    map_x1 = margin
    map_y1 = margin
    map_x2 = page_w - margin
    map_y2 = page_h - margin - footer_h
    map_w = map_x2 - map_x1
    map_h = map_y2 - map_y1

    west, south, east, north = _expand_bounds(station_geom_wgs84.bounds, pct=0.18)

    map_img = stitch_bbox_map(west, south, east, north, zoom=zoom, out_w=map_w, out_h=map_h)

    map_img = draw_overlays(
        map_img, west, south, east, north,
        include_address=False, include_hydrants=False, include_speed=False,
        station_geom_wgs84=station_geom_wgs84, zoom=zoom,
        highlight_station=True,
        marker_scale=1.0
    )
    img.paste(map_img, (map_x1, map_y1))

    f_cell = try_font(34, bold=True)
    f_page = try_font(26, bold=True)

    for f in pages:
        p = f.get("properties") or {}
        row = p.get("row")
        col = p.get("col")
        page_num = p.get("page")
        bbox = p.get("full_bbox") or []
        if len(bbox) != 4:
            continue
        cw, cs, ce, cn = bbox

        tl = lonlat_to_image_xy(cw, cn, west, south, east, north, map_w, map_h, zoom=zoom)
        br = lonlat_to_image_xy(ce, cs, west, south, east, north, map_w, map_h, zoom=zoom)
        if not tl or not br:
            continue
        x1, y1 = tl
        x2, y2 = br
        x1, x2 = sorted([x1, x2])
        y1, y2 = sorted([y1, y2])

        x1 += map_x1
        x2 += map_x1
        y1 += map_y1
        y2 += map_y1

        draw.rectangle((x1, y1, x2, y2), outline=(0, 0, 0), width=4)

        cell_name = f"{row_to_letter.get(row, '?')}{col_to_num.get(col, '?')}"
        draw.text((x1 + 14, y1 + 8), cell_name, font=f_cell, fill=(0, 0, 0))

        pn = str(page_num)
        pw = draw.textlength(pn, font=f_page)
        draw.text(((x1 + x2 - pw) / 2, y2 - 40), pn, font=f_page, fill=(160, 0, 0))

    f_footer = try_font(32, bold=True)
    footer_text = f"Station {station_id} Index" if station_id is not None else "Mapbook Index"
    tw = draw.textlength(footer_text, font=f_footer)
    draw.text(((page_w - tw) / 2, page_h - margin - 100), footer_text, font=f_footer, fill=(0, 0, 0))

    return img


def make_map_page_image(
    map_img: Image.Image,
    page_label: str,
    page_num: int,
    total_pages: int,
    neighbor_labels: dict | None = None,
):
    """
    Build the full portrait page around the already-rendered map image.

    neighbor_labels expects keys:
      {"N": "C5", "S": "A5", "E": "B6", "W": "B4"} (values can be "" if none)

    This version places neighbor page boxes OUTSIDE the map frame
    so they do not cover any map content.
    """
    page_w, page_h = 1650, 2200
    margin = 60
    footer_h = 160

    img = Image.new("RGB", (page_w, page_h), (255, 255, 255))
    draw = ImageDraw.Draw(img)

    # outer page border
    outer_x1, outer_y1 = 40, 40
    outer_x2, outer_y2 = page_w - 40, page_h - 40
    draw.rectangle((outer_x1, outer_y1, outer_x2, outer_y2), outline=(0, 0, 0), width=6)

    # map frame
    map_x1 = margin
    map_y1 = margin
    map_x2 = page_w - margin
    map_y2 = page_h - margin - footer_h
    map_w = map_x2 - map_x1
    map_h = map_y2 - map_y1

    # ensure map matches frame
    if map_img.size != (map_w, map_h):
        map_img = map_img.resize((map_w, map_h), Image.Resampling.LANCZOS)

    img.paste(map_img, (map_x1, map_y1))
    draw.rectangle((map_x1, map_y1, map_x2, map_y2), outline=(0, 0, 0), width=3)

    # -------------------------
    # Corner boxes (page name / number)
    # -------------------------
    box_w, box_h = 280, 120

    bl_x1 = map_x1
    bl_y1 = map_y2 - box_h
    draw.rectangle(
        (bl_x1, bl_y1, bl_x1 + box_w, bl_y1 + box_h),
        fill=(255, 255, 255), outline=(0, 0, 0), width=3
    )

    f_lbl = try_font(22, bold=True)
    f_val = try_font(38, bold=True)
    draw.text((bl_x1 + 16, bl_y1 + 10), "Page", font=f_lbl, fill=(0, 0, 0))
    draw.text((bl_x1 + 16, bl_y1 + 38), "Name:", font=f_lbl, fill=(0, 0, 0))
    draw.text((bl_x1 + 16, bl_y1 + 68), page_label, font=f_val, fill=(0, 0, 0))

    br_x2 = map_x2
    br_x1 = br_x2 - box_w
    br_y1 = bl_y1
    draw.rectangle(
        (br_x1, br_y1, br_x2, br_y1 + box_h),
        fill=(255, 255, 255), outline=(0, 0, 0), width=3
    )

    draw.text((br_x1 + 16, br_y1 + 10), "Page", font=f_lbl, fill=(0, 0, 0))
    draw.text((br_x1 + 16, br_y1 + 38), "Number", font=f_lbl, fill=(0, 0, 0))
    draw.text((br_x1 + 16, br_y1 + 68), f"{page_num} of {total_pages}", font=f_val, fill=(0, 0, 0))

    # centered footer label
    f_center = try_font(56, bold=True)
    cw = draw.textlength(page_label, font=f_center)
    draw.text(((page_w - cw) / 2, map_y2 + 78), page_label, font=f_center, fill=(0, 0, 0))
    # -------------------------
    # Neighbor grid labels OUTSIDE the map frame
    # -------------------------
    if neighbor_labels:
        nb_font = try_font(30, bold=True)
        nb_box_w = 140
        nb_box_h = 60

        def _draw_nb(label, x, y):
            if not label:
                return
            draw.rounded_rectangle(
                (x, y, x + nb_box_w, y + nb_box_h),
                radius=10,
                fill=(255, 255, 255),
                outline=(0, 0, 0),
                width=3,
            )
            tw = draw.textlength(label, font=nb_font)
            draw.text((x + (nb_box_w - tw) / 2, y + 12), label, font=nb_font, fill=(0, 0, 0))

        # page border margins
        outer_x1, outer_y1 = 40, 40
        outer_x2, outer_y2 = page_w - 40, page_h - 40

        # TOP: centered in white space between page border and map frame
        top_x = int((page_w - nb_box_w) / 2)
        top_y = int(outer_y1 + ((map_y1 - outer_y1) - nb_box_h) / 2)

        # LEFT: centered in white space between page border and map frame
        left_x = int(outer_x1 + ((map_x1 - outer_x1) - nb_box_w) / 2)
        left_y = int(map_y1 + (map_h - nb_box_h) / 2)

        # RIGHT: centered in white space between map frame and page border
        right_x = int(map_x2 + ((outer_x2 - map_x2) - nb_box_w) / 2)
        right_y = int(map_y1 + (map_h - nb_box_h) / 2)

        # BOTTOM: centered in the footer, ABOVE the large page label
        bottom_x = int((page_w - nb_box_w) / 2)
        bottom_y = int(map_y2 + 10)

        _draw_nb(neighbor_labels.get("N", ""), top_x, top_y)
        _draw_nb(neighbor_labels.get("W", ""), left_x, left_y)
        _draw_nb(neighbor_labels.get("E", ""), right_x, right_y)
        _draw_nb(neighbor_labels.get("S", ""), bottom_x, bottom_y)

    return img

def _neighbor_labels(page_label: str):
    # expects format LetterNumber like B8
    import re
    m = re.match(r"^([A-Z])(\d+)$", str(page_label).strip())
    if not m:
        return {"N": None, "S": None, "W": None, "E": None}
    row = ord(m.group(1))
    col = int(m.group(2))

    def rch(x): return chr(x) if ord("A") <= x <= ord("Z") else None
    def cnum(x): return x if x >= 1 else None

    return {
        "N": f"{rch(row-1)}{col}" if rch(row-1) else None,
        "S": f"{rch(row+1)}{col}" if rch(row+1) else None,
        "W": f"{rch(row)}{cnum(col-1)}" if cnum(col-1) else None,
        "E": f"{rch(row)}{cnum(col+1)}" if cnum(col+1) else None,
    }


def build_street_index_rows(pages, row_to_letter, col_to_num):
    rows = []

    for feature in pages:
        props = feature.get("properties") or {}
        bbox = props.get("full_bbox") or []
        row = props.get("row")
        col = props.get("col")
        if len(bbox) != 4 or row is None or col is None:
            continue

        west, south, east, north = bbox
        box_label = f"{row_to_letter.get(row, '?')}{col_to_num.get(col, '?')}"

        streets_in_box = {}
        for _, centerline_props in get_centerlines_in_bbox(west, south, east, north, max_records=4000):
            street_name = get_centerline_street_name(centerline_props)
            normalized = normalize_street_name(street_name)
            if not normalized:
                continue
            streets_in_box.setdefault(normalized, normalized)

        if not streets_in_box:
            continue

        address_groups = {}
        for record in get_address_records_in_bbox(west, south, east, north, max_records=5000):
            normalized = record.get("street_normalized") or ""
            house_number = record.get("house_number")
            if not normalized or normalized not in streets_in_box or house_number is None:
                continue
            address_groups.setdefault(normalized, []).append(house_number)

        for normalized, house_numbers in address_groups.items():
            rows.append({
                "street": streets_in_box.get(normalized, normalized),
                "box": box_label,
                "low": min(house_numbers),
                "high": max(house_numbers),
                "_sort_row": row,
                "_sort_col": col,
            })

    rows.sort(key=lambda item: (item["street"], item["_sort_row"], item["_sort_col"]))
    return [
        {
            "street": item["street"],
            "box": item["box"],
            "low": item["low"],
            "high": item["high"],
        }
        for item in rows
    ]


def _format_address_range(low, high) -> str:
    if low is None and high is None:
        return ""
    if low == high:
        return str(low)
    return f"{low}-{high}"


def _truncate_text(draw, text: str, font, max_width: float) -> str:
    if draw.textlength(text, font=font) <= max_width:
        return text

    shortened = text
    while shortened and draw.textlength(shortened + "...", font=font) > max_width:
        shortened = shortened[:-1]
    return (shortened + "...") if shortened else ""


def make_street_index_page_image(station_id: int, page_rows, page_num: int, total_pages: int):
    page_w, page_h = 1650, 2200
    img = Image.new("RGB", (page_w, page_h), (255, 255, 255))
    draw = ImageDraw.Draw(img)

    border = 40
    margin = 90
    maroon = (120, 30, 30)

    draw.rectangle((border, border, page_w - border, page_h - border), outline=(0, 0, 0), width=6)
    draw.line((margin, 210, page_w - margin, 210), fill=maroon, width=6)

    f_title = try_font(52, bold=True)
    f_sub = try_font(28, bold=False)
    f_hdr = try_font(26, bold=True)
    f_row = try_font(24, bold=False)
    f_note = try_font(22, bold=False)

    title = "Street Index"
    subtitle = f"Station {station_id} Street Index"
    tw = draw.textlength(title, font=f_title)
    sw = draw.textlength(subtitle, font=f_sub)
    draw.text(((page_w - tw) / 2, 100), title, font=f_title, fill=(0, 0, 0))
    draw.text(((page_w - sw) / 2, 155), subtitle, font=f_sub, fill=(0, 0, 0))

    table_x1 = margin
    table_x2 = page_w - margin
    header_y = 270
    row_h = 34
    street_x = table_x1 + 20
    box_x = 1035
    range_x = 1210

    draw.rounded_rectangle((table_x1, header_y, table_x2, header_y + 54), radius=12, fill=(240, 240, 240), outline=(0, 0, 0), width=2)
    draw.text((street_x, header_y + 13), "Street", font=f_hdr, fill=(0, 0, 0))
    draw.text((box_x, header_y + 13), "Box", font=f_hdr, fill=(0, 0, 0))
    draw.text((range_x, header_y + 13), "Address Range", font=f_hdr, fill=(0, 0, 0))

    if not page_rows:
        msg = "No street index rows were available for this station."
        mw = draw.textlength(msg, font=f_note)
        draw.text(((page_w - mw) / 2, header_y + 110), msg, font=f_note, fill=(60, 60, 60))
    else:
        y = header_y + 70
        street_w = box_x - street_x - 24
        for row in page_rows:
            draw.line((table_x1, y + row_h, table_x2, y + row_h), fill=(215, 215, 215), width=1)
            street = _truncate_text(draw, str(row.get("street", "")), f_row, street_w)
            box_label = str(row.get("box", ""))
            addr_range = _format_address_range(row.get("low"), row.get("high"))

            draw.text((street_x, y + 4), street, font=f_row, fill=(0, 0, 0))
            draw.text((box_x, y + 4), box_label, font=f_row, fill=(0, 0, 0))
            draw.text((range_x, y + 4), addr_range, font=f_row, fill=(0, 0, 0))
            y += row_h

    footer = f"Street Index Page {page_num} of {total_pages}"
    fw = draw.textlength(footer, font=f_note)
    draw.text(((page_w - fw) / 2, page_h - 120), footer, font=f_note, fill=(0, 0, 0))
    return img


# -----------------------------
# Flask routes
# -----------------------------
@app.route("/healthz")
def healthz():
    address_points_present = os.path.exists(ADDRESS_GPKG_PATH)
    status_code = 200 if address_points_present else 503
    return jsonify({
        "status": "ok" if address_points_present else "degraded",
        "address_points_present": address_points_present,
    }), status_code


@app.route("/")
def home():
    return render_template("index.html")


@app.route("/api/areas")
def areas():
    data = get_all_station_areas_geojson()
    if isinstance(data, dict) and data.get("_arcgis_error"):
        return jsonify({"type": "FeatureCollection", "features": [], "meta": {"error": data}}), 200
    return jsonify(data)


@app.route("/api/grid_for_station/<int:station_id>")
def grid_for_station(station_id: int):
    cell_size_m = float(request.args.get("cell_size_m", "800"))
    overlap_threshold = float(request.args.get("overlap_threshold", "0.10"))

    station_geo = get_station_feature_geojson(station_id)
    if isinstance(station_geo, dict) and station_geo.get("_arcgis_error"):
        return jsonify({"type": "FeatureCollection", "features": [], "meta": {"error": station_geo}}), 200

    if not station_geo.get("features"):
        return jsonify({"type": "FeatureCollection", "features": [], "properties": {"station": station_id}})

    feature = station_geo["features"][0]
    station_geom_wgs84 = shape(feature.get("geometry"))
    props = feature.get("properties", {})

    grid = station_pages_from_city_fishnet(station_geom_wgs84, cell_size_m=cell_size_m, overlap_threshold=overlap_threshold)

    grid["properties"] = {
        "station": props.get("Station", station_id),
        "battalion": props.get("Battalion"),
        "cell_size_m": cell_size_m,
        "page_count": len(grid["features"]),
        "overlap_threshold": overlap_threshold,
    }
    return jsonify(grid)


@app.route("/api/street_index/<int:station_id>")
def street_index_for_station(station_id: int):
    cell_size_m = float(request.args.get("cell_size_m", "500"))
    overlap_threshold = float(request.args.get("overlap_threshold", "0.10"))

    station_geo = get_station_feature_geojson(station_id)
    if isinstance(station_geo, dict) and station_geo.get("_arcgis_error"):
        return jsonify({"station_id": station_id, "page_count": 0, "rows": [], "meta": {"error": station_geo}}), 200

    if not station_geo.get("features"):
        return jsonify({"station_id": station_id, "page_count": 0, "rows": []}), 200

    station_geom = shape(station_geo["features"][0]["geometry"])
    grid = station_pages_from_city_fishnet(
        station_geom_wgs84=station_geom,
        cell_size_m=cell_size_m,
        overlap_threshold=overlap_threshold,
    )
    pages = grid.get("features", [])
    row_to_letter, col_to_num = _rowcol_label_maps(pages)
    rows = build_street_index_rows(pages, row_to_letter, col_to_num)

    return jsonify({
        "station_id": station_id,
        "page_count": len(pages),
        "rows": rows,
    })


@app.route("/api/layer/addresspoints")
def layer_addresspoints_local():
    west = float(request.args.get("west"))
    south = float(request.args.get("south"))
    east = float(request.args.get("east"))
    north = float(request.args.get("north"))
    max_records = int(request.args.get("max", "2000"))

    # keep a few useful columns for popups
    field_map = _get_address_field_map()
    keep = []
    for col in [
        field_map.get("address"),
        field_map.get("street"),
        field_map.get("building"),
        field_map.get("unit"),
        _get_address_column_by_name("ZipCode", "ZIPCODE"),
        _get_address_column_by_name("CFDRA"),
    ]:
        if col and col not in keep:
            keep.append(col)

    subset = _get_address_subset_in_bbox(
        west, south, east, north,
        max_records=max_records,
        columns=keep,
    )
    if subset.empty:
        return jsonify({"type": "FeatureCollection", "features": [], "meta": {"count": 0}})

    subset = subset[keep + ["geometry"]] if keep else subset[["geometry"]]

    gj = json.loads(subset.to_json())
    return jsonify({"type": "FeatureCollection", "features": gj.get("features", []), "meta": {"count": len(gj.get("features", []))}})


@app.route("/api/layer/hydrants")
def layer_hydrants():
    west = float(request.args.get("west"))
    south = float(request.args.get("south"))
    east = float(request.args.get("east"))
    north = float(request.args.get("north"))
    max_records = int(request.args.get("max", "2000"))

    gj = arcgis_query_geojson_by_bbox(
        HYDRANTS_QUERY, west, south, east, north,
        out_fields="FLOW,HYDRANT,FULL_ADDY",
        max_records=max_records
    )
    if isinstance(gj, dict) and gj.get("_arcgis_error"):
        return jsonify({"type": "FeatureCollection", "features": [], "meta": {"error": gj}})
    return jsonify({"type": "FeatureCollection", "features": gj.get("features", []), "meta": {"count": len(gj.get("features", []))}})


@app.route("/api/layer/speedhumps")
def layer_speedhumps():
    west = float(request.args.get("west"))
    south = float(request.args.get("south"))
    east = float(request.args.get("east"))
    north = float(request.args.get("north"))
    max_records = int(request.args.get("max", "2000"))

    gj = arcgis_query_geojson_by_bbox(SPEEDHUMPS_QUERY, west, south, east, north, out_fields="*", max_records=max_records)
    if isinstance(gj, dict) and gj.get("_arcgis_error"):
        return jsonify({"type": "FeatureCollection", "features": [], "meta": {"error": gj}})
    return jsonify({"type": "FeatureCollection", "features": gj.get("features", []), "meta": {"count": len(gj.get("features", []))}})



def fit_bbox_to_aspect(west, south, east, north, target_w_px, target_h_px):
    """
    Expand (never shrink) bbox so its aspect ratio matches target_w_px/target_h_px.
    Works in EPSG:3857 meters to avoid lon/lat distortion.
    """
    # convert bbox corners to meters
    minx, miny = Transformer.from_crs("EPSG:4326", "EPSG:3857", always_xy=True).transform(west, south)
    maxx, maxy = Transformer.from_crs("EPSG:4326", "EPSG:3857", always_xy=True).transform(east, north)

    cx = (minx + maxx) / 2.0
    cy = (miny + maxy) / 2.0

    w_m = maxx - minx
    h_m = maxy - miny
    if w_m <= 0 or h_m <= 0:
        return west, south, east, north

    target_aspect = float(target_w_px) / float(target_h_px)
    current_aspect = w_m / h_m

    # expand the smaller dimension to match aspect
    if current_aspect > target_aspect:
        # too wide: expand height
        new_h = w_m / target_aspect
        h_m = new_h
    else:
        # too tall: expand width
        new_w = h_m * target_aspect
        w_m = new_w

    new_minx = cx - w_m / 2.0
    new_maxx = cx + w_m / 2.0
    new_miny = cy - h_m / 2.0
    new_maxy = cy + h_m / 2.0

    # back to lon/lat
    west2, south2 = Transformer.from_crs("EPSG:3857", "EPSG:4326", always_xy=True).transform(new_minx, new_miny)
    east2, north2 = Transformer.from_crs("EPSG:3857", "EPSG:4326", always_xy=True).transform(new_maxx, new_maxy)

    return west2, south2, east2, north2












# -----------------------------
# MAPBOOK DOWNLOAD (portrait pages, cover + index)
# -----------------------------
def _get_mapbook_options(args) -> dict:
    default_export_scale = os.environ.get("MAPBOOK_EXPORT_SCALE")
    if default_export_scale is None:
        default_export_scale = "0.8" if os.environ.get("RENDER_EXTERNAL_URL") or os.environ.get("RENDER") else "2.0"

    default_export_zoom_delta = os.environ.get(
        "MAPBOOK_EXPORT_ZOOM_DELTA",
        "0" if os.environ.get("RENDER_EXTERNAL_URL") or os.environ.get("RENDER") else "1",
    )
    return {
        "cell_size_m": float(args.get("cell_size_m", "500")),
        "overlap_threshold": float(args.get("overlap_threshold", "0.10")),
        "zoom": int(args.get("zoom", "15")),
        "export_scale": float(args.get("export_scale", default_export_scale)),
        "export_zoom_delta": int(args.get("export_zoom_delta", default_export_zoom_delta)),
        "include_address": args.get("include_address", "0") == "1",
        "include_hydrants": args.get("include_hydrants", "0") == "1",
        "include_speed": args.get("include_speed", "0") == "1",
        "include_centerlines": args.get("include_centerlines", "1") == "1",
        "include_firestations": args.get("include_firestations", "1") == "1",
        "label_streets": args.get("label_streets", "1") == "1",
        "label_address": args.get("label_address", "1") == "1",
    }


def _all_station_ids() -> list[int]:
    areas_geo = get_all_station_areas_geojson()
    station_ids = set()
    for feature in areas_geo.get("features", []):
        props = feature.get("properties") or {}
        station = props.get("Station")
        if station in (None, ""):
            continue
        try:
            station_ids.add(int(station))
        except (TypeError, ValueError):
            continue
    return sorted(station_ids)


def _cleanup_download_job_resources(job: dict) -> None:
    file_path = job.get("file_path")
    temp_dir = job.get("temp_dir")

    try:
        if file_path and os.path.exists(file_path):
            os.remove(file_path)
    except Exception:
        pass

    try:
        if temp_dir and os.path.isdir(temp_dir):
            os.rmdir(temp_dir)
    except Exception:
        pass


def _prune_download_jobs() -> None:
    cutoff = time.time() - DOWNLOAD_JOB_TTL_SECONDS
    stale_job_ids = []

    with _download_jobs_lock:
        for job_id, job in _download_jobs.items():
            if job.get("updated_at", 0) < cutoff:
                stale_job_ids.append(job_id)

        stale_jobs = [_download_jobs.pop(job_id) for job_id in stale_job_ids]

    for job in stale_jobs:
        _cleanup_download_job_resources(job)


def _set_download_job(job_id: str, **updates) -> None:
    with _download_jobs_lock:
        job = _download_jobs.get(job_id)
        if not job:
            return
        job.update(updates)
        job["updated_at"] = time.time()


def _run_mapbook_job(job_id: str, station_id: int, options: dict) -> None:
    _set_download_job(job_id, status="running")
    try:
        pdf_path, temp_dir = build_mapbook_pdf_file(station_id, options)
        _set_download_job(
            job_id,
            status="complete",
            file_path=pdf_path,
            temp_dir=temp_dir,
            download_name=f"station_{station_id}_mapbook.pdf",
        )
    except MemoryError:
        _set_download_job(
            job_id,
            status="error",
            error="Mapbook generation ran out of memory on the server. Try again with fewer overlays or a lighter export setting.",
        )
    except Exception as exc:
        detail = str(exc).strip() or exc.__class__.__name__
        _set_download_job(job_id, status="error", error=detail)
        traceback.print_exc()


def _create_mapbook_job(station_id: int, options: dict) -> str:
    _prune_download_jobs()
    job_id = uuid4().hex
    with _download_jobs_lock:
        _download_jobs[job_id] = {
            "job_id": job_id,
            "kind": "mapbook",
            "station_id": station_id,
            "status": "queued",
            "error": None,
            "file_path": None,
            "temp_dir": None,
            "download_name": None,
            "created_at": time.time(),
            "updated_at": time.time(),
        }

    thread = threading.Thread(
        target=_run_mapbook_job,
        args=(job_id, station_id, dict(options)),
        daemon=True,
    )
    thread.start()
    return job_id


def _build_mapbook_pdf(station_id: int, options: dict, output_target) -> None:
    cell_size_m = options["cell_size_m"]
    overlap_threshold = options["overlap_threshold"]
    zoom = options["zoom"]
    export_scale = options["export_scale"]
    include_address = options["include_address"]
    include_hydrants = options["include_hydrants"]
    include_speed = options["include_speed"]
    include_centerlines = options["include_centerlines"]
    include_firestations = options["include_firestations"]
    label_streets = options["label_streets"]
    label_address = options["label_address"]

    export_zoom_delta = max(0, min(2, int(options.get("export_zoom_delta", 1))))
    export_zoom = min(16, zoom + export_zoom_delta)  # PDF export zoom only

    station_geo = get_station_feature_geojson(station_id)
    if isinstance(station_geo, dict) and station_geo.get("_arcgis_error"):
        raise RuntimeError(f"ArcGIS error while loading station {station_id}: {station_geo}")
    if not station_geo.get("features"):
        raise ValueError(f"No station geometry for station {station_id}")

    station_geom = shape(station_geo["features"][0]["geometry"])
    grid = station_pages_from_city_fishnet(
        station_geom_wgs84=station_geom,
        cell_size_m=cell_size_m,
        overlap_threshold=overlap_threshold,
    )
    pages = grid.get("features", [])
    if not pages:
        raise ValueError("No pages produced for this station with current settings.")

    total_pages = len(pages)
    row_to_letter, col_to_num = _rowcol_label_maps(pages)
    street_index_rows = build_street_index_rows(pages, row_to_letter, col_to_num)

    existing_cells = set()
    for feature in pages:
        props = feature.get("properties") or {}
        if props.get("row") is None or props.get("col") is None:
            continue
        existing_cells.add((props.get("row"), props.get("col")))

    def _cell_label(r, c):
        if (r, c) not in existing_cells:
            return ""
        return f"{row_to_letter.get(r, '?')}{col_to_num.get(c, '?')}"

    c = canvas.Canvas(output_target, pagesize=letter)
    pdf_w, pdf_h = letter

    def add_pil_page(pil_img: Image.Image):
        img_bytes = io.BytesIO()
        page_rgb = pil_img.convert("RGB")
        page_rgb.save(img_bytes, format="JPEG", quality=82, optimize=True)
        img_bytes.seek(0)
        margin = 18
        c.drawImage(
            ImageReader(img_bytes),
            margin, margin,
            width=pdf_w - margin * 2,
            height=pdf_h - margin * 2,
            preserveAspectRatio=True,
            anchor="c",
        )
        c.showPage()
        page_rgb.close()
        pil_img.close()
        img_bytes.close()

    add_pil_page(make_cover_page_image(station_id=station_id))
    add_pil_page(make_overview_page_image(
        station_geom_wgs84=station_geom,
        pages=pages,
        row_to_letter=row_to_letter,
        col_to_num=col_to_num,
        zoom=max(11, min(13, export_zoom - 3)),
        station_id=station_id,
    ))

    marker_scale = export_scale
    map_frame_w = 1530
    map_frame_h = 1880
    render_mode = bool(os.environ.get("RENDER_EXTERNAL_URL") or os.environ.get("RENDER"))
    if render_mode:
        map_frame_w = 1224
        map_frame_h = 1504

    for feature in pages:
        props = feature.get("properties") or {}
        page_num = int(props.get("page"))
        row = props.get("row")
        col = props.get("col")
        west, south, east, north = props.get("full_bbox")

        west, south, east, north = fit_bbox_to_aspect(
            west, south, east, north,
            map_frame_w, map_frame_h,
        )

        page_label = f"{row_to_letter.get(row, '?')}{col_to_num.get(col, '?')}"
        big_w = max(900, int(map_frame_w * export_scale))
        big_h = max(1100, int(map_frame_h * export_scale))

        map_big = stitch_bbox_map(
            west, south, east, north,
            zoom=export_zoom,
            out_w=big_w,
            out_h=big_h,
        )

        map_big = draw_overlays(
            map_big,
            west, south, east, north,
            include_address=include_address,
            include_hydrants=include_hydrants,
            include_speed=include_speed,
            station_geom_wgs84=station_geom,
            zoom=export_zoom,
            highlight_station=False,
            marker_scale=marker_scale,
            label_address=label_address,
            include_centerlines=include_centerlines,
            include_firestations=include_firestations,
            label_streets=label_streets,
            hydrant_scale=marker_scale * 1.35,
        )

        map_img = map_big.resize((map_frame_w, map_frame_h), Image.Resampling.LANCZOS)
        map_big.close()
        map_img = draw_legend_on_map(
            map_img,
            include_address=include_address,
            include_hydrants=include_hydrants,
            include_speed=include_speed,
            include_centerlines=include_centerlines,
            include_firestations=include_firestations,
            marker_scale=1.0,
        )

        neighbor_labels = {
            "N": _cell_label(row + 1, col),
            "S": _cell_label(row - 1, col),
            "E": _cell_label(row, col + 1),
            "W": _cell_label(row, col - 1),
        }
        add_pil_page(make_map_page_image(map_img, page_label, page_num, total_pages, neighbor_labels=neighbor_labels))
        map_img.close()
        time.sleep(0.03)

    rows_per_index_page = 48
    if street_index_rows:
        street_index_pages = [
            street_index_rows[i:i + rows_per_index_page]
            for i in range(0, len(street_index_rows), rows_per_index_page)
        ]
    else:
        street_index_pages = [[]]

    for idx, page_rows in enumerate(street_index_pages, start=1):
        add_pil_page(make_street_index_page_image(
            station_id=station_id,
            page_rows=page_rows,
            page_num=idx,
            total_pages=len(street_index_pages),
        ))

    c.save()


def build_mapbook_pdf_buffer(station_id: int, options: dict) -> io.BytesIO:
    pdf_buf = io.BytesIO()
    _build_mapbook_pdf(station_id, options, pdf_buf)
    pdf_buf.seek(0)
    return pdf_buf


def build_mapbook_pdf_file(station_id: int, options: dict) -> tuple[str, str]:
    temp_dir = tempfile.mkdtemp(prefix="cfd_mapbook_")
    pdf_name = f"station_{station_id}_mapbook.pdf"
    pdf_path = os.path.join(temp_dir, pdf_name)
    _build_mapbook_pdf(station_id, options, pdf_path)
    return pdf_path, temp_dir


@app.route("/download/mapbook/<int:station_id>")
def download_mapbook(station_id: int):
    options = _get_mapbook_options(request.args)
    try:
        pdf_path, temp_dir = build_mapbook_pdf_file(station_id, options)
    except RuntimeError as exc:
        return jsonify({"error": str(exc)}), 500
    except ValueError as exc:
        return jsonify({"error": str(exc)}), 404
    except Exception as exc:
        return jsonify({"error": f"Mapbook generation failed: {exc}"}), 500

    @after_this_request
    def _cleanup_mapbook_file(response):
        try:
            if os.path.exists(pdf_path):
                os.remove(pdf_path)
            if os.path.isdir(temp_dir):
                os.rmdir(temp_dir)
        except Exception:
            pass
        return response

    return send_file(
        pdf_path,
        mimetype="application/pdf",
        as_attachment=True,
        download_name=f"station_{station_id}_mapbook.pdf",
    )


@app.route("/api/jobs/mapbook/<int:station_id>", methods=["POST"])
def start_mapbook_job(station_id: int):
    options = _get_mapbook_options(request.args)
    try:
        station_geo = get_station_feature_geojson(station_id)
        if isinstance(station_geo, dict) and station_geo.get("_arcgis_error"):
            return jsonify({"error": f"ArcGIS error while loading station {station_id}: {station_geo}"}), 500
        if not station_geo.get("features"):
            return jsonify({"error": f"No station geometry for station {station_id}"}), 404
    except Exception as exc:
        return jsonify({"error": str(exc)}), 500

    job_id = _create_mapbook_job(station_id, options)
    return jsonify({
        "job_id": job_id,
        "status": "queued",
        "status_url": f"/api/jobs/{job_id}",
        "download_url": f"/download/job/{job_id}",
    }), 202


@app.route("/api/jobs/<job_id>")
def get_download_job(job_id: str):
    _prune_download_jobs()
    with _download_jobs_lock:
        job = _download_jobs.get(job_id)
        if not job:
            return jsonify({"error": "Job not found or expired."}), 404

        payload = {
            "job_id": job_id,
            "status": job.get("status"),
            "error": job.get("error"),
            "download_name": job.get("download_name"),
        }
        if job.get("status") == "complete":
            payload["download_url"] = f"/download/job/{job_id}"
        return jsonify(payload)


@app.route("/download/job/<job_id>")
def download_generated_job(job_id: str):
    _prune_download_jobs()
    with _download_jobs_lock:
        job = _download_jobs.get(job_id)
        if not job:
            return jsonify({"error": "Job not found or expired."}), 404
        if job.get("status") != "complete" or not job.get("file_path"):
            return jsonify({"error": "Job is not ready yet."}), 409

        file_path = job.get("file_path")
        temp_dir = job.get("temp_dir")
        download_name = job.get("download_name") or "mapbook.pdf"

    @after_this_request
    def _cleanup_generated_job(response):
        with _download_jobs_lock:
            job = _download_jobs.pop(job_id, None)
        if job:
            _cleanup_download_job_resources(job)
        else:
            _cleanup_download_job_resources({"file_path": file_path, "temp_dir": temp_dir})
        return response

    return send_file(
        file_path,
        mimetype="application/pdf",
        as_attachment=True,
        download_name=download_name,
    )


@app.route("/download/mapbooks/all")
def download_all_mapbooks():
    options = _get_mapbook_options(request.args)
    station_ids = _all_station_ids()
    if not station_ids:
        return jsonify({"error": "No station ids were available for bulk export."}), 404

    temp_dir = tempfile.mkdtemp(prefix="cfd_mapbooks_")
    zip_name = f"cfd_all_mapbooks_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.zip"
    zip_path = os.path.join(temp_dir, zip_name)

    export_summary = []
    success_count = 0

    try:
        with zipfile.ZipFile(zip_path, mode="w", compression=zipfile.ZIP_STORED) as archive:
            for station_id in station_ids:
                try:
                    pdf_buf = build_mapbook_pdf_buffer(station_id, options)
                    archive.writestr(f"station_{station_id}_mapbook.pdf", pdf_buf.getvalue())
                    export_summary.append({"station_id": station_id, "status": "ok"})
                    success_count += 1
                except Exception as exc:
                    export_summary.append({"station_id": station_id, "status": "error", "error": str(exc)})

            archive.writestr("bulk_export_summary.json", json.dumps({
                "station_count": len(station_ids),
                "successful_exports": success_count,
                "requested_options": options,
                "stations": export_summary,
            }, indent=2))
    except Exception:
        if os.path.exists(zip_path):
            os.remove(zip_path)
        os.rmdir(temp_dir)
        raise

    if success_count == 0:
        if os.path.exists(zip_path):
            os.remove(zip_path)
        os.rmdir(temp_dir)
        return jsonify({"error": "Bulk export failed for every station."}), 500

    @after_this_request
    def _cleanup_bulk_file(response):
        try:
            if os.path.exists(zip_path):
                os.remove(zip_path)
            if os.path.isdir(temp_dir):
                os.rmdir(temp_dir)
        except Exception:
            pass
        return response

    return send_file(
        zip_path,
        mimetype="application/zip",
        as_attachment=True,
        download_name=zip_name,
    )


if __name__ == "__main__":
    app.run(
        host="0.0.0.0",
        port=int(os.environ.get("PORT", "5000")),
        debug=os.environ.get("FLASK_DEBUG") == "1",
    )











