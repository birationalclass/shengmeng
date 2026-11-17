"""Reproduce the experiment south of Java from the reference's NASA GIBS day.

Run: python build-java-weather.py INPUT_CACHE --download --output OUTPUT_FOLDER
Dependencies: numpy, scipy, Pillow. No credentials. NASA provides a daily Aqua
MODIS visible mosaic and per-product color tiles. This dataset uses official
legend intervals as height/optical thickness bins, not full-resolution Level 2
retrievals. Cloud classes and cloud base are reconstruction parameters.
"""

import argparse
from pathlib import Path
import re
from urllib.parse import urlencode
from urllib.request import urlretrieve
from xml.etree import ElementTree as ET

import numpy as np
from PIL import Image
from scipy.ndimage import gaussian_filter

GIBS = 'https://gibs.earthdata.nasa.gov'
MAP = GIBS + '/wms/epsg4326/best/wms.cgi'
COLORS = GIBS + '/colormaps/v1.3/'
BBOX = '105.91,-13.76,111.43,-8.36'
DATE = '2026-06-19'
DIM = 512


def request(layer, transparent=False):
    args = dict(SERVICE='WMS', REQUEST='GetMap', VERSION='1.1.1',
                STYLES='', FORMAT='image/png' if transparent else 'image/jpeg',
                TRANSPARENT='TRUE' if transparent else 'FALSE',
                SRS='EPSG:4326', BBOX=BBOX, WIDTH=768, HEIGHT=768,
                TIME=DATE, LAYERS=layer)
    return MAP + '?' + urlencode(args)


SOURCES = {
    'aqua-20260619.jpg': request('MODIS_Aqua_CorrectedReflectance_TrueColor'),
    'aqua-top.png': request('MODIS_Aqua_Cloud_Top_Height_Day', True),
    'aqua-tau.png': request('MODIS_Aqua_Cloud_Optical_Thickness', True),
    'aqua-top-palette-alt.xml': COLORS + 'MODIS_VIIRS_Cloud_Top_Height.xml',
    'aqua-tau-palette-alt.xml': COLORS + 'MODIS_VIIRS_Cloud_Optical_Thickness.xml',
}


def smooth(a, b, value):
    t = np.clip((value - a) / (b - a), 0., 1.)
    return t * t * (3. - 2. * t)


def get_palette(path):
    """Combine all represented value ranges with the same display color."""
    by_color = {}
    for node in ET.parse(path).iter('ColorMapEntry'):
        if node.get('nodata') == 'true' or node.get('transparent') == 'true':
            continue
        rgb = tuple(int(x) for x in node.get('rgb').split(','))
        nums = re.findall(r'-?\d+(?:\.\d+)?', node.get('value', ''))
        if not nums:
            continue
        by_color.setdefault(rgb, []).extend(float(x) for x in nums)
    return (np.asarray(list(by_color), dtype=np.float32),
            np.asarray([(min(a) + max(a)) * .5 for a in by_color.values()], dtype=np.float32))


def quantitative_tiles(path, palette, tolerance):
    with Image.open(path) as image:
        source = np.asarray(image.convert('RGBA').resize((DIM, DIM), Image.Resampling.NEAREST))
    palette_rgb, palette_values = get_palette(palette)
    unique, inverse = np.unique(source.reshape(-1, 4), axis=0, return_inverse=True)
    dist2 = np.sum((unique[:, None, :3].astype(np.float32) - palette_rgb[None, ...])**2, axis=2)
    nearest = np.argmin(dist2, axis=1)
    coords = np.arange(len(nearest))
    matched = (dist2[coords, nearest] <= tolerance**2) & (unique[:, 3] >= 128)
    values = np.where(matched, palette_values[nearest], np.nan)
    return values[inverse].reshape(DIM, DIM)


def filtered(data, sigma):
    valid = np.isfinite(data).astype(np.float32)
    confidence = gaussian_filter(valid, sigma)
    mean = gaussian_filter(np.nan_to_num(data), sigma) / np.maximum(.001, confidence)
    return np.where(confidence >= .38, mean, np.nan)


def save_channels(path, *channels):
    pixels = np.rint(255 * np.clip(np.stack(channels, axis=-1), 0, 1))
    Image.fromarray(pixels.astype(np.uint8), 'RGBA').save(path, optimize=True)


def convert(cache, output):
    ht = quantitative_tiles(cache / 'aqua-top.png', cache / 'aqua-top-palette-alt.xml', 6)
    tau = quantitative_tiles(cache / 'aqua-tau.png', cache / 'aqua-tau-palette-alt.xml', 7)
    with Image.open(cache / 'aqua-20260619.jpg') as raster:
        visible = raster.convert('RGB').resize((DIM, DIM), Image.Resampling.LANCZOS)
    rgb = np.asarray(visible, dtype=np.float32) / 255.
    # Calm ocean pixels are blue; the neutral triplet minimum keeps their
    # reflectance from turning into false cloud and retains slim bright bands.
    neutral = np.min(rgb, axis=-1)
    soft = gaussian_filter(neutral, .81)
    low_frequency = gaussian_filter(neutral, 2.25)
    visible_cloud = .85 * smooth(.13, .55, soft) + .15 * smooth(.11, .31, neutral)
    # No invented tau for transparent tiles. Blend the retrieved bins with the
    # observed visible geometry after gentle local sensitivity adjustment.
    opt = np.where(np.isfinite(tau), smooth(.6, 27., tau), smooth(.18, .68, soft))
    opacity = visible_cloud * (.68 + .32 * opt)

    h = filtered(ht, 1.3)
    measured = np.isfinite(h)
    safe_h = np.nan_to_num(h)
    thick = .76 * opt + .24 * smooth(.25, .69, low_frequency)
    convective = smooth(5000., 9500., safe_h) * smooth(.64, .98, thick)
    # A single retrieved top cannot prove stacked clouds. Treat high, compact
    # thick cells as columns, and other elevated top bins as an upper deck.
    upper = smooth(2450., 4650., safe_h) * (1. - convective)
    lo = opacity * (1. - upper)
    hi = opacity * upper
    lo_type = .67 * smooth(620., 3200., safe_h) + .33 * thick
    # Low, moderately thick or optically dense smooth texture -> Sc recipe.
    contours = np.hypot(*np.gradient(low_frequency))
    strat = (1. - smooth(2350., 3550., safe_h)) * smooth(.16, .48, thick)
    strat *= 1. - smooth(.013, .066, contours)
    hi_type = .82 * smooth(.19, .61, soft) + .18 * (1. - smooth(6200., 10500., safe_h))
    top = np.where(measured, np.maximum(1., np.rint(255 * safe_h / 18000.)) / 255., 0.)
    output.mkdir(parents=True, exist_ok=True)
    save_channels(output / 'weather-lo-java.png', lo, lo_type, strat, top)
    save_channels(output / 'weather-hi-java.png', hi, hi_type, top, .22 + .62 * opt)
    visible.save(output / 'satellite-java.jpg', quality=93, optimize=True)
    for label, fraction in [('low map above 0.36', (lo >= .36).mean()),
                            ('high map above 0.36', (hi >= .36).mean()),
                            ('known cloud top', measured.mean()),
                            ('known optical thickness', np.isfinite(tau).mean())]:
        print(f'{label}: {fraction:.1%}')
    return lo, hi, safe_h


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cache', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).parent)
    parser.add_argument('--download', action='store_true')
    args = parser.parse_args()
    if args.download:
        args.cache.mkdir(parents=True, exist_ok=True)
        for file, source in SOURCES.items():
            if not (args.cache / file).is_file():
                urlretrieve(source, args.cache / file)
    convert(args.cache, args.output)
