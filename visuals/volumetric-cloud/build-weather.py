"""Build this sample's weather maps from the public NOAA GOES-19 input scan.

Run: python build-weather.py PATH_TO_CACHED_INPUTS --output THIS_DIRECTORY
Dependencies: numpy, scipy, Pillow, h5py. Five original NetCDF files are cached
under short names by this script; pass --download to populate a fresh cache.
Each output pixel is one sample on a north-up local 600 km square. Outputs are
a browser rendering recipe; they do not claim retrieved cloud type or base.
"""

import argparse
from pathlib import Path
from urllib.request import urlretrieve

import h5py
import numpy as np
from PIL import Image
from scipy.ndimage import gaussian_filter, map_coordinates

SCAN = 'https://noaa-goes19.s3.amazonaws.com/ABI-L2-'
P = '/2025/154/18/OR_ABI-L2-'
T = '_G19_s20251541801173_e202515418035'
SOURCES = {
    'ACHAC': (f'{SCAN}ACHAC{P}ACHAC-M6{T}46_c20251541806421.nc', 'HT'),
    'ACMC': (f'{SCAN}ACMC{P}ACMC-M6{T}46_c20251541805076.nc', 'ACM'),
    'CODC': (f'{SCAN}CODC{P}CODC-M6{T}46_c20251541807012.nc', 'COD'),
    'CMI1': (f'{SCAN}CMIPC{P}CMIPC-M6C01{T}46_c20251541804116.nc', 'CMI'),
    'CMI13': (f'{SCAN}CMIPC{P}CMIPC-M6C13{T}58_c20251541804029.nc', 'CMI'),
}
CENTER = (26., -86.)
SPAN_KM = 600.
PIXELS = 512
TOP_RANGE_M = 18000.


def field(path, name, variable):
    with h5py.File(path, 'r') as f:
        def unpack(key):
            d = f[key]
            raw = d[:]
            value = raw.astype(np.float32) * float(np.squeeze(d.attrs.get('scale_factor', 1)))
            value += float(np.squeeze(d.attrs.get('add_offset', 0)))
            if '_FillValue' in d.attrs:
                value[raw == d.attrs['_FillValue'][0]] = np.nan
            return value

        data = unpack(variable)
        q = f['DQF'][:]
        if name == 'ACHAC':
            data[(q > 1) & (q != 4)] = np.nan
        elif name == 'ACMC':
            data[(q != 0) & (q != 6)] = np.nan
        elif name == 'CODC':
            # Good or degraded day retrievals, except surface ice, twilight,
            # failure to converge, or specular glint. Never fill flagged COD
            # with pseudo-COD numbers: use a separate visible signal below.
            data[((q & (2 | 8 | 16 | 32 | 64)) != 2)] = np.nan
        elif name == 'CMI1':
            # The out-of-range values above unit reflectance occur in bright
            # cloud cores; they are saturated in the display/opacity curves.
            # Treating these valid stored samples as black punches false holes.
            data[(q != 0) & (q != 1) & ~((q == 2) & (data >= 1.))] = np.nan
        else:
            data[(q != 0) & (q != 1)] = np.nan
        proj = dict(f['goes_imager_projection'].attrs)
        return data, unpack('x'), unpack('y'), proj


def angular_grid(proj):
    coord = (np.arange(PIXELS) + 0.5 - PIXELS / 2) * SPAN_KM / PIXELS
    east, north = np.meshgrid(coord, -coord)
    d = np.hypot(east, north) / 6371.0088
    bearing = np.arctan2(east, north)
    phi = np.radians(CENTER[0])
    lat = np.arcsin(np.sin(phi) * np.cos(d) + np.cos(phi) * np.sin(d) * np.cos(bearing))
    lon = np.radians(CENTER[1] - float(np.squeeze(proj['longitude_of_projection_origin'])))
    lon += np.arctan2(np.sin(bearing) * np.sin(d) * np.cos(phi), np.cos(d) - np.sin(phi) * np.sin(lat))
    a = float(np.squeeze(proj['semi_major_axis']))
    b = float(np.squeeze(proj['semi_minor_axis']))
    h = float(np.squeeze(proj['perspective_point_height']))
    e2 = 1 - b * b / (a * a)
    n = a / np.sqrt(1 - e2 * np.sin(lat)**2)
    x = n * np.cos(lat) * np.cos(lon)
    y = n * np.cos(lat) * np.sin(lon)
    z = n * (1 - e2) * np.sin(lat)
    vx = h + a - x
    return np.arctan2(y, np.hypot(vx, z)), np.arctan2(z, vx)


def sample(field_data, sweep):
    raw, xx, yy, _ = field_data
    x, y = sweep
    coords = [(y - yy[0]) / ((yy[-1] - yy[0]) / (len(yy) - 1)),
              (x - xx[0]) / ((xx[-1] - xx[0]) / (len(xx) - 1))]
    valid = np.isfinite(raw)
    denom = map_coordinates(valid.astype(np.float32), coords, order=1, mode='constant', cval=0)
    weighted = map_coordinates(np.where(valid, raw, 0), coords, order=1, mode='constant', cval=0)
    return np.where(denom >= 0.50, weighted / np.maximum(denom, .0001), np.nan)


def smooth(a, b, value):
    t = np.clip((value - a) / (b - a), 0., 1.)
    return t * t * (3. - 2. * t)


def encode(*channels):
    bytes_rgba = np.rint(255 * np.clip(np.stack(channels, axis=-1), 0., 1.))
    return Image.fromarray(bytes_rgba.astype(np.uint8), 'RGBA')


def convert(cache, output, download=False):
    sampled = {}
    for short, (url, variable) in SOURCES.items():
        path = cache / (short + '.nc')
        if download and not path.is_file():
            cache.mkdir(parents=True, exist_ok=True)
            urlretrieve(url, path)
        dataset = field(path, short, variable)
        sampled[short] = sample(dataset, angular_grid(dataset[3]))
        del dataset
    mask, top, tau, vis, ir = (sampled[k] for k in ('ACMC', 'ACHAC', 'CODC', 'CMI1', 'CMI13'))
    valid_top = np.isfinite(top)
    valid_tau = np.isfinite(tau)
    # Map the four measured mask confidence levels after reprojection.
    presence = np.interp(np.nan_to_num(mask), [0., 1., 2., 3.], [0., 0.025, 0.57, 1.])
    visible = np.nan_to_num(vis)
    # Band-1 reflectance is not optical depth. Subtract the local clear-water
    # brightness (including ocean haze/glint) from the visible signal to use
    # it as a rendering-only opacity proxy wherever the COD is not usable.
    clear_weight = (1. - smooth(.62, 1.42, np.nan_to_num(mask))) * np.isfinite(vis)
    background = gaussian_filter(visible * clear_weight, 17)
    weight = gaussian_filter(clear_weight.astype(np.float32), 17)
    ocean = np.where(weight > 0.021, background / np.maximum(0.021, weight), 0.063)
    reflective = np.maximum(0., visible - ocean)
    # Optically thin cloud must still register in the generated high deck.
    optical_strength = np.where(valid_tau, smooth(.8, 26., tau), smooth(.018, .36, reflective))
    optical_strength = np.nan_to_num(optical_strength)
    opacity = presence * (0.45 + 0.55 * optical_strength)

    height = np.nan_to_num(top)
    # Map the product's single retrieved top to one of the two visual
    # families, with a gradual overlap only to avoid abrupt transitions.
    # Bright high tops + cold band 13 signal permit a deep column recipe;
    # diffuse high tops become upper deck. The base is inferred by renderer.
    deep_brightness = np.where(valid_tau, smooth(10., 30., tau), smooth(.22, .57, reflective))
    cold = 1. - smooth(227., 264., np.nan_to_num(ir, nan=280.))
    deep = smooth(5500., 10000., height) * deep_brightness * (.45 + .55 * cold)
    upper = smooth(2900., 6250., height) * (1. - deep)
    upper = np.where(valid_top, upper, (1. - smooth(240., 273., np.nan_to_num(ir, nan=280.))) * 0.8)
    very_low = np.where(valid_top, smooth(80., 380., height), 1.)
    cov_lo = opacity * (1. - upper) * very_low
    cov_hi = opacity * upper
    type_lo = np.clip(.52 * smooth(1350., 5250., height) + .48 * deep, 0., 1.)
    # Stratocumulus weight: low-topped and of intermediate apparent opacity.
    stratocumulus = smooth(360., 900., height) * (1. - smooth(2300., 3550., height))
    stratocumulus *= np.where(valid_tau, smooth(2., 5., tau) * (1. - smooth(20., 29., tau)),
                             smooth(.04, .14, reflective) * (1. - smooth(.20, .37, reflective)))
    type_hi = smooth(.09, .36, reflective) * (.8 + .2 * (1. - smooth(6900., 10800., height)))
    softness = 0.25 + 0.60 * optical_strength
    # Top codes remain available in neighboring texels so linear filtering
    # does not pull measurable cloud edges spuriously down to the water.
    encoded_top = np.where(valid_top, np.maximum(1., np.rint(255 * height / TOP_RANGE_M)) / 255., 0.)
    output.mkdir(parents=True, exist_ok=True)
    encode(cov_lo, type_lo, stratocumulus, encoded_top).save(output / 'weather-lo.png', optimize=True)
    encode(cov_hi, type_hi, encoded_top, softness).save(output / 'weather-hi.png', optimize=True)
    # A tone curve only. Original measured ABI band 1, not the masks or an
    # RGB/artificial weather composite. Same projection/crop as Lo and Hi.
    display = np.clip(visible / .90, 0., 1.) ** .68
    Image.fromarray(np.rint(255 * display).astype(np.uint8), 'L').save(
        output / 'satellite.jpg', quality=93, optimize=True)
    cloudy = np.nan_to_num(mask) >= 1.5
    for label, fraction in [('cloud mask', cloudy.mean()),
                            ('measured top among cloudy', valid_top[cloudy].mean()),
                            ('retained COD among cloudy', valid_tau[cloudy].mean()),
                            ('noticeable Lo', (cov_lo >= .36).mean()),
                            ('noticeable Hi', (cov_hi >= .36).mean()),
                            ('deepest Lo', ((cov_lo >= .36) & (height >= 8500)).mean())]:
        print(f'{label}: {fraction:.1%}')
    return cov_lo, cov_hi, height


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cache', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).parent)
    parser.add_argument('--download', action='store_true')
    args = parser.parse_args()
    convert(args.cache, args.output, args.download)
