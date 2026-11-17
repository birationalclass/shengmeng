// North is the first image row. World +x is east, +z is south (km).
// Lo RGBA: coverage, Cu→TCu→Cb, stratocumulus weight, top / 18 km.
// Hi RGBA: coverage, As→Ac, top / 18 km, opacity/edge proxy.
// The proxy types and the rendered cloud base are inferred; ACHA measured
// tops, ACM mask, COD, and visible/IR pixels come from the same ABI scan.
export const weatherData = Object.freeze({
  spanKm: 600,
  centerLat: 26,
  centerLon: -86,
  observedAt: '2025-06-03T18:01:17Z',
  label: 'GOES-19 ABI · 墨西哥湾',
  detail: '2025-06-03 18:01:17 UTC · 26°N 86°W · 600 × 600 km',
  notes: '覆盖与云顶取自同步卫星产品；云底和云型按云顶与反射率估计。光学厚度质量不足处使用可见光反射率作为渲染线索。',
  sourceUrl: 'https://www.ncei.noaa.gov/products/goes-terrestrial-weather-abi-glm',
  start: Object.freeze({ x: -45, z: 56, yaw: 2.80 }),
});
