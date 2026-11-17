// NASA GIBS Aqua daily visible mosaic and MODIS displayed retrieval bins
// from the place/date the reference author identified on Zoom Earth.
export const javaWeatherData = Object.freeze({
  spanKm: 600,
  centerLat: -11.064902,
  centerLon: 108.672016,
  observedAt: '2026-06-19',
  label: 'MODIS / Aqua · 爪哇岛以南',
  detail: '2026-06-19 午后 · 11.06°S 108.67°E · 约 600 × 600 km',
  notes: '使用 NASA GIBS 同日同海域影像重建。云顶与光学厚度取公开图层区间，云型和云底由模型估计。',
  sourceUrl: 'https://worldview.earthdata.nasa.gov/?v=105.91,-13.76,111.43,-8.36&t=2026-06-19&l=MODIS_Aqua_CorrectedReflectance_TrueColor',
  referenceUrl: 'https://zoom.earth/maps/satellite-hd/#view=-11.064902,108.672016,9z/date=2026-06-19,pm',
  lowTexture: 'weather-lo-java.png',
  highTexture: 'weather-hi-java.png',
  preview: 'satellite-java.jpg',
  start: Object.freeze({ x: 39, z: -61, yaw: 2.09 }),
});
