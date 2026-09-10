// CSS design tokens are the single source for visual pacing.
export function visualMotion() {
 const css=getComputedStyle(document.documentElement);
 const milliseconds=name=>{
  const value=css.getPropertyValue(`--motion-${name}`).trim();
  return Number.parseFloat(value)*(value.endsWith('ms')?1:1000);
 };
 return {initial:{
  axis:milliseconds('initial-axis'),pop:milliseconds('initial-pop'),
  stagger:milliseconds('initial-stagger'),axisExit:milliseconds('initial-axis-exit'),
  arrow:milliseconds('initial-arrow')},
  emphasis:milliseconds('emphasis'),enter:milliseconds('enter'),
  exit:milliseconds('exit'),hold:milliseconds('hold'),
  easing:css.getPropertyValue('--motion-easing').trim(),
  reduced:matchMedia('(prefers-reduced-motion:reduce)').matches};
}
