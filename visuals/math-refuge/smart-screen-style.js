export const SCREEN_FONT='"Segoe UI", "Microsoft YaHei", system-ui, sans-serif';
export const SCREEN_MONO='Consolas, "Cascadia Mono", monospace';
export const SCREEN_COLORS={text:'#d4edf0',active:'#85d3df',muted:'#91acb1'};
export const CONTROL_VISUAL_SCALE=.9;
export function beginControlInk(ctx){
 ctx.save();ctx.translate(64,64);ctx.scale(CONTROL_VISUAL_SCALE,CONTROL_VISUAL_SCALE);ctx.translate(-64,-64);
}
