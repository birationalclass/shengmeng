// One draw per page environment, independent of clock, weather and wind integration.
// Translating the existing noise field changes cloud arrangement without regenerating textures.
export function createCloudLayout(random=Math.random){return Object.freeze({x:(random()-.5)*256,z:(random()-.5)*256});}
