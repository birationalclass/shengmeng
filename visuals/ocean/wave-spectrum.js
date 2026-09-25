// Independent discretization of the Pierson–Moskowitz spectrum. Phases and
// frequencies are fixed across frames; wind changes only energy and spreading.
// The output is normalized for this scene's visual wave-height control.
export function makeWaveSpectrum(wind=.45) {
  const g=9.81, bands=16, speed=3+12*Math.max(0,Math.min(1,wind));
  const components=[];
  const logStep=Math.log(120/.65)/(bands-1);
  for(let i=0;i<bands;i++) {
    const wavelength=120*Math.exp(-i*logStep),k=2*Math.PI/wavelength;
    const omega=Math.sqrt(g*k*Math.tanh(k*8));
    const omegaLow=Math.sqrt(g*k*Math.exp(-logStep/2));
    const omegaHigh=Math.sqrt(g*k*Math.exp(logStep/2));
    const density=.0081*g*g/Math.pow(omega,5)*Math.exp(-.74*Math.pow(g/(speed*omega),4));
    for(let j=0;j<2;j++) {
      const spread=(.15+.38*i/(bands-1))*(j===0?-1:1);
      const angle=.20+spread+Math.sin(i*2.399+j)*.12;
      const amplitude=Math.sqrt(Math.max(0,density*(omegaHigh-omegaLow)));
      components.push({x:Math.cos(angle),z:Math.sin(angle),k,omega,amplitude,phase:(i*2+j)*2.39996323+Math.sin(i*4.37+j)*2});
    }
  }
  const rms=Math.sqrt(components.reduce((sum,c)=>sum+c.amplitude*c.amplitude/2,0));
  const normalization=.17/Math.max(.0001,rms);
  for(const c of components)c.amplitude*=normalization;
  return components;
}
