from pathlib import Path
import numpy as np
import soundfile as sf
from scipy.signal import butter,sosfilt,fftconvolve
import sys,json
source,target=sys.argv[1:]
x,sr=sf.read(source,always_2d=True);x=x.mean(axis=1)
# Preserve the low speaking voice and sibilants while removing subsonic rumble.
x=sosfilt(butter(2,65,fs=sr,btype='highpass',output='sos'),x)
x=sosfilt(butter(2,8500,fs=sr,btype='lowpass',output='sos'),x)
x[:int(.025*sr)]*=np.linspace(0,1,int(.025*sr))
x[-int(.16*sr):]*=np.linspace(1,0,int(.16*sr))
# A clear central voice with distant, asymmetric rock-face reflections.
n=int(4.4*sr);t=np.arange(n)/sr;stereo=[]
for ch in range(2):
    rng=np.random.default_rng(826+ch)
    noise=sosfilt(butter(2,3900,fs=sr,btype='lowpass',output='sos'),rng.normal(size=n))
    envelope=np.exp(-6.908*t/3.2)*np.minimum(np.maximum((t-.12)/.15,0),1)
    diffuse=noise*envelope
    diffuse*=.28/np.sqrt(np.sum(diffuse**2))
    taps=[(.27,.30),(.57,.22),(1.06,.14),(1.59,.08),(2.27,.035)] if ch==0 else [(.39,.28),(.76,.21),(1.22,.13),(1.87,.065),(2.51,.03)]
    # Low-pass discrete echoes to suggest distance; do not smear consonants in the direct voice.
    reflected=np.zeros(n)
    for delay,gain in taps:reflected[round(delay*sr)]+=gain
    reflected=sosfilt(butter(1,4700,fs=sr,btype='lowpass',output='sos'),reflected)
    wet=fftconvolve(x,reflected+diffuse)
    dry=np.pad(x,(0,len(wet)-len(x)))
    stereo.append(dry+.88*wet)
y=np.column_stack(stereo);y[-round(.8*sr):]*=np.linspace(1,0,round(.8*sr))[:,None]
sf.write(target,y,sr,subtype='FLOAT')
print(json.dumps({'sample_rate':sr,'seconds':len(y)/sr,'dry_peak':float(np.max(np.abs(x))),'render_peak':float(np.max(np.abs(y))),'stereo_correlation':float(np.corrcoef(y.T)[0,1])},indent=2))
