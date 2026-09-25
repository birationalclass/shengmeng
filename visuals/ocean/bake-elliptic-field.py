"""Bake distance to curve polylines in metres; no filled interior.
Run with Python + numpy + Pillow. R/G store centimetres; linear decoding
commutes with texture filtering. Sample centres match GPU texel centres.
"""
from pathlib import Path
import numpy as np
from PIL import Image

N=4096
LO=np.array([-4096.,-8192.]); SIZE=16384.
axis=np.arange(N,dtype=np.float32)*SIZE/N+SIZE/N/2
field=np.full((N,N),400.**2,dtype=np.float32)
t=np.linspace(0,2*np.pi,2401)
x=(1-np.cos(t))/2
ring=np.column_stack((x,.5*np.sin(t)*np.sqrt(2-x)))*1000
t=np.linspace(-2,2,4001)
x=2+t*t
open_curve=np.column_stack((x,t*np.sqrt(x*(x-1))))*1000
for curve in (ring,open_curve):
    for a,b in zip(curve[:-1],curve[1:]):
        low=np.maximum(0,np.floor((np.minimum(a,b)-400-LO)*N/SIZE).astype(int))
        high=np.minimum(N,np.ceil((np.maximum(a,b)+400-LO)*N/SIZE).astype(int)+1)
        if np.any(high<=low):continue
        dx=axis[low[0]:high[0]][None,:]+LO[0]-a[0]
        dz=axis[low[1]:high[1]][:,None]+LO[1]-a[1]
        v=b-a
        s=np.clip((dx*v[0]+dz*v[1])/np.dot(v,v),0,1)
        dist=(dx-s*v[0])**2+(dz-s*v[1])**2
        target=field[low[1]:high[1],low[0]:high[0]]
        np.minimum(target,dist,out=target)
packed=np.rint(np.sqrt(field)*100).astype(np.uint16)
rgb=np.zeros((N,N,3),dtype=np.uint8)
rgb[:,:,0]=packed>>8;rgb[:,:,1]=packed&255
Image.fromarray(rgb).save(Path(__file__).with_name('elliptic-distance.png'))
print('Baked 4096² curve-distance field, 4 m texels, 0.01 m encoding.')
