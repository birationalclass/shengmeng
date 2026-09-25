import bpy, math, json, struct, gzip
from pathlib import Path
import numpy as np
from mathutils.bvhtree import BVHTree
# Quantized 1 mm positions + triangle indices; frame topology is independent.
manifest={'version':1,'solver':'Blender Mantaflow FLIP/PIC','resolution':RES,
          'fps':12,'sourceFps':24,'duration':(FRAMES-1)/24,
          'bounds':[[0,-2.5,-1.8],[12,2.5,2.7]],'origin':[0,-2.5,-1.8],
          'quantization':.001,'frames':[],'reference':'https://www.youtube.com/watch?v=ok1ViHVcXYs',
          'note':'Small simulation study, not the FLIP Fluids addon or a finished photoreal replica.'}
for frame in range(1,FRAMES+1,2):
    scene.frame_set(frame)
    dg=bpy.context.evaluated_depsgraph_get();ev=domain.evaluated_get(dg)
    mesh=ev.to_mesh();mesh.calc_loop_triangles()
    p=np.empty(len(mesh.vertices)*3,dtype=np.float32);mesh.vertices.foreach_get('co',p)
    p=p.reshape(-1,3)
    matrix=np.array(ev.matrix_world,dtype=np.float32)
    p=p@matrix[:3,:3].T+matrix[:3,3]
    q=np.rint((p-np.array(manifest['origin']))/.001).clip(0,65535).astype('<u2')
    idx=np.empty(len(mesh.loop_triangles)*3,dtype='<u4');mesh.loop_triangles.foreach_get('vertices',idx)
    particles=[]
    surface=BVHTree.FromPolygons(p.tolist(),idx.reshape(-1,3).tolist(),all_triangles=True)
    for ob in scene.objects:
        for ps in ob.evaluated_get(dg).particle_systems:
            if ps.settings.type not in {'FOAM','SPRAY'}: continue
            stride=max(1,math.ceil(len(ps.particles)/16000))
            for n in range(0,len(ps.particles),stride):
                part=ps.particles[n]
                if part.alive_state!='ALIVE': continue
                point=part.location
                if ps.settings.type=='FOAM':
                    # Reconstructed mesh extends beyond the particle surface.
                    # Attach foam to nearby exposed liquid, not submerged cells.
                    hit,normal,face,distance=surface.find_nearest(point)
                    if hit is None or normal.z<.15 or distance>.24: continue
                    point=hit+normal*.018
                particles.append(tuple(point))
    # Deterministic reduction bounds browser memory while preserving distribution.
    particles=particles[::max(1,math.ceil(len(particles)/12000))]
    pp=np.asarray(particles,dtype='<f4').reshape(-1,3)
    name=f'frame-{frame:04}.bin.gz'
    with gzip.open(OUT/name,'wb',compresslevel=6) as f:
        f.write(struct.pack('<III',len(p),len(idx),len(pp)))
        f.write(q.tobytes());f.write(idx.tobytes());f.write(pp.tobytes())
    manifest['frames'].append({'file':name,'frame':frame,'vertices':len(p),'triangles':len(idx)//3,'particles':len(pp)})
    ev.to_mesh_clear()
    print('EXPORTED',frame,len(p),len(idx)//3,len(pp),flush=True)
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf8')
print('EXPORT_FINISHED',flush=True)
