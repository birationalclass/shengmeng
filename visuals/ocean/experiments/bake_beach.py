"""Independent Mantaflow beach tank. Run with Blender --background --python.

This is a small reproduction study of the fluid/whitewater workflow, not the
video author's FLIP Fluids addon or assets. Output is a real changing-topology
surface cache for browser playback. Blender's Z-up is converted by the viewer.
"""
import bpy, math, os, sys, json, struct, gzip
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parent
WORK = Path(os.environ.get('OCEAN_BAKE_WORK', str(ROOT / 'work')))
OUT = ROOT / os.environ.get('OCEAN_VARIANT', 'beach-cache')
WORK.mkdir(parents=True, exist_ok=True)
OUT.mkdir(parents=True, exist_ok=True)
FRAMES = int(os.environ.get('OCEAN_FRAMES', '144'))
RES = int(os.environ.get('OCEAN_RESOLUTION', '80'))
if os.environ.get('OCEAN_EXPORT_ONLY') == '1':
    import runpy
    bpy.ops.wm.open_mainfile(filepath=str(WORK/'beach-tank.blend'))
    runpy.run_path(str(ROOT/'export_beach.py'), init_globals={'ROOT':ROOT,'OUT':OUT,'RES':RES,'FRAMES':FRAMES,'scene':bpy.context.scene,'domain':bpy.data.objects['Beach liquid domain']})
    sys.exit(0)
bpy.ops.wm.read_factory_settings(use_empty=True)
scene = bpy.context.scene
scene.render.fps = 24
scene.frame_start = 1
scene.frame_end = FRAMES
scene.gravity = (0, 0, -9.81)

def cube(name, lo, hi):
    bpy.ops.mesh.primitive_cube_add(location=tuple((a+b)/2 for a,b in zip(lo,hi)))
    ob=bpy.context.object; ob.name=name
    ob.dimensions=tuple(b-a for a,b in zip(lo,hi))
    bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)
    return ob

def wedge(name, x0, x1, bottom0, bottom1, top):
    verts=[(x0,-2.5,bottom0),(x1,-2.5,bottom1),(x1,2.5,bottom1),(x0,2.5,bottom0),
           (x0,-2.5,top),(x1,-2.5,top),(x1,2.5,top),(x0,2.5,top)]
    faces=[(3,2,1,0),(4,5,6,7),(0,1,5,4),(1,2,6,5),(2,3,7,6),(3,0,4,7)]
    mesh=bpy.data.meshes.new(name);mesh.from_pydata(verts,[],faces);mesh.update()
    ob=bpy.data.objects.new(name,mesh);scene.collection.objects.link(ob);return ob

domain=cube('Beach liquid domain',(0,-2.5,-1.8),(12,2.5,2.7))
mod=domain.modifiers.new('Mantaflow liquid','FLUID');mod.fluid_type='DOMAIN'
ds=mod.domain_settings;ds.domain_type='LIQUID'
ds.resolution_max=RES;ds.cache_type='ALL';ds.cache_frame_start=1;ds.cache_frame_end=FRAMES
ds.cache_directory=str(WORK/'cache');ds.cache_resumable=False
ds.use_mesh=True;ds.mesh_scale=2
ds.use_spray_particles=True;ds.use_foam_particles=True;ds.use_bubble_particles=True
ds.timesteps_min=2;ds.timesteps_max=6
ds.flip_ratio=.95

# Seabed rises 0.19 m per metre; the water contact is near x=9.1 m.
bed=wedge('Sloping sand',0,12,-2.3,-2.3,-1.7)
for v in bed.data.vertices:
    if v.co.z > -2: v.co.z=-1.7+.19*v.co.x
eff=bed.modifiers.new('Beach collision','FLUID');eff.fluid_type='EFFECTOR'
eff.effector_settings.surface_distance=.001

water=wedge('Initial water',.75,8.9,-1.7+.19*.75+.07,-1.7+.19*8.9+.02,.10)
flow=water.modifiers.new('Initial liquid volume','FLUID');flow.fluid_type='FLOW'
flow.flow_settings.flow_type='LIQUID';flow.flow_settings.flow_behavior='GEOMETRY'

paddle=cube('Wave paddle',(.05,-2.5,-1.8),(.7,2.5,1.5))
eff=paddle.modifiers.new('Moving paddle collision','FLUID');eff.fluid_type='EFFECTOR'
eff.effector_settings.surface_distance=.001
for frame in range(1,FRAMES+1):
    t=(frame-1)/24
    ramp=min(1.,t/.8)
    stroke=float(os.environ.get('OCEAN_PADDLE_STROKE','.62'))
    period=float(os.environ.get('OCEAN_PADDLE_PERIOD','2.1'))
    paddle.location.x=.375 + stroke*ramp*(.5-.5*math.cos(2*math.pi*t/period))
    paddle.keyframe_insert(data_path='location',frame=frame)
for ob in [bed,water,paddle]: ob.hide_render=True
bpy.context.view_layer.objects.active=domain
domain.select_set(True)
scene.frame_set(1)
bpy.ops.wm.save_as_mainfile(filepath=str(WORK/'beach-tank.blend'))
print('BAKE_START',RES,FRAMES,flush=True)
bpy.ops.fluid.bake_all()
print('BAKE_FINISHED',flush=True)
bpy.ops.wm.save_as_mainfile(filepath=str(WORK/'beach-tank.blend'))

import runpy
runpy.run_path(str(ROOT/'export_beach.py'), init_globals={'ROOT':ROOT,'OUT':OUT,'RES':RES,'FRAMES':FRAMES,'scene':scene,'domain':domain})
