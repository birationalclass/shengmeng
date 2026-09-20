import bpy, math, random, json, sys
from pathlib import Path
from mathutils import Vector, Matrix
R=Path(__file__).resolve().parent
random.seed(26)
bpy.ops.object.select_all(action='SELECT');bpy.ops.object.delete(use_global=False)
bpy.context.preferences.filepaths.save_version=0
# Each architectural category is one mesh, retaining physically modelled detailing.
materials={}; batches={}
def mat(name,color,rough=.6,metal=0):
 m=bpy.data.materials.new(name);m.diffuse_color=(*color,1);m.use_nodes=True;p=m.node_tree.nodes.get('Principled BSDF');p.inputs['Base Color'].default_value=(*color,1);p.inputs['Roughness'].default_value=rough;p.inputs['Metallic'].default_value=metal;materials[name]=m;return name
stone=mat('Warm weathered limestone',(.43,.40,.32),.91)
lightstone=mat('Stone balustrades',(.64,.61,.50),.82)
red=mat('Cinnabar timber',(.30,.036,.018),.52)
dark=mat('Deep timber recess',(.045,.033,.023),.78)
green=mat('Jade painted bracket sets',(.035,.15,.115),.43)
blue=mat('Indigo beam painting',(.024,.065,.11),.51)
gold=mat('Ochre glazed tile',(.53,.29,.058),.32,.12)
ridge=mat('Sunlit tile rolls',(.67,.39,.085),.30,.13)
soil=mat('Forest earth',(.115,.135,.071),1)
watermat=mat('Lake water',(.07,.17,.18),.18,.4)
for name in [stone,lightstone,red,gold,ridge,soil]:
 m=materials[name];n=m.node_tree.nodes;l=m.node_tree.links;p=n.get('Principled BSDF');noise=n.new('ShaderNodeTexNoise');noise.inputs['Scale'].default_value=5 if name in [stone,soil] else 24;noise.inputs['Detail'].default_value=3
 bump=n.new('ShaderNodeBump');bump.inputs['Strength'].default_value=.2;bump.inputs['Distance'].default_value=.075 if name in [stone,soil] else .012;l.new(noise.outputs['Fac'],bump.inputs['Height']);l.new(bump.outputs['Normal'],p.inputs['Normal'])
def mesh(name,vs,fs,ma):
 if name not in batches:batches[name]=[[],[],ma]
 v,f,_=batches[name];off=len(v);v.extend(vs);f.extend([tuple(off+i for i in face) for face in fs])
def box(name,c,s,ma,angle=0):
 x,y,z=c;a,b,h=[v/2 for v in s];vs=[]
 for dz in [-h,h]:
  for dx,dy in [(-a,-b),(a,-b),(a,b),(-a,b)]:vs.append((x+dx*math.cos(angle)-dy*math.sin(angle),y+dx*math.sin(angle)+dy*math.cos(angle),z+dz))
 mesh(name,vs,[(0,3,2,1),(4,5,6,7),(0,1,5,4),(1,2,6,5),(2,3,7,6),(3,0,4,7)],ma)
def tube(name,a,b,r,ma,n=8):
 a,b=Vector(a),Vector(b);d=(b-a).normalized();u=d.cross(Vector((0,0,1)))
 if u.length<.01:u=d.cross(Vector((0,1,0)))
 u.normalize();v=d.cross(u);vs=[tuple(p+r*(math.cos(t*math.tau/n)*u+math.sin(t*math.tau/n)*v)) for p in [a,b] for t in range(n)]
 fs=[tuple(reversed(range(n))),tuple(range(n,2*n))]+[(i,(i+1)%n,(i+1)%n+n,i+n) for i in range(n)];mesh(name,vs,fs,ma)
def ring(name,r,z,h,ma,c=(0,5),n=8):
 vs=[(c[0]+r*math.cos(math.tau*i/n+math.pi/8),c[1]+r*math.sin(math.tau*i/n+math.pi/8),zz) for zz in [z,z+h] for i in range(n)]
 mesh(name,vs,[tuple(reversed(range(n))),tuple(range(n,2*n))]+[(i,(i+1)%n,(i+1)%n+n,i+n) for i in range(n)],ma)
def rail(a,b,z,ma=lightstone):
 a,b=Vector((*a,z)),Vector((*b,z));length=(b-a).length;num=max(2,int(length/.75))
 for i in range(num+1):
  q=a.lerp(b,i/num);box('Carved rail posts',tuple(q+Vector((0,0,.52))),(.14,.14,1.04),ma);tube('Rail finials',tuple(q+Vector((0,0,1.04))),tuple(q+Vector((0,0,1.15))),.13,ma)
 for h in [.32,.88]:tube('Continuous handrails',tuple(a+Vector((0,0,h))),tuple(b+Vector((0,0,h))),.065,ma)
def octrail(r,z):
 for i in range(8):
  a=math.pi/8+i*math.tau/8;b=a+math.tau/8;rail((r*math.cos(a),5+r*math.sin(a)),(r*math.cos(b),5+r*math.sin(b)),z)
def roof_oct(r,z,h,inner=.65):
 # Swept concave roof surface, raised hip corners, separate tile rolls and eave caps.
 for side in range(8):
  a=math.pi/8+side*math.tau/8;b=a+math.tau/8
  def p(u,t):
   rr=inner+(r-inner)*t;dx=(1-u)*math.cos(a)+u*math.cos(b);dy=(1-u)*math.sin(a)+u*math.sin(b)
   zz=z+h*(1-t)**1.65+.38*t**7*(abs(2*u-1)**3)
   return (rr*dx,5+rr*dy,zz)
  vs=[p(i/16,j/12) for j in range(13) for i in range(17)];fs=[]
  for j in range(12):
   for i in range(16):k=j*17+i;fs.append((k,k+1,k+18,k+17))
  mesh('Eight curved tiled roof faces',vs,fs,gold)
  for i in range(25):
   u=i/24
   for j in range(12):
    aa=Vector(p(u,j/12))+Vector((0,0,.045));bb=Vector(p(u,(j+1)/12))+Vector((0,0,.045));tube('Individual radial tile rolls',aa,bb,.043,ridge,6)
  for j in range(12):tube('Raised roof hip ridges',p(0,j/12),p(0,(j+1)/12),.115,ridge)
  for i in range(24):tube('Scalloped eave trim',p(i/24,1),p((i+1)/24,1),.10,green)
  # Eave end ornaments, geometrically modelled.
  end=Vector(p(0,1));tube('Upturned eave ornaments',end,end+Vector((math.cos(a)*.23,math.sin(a)*.23,.48)),.09,ridge)
def pavilion_floor(r,z,h):
 ring('Octagonal dark interior',r*.88,z,h,dark)
 ring('Vermilion floor skirt',r,z,.24,red)
 for side in range(8):
  a=math.pi/8+side*math.tau/8;b=a+math.tau/8;A=Vector((r*math.cos(a),5+r*math.sin(a),z));B=Vector((r*math.cos(b),5+r*math.sin(b),z));t=(B-A).normalized();normal=Vector(((A.x+B.x)/2,(A.y+B.y)/2-5,0)).normalized();ang=math.atan2(t.y,t.x)
  for u in [0,.333,.667]:
   q=A.lerp(B,u);tube('Red octagonal columns',q,q+Vector((0,0,h)),.13,red,12)
   for level in range(3):
    qc=q+normal*(.15+level*.14)+Vector((0,0,h-.35+level*.13));box('Interlocking jade dougong',qc,(.58+level*.16,.23,.13),green,ang)
  mid=(A+B)/2+Vector((0,0,h-.22));box('Painted beam bands',mid,((B-A).length,.22,.36),blue,ang)
  for u in [i/18 for i in range(1,18)]:
   q=A.lerp(B,u)+normal*.018;tube('Lattice window mullions',q+Vector((0,0,.48)),q+Vector((0,0,h-.6)),.026,red,6)
  for hh in [.55,1.25,h-.7]:tube('Lattice horizontal rails',A+Vector((0,0,hh)),B+Vector((0,0,hh)),.028,ridge,6)

def hall(cx,cy,z,w,d,h):
 box('Hall shadow interiors',(cx,cy,z+h/2),(w,d,h),dark)
 box('Hall stone plinths',(cx,cy,z-.18),(w+1,d+1,.36),lightstone)
 for x in [cx-w/2+i*w/10 for i in range(11)]:
  for y in [cy-d/2-.12,cy+d/2+.12]:tube('Hall red colonnades',(x,y,z),(x,y,z+h),.12,red)
 for y in [cy-d/2-.12,cy+d/2+.12]:
  box('Hall painted lintels',(cx,y,z+h-.18),(w+.5,.24,.35),green)
  for x in [cx-w/2+i*w/30 for i in range(31)]:box('Hall lattice screens',(x,y,z+h*.47),(.035,.08,h*.65),red)
 # Four sloping roof faces, double sweeping front/back with turned corners.
 for sign in [-1,1]:
  def p(u,t):
   xx=cx+(u-.5)*(w+2.4*t);yy=cy+sign*(d/2+1)*t;zz=z+h+1.7*(1-t)**1.6+.34*t**8*abs(2*u-1)**4
   return xx,yy,zz
  vs=[p(i/40,j/10) for j in range(11) for i in range(41)];fs=[]
  for j in range(10):
   for i in range(40):k=j*41+i;fs.append((k,k+1,k+42,k+41))
  mesh('Hall sweeping gold roofs',vs,fs,gold)
  for i in range(int(w/.24)+1):
   u=i/int(w/.24)
   for j in range(10):tube('Hall roof tile rolls',p(u,j/10),p(u,(j+1)/10),.043,ridge,6)
  for u in [0,1]:
   for j in range(10):tube('Hall roof edge ridges',p(u,j/10),p(u,(j+1)/10),.09,ridge)
  tube('Hall eave fascia',p(0,1),p(1,1),.12,green)
 tube('Hall main ridge',(cx-w/2,cy,z+h+1.74),(cx+w/2,cy,z+h+1.74),.16,ridge)

def height(x,y):return max(-.4,14*math.exp(-(x/52)**2-((y-12)/29)**2)+.8*math.sin(x*.16)*math.cos(y*.15)-1.2)
vs=[];fs=[];nx=100;ny=65
for j in range(ny+1):
 y=-32+j*1.3
 for i in range(nx+1):x=-80+i*1.6;vs.append((x,y,height(x,y)))
for j in range(ny):
 for i in range(nx):k=j*(nx+1)+i;fs.append((k,k+1,k+nx+2,k+nx+1))
mesh('Rolling forested hill',vs,fs,soil)
box('Lake basin',(0,-94,-.65),(360,128,.7),watermat)
box('Lakeside granite embankment',(0,-32,0),(160,1.3,1.7),stone)
rail((-78,-32.8),(78,-32.8),.8)
# Monumental rectangular base with individual masonry courses and perimeter terrace.
box('Great stone terrace core',(0,4,8.3),(25,21,13.4),stone)
for row in range(26):
 z=1.7+row*.5
 for col in range(21):
  x=-12.4+col*1.2+(.6 if row%2 else 0)
  if x<12.4:box('Terrace ashlar joints',(x,-6.53,z),(1.17,.10,.475),stone)
box('Upper terrace cornice',(0,4,15.15),(26,22,.42),lightstone)
for a,b in [((-13,-7),(13,-7)),((-13,-7),(-13,15)),((13,-7),(13,15)),((-13,15),(13,15))]:rail(a,b,15.36)
# Iconic diagonal exterior stairs on the front face.
for side in [-1,1]:
 for i in range(35):
  x=side*(11.8-i*.31);z=4.0+i*.28
  box('Diagonal terrace stone steps',(x,-7.35,z),(.34,1.5,.30),lightstone)
 for dz in [0,.9]:tube('Diagonal stair parapets',(side*11.9,-8.12,4.2+dz),(side*1.1,-8.12,13.75+dz),.16,stone)
# Four nested eaves above three principal octagonal storeys.
ring('Tower octagonal podium',7.3,15.4,.8,lightstone);octrail(7.1,16.2)
for r,z,h in [(5.7,16.3,3.5),(4.8,21.3,3.1),(4.0,25.9,2.9)]:
 pavilion_floor(r,z,h);roof_oct(r+1.65,z+h-.05,1.8,inner=r*.67)
 ring('Upper veranda decks',r+.55,z-.08,.19,green)
 octrail(r+.5,z+.1)
roof_oct(4.7,30.1,3.8,.2)
for z,r,h in [(33.6,.37,.40),(34,.24,.7),(34.7,.1,.8)]:tube('Gilded crowning finial',(0,5,z),(0,5,z+h),r,ridge,16)
# Descending ceremonial axis and side precincts.
for cy,z,w,d,h in [(-11,3.4,19,6,3.1),(-21,1.3,24,6,3.0),(-29,.85,14,3,2.7)]:hall(0,cy,z,w,d,h)
for side in [-1,1]:
 box('Flanking terrace walls',(side*25,0,7),(15,15,7.5),stone)
 for xx in [side*20,side*29]:hall(xx,0,10.8,5.5,4,2.3)
 for x in range(-70,71,5):
  if side==1:break
  # Lakefront long corridor.
  hall(x,-30,1.0,4.9,2,1.9)
# Side stairs and paths linking lower halls.
for side in [-1,1]:
 for i in range(22):box('Axis side stair treads',(side*12,-23+i*.46,1.05+i*.15),(2,.46,.19),lightstone)
# Commit geometry to category meshes.
for name,(vs,fs,ma) in batches.items():
 me=bpy.data.meshes.new(name);me.from_pydata(vs,[],fs);me.materials.append(materials[ma]);ob=bpy.data.objects.new(name,me);bpy.context.collection.objects.link(ob)
print('ARCHITECTURE_READY',len(bpy.data.objects),flush=True)
# Reuse a CC0 scanned tree mesh with linked instances. All foliage is actual geometry.
asset=R.parent/'courtyard-study/assets/island_tree_01'
with bpy.data.libraries.load(str(asset/'island_tree_01.blend'),link=False) as (a,b):b.objects=[n for n in a.objects if n=='island_tree_01_LOD1']
tree=b.objects[0];bpy.context.collection.objects.link(tree)
for im in bpy.data.images:
 p=asset/'textures'/Path(im.filepath).name
 if p.exists():im.filepath=str(p);im.reload()
bpy.context.view_layer.objects.active=tree;tree.select_set(True)
for mod in list(tree.modifiers):tree.modifiers.remove(mod)
if len(tree.data.polygons)>100000:
 mod=tree.modifiers.new('Forest render LOD','DECIMATE');mod.ratio=100000/len(tree.data.polygons);bpy.ops.object.modifier_apply(modifier=mod.name)
coords=[tree.matrix_world@Vector(v) for v in tree.bound_box];lo=Vector([min(v[i] for v in coords) for i in range(3)]);hi=Vector([max(v[i] for v in coords) for i in range(3)]);anchor=Vector(((lo.x+hi.x)/2,(lo.y+hi.y)/2,lo.z));source=tree.matrix_world.copy()
placed=0
for j in range(13):
 for i in range(29):
  x=-73+i*5.2+random.uniform(-2,2);y=-25+j*5.7+random.uniform(-2,2)
  if abs(x)<17 and y<19:continue
  if 15<abs(x)<34 and -9<y<11:continue
  h=random.uniform(5.3,10.2);sc=h/max(.1,hi.z-lo.z)
  ob=tree.copy();ob.data=tree.data;ob.name='Forest scanned tree %03d'%placed;bpy.context.collection.objects.link(ob)
  ob.matrix_world=Matrix.Translation(Vector((x,y,height(x,y)-.18)))@Matrix.Rotation(random.random()*math.tau,4,'Z')@Matrix.Scale(sc,4)@Matrix.Translation(-anchor)@source;placed+=1
bpy.data.objects.remove(tree,do_unlink=True)
print('FOREST_READY',placed,flush=True)
# Lighting, camera and physically based still render.
world=bpy.data.worlds.new('Late afternoon clear sky');bpy.context.scene.world=world;world.use_nodes=True;n=world.node_tree.nodes;l=world.node_tree.links;sky=n.new('ShaderNodeTexSky');sky.sky_type='NISHITA';sky.sun_elevation=math.radians(25);sky.sun_rotation=math.radians(135);sky.air_density=1.15;sky.dust_density=1.2;n.get('Background').inputs['Color'].default_value=(.40,.58,.80,1);n.get('Background').inputs['Strength'].default_value=.7
bpy.ops.object.light_add(type='SUN',location=(-50,-70,90));bpy.context.object.name='Warm afternoon sunlight';bpy.context.object.rotation_euler=(math.radians(28),math.radians(-25),math.radians(-30));bpy.context.object.data.energy=3.0;bpy.context.object.data.angle=math.radians(3)
bpy.ops.object.camera_add(location=(22,-155,39));cam=bpy.context.object;cam.rotation_euler=(Vector((0,1,14))-cam.location).to_track_quat('-Z','Y').to_euler();cam.data.lens=53;bpy.context.scene.camera=cam
scene=bpy.context.scene;scene.render.engine='CYCLES';scene.cycles.samples=64;scene.cycles.use_denoising=True;scene.cycles.max_bounces=7
try:
 prefs=bpy.context.preferences.addons['cycles'].preferences;prefs.compute_device_type='METAL';prefs.get_devices()
 for dev in prefs.devices:dev.use=dev.type=='METAL'
 scene.cycles.device='GPU'
except:pass
scene.render.resolution_x=1440;scene.render.resolution_y=960;scene.render.resolution_percentage=100;scene.view_settings.view_transform='AgX';scene.view_settings.exposure=.65
# Add gentle wind ripples to the actual lake, kept separate from web reflection shader.
m=materials[watermat];p=m.node_tree.nodes.get('Principled BSDF');p.inputs['IOR'].default_value=1.333;p.inputs['Metallic'].default_value=.0;p.inputs['Transmission Weight'].default_value=.35
n=m.node_tree.nodes;l=m.node_tree.links;noise=n.new('ShaderNodeTexNoise');noise.inputs['Scale'].default_value=2.1;noise.inputs['Detail'].default_value=2;bump=n.new('ShaderNodeBump');bump.inputs['Strength'].default_value=.13;bump.inputs['Distance'].default_value=.045;l.new(noise.outputs['Fac'],bump.inputs['Height']);l.new(bump.outputs['Normal'],p.inputs['Normal'])
bpy.ops.wm.save_as_mainfile(filepath=str(R/'foxiang.blend'))
scene.render.filepath=str(R/'preview.png');bpy.ops.render.render(write_still=True)
print('RENDER_DONE',flush=True)
# A separate browser LOD reduces forest geometry while preserving the editable render scene.
forest=[o for o in bpy.data.objects if o.name.startswith('Forest scanned tree')]
if forest:
 ob=forest[0];ob.data=ob.data.copy();bpy.context.view_layer.objects.active=ob
 mod=ob.modifiers.new('Browser forest LOD','DECIMATE');mod.ratio=.36;bpy.ops.object.modifier_apply(modifier=mod.name)
 for other in forest[1:]:other.data=ob.data
# Export browser geometry; scan texture maps are retained, procedural micro-bump is simplified.
for im in bpy.data.images:
 if im.has_data and max(im.size)>1024:
  w,h=im.size;im.scale(round(w*1024/max(w,h)),round(h*1024/max(w,h)))
bpy.ops.object.select_all(action='DESELECT')
for ob in scene.objects:
 if ob.type=='MESH' and ob.name!='Lake basin':ob.select_set(True)
bpy.ops.export_scene.gltf(filepath=str(R/'foxiang.glb'),export_format='GLB',use_selection=True,export_apply=True,export_gpu_instances=True,export_draco_mesh_compression_enable=True,export_draco_mesh_compression_level=6,export_cameras=False,export_lights=False)
print('EXPORT_DONE',flush=True)
