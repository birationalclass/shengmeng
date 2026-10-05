from pathlib import Path
import re,json,hashlib,zipfile,datetime
import argparse
parser=argparse.ArgumentParser(description='Export kernel-checked Linear proof evidence.')
parser.add_argument('--build-log',type=Path,required=True)
parser.add_argument('--axiom-log',type=Path,required=True)
parser.add_argument('--full-audit',type=Path,required=True)
args=parser.parse_args()
root=Path(__file__).resolve().parents[1];source=root/'source'
axiom=args.axiom_log.read_text();build=args.build_log.read_text()
full_audit=json.loads(args.full_audit.read_text())
assert full_audit['ok'] and full_audit['audited']>0
assert full_audit['root']=='Linear' and full_audit['violations']==[]
(root/'full-audit.json').write_text(json.dumps(full_audit,indent=2)+'\n')
assert 'Build completed successfully' in build
assert 'sorryAx' not in axiom and 'error:' not in axiom
files=[];decls={}
for file in sorted(source.rglob('*.lean')):
 if '.lake' in file.parts:continue
 text=file.read_text(); rel=str(file.relative_to(source));files.append({'path':rel,'sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'lineCount':len(text.splitlines())})
 for m in re.finditer(r'^(?:@\[simp\] )?theorem\s+(\w+)',text,re.M):
  name=m.group(1);stop=re.search(r'\n/--|\nend LinearStudy',text[m.end():]);end=m.end()+stop.start() if stop else len(text)
  ax=re.search(r"'LinearStudy\."+name+r"' depends on axioms: \[([^\]]*)\]",axiom)
  noax="'LinearStudy."+name+"' does not depend on any axioms" in axiom
  assert ax or noax,name
  axioms=[] if noax else [x.strip() for x in ax.group(1).split(',')]
  assert set(axioms)<= {'propext','Classical.choice','Quot.sound'}
  decls[name]={'path':rel,'line':text[:m.start()].count('\n')+1,'code':text[m.start():end].strip(),'axioms':axioms,'verified':True}
snapshot={'checkedAt':datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).isoformat(timespec='minutes'),'lean':'4.35.0-rc3','mathlib':'2a885768dae569d938bb9ff3474da6a8753bb90a','mainTheoremVerified':False,'targetDefinition':'LinearStudy.Lemma31Goal','scope':'The algebraic helper theorems are verified; complete-intersection pairing existence, Jacobian identification, and arbitrary parameter-lift compatibility remain open.','files':files,'declarations':decls}
(root/'snapshot.json').write_text(json.dumps(snapshot,indent=2,ensure_ascii=False)+'\n')
(root/'verification.txt').write_text('LINEAR FORMALIZATION: LOCAL BUILD AND AXIOM AUDIT\nFull Lemma 3.1 is NOT yet proved. Lemma31Goal is a Prop definition.\n\n$ lake build\n'+build+'\n$ lake env lean CheckAxioms.lean\n'+axiom+'\n$ lake env axiom-audit --root Linear --json\n'+args.full_audit.read_text())
with zipfile.ZipFile(root/'linear-lean.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in source.rglob('*'):
  if f.is_file() and '.lake' not in f.parts:z.write(f,Path('linear')/f.relative_to(source))
print('Exported',len(decls),'audited theorem declarations; full goal open.')
