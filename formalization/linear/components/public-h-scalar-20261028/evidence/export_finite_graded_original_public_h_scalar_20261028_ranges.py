from pathlib import Path
import os,sys,json,hashlib,datetime
from zoneinfo import ZoneInfo
r=Path('D:/codex/Math/formalization/linear');os.chdir(r);sys.path.insert(0,str(r));from lean_runner import run_file
res=r/'research';cid='finite-graded-original-public-h-scalar-20261028';sha=lambda b:hashlib.sha256(b).hexdigest();iv=json.loads((res/(cid+'-closed-source-inventory.json')).read_text(encoding='utf-8'));sources=iv['closedSourceHashes'];mods=sorted(sources);cache=Path('D:/codex/Lean/negativity/.lake/packages');env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONIOENCODING']='utf-8';env['LEAN_PATH']=os.pathsep.join([str(r/'.lake/build/lib/lean')]+[str(p/'.lake/build/lib/lean') for p in cache.iterdir() if p.is_dir()]);found={};deps={};parts=[];allLogs=[]
import copy
priorRecords=[res/'finite-graded-original-actual-h-scalar-20261028-all-source-ranges.verification.json',res/'finite-graded-original-scalar-cech-20261028-all-source-ranges.verification.json',res/'finite-graded-specified-top-naturality-20261027-all-source-ranges.verification.json',res/'finite-graded-coefficient-naturality-20261027-all-source-ranges.verification.json',res/'arbitrary-finite-graded-actual-top-duality-20261027-all-source-ranges.verification.json'];reusedRecords=[];reusable={}
for priorp in priorRecords:
 prior=json.loads(priorp.read_text(encoding='utf-8'))
 if 'parts' not in prior:
  assert prior['accepted'] and prior['returnCode']==0 and prior['resourceRecord']['artifacts_accepted'] and prior['resourceRecord']['status']=='passed'
  prior['parts']=[{k:prior[k] for k in ['accepted','returnCode','source','sourceSha256','log','logSha256','resource','resourceRecord']}]
  prior['parts'][0].update(selectedModules=sorted(prior['closedSourceHashes']),allSourceHashes=prior['closedSourceHashes'],originalVerificationWasSingleAcceptedControllerRun=True)
  prior['allPartitionsAccepted']=True;prior['sequentialOnly']=True
 assert prior['accepted'] and prior['allPartitionsAccepted'] and prior['sequentialOnly']
 selected={m:h for m,h in sources.items() if m not in reusable and prior['closedSourceHashes'].get(m)==h}
 if not selected:continue
 for m,h in selected.items():assert sha((r/(m.replace('.','/')+'.lean')).read_bytes())==h
 assert sha(Path(prior['source']).read_bytes())==prior['sourceSha256'] and sha(Path(prior['log']).read_bytes())==prior['logSha256']
 for part0 in prior['parts']:
  assert part0['accepted'] and part0['returnCode']==0 and part0['resourceRecord']['artifacts_accepted'] and part0['resourceRecord']['status']=='passed'
  assert sha(Path(part0['source']).read_bytes())==part0['sourceSha256'] and sha(Path(part0['log']).read_bytes())==part0['logSha256']
  assert json.loads(Path(part0['resource']).read_text(encoding='utf-8'))==part0['resourceRecord']
  part=copy.deepcopy(part0);part['metadataReusedFromExactUnchangedSources']=str(priorp)
  if not any(z['sourceSha256']==part['sourceSha256'] and z['logSha256']==part['logSha256'] for z in parts):parts.append(part)
 for n,x in prior['declarationRanges'].items():
  if x['module'] not in selected:continue
  if n in found:assert found[n]==x
  else:found[n]=copy.deepcopy(x)
 for n,x in prior['constants'].items():
  if not any(m in selected for m in [x['module']]+x.get('observedGeneratedEquationOrigins',[])):continue
  if n in deps:
   assert deps[n]['constantDependencies']==x['constantDependencies'],n
   if deps[n]['module']!=x['module']:
    assert ('.eq_' in n or n.endswith('.congr_simp')),n
    origins=sorted(set([deps[n]['module'],x['module']]+deps[n].get('observedGeneratedEquationOrigins',[])+x.get('observedGeneratedEquationOrigins',[])))
    deps[n]['observedGeneratedEquationOrigins']=origins;deps[n]['generatedEquationHasIdenticalProjectDependencies']=True
  else:deps[n]=copy.deepcopy(x)
 reusable.update(selected);allLogs.append('\n'.join(line for line in Path(prior['log']).read_text(encoding='utf-8').splitlines() if line.startswith(('SOURCE_RANGE|','SOURCE_DEPENDENCIES|')) and len(line.split('|'))>=3 and line.split('|')[2] in selected));reusedRecords.append({'record':str(priorp),'recordSha256':sha(priorp.read_bytes()),'unchangedModules':len(selected),'acceptedPartitionsReused':len(prior['parts']),'allReusedSourceHashesMatch':True,'doesNotClaimRecompilation':True,'filteredToActualSourceOwners':True,'priorTotalModules':len(prior['closedSourceHashes'])})
mods=sorted(set(sources)-set(reusable));assert 0<len(mods)<=60 and len(reusable)>0
print(json.dumps({'reusedUnchangedModules':len(reusable),'reusedAcceptedPartitions':len(parts),'newModulesForBoundedExport':len(mods),'wholeProjectRebuildClaimed':False}),flush=True)
for i in range(0,len(mods),60):
 now=datetime.datetime.now(ZoneInfo('Asia/Shanghai'));assert 210<=now.hour*60+now.minute<578,'Stop before launch cutoff'
 selected=mods[i:i+60];n=i//60+1;p=res/('FiniteGradedOriginalPublicHScalarRanges20261028Part'+str(n)+'.lean');rp=res/(cid+'-ranges-part'+str(n)+'.json');log=p.with_suffix('.compiler.log')
 code='module\n'+''.join('import all '+m+'\n' for m in selected)+'import Lean.DeclarationRange\nimport Lean.Util.FoldConsts\nset_option maxHeartbeats 5000\nrun_cmd do\n  let env ← Lean.getEnv\n  let selected : List String := '+json.dumps(selected,ensure_ascii=False).replace(', ', ',')+'\n  let isOwn := fun (n : Lean.Name) => match env.getModuleIdxFor? n with\n    | none => false\n    | some idx => (env.header.moduleNames[idx]!).toString.startsWith "Linear."\n  let mut count : Nat := 0\n  let mut seen : Lean.NameSet := {}\n  for i in [:env.header.moduleData.size] do\n    let owner := env.header.moduleNames[i]!\n    unless selected.contains owner.toString do continue\n    let data := env.header.moduleData[i]!\n    for name in data.constNames ++ data.extraConstNames do\n      if seen.contains name then continue\n      seen := seen.insert name\n      let some info := env.find? name | continue\n      let some idx := env.getModuleIdxFor? name | continue\n      let modName := env.header.moduleNames[idx]!\n      unless selected.contains modName.toString do continue\n      let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.filter isOwn |>.map toString)\n      Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"\n      let some ranges ← Lean.findDeclarationRanges? name | continue\n      let q := ranges.range\n      Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{q.pos.line}|{q.pos.column}|{q.endPos.line}|{q.endPos.column}|{deps}"\n      count := count+1\n  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"\n'
 if rp.exists():
  part=json.loads(rp.read_text(encoding='utf-8'));assert part['accepted'] and part['allSourceHashes']==sources and part['sourceSha256']==sha(code.encode()) and sha(log.read_bytes())==part['logSha256'];out=log.read_text(encoding='utf-8');print('Recover passed partition '+str(n)+';no compile retry',flush=True)
 else:
  assert not p.exists(),'Existing unverified driver requires manual diagnosis;no automatic retry'
  p.write_text(code,encoding='utf-8',newline='\n');rr=run_file(p,cwd=r,env=env);out=rr.stdout+rr.stderr;log.write_text(out,encoding='utf-8',newline='\n');part={'accepted':rr.returncode==0 and rr.resource_record.get('artifacts_accepted',False),'selectedModules':selected,'allSourceHashes':sources,'source':str(p),'sourceSha256':rr.source_sha256,'log':str(log),'logSha256':sha(log.read_bytes()),'resource':str(rr.resource_log),'resourceRecord':rr.resource_record,'returnCode':rr.returncode};rp.write_text(json.dumps(part,indent=2)+'\n',encoding='utf-8',newline='\n');assert part['accepted'],out[-3000:]
 for m,h in sources.items():assert sha((r/(m.replace('.','/')+'.lean')).read_bytes())==h
 for line in out.splitlines():
  if line.startswith('SOURCE_RANGE|'):
   v=line.split('|');assert v[1] not in found;found[v[1]]={'module':v[2],'startLine':int(v[3]),'startColumn':int(v[4]),'endLine':int(v[5]),'endColumn':int(v[6]),'constantDependencies':v[7].split(',') if v[7] else []}
  elif line.startswith('SOURCE_DEPENDENCIES|'):
   v=line.split('|');newDeps=v[3].split(',') if v[3] else []
   if v[1] in deps:
    import re
    isEquation=v[1] in ['LinearStudy.nativeProjectiveRingIntegerPiece.eq_1','MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential.eq_1','LinearStudy.gradedIntegerProjection.eq_1','LinearStudy.projectiveNativeChartHomogeneousElement.congr_simp','LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution.congr_simp'];isExternalHelper=v[1]=='IsLocalization.Away.liftAlgHom.congr_simp';assert deps[v[1]]['constantDependencies']==newDeps and ((isEquation and v[1].rsplit('.',1)[0] in newDeps) or (isExternalHelper and newDeps==[])),'Unexpected duplicate constant;manual diagnosis required: '+v[1]
    row=deps[v[1]];origins=row.setdefault('observedGeneratedEquationOrigins',[row['module']]);assert v[2] not in origins;origins.append(v[2]);row['generatedEquationHasIdenticalProjectDependencies']=True
   else:deps[v[1]]={'module':v[2],'constantDependencies':newDeps}
 parts.append(part);allLogs.append(out);print(json.dumps({'part':n,'selected':len(selected),'passed':True,'peakJobMiB':part['resourceRecord'].get('peak_job_memory_mib')}),flush=True)
assert set(x['module'] for x in deps.values())==set(sources)
missing=sorted({d for x in deps.values() for d in x['constantDependencies'] if d not in deps});assert not missing,missing
fullLog=res/(cid+'-all-source-ranges.log');fullLog.write_text('\n'.join(allLogs),encoding='utf-8',newline='\n');record={'checkedAt':datetime.datetime.now(ZoneInfo('Asia/Shanghai')).isoformat(),'accepted':True,'partitioned':True,'sequentialOnly':True,'allPartitionsAccepted':True,'parts':parts,'source':str(Path(__file__)),'sourceSha256':sha(Path(__file__).read_bytes()),'log':str(fullLog),'logSha256':sha(fullLog.read_bytes()),'closedSourceHashes':sources,'closedModuleCount':len(sources),'declarationRanges':found,'constants':deps,'resourceRecord':{'artifacts_accepted':True,'status':'all_sequential_partitions_passed','peak_job_memory_mib':max(x['resourceRecord']['peak_job_memory_mib'] for x in parts)},'generatedEquationOriginAccounting':{n:{'observedCompilerModules':x['observedGeneratedEquationOrigins'],'projectDependencies':x['constantDependencies'],'rangeRule':('Count the unique original project definition range for its generated equation or congruence helper;all observed owners have identical project dependencies.' if ('.eq_' in n or n in ['LinearStudy.projectiveNativeChartHomogeneousElement.congr_simp','LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution.congr_simp']) else 'External generated helper with no project dependencies;account at its actual ranged project callers.')} for n,x in deps.items() if 'observedGeneratedEquationOrigins' in x},'reusedExactSourceMetadata':{'records':reusedRecords,'unchangedModules':len(reusable),'acceptedPartitionsReused':len(parts)-1,'allReusedSourceHashesMatch':True,'doesNotClaimRecompilation':True,'filteredToActualSourceOwners':True,'filteredConstantDependencyGraphClosed':True},'wholeProjectLeanBuildClaimed':False,'published':False,'original4_1':False,'original4_2':False,'mainTheorem':False};rp=res/(cid+'-all-source-ranges.verification.json');rp.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n');print(json.dumps({'accepted':True,'modules':len(sources),'ranges':len(found),'constants':len(deps),'partitions':len(parts),'record':str(rp)}))
