"""Extract student IDs/names only; keep output outside the public site directory."""
import argparse, json, os, re
from name_initials import name_initials
from pathlib import Path
from zipfile import ZipFile
import xml.etree.ElementTree as E
p=argparse.ArgumentParser();p.add_argument('workbook');p.add_argument('output');args=p.parse_args()
output=Path(args.output).resolve();repo=Path(__file__).resolve().parents[2]
if output.is_relative_to(repo):raise SystemExit('Roster must be stored outside the public site repository.')
ns={'s':'http://schemas.openxmlformats.org/spreadsheetml/2006/main'};records=[]
with ZipFile(args.workbook) as z:
 strings=[''.join(e.itertext()) for e in E.fromstring(z.read('xl/sharedStrings.xml')).findall('s:si',ns)] if 'xl/sharedStrings.xml' in z.namelist() else []
 for sheet in [n for n in z.namelist() if re.fullmatch(r'xl/worksheets/sheet\d+\.xml',n)]:
  columns=None
  for row in E.fromstring(z.read(sheet)).findall('s:sheetData/s:row',ns):
   cells={}
   for c in row.findall('s:c',ns):
    v=c.find('s:v',ns);val=v.text if v is not None else ''.join(c.find('s:is',ns).itertext()) if c.find('s:is',ns) is not None else ''
    if c.get('t')=='s':val=strings[int(val)]
    cells[re.sub(r'\d','',c.get('r'))]=str(val).strip()
   if '学号' in cells.values() and '姓名' in cells.values():columns=tuple(next(k for k,v in cells.items() if v==label) for label in ['学号','姓名']);continue
   if not columns:continue
   sid,name=(cells.get(k,'') for k in columns)
   if re.fullmatch(r'\d{11}',sid) and name:records.append({'id':sid,'name':name,'initials':name_initials(name)})
if not records or len({r['id'] for r in records})!=len(records):raise SystemExit('Empty roster or duplicate student IDs; review the workbook.')
output.parent.mkdir(parents=True,exist_ok=True,mode=0o700)
fd=os.open(output,os.O_WRONLY|os.O_CREAT|os.O_TRUNC,0o600)
with os.fdopen(fd,'w') as f:json.dump(records,f,ensure_ascii=False)
print(f'Imported {len(records)} students; private output written.')
