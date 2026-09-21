"""Prepare a private D1 import; never write roster SQL into the Pages repository."""
import json, os, re, argparse
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('roster');p.add_argument('output');a=p.parse_args()
destination=Path(a.output).resolve()
if destination.is_relative_to(Path(__file__).resolve().parents[3]):
    raise SystemExit('Write private SQL outside the repository.')
rows=json.loads(Path(a.roster).read_text())
def quote(text):return "'"+text.replace("'","''")+"'"
sql=[]
for r in rows:
    if not re.fullmatch(r'\d{11}',r['id']) or not re.fullmatch(r'[A-Z]{1,80}',r['initials']) or not r['name'].strip():
        raise SystemExit('Invalid private roster row.')
    sql.append('INSERT INTO students(id,name,initials) VALUES('+','.join(quote(r[k]) for k in ['id','name','initials'])+') ON CONFLICT(id) DO UPDATE SET name=excluded.name,initials=excluded.initials;')
destination.parent.mkdir(parents=True,exist_ok=True,mode=0o700)
fd=os.open(destination,os.O_WRONLY|os.O_CREAT|os.O_TRUNC,0o600)
os.fchmod(fd,0o600)
with os.fdopen(fd,'w') as f:f.write('\n'.join(sql)+'\n')
print(f'Prepared {len(rows)} private roster entries.')
