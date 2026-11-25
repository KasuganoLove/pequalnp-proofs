from pathlib import Path
import datetime,hashlib,json,resource,subprocess,time,sys
p=Path(__file__).resolve().parent
solver=Path('/workspace/scratch/65f339da29fe/pnp-tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical')
cnf=p/'subdivision-k4-free-or-14.cnf'
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
start=datetime.datetime.now(datetime.timezone.utc).isoformat(); begin=time.monotonic()
with (p/'cadical.log').open('w') as log:
    r=subprocess.run([str(solver),'-t','300',str(cnf)],stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits,timeout=315)
text=(p/'cadical.log').read_text()
outcome='SAT' if 's SATISFIABLE' in text else ('UNSAT' if 's UNSATISFIABLE' in text else 'UNKNOWN')
result={'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-begin,'solver_exit':r.returncode,'outcome':outcome,'time_limit_seconds':300,'address_space_limit_bytes':2*1024**3,'formula':'PEqualNP.Defs.LratEncoding.enc2 11 14 label physicalRows','cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest(),'physical_boundary_rows':24,'formal_unsat_certificate':False}
(p/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
