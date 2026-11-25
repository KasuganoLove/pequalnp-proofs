from pathlib import Path
import datetime,hashlib,json,os,resource,subprocess,time
P=Path(__file__).resolve().parent
solver=Path(os.environ.get('PNP650_CADICAL','/workspace/scratch/65f339da29fe/pnp-tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'))
formula=P/'five-point-23-dense.cnf'
def limits():resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
start=datetime.datetime.now(datetime.timezone.utc).isoformat();begin=time.monotonic();timed_out=False
with (P/'cadical.log').open('w') as log:
    proc=subprocess.Popen([str(solver),'-t','300',str(formula)],stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits)
    (P/'solver.pid').write_text(str(proc.pid)+'\n')
    try:code=proc.wait(timeout=315)
    except subprocess.TimeoutExpired:timed_out=True;proc.kill();code=proc.wait()
text=(P/'cadical.log').read_text()
outcome='SAT' if 's SATISFIABLE' in text else 'UNSAT' if 's UNSATISFIABLE' in text else 'UNKNOWN'
record={'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_wall_seconds':time.monotonic()-begin,'exit_code':code,'outcome':outcome,'outer_timeout':timed_out,'time_limit_seconds':300,'address_space_limit_bytes':1024**3,'cnf_sha256':hashlib.sha256(formula.read_bytes()).hexdigest(),'formal_unsat_certificate':False,'repeated_run':False}
(P/'sat-result.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
