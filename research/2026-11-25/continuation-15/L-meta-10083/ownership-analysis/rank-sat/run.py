from pathlib import Path
import datetime,hashlib,json,os,resource,subprocess,time
P=Path(__file__).resolve().parent
default=Path('/workspace/scratch/65f339da29fe/pnp-tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical')
solver=Path(os.environ.get('PNP10083_CADICAL',str(default)))
formula=P/'rank14.cnf'; proof=P/'rank14.lrat.gz'
def limits(): resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
start=datetime.datetime.now(datetime.timezone.utc).isoformat(); begin=time.monotonic(); timed_out=False
cmd=[str(solver),'-t','300','--lrat','--no-binary',str(formula),str(proof)]
with (P/'cadical.log').open('w') as log:
    proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits)
    (P/'solver.pid').write_text(str(proc.pid)+'\n')
    try: code=proc.wait(timeout=315)
    except subprocess.TimeoutExpired:
        timed_out=True; proc.kill(); code=proc.wait()
out=(P/'cadical.log').read_text()
outcome='SAT' if 's SATISFIABLE' in out else 'UNSAT' if 's UNSATISFIABLE' in out else 'UNKNOWN'
record={'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'elapsed_wall_seconds':time.monotonic()-begin,'exit_code':code,'outcome':outcome,
        'outer_timeout':timed_out,'time_limit_seconds':300,'address_space_limit_bytes':1024**3,
        'cnf_sha256':hashlib.sha256(formula.read_bytes()).hexdigest(),
        'proof_format':'gzip-compressed text LRAT','proof_bytes':proof.stat().st_size if proof.exists() else None,
        'formal_proof_checked':False,'repeated_run':False}
(P/'sat-result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
