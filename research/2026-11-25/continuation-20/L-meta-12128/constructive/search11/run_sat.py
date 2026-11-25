#!/usr/bin/env python3
"""One authorized120second/2GiB monotone upper-witness search; no retries."""
import pathlib,subprocess,resource,time,datetime,json
b=pathlib.Path(__file__).resolve().parent;exe='/workspace/scratch/65f339da29fe/pnp-tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
def cap():resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
cmd=[exe,'--sat','--seed=2','-t','120','--stats',str(b/'formula.cnf')];start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic();(b/'run-start.json').write_text(json.dumps({'started_at':start,'command':cmd,'time_limit_s':120,'address_space_limit_bytes':2*1024**3},indent=2)+'\n');print('START '+start,flush=True)
with (b/'solver.log').open('w') as log:
 p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,preexec_fn=cap)
 try:code=p.wait(timeout=125);timeout=False
 except subprocess.TimeoutExpired:p.kill();code=p.wait();timeout=True
text=(b/'solver.log').read_text();status='SAT' if code==10 else 'UNSAT' if code==20 else 'UNKNOWN';r={'started_at':start,'finished_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seconds':time.monotonic()-t,'exit_code':code,'status':status,'outer_timeout':timeout,'peak_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'solver_command':cmd,'scope':'One bounded monotone upper-witness search. UNSAT/UNKNOWN is not a formal lower-bound certificate.'};(b/'result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
