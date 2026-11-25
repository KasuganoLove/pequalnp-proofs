from pathlib import Path
import datetime,json,resource,subprocess,time,sys
P=Path(__file__).resolve().parent
task=int(sys.argv[1]) if len(sys.argv)>1 else 10487
budget=int(sys.argv[2]) if len(sys.argv)>2 else 10
outdir=P.parent.parent/f'L-meta-{task}'/'signed-probe'
outdir.mkdir(exist_ok=True)
def limits():resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
start=datetime.datetime.now(datetime.timezone.utc).isoformat();before=time.monotonic()
with (outdir/'result.json').open('w') as out,(outdir/'stderr.log').open('w') as err:
 p=subprocess.Popen([str(P/'probe'),str(task),str(budget),'60'],stdout=out,stderr=err,preexec_fn=limits)
 try: code=p.wait(timeout=65)
 except subprocess.TimeoutExpired:p.kill();code=p.wait()
r={'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_wall_seconds':time.monotonic()-before,'exit_code':code,'address_space_limit_bytes':1024**3,'maximum_resident_set_size_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'binary_budget':budget,'task':f'L-meta-{task}','free_NOT_count':'unbounded','formal_certificate':False}
(outdir/'run.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
