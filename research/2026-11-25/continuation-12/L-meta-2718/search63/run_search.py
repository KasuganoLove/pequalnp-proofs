from pathlib import Path
import datetime,hashlib,json,resource,subprocess,time
P=Path(__file__).resolve().parent

def limits():
    resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))

start=datetime.datetime.now(datetime.timezone.utc).isoformat();begin=time.monotonic()
with (P/'process.log').open('w') as f:
    r=subprocess.run([str(P/'search63'),'300'],cwd=P,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits,timeout=315)
record={'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_wall_seconds':time.monotonic()-begin,'exit_code':r.returncode,'address_space_limit_bytes':1024**3,'thread_count':1,'source_sha256':hashlib.sha256((P/'search63.cpp').read_bytes()).hexdigest(),'search_budget_seconds':300,'formal_nonexistence_proof':False}
(P/'process-result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
if (P/'candidate-63.json').exists():
    subprocess.run(['python',str(P/'verify.py'),'candidate-63.json'],cwd=P,check=True)
subprocess.run(['python',str(P/'verify.py'),'best-63.json'],cwd=P,check=True)
