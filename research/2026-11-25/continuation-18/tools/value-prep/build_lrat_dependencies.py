#!/usr/bin/env python3
"""Build byte-pinned generic LRAT dependencies, one Lean process at a time.

This does not claim/check a VALUE task, invoke the authoritative proof checker,
change the dependency manifest, or contact a remote repository.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import resource
import subprocess
import time

BASE = Path('/workspace/scratch/65f339da29fe')
ROOT = BASE / 'pequalnp-proofs'
HERE = Path(__file__).resolve().parent
UPSTREAM = HERE / 'upstream'
PIN = '57d6c2fdf69978aecff3559c7ab6b442a2d3c3f1'
SOURCES = {
    'PEqualNP.Library.LRAT.Checker': 'd0b10c183b5f980fa67d88e1f48fd48c4a8198d0',
    'PEqualNP.MetaComplexity.Helpers.Shannon': '176a956460eb82b863225f405e215d498136cb3f',
    'PEqualNP.Library.LRAT.LinkN': 'ddea982d0c14d4183789f35d8c583bc51bc53383',
    'PEqualNP.Library.LRAT.LinkN2': '9a273de3c59200c5ee3c00306b01f15a95217986',
}

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def main():
    env = os.environ.copy()
    env['ELAN_HOME'] = str(BASE / 'pnp-tools/elan')
    env['PATH'] = str(BASE / 'pnp-tools/elan/bin') + os.pathsep + env['PATH']
    result = {'upstream_pin': PIN, 'kind': 'ordinary_generic_library_build',
              'authoritative_task_check': False, 'started_utc': now(),
              'lean_threads': 1, 'lean_memory_limit_mb': 6500, 'stages': []}
    for module, expected in SOURCES.items():
        rel = Path(module.replace('.', '/') + '.lean')
        source = ROOT / 'lean' / rel
        if not source.exists():
            official = UPSTREAM / 'lean' / rel
            data = official.read_bytes()
            assert blob(data) == expected, (module, 'reference blob mismatch')
            source.parent.mkdir(parents=True, exist_ok=True)
            with source.open('xb') as stream:
                stream.write(data)
        assert blob(source.read_bytes()) == expected, (module, 'local source mismatch')
    for module, expected in SOURCES.items():
        rel = Path(module.replace('.', '/'))
        source = ROOT / 'lean' / rel.with_suffix('.lean')
        target = ROOT / 'lean/.lake/build/lib/lean' / rel.with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        label = module.rsplit('.', 1)[1]
        log = HERE / ('build-' + label + '.log')
        timing = HERE / ('build-' + label + '.time.txt')
        command = ['lake', 'env', 'lean',
                   '-j1', '-M6500', '-o', str(target), str(source.relative_to(ROOT / 'lean'))]
        stage = {'module': module, 'source_git_blob': expected,
                 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                 'command': command, 'cwd': str(ROOT / 'lean'), 'started_utc': now()}
        started = time.monotonic()
        usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
        print('START ' + module, flush=True)
        with log.open('w') as stream:
            try:
                completed = subprocess.run(command, cwd=ROOT / 'lean', env=env,
                                           stdout=stream, stderr=subprocess.STDOUT, timeout=600)
                stage['exit_code'] = completed.returncode
            except subprocess.TimeoutExpired:
                stage['exit_code'] = None
                stage['timeout_seconds'] = 600
        stage['elapsed_seconds'] = time.monotonic() - started
        usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
        timing.write_text(json.dumps({
            'elapsed_seconds': stage['elapsed_seconds'],
            'user_seconds': usage_after.ru_utime - usage_before.ru_utime,
            'system_seconds': usage_after.ru_stime - usage_before.ru_stime,
            'cumulative_build_peak_child_rss_kib': usage_after.ru_maxrss,
            'peak_scope': 'maximum child RSS across completed stages in this runner'
        }, indent=2) + '\n')
        stage['ended_utc'] = now()
        stage['log'] = log.name
        stage['time_log'] = timing.name
        stage['olean_exists'] = target.exists()
        if target.exists():
            stage['olean_sha256'] = hashlib.sha256(target.read_bytes()).hexdigest()
            stage['olean_bytes'] = target.stat().st_size
        result['stages'].append(stage)
        result['completed_utc'] = now()
        result['success'] = all(x.get('exit_code') == 0 for x in result['stages']) and len(result['stages']) == len(SOURCES)
        (HERE / 'build-results.json').write_text(json.dumps(result, indent=2) + '\n')
        print('END ' + module + ' exit=' + str(stage['exit_code']) + ' seconds=' + str(round(stage['elapsed_seconds'], 3)), flush=True)
        if stage['exit_code'] != 0:
            raise SystemExit(1)

if __name__ == '__main__':
    main()
