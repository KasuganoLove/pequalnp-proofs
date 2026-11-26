from pathlib import Path
import hashlib
import json
import re
import shutil

ROOT = Path('/workspace/scratch/65f339da29fe')
SOURCE = ROOT / 'pnp-session-2026-11-25/continuation-9/L-meta-2590'
ARCHIVE = ROOT / 'pnp-research-2026-11-24/research/2026-11-25/continuation-9'
OUT = ROOT / 'pnp-session-2026-11-25/continuation9-payload'


def object_sha(kind, data):
    return hashlib.sha1(kind.encode() + b' ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def directory_sha(directory):
    rows = []
    for p in sorted(directory.iterdir(), key=lambda p: p.name + ('/' if p.is_dir() else '')):
        mode, sha = ('40000', directory_sha(p)) if p.is_dir() else (('100755' if p.name == 'reproduce.sh' else '100644'), object_sha('blob', p.read_bytes()))
        rows.append(mode.encode() + b' ' + p.name.encode() + b'\0' + bytes.fromhex(sha))
    return object_sha('tree', b''.join(rows))


def main():
    ARCHIVE.mkdir(parents=True, exist_ok=True)
    OUT.mkdir(exist_ok=True)
    task = ARCHIVE / 'L-meta-2590'
    task.mkdir(exist_ok=True)
    for name in ['gap.json', 'statement.txt', 'ExportCNF.lean',
                 'Pnp2590OwnershipSearch.cpp', 'Pnp2590OwnershipVerify.py',
                 'ownership-search-1.log', 'ownership-search-1.json',
                 'ownership-search-1-verification.json', 'ownership-handoff.md',
                 'petersen-19-cadical.log', 'petersen-19-cadical-result.json',
                 'petersen-19.solution']:
        shutil.copy2(SOURCE / name, task / name)
    shutil.copytree(SOURCE / 'clean-case', task / 'clean-case', dirs_exist_ok=True)
    shutil.copytree(SOURCE / 'upstream-audit/curated', task / 'upstream-audit', dirs_exist_ok=True)
    shutil.copytree(SOURCE / 'upstream-audit/stronger-deleted-curated',
                    task / 'upstream-audit/stronger-deleted-curated', dirs_exist_ok=True)
    for name in ['stronger-deleted-status.json', 'stronger-deleted-audit.md',
                 'stronger-deleted-audit.json']:
        if (SOURCE / 'upstream-audit' / name).exists():
            shutil.copy2(SOURCE / 'upstream-audit' / name, task / 'upstream-audit' / name)
    review = SOURCE.parent / 'stage-results-readiness-review.md'
    if review.exists():
        shutil.copy2(review, ARCHIVE / review.name)
    shutil.copy2(Path(__file__), ARCHIVE / 'prepare_continuation9.py')
    supporting = ARCHIVE / 'supporting-evidence'
    supporting.mkdir(exist_ok=True)
    shutil.copy2(ROOT / 'pnp-session-2026-11-25/continuation-5/L-meta-4201/env-upstream-blobs.json',
                 supporting / 'env-upstream-blobs.json')
    stale = SOURCE.parent / 'L-meta-949'
    stale_out = ARCHIVE / 'L-meta-949'
    stale_out.mkdir(exist_ok=True)
    for name in ['gap.json', 'statement.txt', 'official-950-artifact.json',
                 'ownership-scope-audit.md']:
        shutil.copy2(stale / name, stale_out / name)
    shutil.copytree(stale / 'audit-curated', stale_out / 'audit-curated', dirs_exist_ok=True)
    (stale_out / 'handoff.json').write_text(json.dumps({
        'task': 'L-meta-949', 'offer_kind': 'reduction_only',
        'released_at_utc': '2026-11-25T08:07:05.892352+00:00',
        'release_reason': 'statement_seems_false', 'http_status': 200,
        'reason': 'The already checked L-meta-950 is the exact logical opposite under identical premises.',
        'existing_proof_pr': 'https://github.com/open-goat/pequalnp-proofs/pull/1995',
        'github_merged_at_utc': '2026-11-23T19:56:27Z',
        'desk_status_at_utc': '2026-11-23T19:56:33.901Z',
        'new_search_or_lean_run': False, 'new_official_pr': False,
    }, indent=2) + '\n')

    public_lease = {
        'task': 'L-meta-2590',
        'allocation': 'Existing lease returned by the default desk for the owner handle; not a newly allocated independent lease.',
        'last_successful_renewal_utc': '2026-11-25T07:45:34.570468+00:00',
        'closed_response_utc': '2026-11-25T07:53:45.892791+00:00',
        'closed_response_status': 410,
        'closed_response_message': 'no such live lease: it expired or was released. Ask /desk/next again.',
        'new_proof_work_stopped': True,
        'full_task_proved': False,
        'official_pr_created': False,
        'private_credentials_included': False,
    }
    (ARCHIVE / 'lease-handoff.json').write_text(json.dumps(public_lease, indent=2) + '\n')

    files = [p for p in sorted(ARCHIVE.rglob('*')) if p.is_file() and p != ARCHIVE / 'manifest.json']
    manifest = []
    for p in files:
        data = p.read_bytes()
        text = data.decode('utf-8')
        if re.search(r'[?&]lease=[A-Za-z0-9_-]+', text):
            raise ValueError('Private lease URL in ' + str(p))
        manifest.append({'path': str(p.relative_to(ARCHIVE)), 'bytes': len(data),
                         'sha256': hashlib.sha256(data).hexdigest()})
    (ARCHIVE / 'manifest.json').write_text(json.dumps({'files': manifest}, indent=2) + '\n')
    files.append(ARCHIVE / 'manifest.json')

    entries = []
    for p in sorted(files):
        data = p.read_bytes()
        entry = {'path': str(p.relative_to(ARCHIVE)),
                 'mode': '100755' if p.name == 'reproduce.sh' else '100644', 'type': 'blob'}
        if p.suffix == '.lean' and 'upstream-audit' in p.parts:
            # These exact source objects are in the common GitHub fork network.
            entry['sha'] = object_sha('blob', data)
        else:
            entry['content'] = data.decode('utf-8')
        entries.append(entry)
    chunks, current, size = [], [], 0
    for entry in entries:
        count = len(json.dumps(entry, ensure_ascii=False).encode())
        if current and size + count > 250000:
            chunks.append(current)
            current, size = [], 0
        current.append(entry)
        size += count
    if current:
        chunks.append(current)
    for i, chunk in enumerate(chunks):
        (OUT / f'chunk-{i}.json').write_text(json.dumps(chunk, ensure_ascii=False))
    summary = {'files': len(files), 'bytes': sum(p.stat().st_size for p in files),
               'chunks': len(chunks), 'archive_tree': directory_sha(ARCHIVE),
               'expected_entries': [{'name': p.name, 'type': 'dir' if p.is_dir() else 'file',
                                     'sha': directory_sha(p) if p.is_dir() else object_sha('blob', p.read_bytes())}
                                    for p in sorted(ARCHIVE.iterdir())]}
    (OUT / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'expected_entries'}))


if __name__ == '__main__':
    main()
