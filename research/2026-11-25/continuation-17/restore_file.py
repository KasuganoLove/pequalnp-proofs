#!/usr/bin/env python3
"""Restore an exact archived text file; no solver, Lean, network or Git action."""
from pathlib import Path
import argparse, hashlib, json

ROOT = Path(__file__).resolve().parent

def read_file(relative):
    entries = {x['path']: x for x in json.loads((ROOT / 'large-files.json').read_text())['files']}
    if relative not in entries:
        return (ROOT / relative).read_bytes()
    entry = entries[relative]
    chunks = []
    for part in entry['parts']:
        data = (ROOT / part['path']).read_bytes()
        assert len(data) == part['bytes']
        assert hashlib.sha256(data).hexdigest() == part['sha256']
        chunks.append(data)
    data = b''.join(chunks)
    assert len(data) == entry['bytes']
    assert hashlib.sha256(data).hexdigest() == entry['sha256']
    return data

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--verify-only', action='store_true')
    parser.add_argument('relative', nargs='?')
    parser.add_argument('destination', nargs='?')
    args = parser.parse_args()
    if args.verify_only:
        entries = json.loads((ROOT / 'large-files.json').read_text())['files']
        for entry in entries:
            read_file(entry['path'])
        print(json.dumps({'verified_exact_part_sets': len(entries), 'files_written': 0}))
        return
    if not args.relative or not args.destination:
        parser.error('Provide archive-relative file path and destination, or --verify-only')
    relative = Path(args.relative)
    if relative.is_absolute() or '..' in relative.parts:
        parser.error('Archive path must be relative and may not contain ..')
    data = read_file(relative.as_posix())
    target = Path(args.destination)
    if target.exists() and target.read_bytes() != data:
        raise SystemExit('Refusing to overwrite differing destination: ' + str(target))
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    print(json.dumps({'destination': str(target), 'bytes': len(data),
                      'sha256': hashlib.sha256(data).hexdigest()}))

if __name__ == '__main__':
    main()
