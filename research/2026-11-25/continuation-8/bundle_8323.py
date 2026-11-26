#!/usr/bin/env python3
"""Bundle checked research modules into an independently checkable task file."""
from pathlib import Path
import argparse
import hashlib
import json
import re


def strip_comments(source):
    out = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith('/-', i):
            if depth == 0:
                out.append(' ')
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
            if depth == 0:
                out.append(' ')
        elif depth:
            if source[i] == '\n':
                out.append('\n')
            i += 1
        elif source.startswith('--', i):
            j = source.find('\n', i)
            i = len(source) if j < 0 else j
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError('Unterminated Lean comment')
    return ''.join(out)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--lean-root', type=Path, required=True)
    p.add_argument('--root-module', default='Pnp4201CleanCase')
    p.add_argument('--root-theorem', default='exact_8323')
    p.add_argument('--public-record', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    goal = 'PEqualNP.Outside.L_meta_8323'
    modules = []
    bodies = {}
    originals = {}
    visiting = set()

    def visit(module):
        if module == 'Mathlib' or module.startswith('Mathlib.'):
            return
        if module == 'PEqualNP.Defs' or module.startswith('PEqualNP.Defs.'):
            return
        if module in bodies:
            return
        if module in visiting:
            raise ValueError('Dependency cycle: ' + module)
        visiting.add(module)
        path = args.lean_root.joinpath(*module.split('.')).with_suffix('.lean')
        original = path.read_text()
        source = strip_comments(original)
        imports = re.findall(r'^import ([\w.]+)\s*$', source, re.M)
        for dependency in imports:
            visit(dependency)
        source = re.sub(r'^import [\w.]+\s*$', '', source, flags=re.M)
        if '"' in source:
            raise ValueError('Noncomment string in ' + module)
        originals[module] = original
        bodies[module] = source
        modules.append(module)
        visiting.remove(module)

    visit(args.root_module)
    prefixes = {
        m: m if m.startswith('PEqualNP.') else 'PEqualNP.Outside.' + m
        for m in modules
    }
    names = {m: 'Part' + str(i) for i, m in enumerate(modules)}
    replacements = sorted(
        [(prefixes[m], goal + '.' + names[m]) for m in modules],
        key=lambda pair: -len(pair[0]),
    )
    chunks = ['import Mathlib\nimport PEqualNP.Defs\n']
    manifest = []
    for module in modules:
        body = bodies[module]
        for old, new in replacements:
            body = re.sub(re.escape(old) + r'(?![A-Za-z0-9_])', new, body)
        # A few research references use sibling namespaces relative to Outside.
        # Qualify those after full-name rewriting, without changing identifiers.
        for sibling in modules:
            if not sibling.startswith('PEqualNP.'):
                body = re.sub(
                    r'(?<![A-Za-z0-9_.])' + re.escape(sibling) + r'(?=\.)',
                    goal + '.' + names[sibling], body,
                )
        # All original declarations live inside the enclosing task namespace.
        # Namespace and declaration names are relative; references remain full.
        body = re.sub(
            r'^(namespace|end) ' + re.escape(goal) + r'\.',
            r'\1 ', body, flags=re.M,
        )
        body = re.sub(
            r'^((?:(?:private|protected|noncomputable) )?(?:theorem|lemma|def|abbrev)) '
            + re.escape(goal) + r'\.',
            r'\1 ', body, flags=re.M,
        )
        body = re.sub(r'\n[ \t]*\n(?:[ \t]*\n)+', '\n\n', body).strip()
        chunks.append(
            '\n-- Source module: ' + module + '\n'
            + 'namespace ' + goal + '\n\n' + body + '\n\n'
            + 'end ' + goal + '\n'
        )
        manifest.append({
            'module': module,
            'source_sha256': hashlib.sha256(originals[module].encode()).hexdigest(),
            'bundled_namespace': goal + '.' + names[module],
        })
    record = json.loads(args.public_record.read_text())
    statement = record['formal_statement']
    chunks.append(
        '\ntheorem ' + goal + ' : ' + statement + ' := by\n'
        + '  exact ' + goal + '.' + names[args.root_module] + '.'
        + args.root_theorem + '\n'
    )
    result = ''.join(chunks)
    if len(result.encode()) > 512 * 1024:
        raise ValueError('Bundled source exceeds the task file limit')
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(result)
    meta = {
        'modules': manifest,
        'bytes': len(result.encode()),
        'sha256': hashlib.sha256(result.encode()).hexdigest(),
        'statement_sha256': hashlib.sha256(statement.encode()).hexdigest(),
        'attribution': 'Upstream L1501 and L2235 proofs plus the recorded research modules.',
    }
    args.out.with_suffix('.bundle.json').write_text(json.dumps(meta, indent=2) + '\n')
    print(json.dumps({'modules': len(modules), 'bytes': meta['bytes'], 'sha256': meta['sha256']}))


if __name__ == '__main__':
    main()
