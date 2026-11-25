#!/usr/bin/env python3
"""Regenerate the self-chosen two-variable contradictory sanity sample."""
import pathlib,sys
pathlib.Path(sys.argv[1] if len(sys.argv)>1 else 'sanity.cnf').write_text('p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n')
