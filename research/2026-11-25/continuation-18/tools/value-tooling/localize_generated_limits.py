#!/usr/bin/env python3
"""Localize the known upstream genrow limit options without changing proof content.
Output remains a lower-bound component, not a complete canonical VALUE submission.
"""
import argparse,pathlib,re
p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('output');p.add_argument('--heartbeats',type=int,default=10000000);p.add_argument('--recdepth',type=int,default=1000000);a=p.parse_args()
s=pathlib.Path(a.input).read_text();globals=re.findall(r'^set_option (maxRecDepth|maxHeartbeats) [0-9]+\s*$',s,re.M)
assert sorted(globals)==['maxHeartbeats','maxRecDepth'],'Expected exactly the two known genrow global options'
s=re.sub(r'^set_option (?:maxRecDepth|maxHeartbeats) [0-9]+\s*\n','',s,flags=re.M)
prefix=f'set_option maxRecDepth {a.recdepth} in\nset_option maxHeartbeats {a.heartbeats} in\n'
s=re.sub(r'^((?:noncomputable )?(?:def|theorem)\b)',lambda m:prefix+m[0],s,flags=re.M)
assert not re.search(r'^set_option .*[^n]$',s,re.M),'Unexpected global option remains'
pathlib.Path(a.output).write_text(s)
