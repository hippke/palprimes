#!/usr/bin/env python3
"""Compile one OK2 module via k2build (deps must be built) and print only its error messages in full.
usage: errs.py OK2.Items.M10_L [--mem 20G]"""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import k2build

mod = sys.argv[1]
mem = sys.argv[sys.argv.index('--mem') + 1] if '--mem' in sys.argv else '20G'
m, rc, dt, msg, errs = k2build.build(mod, mem)
print(f'{mod}: rc={rc} ({dt:.0f}s)')
blocks = re.split(r'\n(?=/\S+\.lean:\d+:\d+: )', msg)
for b in blocks:
    if re.match(r'/\S+\.lean:\d+:\d+: error', b):
        print(b[:3000])
        print('-----')
