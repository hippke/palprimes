"""major2d: number of checker nodes per level-0 cell (input of gen_chunks.py).
Mirrors `cfg2`, `cfg3` (Palprimes/Major2D/B2Cfg.lean, B3Cfg.lean): levels below dmin count as failing,
thr is the list of thresholds.
usage: nodes.py b   (writes nodes_b{b}.json next to this script)"""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
import sys, json
sys.path.insert(0, HERE)
import ref
from gen import JS, PAR

b = int(sys.argv[1])
P = PAR[b]
d, half = ref.load(JS[b])
DMIN = {2: 1, 3: 0}[b]
THR = {2: [0], 3: [0, 2767011611056432742, 5534023222112865484, 9223372036854775808, 13835058055282163712,
             36893488147419103232]}[b]   # cfg3.thr
B = ref.Base(b, P["l"], P["n0"], half, P["Q0"], P["dmax"], THR)
cells = ref.canonical(b, P["l"], P["Q0"])
orig = ref.cell_ok
cnt = [0]


def co(B_, d_, J, K, stats=None):
    cnt[0] += 1
    return False if d_ < DMIN else orig(B_, d_, J, K, stats)


ref.cell_ok = co
out = []
for j, k in cells:
    cnt[0] = 0
    st, per = {}, {}
    assert ref.check(B, 0, 2 * j + 1, 2 * k + 1, st, per)
    out.append(cnt[0])
json.dump(out, open(os.path.join(HERE, f"nodes_b{b}.json"), "w"))
print(sum(out), max(out), min(out))
