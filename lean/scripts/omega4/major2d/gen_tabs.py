"""major2d: write B{b}Tab.lean (range checks of the phase tables, one declaration per range) and the
per-level TabGood lemmas text (printed, to be placed in B{b}Check.lean).  usage: gen_tabs.py b"""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
import sys
b = int(sys.argv[1])
Q0, R = {2: (192, 384), 3: (64, 256)}[b]
LEAN = os.path.join(HERE, '..', '..', '..', 'Palprimes', 'Major2D') + os.sep
out = [f"import Palprimes.Major2D.TabR\nimport Palprimes.Major2D.B{b}Cfg\n",
       f"/-! # Base {b}: range checks of the phase tables ({R} entries per declaration) -/\n",
       "namespace Palprimes.M2\n", "set_option maxRecDepth 100000\n"]
lv = []
for d in range(6):
    M = 4 * Q0 * 2 ** d
    k = M // R
    names = []
    for i in range(k):
        nm = f"tab{b}_{d}_{i}"
        names.append(nm)
        out.append(f"theorem {nm} : tabOKr {M} (tab{b} {d}) ({R} * {i}) {R} = true := by decide +kernel")
    if k == 1:
        body = f"""intro i hi
    have : i = 0 := by omega
    subst this; exact {names[0]}"""
    else:
        body = f"""intro i hi
    have hi' : i < {k} := by omega
    interval_cases i
    exacts [{", ".join(names)}]"""
    lv.append(f"""theorem tab{b}_lv{d} : TabGood {M} (tab{b} {d}) :=
  tabGood_of_ranges {M} (tab{b} {d}) {R} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    {body})
""")
out.append("\nend Palprimes.M2\n")
if len(sys.argv) < 3:
    open(LEAN + f"B{b}Tab.lean", "w").write("\n".join(out))
if len(sys.argv) > 3 and sys.argv[3] == "split":
    # one file per group of at most G ranges
    G = int(sys.argv[4])
    thms = [x for x in out if x.startswith("theorem")]
    files = []
    for g in range(0, len(thms), G):
        nm = f"B{b}Tab{g // G:02d}"
        files.append(nm)
        open(LEAN + nm + ".lean", "w").write("\n".join([f"import Palprimes.Major2D.TabR\nimport Palprimes.Major2D.B{b}Cfg\n",
            f"/-! # Base {b}: range checks of the phase tables, part {g // G} -/\n", "namespace Palprimes.M2\n",
            "set_option maxRecDepth 100000\n"] + thms[g:g + G] + ["\nend Palprimes.M2\n"]))
    open(LEAN + f"B{b}Tab.lean", "w").write("\n".join(f"import Palprimes.Major2D.{f}" for f in files) + "\n")
    print("files", len(files))
open(os.path.join(HERE, f"tablv{b}.txt"), "w").write("\n".join(lv))
print("ok")
