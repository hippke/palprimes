"""Runs every check of the paper one after the other (one child process at a time) and writes logs/.
Usage (from any folder): python -I scripts/run_all.py"""
import subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PY = sys.executable
SHIFT = str(-round(1e-6 * 2 ** 50))   # tau_0 lowered by about 1e-6 (negative control)
jobs = [
    ("certify.log", [["certify.py", "data/majorant_r3_l4.json"], ["certify.py", "data/majorant_r4_l4.json"],
                     ["certify.py", "data/majorant_r3_l4.json", SHIFT], ["certify.py", "data/majorant_r4_l4.json", SHIFT],
                     ["neg_control.py", "data/majorant_r3_l4.json"], ["neg_control.py", "data/majorant_r4_l4.json"]]),
    # sensitivity: a shift of -2e-9 (beyond the float grid margin of about 9e-10) must fail, -2e-10 should still pass
    ("certify_sensitivity.log", [["certify.py", f, str(round(sh * 2 ** 50))]
                                 for f in ("data/majorant_r3_l4.json", "data/majorant_r4_l4.json") for sh in (-2e-9, -2e-10)]),
    ("greaves_k.log", [["greaves_k.py"]]),
    ("theory_checks.log", [["theory_checks.py"]]),
    ("prop_h_test.log", [["prop_h_test.py"]]),
]
(ROOT / "logs").mkdir(exist_ok=True)
for log, cmds in jobs:
    with open(ROOT / "logs" / log, "w") as f:
        for c in cmds:
            t0 = time.time()
            f.write("### " + " ".join(c) + "\n"); f.flush()
            subprocess.run([PY, "-I", str(ROOT / "scripts" / c[0])] + c[1:], stdout=f, stderr=subprocess.STDOUT, cwd=ROOT)
            f.write(f"### wall time {time.time() - t0:.1f} s\n\n"); f.flush()
    print(log, "done", flush=True)
