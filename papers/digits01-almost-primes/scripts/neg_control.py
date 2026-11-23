"""Negative control for a block majorant. Lowers tau_0 by 1e-6 (an integer shift of ints[0]) and exhibits,
by a rigorous arb point evaluation, a point t with T(t) - K(t)^p < 0, i.e. the shifted function is not a
majorant. The candidate point comes from a float grid of 2,000,001 points on [0, 1/2].

Usage: python -I neg_control.py data/majorant_r3_l4.json
"""
import sys, json
from pathlib import Path
import numpy as np
from flint import arb, ctx

ctx.prec = 192
ROOT = Path(__file__).resolve().parent.parent

path = Path(sys.argv[1])
if not path.is_absolute():
    path = ROOT / path
d = json.load(open(path))
r, l = d["r"], d["l"]
S = 2 ** d["scale_log2"]
ints = list(d["ints"])
sh = -round(1e-6 * S)
ints[0] += sh
tau = np.array(ints, float) / S
H = len(ints) - 1
pf = d["p_num"] / d["p_den"]
t = np.linspace(0, 0.5, 2_000_001)
T = np.full_like(t, tau[0])
for k in range(1, H + 1):
    if tau[k] != 0:
        T += 2 * tau[k] * np.cos(2 * np.pi * k * t)
K = np.ones_like(t)
for i in range(l):
    K *= np.abs(np.cos(np.pi * r ** i * t))
gap = T - K ** pf
j = int(np.argmin(gap))
t0 = t[j]
q = arb(round(t0 * 2 ** 40)) / 2 ** 40          # dyadic point next to the float minimum
Ta = arb(ints[0]) / S + 2 * sum(arb(ints[k]) / S * arb.cos_pi(2 * k * q) for k in range(1, H + 1))
Ka = arb(1)
for i in range(l):
    Ka *= abs(arb.cos_pi(r ** i * q))
Ga = (Ka.log() * arb(d["p_num"]) / d["p_den"]).exp()
diff = Ta - Ga
print(f"{path.name}: tau0 shifted by {sh}/2^{d['scale_log2']} (about -1e-6)")
print(f"  float minimum of T - K^p on the grid {gap.min():.4e} at t = {t0:.10f}")
print(f"  arb value of T - K^p at the dyadic point t = {float(q):.12f}: {diff.str(5)}")
print(f"  REFUTED={bool(diff < 0)}")
print(f"  unshifted float minimum of T - K^p on the grid: {(gap - sh / S).min():.4e}")
