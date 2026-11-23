"""Greaves' weighted sieve (Acta Arith. 40 (1982), Corollary 1) and the table of k(r).

Constants from the note added in proof of Greaves' paper: alpha = 0.1505528, beta = 0.87695, T0 = 0.074368.
U_R = (1 + 3^-R e^{-beta/3})^-1, Delta_R = log(4 U_R / (3 e^alpha)) / log 3,
N_R = (1 - U_R)(R - 1/2) - Delta_R, delta_R = max(Delta_R, Delta_R + N_R).
At level theta the sieve gives Omega <= R as soon as R - delta_R > 1/theta.

Output: thresholds 1/(R - delta_R), checks of the parameter conditions for every R used,
k(r) at the level lambda/2 = log 2/(2 log r), k(r) at the certified block levels (r = 3, 4),
the bound k(r) <= floor(2 log_2 r + Delta_inf) + 1 <= 2 log_2 r + 1.13 for 3 <= r <= 5000,
and the conditions of the square lemma (Lemma 3) and the side condition of Theorem 1(b).
"""
from mpmath import mp, mpf, log, exp, floor, binomial

mp.dps = 30
alpha = mpf('0.1505528'); beta = mpf('0.87695'); T0 = mpf('0.074368')


def U(R): return 1 / (1 + mpf(3) ** (-R) * exp(-beta / 3))
def Delta(R): return log(4 * U(R) / (3 * exp(alpha))) / log(3)
def N(R): return (1 - U(R)) * (R - mpf(1) / 2) - Delta(R)
def delta(R): return max(Delta(R), Delta(R) + N(R))


Dinf = log(mpf(4) / (3 * exp(alpha))) / log(3)
print(f"Delta_inf = {mp.nstr(Dinf, 12)}")
print("\n== Greaves thresholds and parameters at g = R - delta_R (V = g - R U_R)")
print("R  U_R  Delta_R  N_R  1/(R-delta_R)  V  3V+U_R  (1-U_R)/3")
allok = True
for R in list(range(3, 31)) + [40, 60, 100]:
    g = R - delta(R); V = g - R * U(R)
    ok = (N(R) < 0) and (V < mpf(1) / 4) and (3 * V + U(R) <= 1) and (U(R) > mpf(1) / 2) \
        and ((1 - U(R)) / 3 < T0) and (Delta(R) <= Dinf)
    allok &= ok
    if R <= 12 or R in (20, 40, 100):
        print("  ".join(mp.nstr(x, 9) for x in (R, U(R), Delta(R), N(R), 1 / (R - delta(R)), V, 3 * V + U(R), (1 - U(R)) / 3)))
print("all R in 3..30, 40, 60, 100: N_R < 0, V < 1/4, 3V + U_R <= 1, U_R > 1/2, (1-U_R)/3 < T0, Delta_R <= Delta_inf:", allok)
print("(R - 1/2) 3^-R e^{-beta/3} at R = 3:", mp.nstr(mpf(5) / 2 / 27 * exp(-beta / 3), 8), " < Delta_3 =", mp.nstr(Delta(3), 8))


def kR(theta):
    """least R >= 3 with R - delta_R > 1/theta."""
    R = 3
    while not (R - delta(R) > 1 / theta):
        R += 1
    return R


# certified block levels (lower bounds of psi_T from certify.py, truncated to 8 digits) used times (1 - 1e-4)
blocks = {3: mpf('0.35368507'), 4: mpf('0.26029616')}
print("\n== k(r)")
print("   r  lambda/2    k(lambda/2)  block level  k(block)  k(r)  2log2(r)+1.13  8r/pi")
for r in list(range(3, 21)) + [50, 100, 1000]:
    th = log(2) / log(r) / 2
    k = kR(th)
    kb = kR(blocks[r] * (1 - mpf('1e-4'))) if r in blocks else None
    kfin = min(k, kb) if kb else k
    bl = mp.nstr(blocks[r], 8) if r in blocks else "-"
    print(f"{r:4d}  {mp.nstr(th, 7):10s}  {k:3d}          {bl:11s}  {str(kb) if kb else '-':8s}  {kfin:4d}  "
          f"{mp.nstr(2 * log(r) / log(2) + mpf('1.13'), 5):13s}  {mp.nstr(8 * r / mp.pi, 4)}")
bad = [r for r in range(3, 5001) if kR(log(2) / log(r) / 2) > floor(2 * log(r) / log(2) + Dinf) + 1]
print("r in 3..5000 with k(lambda/2) > floor(2 log2 r + Delta_inf) + 1:", bad)
print("max over 3 <= r <= 5000 of k(lambda/2) - 2 log2 r:",
      mp.nstr(max(kR(log(2) / log(r) / 2) - 2 * log(r) / log(2) for r in range(3, 5001)), 8))

print("\n== conditions with k = 2 for r = 3, 4 (m_4 = 3/8)")
for r in (3, 4):
    m4 = binomial(4, 2) / mpf(16); psi4 = -log(m4) / log(r); c2 = 2 * psi4 - 1
    print(f"r={r}: r m_4^2 = {mp.nstr(r * m4 ** 2, 6)} < 1, psi_4 = {mp.nstr(psi4, 6)}, c_2 = {mp.nstr(c2, 6)}")
    for name, th in (("lambda/2", log(2) / log(r) / 2), ("block", blocks[r])):
        need = 2 * th + th * c2 / 2
        print(f"   Lemma 3 at {name} theta = {mp.nstr(th, 7)}: 4 theta = {mp.nstr(4 * th, 5)}, "
              f"2 theta + theta c_2/2 = {mp.nstr(need, 6)} < psi_4: {need < psi4}")
    lam = log(2) / log(r)
    th0 = lam / 2 * mpf('0.95')
    print(f"   side condition of Theorem 1(b): (1-p) theta_0 c_2/(4k) with p = 0.99, theta_0 = 0.95 lambda/2 = "
          f"{mp.nstr(th0, 6)}: {mp.nstr(mpf('0.01') * th0 * c2 / 8, 4)}")
print("\n== k = r - 1 always satisfies r m_{2k}^2 < 1 (r m_{2(r-1)}^2 for r = 3..12):")
print("  ", [mp.nstr(r * (binomial(2 * (r - 1), r - 1) / mpf(4) ** (r - 1)) ** 2, 4) for r in range(3, 13)])
print("least k with r m_{2k}^2 < 1, the level 1/(4k) of the small-moduli lemma and pi/(4r):")
for r in list(range(3, 11)) + [20, 50, 100]:
    k = 1
    while not (r * (binomial(2 * k, k) / mpf(4) ** k) ** 2 < 1):
        k += 1
    print(f"   r={r}: k={k}, c_k={mp.nstr(-2 * log(binomial(2 * k, k) / mpf(4) ** k) / log(r) - 1, 4)}, "
          f"1/(4k)={mp.nstr(mpf(1) / (4 * k), 4)}, pi/(4r)={mp.nstr(mp.pi / (4 * r), 4)}")

print("\n== sensitivity to the truncation of alpha and beta, and margins of the k(r) decisions")
def deltaab(R, a, b):
    U_ = 1 / (1 + mpf(3) ** (-R) * exp(-b / 3)); D_ = log(4 * U_ / (3 * exp(a))) / log(3)
    N_ = (1 - U_) * (R - mpf(1) / 2) - D_
    return max(D_, D_ + N_)
sens = max(abs(deltaab(R, alpha + da, beta + db) - delta(R)) for R in range(3, 60)
           for da in (0, mpf('1e-7')) for db in (0, mpf('1e-5')))
print("max |change of delta_R|, R = 3..59, alpha + 1e-7 and/or beta + 1e-5:", mp.nstr(sens, 4))
def margin(theta):
    """distance of 1/theta to the nearest threshold R - delta_R."""
    return min(abs(R - delta(R) - 1 / theta) for R in range(3, 40))
tab = list(range(3, 13)) + [16, 20, 50, 100, 1000]
mt = min(margin(blocks[r] if r in blocks else log(2) / log(r) / 2) for r in tab)
print("smallest margin over the rows of Table 1:", mp.nstr(mt, 4))
m5000 = min((margin(log(2) / log(r) / 2), r) for r in range(5, 5001))
print("smallest margin at lambda/2 over 5 <= r <= 5000:", mp.nstr(m5000[0], 4), "at r =", m5000[1])
