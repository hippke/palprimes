"""major2d (2026-11-22): exact-integer reference of the Lean checker (Palprimes/Major2D).  Mirrors the Lean definitions.

Cells at level d: centre (J/N, K/N), N = 2 Q0 2^d, J, K odd, half-width 1/N.  Doubled frequencies (U, V): a term (U, V, c)
of a sum with denominator Dn is (c/Dn) cos(2 pi (U x + V y)/2).  Phase index n = (U J + V K) mod M, M = 2N, table e(n/M).
TM: coefficients of sigma^a rho^b (|sigma|, |rho| <= 1, sigma = 2 pi s/(2r), r = Rn/2^RB >= pi/N) at scale 2^-Q, remainder.
"""
import math, json, sys, time
from fractions import Fraction

P = 62          # table scale
Q = 64          # TM scale
H = 160         # packed field width
OK = 1 << 80    # coefficient offset
RB = 80
EPS_TAB_UNITS = 4  # table error <= 4 * 2^-62 = 2^-60 per component
PI_LO = (314159265358979323846, 10 ** 20)
PI_HI = (314159265358979323847, 10 ** 20)
NTAY = 28
MASK64 = (1 << 64) - 1
MASKH = (1 << H) - 1
EVEN = [(0, 0), (2, 0), (1, 1), (0, 2)]
ODD = [(1, 0), (0, 1), (3, 0), (2, 1), (1, 2), (0, 3)]
FACT6 = {(0, 0): 6, (1, 0): 6, (0, 1): 6, (2, 0): 3, (1, 1): 6, (0, 2): 3, (3, 0): 1, (2, 1): 3, (1, 2): 3, (0, 3): 1}
MONS = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2), (3, 0), (2, 1), (1, 2), (0, 3)]


def fdiv(a, b):
    return a // b   # floor (b > 0)


def cdiv(a, b):
    return -((-a) // b)


# ---------------- table ----------------
def taySums(a, b, n):
    """Sigma_{k<n} (i a/b)^k / k! = (re + i im) / den, den = b^(n-1) (n-1)!  (exact)."""
    den = b ** (n - 1) * math.factorial(n - 1)
    re = im = 0
    for k in range(n):
        ck = a ** k * b ** (n - 1 - k) * (math.factorial(n - 1) // math.factorial(k))
        m = k % 4
        if m == 0: re += ck
        elif m == 1: im += ck
        elif m == 2: re -= ck
        else: im -= ck
    return re, im, den


def entry(n, M):
    """(Cf, Sf): floor((cos(2 pi n/M) + 1) 2^P), same for sin.  M divisible by 4."""
    q, r = divmod(4 * n, M)
    r //= 4  # n = q M/4 + r'
    rp = n - q * (M // 4)
    a = 2 * PI_LO[0] * rp
    b = PI_LO[1] * M
    re, im, den = taySums(a, b, NTAY)
    if q == 0: c, s = re, im
    elif q == 1: c, s = -im, re
    elif q == 2: c, s = -re, -im
    else: c, s = im, -re
    Cf = fdiv((c + den) << P, den)
    Sf = fdiv((s + den) << P, den)
    return Cf, Sf


_tabs = {}


def table(M):
    if M not in _tabs:
        _tabs[M] = [entry(n, M) for n in range(M)]
    return _tabs[M]


# ---------------- sums ----------------
def kappa(U, V, c, ab):
    a, b_ = ab
    return c * U ** a * V ** b_ * FACT6[ab]


class Sum:
    def __init__(self, terms, Dn, offset):
        """terms: list of (U, V, c) (c >= 0 integers), Dn denominator."""
        self.terms = terms
        self.Dn = Dn
        self.off = offset
        self.packed = []
        for (U, V, c) in terms:
            KE = sum((kappa(U, V, c, ab) + OK) << (H * j) for j, ab in enumerate(EVEN)) + (1 << (H * 4))
            KO = sum((kappa(U, V, c, ab) + OK) << (H * j) for j, ab in enumerate(ODD)) + (1 << (H * 6))
            for ab in MONS:
                assert abs(kappa(U, V, c, ab)) < OK
            assert U + offset >= 0 and V + offset >= 0
            self.packed.append((U + offset, V + offset, KE, KO))
        self.sk = {ab: sum(kappa(U, V, c, ab) for (U, V, c) in terms) for ab in MONS}
        self.G0 = sum(c for (U, V, c) in terms)
        self.G4 = sum(c * (abs(U) + abs(V)) ** 4 for (U, V, c) in terms)


def Rn(N):
    return cdiv(PI_HI[0] << RB, PI_HI[1] * N)


def remConst(S, N):
    """ceil(2^Q [G4 r^4 (1 + 2 eps)/24 + 2 eps G0]/Dn) + 10, r = Rn/2^RB, eps = 2^-60."""
    r = Fraction(Rn(N), 1 << RB)
    eps = Fraction(EPS_TAB_UNITS, 1 << P)
    val = (Fraction(S.G4) * r ** 4 * (1 + 2 * eps) / 24 + 2 * eps * S.G0) / S.Dn * (1 << Q)
    return math.ceil(val) + 10


def tm(S, tab, M, J, K, N):
    AE = AO = 0
    TAB = tab
    for (Uo, Vo, KE, KO) in S.packed:
        n = (Uo * J + Vo * K) % M
        Cf, Sf = TAB[n]
        AE += Cf * KE
        AO += Sf * KO
    sC = AE >> (4 * H)
    sS = AO >> (6 * H)
    rn = Rn(N)
    coef = {}
    for j, ab in enumerate(EVEN):
        F = (AE >> (H * j)) & MASKH
        Sab = F - OK * sC - (S.sk[ab] << P)
        k = ab[0] + ab[1]
        sg = 1 if k == 0 else -1
        coef[ab] = fdiv(sg * Sab * rn ** k << Q, 6 * S.Dn * (1 << P) * (1 << (k * RB)))
    for j, ab in enumerate(ODD):
        F = (AO >> (H * j)) & MASKH
        Sab = F - OK * sS - (S.sk[ab] << P)
        k = ab[0] + ab[1]
        sg = -1 if k == 1 else 1
        coef[ab] = fdiv(sg * Sab * rn ** k << Q, 6 * S.Dn * (1 << P) * (1 << (k * RB)))
    return [coef[ab] for ab in MONS], remConst(S, N)


# ---------------- products ----------------
def prodSum(sums):
    """list of (terms, Dn) -> (terms, Dn) of the product (cos a cos b = (cos(a+b) + cos(a-b))/2)."""
    if not sums:
        return [(0, 0, 1)], 1
    if len(sums) == 1:
        return sums[0]
    (t1, d1) = sums[0]
    (t2, d2) = prodSum(sums[1:])
    out = []
    for (U1, V1, c1) in t1:
        for (U2, V2, c2) in t2:
            out.append((U1 + U2, V1 + V2, c1 * c2))
            out.append((U1 - U2, V1 - V2, c1 * c2))
    return out, 2 * d1 * d2


# ---------------- power bound ----------------
class PowEps:
    def __init__(self, n0):
        self.n0 = n0
        # U2 >= 2^(1/n0) 2^Q, Vn_j >= (1 + j/256)^(-1/n0) 2^Q
        import mpmath
        mpmath.mp.prec = 200
        self.U2 = int(mpmath.ceil(mpmath.mpf(2) ** (mpmath.mpf(1) / n0) * 2 ** Q)) + 1
        assert self.U2 ** n0 >= 2 << (Q * n0)
        self.V = []
        for j in range(256):
            v = int(mpmath.ceil((1 + mpmath.mpf(j) / 256) ** (-mpmath.mpf(1) / n0) * 2 ** Q)) + 1
            assert v ** n0 * (256 + j) >= 256 << (Q * n0)
            self.V.append(v)

    def inv(self, X):
        """upper bound (scale Q) of (X/2^Q)^(-1/n0), 1 <= X <= 2^Q."""
        L = X.bit_length() - 1
        e = Q - L
        j = ((X << 8) >> L) - 256
        return cdiv(self.U2 ** e * self.V[j], 1 << (Q * e))


# ---------------- base data ----------------
class Base:
    def __init__(self, b, l, n0, Tterms_half, Q0, dmax, thr):
        self.b, self.l, self.n0, self.Q0, self.dmax, self.thr = b, l, n0, Q0, dmax, thr
        self.off = 4 * Q0 * (1 << 24)
        self.T = Sum(Tterms_half, 1 << 52, self.off)
        self.fac = []
        for i in range(l):
            cx, cy = b ** i, b ** (l - 1 - i)
            if b == 2:
                self.fac.append(([(cx, cy, 1)], 1))
            elif b == 3:
                self.fac.append(([(0, 0, 1), (2 * cx, 2 * cy, 2)], 3))
        self.facS = [Sum(t, d, self.off) for (t, d) in self.fac]
        self.prodS = {}
        self.pe = PowEps(n0)

    def A(self, I):
        I = tuple(I)
        if I not in self.prodS:
            t, d = prodSum([self.fac[i] for i in I])
            self.prodS[I] = Sum(t, d, self.off)
        return self.prodS[I]


def lower_ok(h, remH):
    """h: 10 coefficients (scale 2^(2Q)), polynomial on [-1,1]^2; True if min > remH (certified)."""
    h00, h10, h01, h20, h11, h02, h30, h21, h12, h03 = h
    c3 = abs(h30) + abs(h21) + abs(h12) + abs(h03)
    base = h00 - c3 - remH
    if base - abs(h10) - abs(h01) - abs(h20) - abs(h11) - abs(h02) > 0:
        return True
    a, bb, c = h20, h11, h02
    D = 4 * a * c - bb * bb
    if a > 0 and D > 0:
        Nn = c * h10 * h10 - bb * h10 * h01 + a * h01 * h01
        if base * D > Nn:
            return True
    return False


def cell_ok(B, d, J, K, stats=None):
    N = 2 * B.Q0 << d
    M = 2 * N
    tab = table(M)
    tc, rT = tm(B.T, tab, M, J, K, N)
    fs = [tm(S, tab, M, J, K, N) for S in B.facS]
    one = 1 << Q
    sgn, dfn, sup, a0 = [], [], [], []
    for (c, r) in fs:
        s = 1 if c[0] >= 0 else -1
        rest = sum(abs(x) for x in c[1:])
        sgn.append(s)
        dfn.append(abs(c[0]) - rest - r >= 0)
        sup.append(min(one, abs(c[0]) + rest + r))
        a0.append(abs(c[0]))
    F0 = [i for i in range(B.l) if not dfn[i]]
    tried = set()
    for thr in B.thr:
        F = tuple(i for i in range(B.l) if (not dfn[i]) or a0[i] < thr)
        if F in tried:
            continue
        tried.add(F)
        I = [i for i in range(B.l) if i not in F]
        Ac, rA = tm(B.A(I), tab, M, J, K, N)
        sg = 1
        for i in I: sg *= sgn[i]
        Ac = [sg * x for x in Ac]
        St = one
        for i in F: St = cdiv(St * sup[i], one)
        Ct = min(one, max(Ac[0], 1))
        X = fdiv(St * Ct, one)
        if X < 1:
            continue
        pe = B.pe.inv(X)
        Wt = cdiv(St * pe, one)
        K1 = cdiv(Wt * (B.n0 - 1), B.n0)
        K0 = cdiv(Wt * Ct, B.n0 * one)
        h = [tc[k] * one - K1 * Ac[k] for k in range(10)]
        h[0] -= K0 * one
        remH = rT * one + K1 * rA
        if lower_ok(h, remH):
            if stats is not None:
                stats[len(tried) - 1] = stats.get(len(tried) - 1, 0) + 1
            return True
    return False


def check(B, d, J, K, stats, per):
    if cell_ok(B, d, J, K, stats):
        per[d] = per.get(d, 0) + 1
        return True
    if d >= B.dmax:
        return False
    return all(check(B, d + 1, 2 * J + a, 2 * K + c, stats, per) for (a, c) in ((-1, -1), (1, -1), (-1, 1), (1, 1)))


def canonical(b, l, Q0):
    m = b * b - 1
    st = Q0 // m
    lam = [(a, c) for a in range(m) for c in range(m) if (a + b ** (l - 1) * c) % m == 0]
    out = []
    for j in range(Q0):
        for k in range(Q0):
            code = j * Q0 + k
            best = code
            for (a, c) in lam:
                for sw in (0, 1):
                    for ng in (0, 1):
                        j2, k2 = (k, j) if sw else (j, k)
                        if ng: j2, k2 = Q0 - 1 - j2, Q0 - 1 - k2
                        best = min(best, ((j2 + a * st) % Q0) * Q0 + (k2 + c * st) % Q0)
            if best == code:
                out.append((j, k))
    return out


def load(fn):
    d = json.load(open(fn))
    half = [(2 * u, 2 * v, (n if (u, v) == (0, 0) else 2 * n)) for (u, v, n) in d["terms"] if (u, v) == (0, 0) or u > 0 or (u == 0 and v > 0)]
    # put (0,0) first
    half.sort(key=lambda t: (t[0] != 0 or t[1] != 0, t[0], t[1]))
    return d, half


if __name__ == "__main__":
    fn = sys.argv[1]; Q0 = int(sys.argv[2]); dmax = int(sys.argv[3])
    d, half = load(fn)
    from fractions import Fraction as Fr
    p = Fr(d["p"]); n0 = (1 / (1 - p)).numerator
    one = 1 << Q
    thr = [0, int(0.15 * one), int(0.3 * one), int(0.5 * one), int(0.75 * one), one + 1]
    B = Base(d["b"], d["l"], n0, half, Q0, dmax, thr)
    cells = canonical(d["b"], d["l"], Q0)
    lim = int(sys.argv[4]) if len(sys.argv) > 4 else len(cells)
    stats, per = {}, {}
    t0 = time.time(); bad = []
    for (j, k) in cells[:lim]:
        if not check(B, 0, 2 * j + 1, 2 * k + 1, stats, per):
            bad.append((j, k))
    print("cells", lim, "bad", len(bad), bad[:10], "leaves", sum(per.values()), "per", dict(sorted(per.items())), "opt", stats,
          f"{time.time() - t0:.0f}s")
