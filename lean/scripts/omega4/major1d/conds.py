"""Exact exponent forms of (ii), (iii) at kappa = eps = 0 (strict), as Nat inequalities."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
import sys, math, json, time
sys.path.insert(0, HERE)
from fractions import Fraction as Fr
import cells as C
th = Fr(2608, 10000); dl = Fr(47, 100)
def forms(b):
    d = json.load(open(C.FIN + C.FILES[b])); p = Fr(d['p']); c = d['c']
    c0 = c[0]; Anum = c[0] + 2 * sum(c[1:])
    # (ii): 2th log b + log(c0/2^52) < rho log r, rho = 2 th (1-p)/3, r = 3b^2/(2b^2+1)
    g2 = 2 * th; rho = 2 * th * (1 - p) / 3
    D = math.lcm(g2.denominator, rho.denominator); g = int(g2 * D); s = int(rho * D)
    # b^g * c0^D * (2b^2+1)^s < (3b^2)^s * 2^(52 D)
    # (iii): log(Anum/2^52) < sig log r, sig = dl (1-p)/3
    sig = dl * (1 - p) / 3; E = sig.denominator; k = sig.numerator
    # Anum^E * (2b^2+1)^k < (3b^2)^k * 2^(52 E)
    lr = math.log(3 * b * b / (2 * b * b + 1))
    mii = float(rho) * lr - float(g2) * math.log(b) - math.log(c0 / 2**52)
    miii = float(sig) * lr - math.log(Anum / 2**52)
    return dict(p=p, c0=c0, Anum=Anum, D=D, g=g, s=s, E=E, k=k, mii=mii / math.log(b), miii=miii / math.log(b))
if __name__ == '__main__':
    for b in range(4, 10):
        f = forms(b)
        t = time.time()
        ok2 = b**f['g'] * f['c0']**f['D'] * (2*b*b+1)**f['s'] < (3*b*b)**f['s'] * 2**(52*f['D'])
        ok3 = f['Anum']**f['E'] * (2*b*b+1)**f['k'] < (3*b*b)**f['k'] * 2**(52*f['E'])
        print(b, {k: v for k, v in f.items() if k not in ('c0', 'Anum')}, ok2, ok3, '%.2fs' % (time.time() - t))
