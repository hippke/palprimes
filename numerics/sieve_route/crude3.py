import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar
def rankin(t):
    r=minimize_scalar(lambda a: -a*t/2+(np.exp(a)-1), bounds=(1e-6,20), method='bounded'); return np.exp(r.fun)
def g(v):
    if v<=1: return v
    vv=min(v,np.e); return 2*vv-vv*np.log(vv)-1
def Fc(t,eg):
    vals=[eg*max(1.0,2.0/t), eg/g(t/2)]
    tau=rankin(t)
    if tau<1: vals.append(1/(1-tau))
    return min(vals)
def W(th,ze,et,lam,eg):
    s0=th/ze
    I1=quad(lambda t: Fc(t,eg)-1, s0-1, 60, limit=200)[0]
    f=1-I1/s0
    T=quad(lambda u:(1-u/et)*Fc((th-u)/ze,eg)/u, ze, et, limit=200)[0]
    return f,T,lam*f-T
for eg in [np.exp(0.5772156649), np.exp(0.5773), np.exp(2/3)]:
  for ze in [0.05,0.055,0.06,0.065]:
    f,T,w=W(0.24,ze,0.23,1.6,eg)
    print(f"eg={eg:.4f} z=x^{ze}: f={f:.4f} T={T:.4f} W={w:+.4f}")
