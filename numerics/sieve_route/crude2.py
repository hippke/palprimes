import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar
eg=np.exp(0.5772156649)
def Ein(a): return quad(lambda t:(np.exp(t)-1)/t if t>0 else 1.0,0,a)[0]
def rankin(t, sharp):
    f=(lambda a: -a*t/2+Ein(a)) if sharp else (lambda a: -a*t/2+(np.exp(a)-1))
    r=minimize_scalar(f, bounds=(1e-6,20), method='bounded'); return np.exp(r.fun)
def g(v):
    if v<=1: return v
    vv=min(v,np.e); return 2*vv-vv*np.log(vv)-1
def Fc(t, sharp=False, smooth=True):
    vals=[eg*max(1.0,2.0/t)]
    if smooth: vals.append(eg/g(t/2))
    tau=rankin(t,sharp)
    if tau<1: vals.append(1/(1-tau))
    return min(vals)
th,ze,et,lam=0.24,0.06,0.23,1.6
for sharp in [False,True]:
  for smooth in [False,True]:
    s0=th/ze
    I1=quad(lambda t: Fc(t,sharp,smooth)-1, s0-1, 60, limit=200)[0]
    f=1-I1/s0
    T=quad(lambda u:(1-u/et)*Fc((th-u)/ze,sharp,smooth)/u, ze, et, limit=200)[0]
    print(f"sharpRankin={sharp} smooth={smooth}: f_c(4)={f:.4f} T={T:.4f} W/XV={lam*f-T:+.4f}")
