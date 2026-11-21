import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar
eg=np.exp(0.5772156649)
def rankin(t, c1=0.0):
    # relative tail bound tau for xi = p^{t/2}: min_a exp(-a t/2 + (e^a-1)(1+c1))
    r=minimize_scalar(lambda a: -a*t/2+(np.exp(a)-1)*(1+c1), bounds=(1e-6,20), method='bounded')
    return np.exp(r.fun)
def Fc(t, G2=True):
    vals=[]
    if G2:
        vals.append(eg*max(1.0, 2.0/t))
    tau=rankin(t)
    if tau<1: vals.append(1/(1-tau))
    return min(vals)
th,ze,et,lam=0.24,0.06,0.23,1.6
s0=th/ze
I1=quad(lambda t: Fc(t)-1, s0-1, 200, limit=400)[0]
f=1-I1/s0
T=quad(lambda u:(1-u/et)*Fc((th-u)/ze)/u, ze, et, limit=400)[0]
print("f_c(4)=",f," T=",T," W/XV=",lam*f-T)
for t in [3,4,5,6,8,10]: print(t, Fc(t), rankin(t))
