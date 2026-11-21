from fractions import Fraction as Fr
import math
th,ze,et,lam=Fr(6,25),Fr(1,20),Fr(23,100),Fr(8,5)
def gK(v, h):
    # v - sum_j (v-c_j)_+ (min(c_{j+1},v)-c_j)/c_j, grid c_j = 1 + j h
    if v<=1: return v
    s=Fr(0); c=Fr(1)
    while c<v:
        c2=min(c+h,v); s+=(v-c)*(c2-c)/c; c=c+h
    return v-s
def tau(v):
    # min over integer k>=2 of e^{k-1} k^{-floor v}
    fv=math.floor(v)
    return min(math.exp(k-1)*k**(-fv) for k in range(2,40))
def run(E, hu_R, hu_B, hc, u0, vcap):
    # Richert
    eR=0.0; u=ze
    while u<et:
        u2=min(u+hu_R,et)
        v=(th-u2)/(2*ze)          # v at right endpoint (smallest)
        g=gK(v,hc) if v>1 else v
        eR+=float((u2-u)/u*(1-u/et))/float(g)
        u=u2
    eR*=E
    # Buchstab on [u0, ze]
    eB=0.0; u=u0
    while u<ze:
        u2=min(u+hu_B,ze)
        v=((th/u2)-1)/2
        F1=E/float(gK(min(v,vcap),hc))
        t=tau(float(v)); F2=1/(1-t) if t<1 else 1e9
        F=min(F1,F2)
        eB+=float((u2-u)/u)*float(ze/u)*(F-1)
        u=u2
    return eR,eB,float(lam)*(1-eB)-eR
for E in [math.exp(0.5773), math.exp(2/3)]:
  for (hR,hB,hc) in [(Fr(1,200),Fr(1,1000),Fr(1,20)),(Fr(1,400),Fr(1,2000),Fr(1,40)),(Fr(1,100),Fr(1,500),Fr(1,10))]:
    eR,eB,W=run(E,hR,hB,hc,Fr(1,100),Fr(27,10))
    print(f"E={E:.4f} hR={hR} hB={hB} hc={hc}: eR={eR:.4f} eB={eB:.4f} W={W:+.4f}")
