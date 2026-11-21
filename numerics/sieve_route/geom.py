import math
th,ze,et,lam=0.24,0.05,0.23,1.6
L2=math.log(2)
def gK(v,m):
    # smooth bound: v - sum_j (v - c_j)_+ * log2/m over grid c_j=2^{j/m} < v (weights at left endpoints)
    if v<=1: return v
    s=0.0; j=0
    while 2**(j/m)<v:
        s+=(v-2**(j/m))*L2/m; j+=1
    return v-s
def tau(v):
    fv=math.floor(v); return min(math.exp(k-1)*k**(-fv) for k in range(2,40))
def run(E,mR,mB,mc,u0=0.01,vcap=2.7):
    eR=0.0; i=0
    while ze*2**(i/mR)<et:
        u=ze*2**(i/mR); u2=min(ze*2**((i+1)/mR),et)
        v=(th-u2)/(2*ze); g=gK(v,mc)
        eR+=L2/mR*(1-u/et)/g; i+=1
    eR*=E
    eB=0.0; i=0
    while u0*2**(i/mB)<ze:
        u=u0*2**(i/mB); u2=min(u0*2**((i+1)/mB),ze)
        v=(th/u2-1)/2
        F=min(E/gK(min(v,vcap),mc), (1/(1-tau(v)) if tau(v)<1 else 1e9))
        eB+=L2/mB*(ze/u)*(F-1); i+=1
    return eR,eB,lam*(1-eB)-eR
for E in [math.exp(0.5773), math.exp(2/3)]:
  for (mR,mB,mc) in [(8,8,8),(16,16,16),(32,16,16),(32,32,32),(64,32,32)]:
    eR,eB,W=run(E,mR,mB,mc)
    print(f"E={E:.4f} mR={mR} mB={mB} mc={mc}: eR={eR:.4f} eB={eB:.4f} W={W:+.4f}")
