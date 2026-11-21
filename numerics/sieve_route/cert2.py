from fractions import Fraction as Fr
import math
th=Fr(99,100); E=Fr(17813,10000); lam=Fr(8,5); EUP=Fr(27182818286,10**10)
def logub(r):           # log r <= t - t^2/2 + t^3/3 + t^4/(1-t), t=r-1 in [0,1)
    t=r-1; assert 0<=t<1; return t-t*t/2+t**3/3+t**4/(1-t)
def gQ(v,c):            # rational lower bound of gKc(c,n,v)
    return v-sum(max(v-c[j],0)*logub(c[j+1]/c[j]) for j in range(len(c)-1))
def expub(q):           # e^{q} upper, q rational >=0 : e^q <= EUP^ceil? use (EUP)^(k) for integer k only
    raise
def rankin_m(v,k):      # m = 1 - k^{-v} e^{(k-1)(1+1/100)} ; bound e^{(k-1)*101/100} <= EUP^(k-1) * e^{(k-1)/100}
    # e^{(k-1)/100} <= 1/(1-(k-1)/100)
    eb=EUP**(k-1)/(1-Fr(k-1,100))
    fv=math.floor(v)
    return 1-Fr(1,k)**fv*eb
def build(nR,nB,nl,nc):
    c=[1+Fr(i,nc)*Fr(18,10) for i in range(nc+1)]   # inner grid 1..2.8
    lad=[1+Fr(i,nl)*Fr(17,10) for i in range(nl+1)]  # 1..2.7
    def ladfloor(v):
        best=None
        for l in lad:
            if l<=v: best=l
        return best
    # Richert grid arithmetic from 49/1000 to 23/100
    aR=[Fr(49,1000)+(Fr(23,100)-Fr(49,1000))*Fr(i,nR) for i in range(nR+1)]
    R=[];eR=Fr(0)
    for a,b in zip(aR,aR[1:]):
        vmax=10*(Fr(6,25)-b)-Fr(1,1000)       # strict
        if vmax<=1: v=vmax; g=v-Fr(1,1000)
        else:
            v=ladfloor(vmax); g=gQ(v,c)-Fr(1,1000)
        M=(1-a/Fr(23,100))*E/(th*g)
        l=logub(b/a); eR+=M*l; R.append((a,b,v,g,M,l))
    # Buchstab grid in v from v(1/20) to v(1/200): u=0.12/(v+1/2)
    vlo=Fr(12,100)/Fr(1,20)-Fr(1,2); vhi=Fr(12,100)/Fr(1,200)-Fr(1,2)
    vs=[vlo+(vhi-vlo)*Fr(i,nB) for i in range(nB+1)]
    aB=sorted(Fr(12,100)/(v+Fr(1,2)) for v in vs)
    Bl=[];eB=Fr(0)
    for a,b in zip(aB,aB[1:]):
        vb=Fr(12,100)/b-Fr(1,2)               # (2v+1) b <= 6/25 exactly
        cands=[]
        vl=ladfloor(min(vb,Fr(27,10)))
        g=gQ(vl,c)-Fr(1,1000); cands.append(("S",vl,th/E*g,g))
        for k in range(2,30):
            m=rankin_m(vb,k)
            if m>0: cands.append(("R%d"%k,vb,m,None))
        best=max(cands,key=lambda z:z[2])
        m=best[2]; m=min(m,Fr(1))
        M=Fr(1)/(20*th**3*a)*(1/m-1)
        l=logub(b/a); eB+=M*l; Bl.append((a,b,best,M,l))
    eT=Fr(1,2000)
    W=lam*(1-eB-eT)-eR
    return float(eR),float(eB),float(W),R,Bl,c,lad
for args in [(36,16,18,20),(48,24,17,18),(60,30,17,18),(72,40,34,36)]:
    eR,eB,W,*_=build(*args)
    print(args, f"eR={eR:.4f} eB={eB:.4f} W={W:+.4f}")

def build2(nR,nB,nl,nc,mode):
    import cert2 as C
