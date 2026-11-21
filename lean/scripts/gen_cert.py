from fractions import Fraction as Fr
import math
def logub(r):
    t=r-1; return t-t*t/2+t**3/3+t**4/(1-t)
c=[1+Fr(i,10) for i in range(19)]
def gQ(v): return v-sum(max(v-c[i],0)*logub(c[i+1]/c[i]) for i in range(18))
E=Fr(27182818286,10**10)
def up6(x): return Fr(math.ceil(x*10**6),10**6)
nR=48; aR=lambda j: Fr(49,1000)+j*Fr(181,48000)
R=[]
for j in range(nR):
    a,b=aR(j),aR(j+1)
    v=min(10*(Fr(6,25)-b)-Fr(1,1000),Fr(28,10)); g=gQ(v)-Fr(1,10000)
    assert g>0 and b<2*a and v>=0
    val=(1-a/Fr(23,100))*Fr(17813,10000)/(Fr(99,100)*g)*logub(b/a)
    R.append(up6(val))
nB=20; aB=lambda j: Fr(1,200)+j*Fr(9,4000)
Bd=[]
for j in range(nB):
    a,b=aB(j),aB(j+1); assert b<2*a
    vb=Fr(3,25)/b-Fr(1,2)
    v=min(vb,Fr(28,10)); g=gQ(v)-Fr(1,10000); m=Fr(99,100)*Fr(10000,17813)*g
    best=None
    if g>0 and m<=1:
        val=1/(20*Fr(99,100)**3*a)*(1/m-1)*logub(b/a); best=('S',v,up6(val))
    n=math.floor(vb)
    for k in range(2,60):
        mQ=1-Fr(1,k)**n*E**(k-1)/(1-Fr(k-1,100))
        if mQ>0:
            val=1/(20*Fr(99,100)**3*a)*(1/mQ-1)*logub(b/a)
            if best is None or up6(val)<best[2]: best=('R',(k,n),up6(val))
    Bd.append(best)
QR=sum(R); QB=sum(x[2] for x in Bd); d=Fr(1,1000)
W=Fr(8,5)*(1-(Fr(1,2000)+d)-(QB+d))-(QR+d)
print("QR",float(QR),"QB",float(QB),"margin",float(W))
print([ (x[0], x[1] if x[0]=='R' else float(x[1])) for x in Bd])
import os, pickle; pickle.dump((R,Bd,QR,QB),open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'cert_data.pkl'),'wb'))
