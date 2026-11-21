import sys, itertools, numpy as np
sys.argv=[sys.argv[0]]
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); from sieve_feasibility import *
al, be = 0.06225, 0.2218
parts = [p for om in range(1, 7) for p in itertools.combinations_with_replacement(range(1, 7), om) if sum(p) == 6]
for c0 in [0.0, 0.125]:
  for a in parts:
    om=len(a); c=np.r_[np.zeros(om),np.ones(om)]; A=[];b=[]
    for i in range(om):
        r=np.zeros(2*om); r[i]=-1/be; r[om+i]=-1; A.append(r); b.append(-1)
    A.append(np.r_[np.array(a,float),np.zeros(om)]); b.append(1)
    bounds=[((max(c0,al) if a[i]>=2 else al),1) for i in range(om)]+[(0,None)]*om
    r=linprog(c,A_ub=np.array(A),b_ub=b,bounds=bounds)
    print(c0, a, "min penalty %.3f" % r.fun if r.status==0 else "infeasible", "t=", np.round(r.x[:om],3) if r.status==0 else "")
