#!/usr/bin/env python3
"""Certified upper bound on the confined-word count via the DETERMINISTIC cell graph.
Each word's rounded-state path is unique; rounding error accumulates <= p*delta/2, so
  N_D(p) <= #paths of det-graph on strip [-(D+eta), D+eta], eta = p*delta/2,
valid for all p <= P_MAX. Collatz-Wielandt upper bound in exact integers, after trim."""
from fractions import Fraction
import math
import numpy as np
LOG23=math.log2(3.0); BMAX=30
def certify(D, delta, PMAX):
    eta=PMAX*delta/2
    Dw=D+eta
    n=int(math.floor(2*Dw/delta))+1
    x0=-Dw
    # deterministic target per (i,b): j = round((x_i + s_b - x0)/delta)
    adj=[[] for _ in range(n)]
    for i in range(n):
        xi=x0+i*delta
        for b in range(1,BMAX+1):
            s=LOG23-b
            xt=xi+s
            if -Dw-delta/2<=xt<=Dw+delta/2:
                j=int(round((xt-x0)/delta))
                if 0<=j<n: adj[i].append(j)
    # trim to recurrent core
    alive=[True]*n; changed=True
    while changed:
        changed=False
        indeg=[0]*n
        for i in range(n):
            if alive[i]:
                for j in adj[i]:
                    if alive[j]: indeg[j]+=1
        for i in range(n):
            if alive[i] and (indeg[i]==0 or not any(alive[j] for j in adj[i])):
                alive[i]=False; changed=True
    keep=[i for i in range(n) if alive[i]]
    if not keep: return 0.0,1.0,0
    rmp={i:k for k,i in enumerate(keep)}
    A=[[rmp[j] for j in adj[i] if alive[j]] for i in keep]
    m=len(keep)
    v=np.ones(m)
    for _ in range(600):
        w=np.zeros(m)
        for i in range(m):
            for j in A[i]: w[j]+=v[i]
        nv=np.linalg.norm(w); v=w/nv
    V=[int(t*10**12)+1 for t in v]
    # tighten: exact integer power iterations before Collatz-Wielandt
    for _ in range(40):
        W=[0]*m
        for i in range(m):
            for j in A[i]: W[j]+=V[i]
        V=[w if w>0 else 1 for w in W]
    TV=[0]*m
    for i in range(m):
        for j in A[i]: TV[j]+=V[i]
    ub=max(Fraction(TV[j],V[j]) for j in range(m))
    return nv,float(ub),m
for D,delta,PMAX in [(0.9,0.0008,100),(1.0,0.0008,100),(1.1,0.0008,100),(1.15,0.0005,100),(1.2,0.0005,100)]:
    fl,ub,m=certify(D,delta,PMAX)
    print(f"D={D:.2f} (delta={delta}, p<=({PMAX}), core={m}): float={fl:.4f}  CERTIFIED N_D(p) <= C*({ub:.4f})^p"
          f"{'   < 2: NARROW-BAND COUNT CERTIFIED' if ub<2 else ''}")
