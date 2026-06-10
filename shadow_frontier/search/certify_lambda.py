#!/usr/bin/env python3
"""Certified enclosure of lambda(D) and D* via exact-integer Collatz-Wielandt.
UPPER graph: outward rounding (shift may land in 2 cells: include both; strip widened
by one cell) - every confined word is a path => N_D(p) <= paths => lambda(D) <= CW-upper.
LOWER graph: inward (edge only if the whole shifted cell lies in one target cell inside
the strip) - every path IS a confined word => lambda(D) >= CW-lower.
Bounds computed in exact integers: lambda <= max_j (T V)_j/V_j, lambda >= min_j (T V)_j/V_j
for any positive integer vector V (Collatz-Wielandt), V from float Perron iterate."""
from fractions import Fraction
import math
import numpy as np
LOG23=math.log2(3.0)
BMAX=25

def graphs(D, delta):
    n=int(round(2*D/delta))+1
    xs=[-D+i*delta for i in range(n)]
    up=[[] for _ in range(n)]; lo=[[] for _ in range(n)]   # lists of target indices per source
    for i,x in enumerate(xs):
        for b in range(1,BMAX+1):
            s=LOG23-b
            a=x+s; bb=x+delta+s   # image interval of the cell [x, x+delta)
            # upper: any overlap with [-D-delta, D+delta]
            j1=math.floor((a+D)/delta); j2=math.floor((bb+D)/delta)
            for j in range(j1,j2+1):
                if -1<=j<=n: up[i].append(min(max(j,0),n-1))
            # lower: whole image inside one cell strictly inside the strip
            if a>=-D and bb<=D+delta:
                ja=math.floor((a+D)/delta); jb=math.floor((bb-1e-15+D)/delta)
                if ja==jb and 0<=ja<n: lo[i].append(ja)
    return up,lo,n

def perron_int(adj, n, iters=300):
    v=np.ones(n)
    for _ in range(iters):
        w=np.zeros(n)
        for i in range(n):
            for j in adj[i]: w[j]+=v[i]
        nv=np.linalg.norm(w)
        if nv==0: return None,0.0
        v=w/nv
    V=[int(x*10**12)+1 for x in v]
    return V,nv

def cw_bounds(adj,n,V,mode):
    # exact integer ratios of (T V)_j / V_j  -- T acts by column j gets sum over i with j in adj[i] of V_i
    TV=[0]*n
    for i in range(n):
        for j in adj[i]: TV[j]+=V[i]
    rs=[Fraction(TV[j],V[j]) for j in range(n) if TV[j]>0 or mode=='min']
    return (max(rs) if mode=='max' else min(Fraction(TV[j],V[j]) for j in range(n)))

def trim(adj,n):
    # iteratively remove vertices with no out- or no in-edges (keep recurrent core)
    alive=[True]*n
    changed=True
    while changed:
        changed=False
        indeg=[0]*n
        for i in range(n):
            if alive[i]:
                for j in adj[i]:
                    if alive[j]: indeg[j]+=1
        for i in range(n):
            if alive[i]:
                outs=any(alive[j] for j in adj[i])
                if not outs or indeg[i]==0:
                    alive[i]=False; changed=True
    keep=[i for i in range(n) if alive[i]]
    rmp={i:k for k,i in enumerate(keep)}
    adj2=[[rmp[j] for j in adj[i] if alive[j]] for i in keep]
    return adj2,len(keep)

for D,delta in [(1.05,0.003),(1.10,0.003),(1.15,0.003),(1.232,0.003),(1.35,0.003)]:
    up,lo,n=graphs(D,delta)
    up2,n2=trim(up,n)
    if n2==0:
        print(f"D={D:.3f}: upper graph empty after trim => lambda(D) <= 1"); continue
    Vu,fl=perron_int(up2,n2,iters=500)
    ub=cw_bounds(up2,n2,Vu,'max')
    print(f"D={D:.3f} (delta={delta}, core n={n2}/{n}): float~{fl:.4f}  CERTIFIED lambda(D) <= {float(ub):.4f}"
          f"   {'< 2: NARROW-BAND THEOREM CERTIFIED AT THIS D' if ub<2 else ''}")
