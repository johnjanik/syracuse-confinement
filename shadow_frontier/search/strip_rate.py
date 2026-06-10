#!/usr/bin/env python3
"""Growth rate lambda(D) of valuation words with discrepancy |B_j - j*log2(3)| <= D
confined to a strip, via transfer matrix on a discretized strip. theta(D)=ln lambda/ln 2:
theta < 1 => banded windows of half-width D force repetition before filling the band."""
import numpy as np, math
LOG23=math.log2(3.0); LN2=math.log(2.0)
def lam(D, grid=0.02, bmax=18, bias_eps=0.0):
    xs=np.arange(-D,D+1e-9,grid); n=len(xs)
    T=np.zeros((n,n))
    for i,s in enumerate(xs):
        for b in range(1,bmax+1):
            s2=s+LOG23-b
            if -D-1e-9<=s2<=D+1e-9:
                j=int(round((s2+D)/grid))
                if 0<=j<n: T[j,i]+=1.0
    # power iteration
    v=np.ones(n)
    for _ in range(600):
        v=T@v; nv=np.linalg.norm(v)
        if nv==0: return 0.0
        v/=nv
    return float(nv)
print(f"{'D':>5} {'lambda(D)':>10} {'theta=ln l/ln2':>14}   (theta<1: narrow-band squeeze ACTIVE)")
for D in (0.5,0.8,1.0,1.5,2.0,3.0,4.0,6.0,9.0,13.0):
    l=lam(D)
    print(f"{D:>5.1f} {l:>10.4f} {math.log(l)/LN2 if l>0 else float('nan'):>14.3f}")
