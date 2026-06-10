#!/usr/bin/env python3
"""Target 2 at scale: run-start ghost-depth law, global vs net-ascending windows,
against the natural law P[g=j] = 2^{-(j-1)} (j>=2 at run starts... natural odd x:
P[v2(x+1)=j] = 2^{-j}; run starts condition g>=2: P[g=j|g>=2] = 2^{-(j-1)})."""
import math, random
import numpy as np
random.seed(17)
def v2(n):
    c=0
    while n%2==0: n//=2;c+=1
    return c
glob=[]; asc=[]
for trial in range(250):
    x=random.randrange(10**45,10**46)*2+1
    xs=[x]
    while x!=1 and len(xs)<4000:
        y=3*x+1; x=y>>v2(y); xs.append(x)
    # run starts: x = 3 mod 4 whose predecessor step was not in a run (or index 0)
    gs=[]
    i=0
    while i<len(xs)-1:
        g=v2(xs[i]+1)
        if g>=2:
            gs.append((i,g)); i+=g-1   # run consumes g-1 steps
        else: i+=1
    glob.extend(g for _,g in gs)
    # net-ascending dip-tolerant windows: end >= 4x start, never below start
    W=48
    for s in range(0,len(xs)-W,W//2):
        seg=xs[s:s+W]
        if min(seg)>=seg[0] and seg[-1]>=4*seg[0]:
            asc.extend(g for i,g in gs if s<=i<s+W)
glob=np.array(glob); asc=np.array(asc)
print(f"run starts: global n={len(glob)}, ascending-window n={len(asc)}")
print(f"{'g':>3} {'natural':>8} {'global':>8} {'ascending':>9}")
for g in range(2,11):
    nat=2.0**-(g-1)
    pg=(glob==g).mean(); pa=(asc==g).mean() if len(asc)>0 else float('nan')
    print(f"{g:>3} {nat:>8.4f} {pg:>8.4f} {pa:>9.4f}")
print(f"mean depth: natural=3.000 global={glob.mean():.3f} ascending={asc.mean():.3f}")
print(f"mean run length (g-1): natural=2.000 global={glob.mean()-1:.3f} ascending={asc.mean()-1:.3f}")
