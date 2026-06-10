#!/usr/bin/env python3
"""Target 2 diagnostics: band-crossing statistics on real orbits.
For maximal ascending (no-descent) stretches: crossing speed delta
(steps per height-bit vs the minimum 1/(log2(3)-1)), b=1 density,
max run of 1s, and max ghost proximity v2(x_n+1) - testing the
run-length <=> 2-adic identity (k-run of 1s => x = -1 mod 2^{k+1})."""
import math, random, json
import numpy as np
LOG23=math.log2(3.0)
random.seed(13)
rows=[]
for trial in range(400):
    x=random.randrange(10**40,10**41)*2+1
    prev=x; stretch=[]
    for _ in range(3000):
        y=3*x+1;b=0
        while y%2==0: y//=2;b+=1
        if y>x:
            stretch.append((b,x))
        else:
            if len(stretch)>=8:
                bs=[b for b,_ in stretch]
                xs=[xx for _,xx in stretch]
                gain=math.log2(float(3*xs[-1]+1))-b-math.log2(float(xs[0])) if False else \
                     (len(bs)*LOG23-sum(bs))
                if gain>0.5:
                    d1=bs.count(1)/len(bs)
                    # max run of 1s
                    mr=0;cur=0
                    for bb in bs:
                        cur=cur+1 if bb==1 else 0; mr=max(mr,cur)
                    mv=max(( (xx+1)&-(xx+1) ).bit_length()-1 for xx in xs)
                    speed=len(bs)/gain    # steps per height-bit (min = 1/(log23-1) = 1.71)
                    rows.append((len(bs),gain,speed,d1,mr,mv))
            stretch=[]
        x=y
        if x==1: break
rows=np.array(rows)
print(f"ascending stretches collected: {len(rows)}")
print(f"{'len':>5} {'gain(bits)':>10} {'steps/bit':>9} {'1-density':>9} {'maxrun1':>7} {'max v2(x+1)':>11}")
# bin by speed
spd=rows[:,2]
for lo,hi in [(1.71,2.0),(2.0,2.5),(2.5,3.5),(3.5,6.0)]:
    sel=(spd>=lo)&(spd<hi)
    if sel.sum()>5:
        r=rows[sel]
        print(f"speed {lo:.2f}-{hi:.2f}: n={sel.sum():4d}  1-dens={r[:,3].mean():.3f}  maxrun={r[:,4].mean():.2f}  max v2(x+1)={r[:,5].mean():.2f}  (run+1<=v2 check: {np.mean(r[:,5]>=r[:,4]+1):.2f})")
# the run <-> v2 identity check globally
ok=np.mean(rows[:,5]>=rows[:,4]+1)
print(f"\nidentity check P[max v2(x+1) >= maxrun+1] = {ok:.3f}  (theory: 1.000)")
# correlation: fast crossings vs ghost proximity
from numpy import corrcoef
print(f"corr(1/speed, max v2(x+1)) = {corrcoef(1/rows[:,2],rows[:,5])[0,1]:.3f}")
print(f"corr(1-density, maxrun)    = {corrcoef(rows[:,3],rows[:,4])[0,1]:.3f}")
np.save('results/crossing_stats.npy',rows)
