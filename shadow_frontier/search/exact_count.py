#!/usr/bin/env python3
"""EXACT confined-word count N_D(p) via the rotation-driven integer recursion.
A word is D-confined iff B_j is an integer in [j*log2(3)-D, j*log2(3)+D] for all j:
at most floor(2D)+1 integer values per position. Track exact bigint counts per
admissible B_j value; transitions B_{j+1} = B_j + b, b>=1. No discretization."""
import math
from fractions import Fraction
LOG23=math.log2(3.0)   # float is fine: used only to locate integer windows; certify with
# interval shift: use high-precision log2(3) via Fraction approximation
from decimal import Decimal, getcontext
getcontext().prec=60
L23=Decimal(3).ln()/Decimal(2).ln()
def exact_lambda(D,p):
    Dd=Decimal(str(D))
    # admissible integers at position j: ceil(j*L-D) .. floor(j*L+D)
    cur={0:1}  # B_0 = 0
    import sys
    for j in range(1,p+1):
        lo=int((Decimal(j)*L23-Dd).to_integral_value(rounding='ROUND_CEILING'))
        hi=int((Decimal(j)*L23+Dd).to_integral_value(rounding='ROUND_FLOOR'))
        nxt={}
        for B,c in cur.items():
            for Bn in range(max(lo,B+1),hi+1):   # b = Bn-B >= 1
                nxt[Bn]=nxt.get(Bn,0)+c
        cur=nxt
        if not cur: return 0.0,j
    N=sum(cur.values())
    return (math.log2(N)/p if N>0 else 0.0), N
print(f"{'D':>5} {'p':>5} {'log2 N/p (=theta exact!)':>24} {'lambda=2^theta':>13}")
for D in (0.8,0.9,1.0,1.1,1.2,1.232,1.3,1.5,2.0):
    th,N=exact_lambda(D,3000)
    print(f"{D:>5.3f} {3000:>5} {th:>24.5f} {2**th:>13.4f}")
# refine D*: theta(D)=1 <=> lambda=2
print("\nrefining D* with exact counts (p=3000):")
lo,hi=1.1,1.4
for _ in range(10):
    mid=(lo+hi)/2
    th,_=exact_lambda(mid,3000)
    if th>1: hi=mid
    else: lo=mid
print(f"  D* = {(lo+hi)/2:.4f}  (EXACT-COUNT method; band ratio {2**(2*(lo+hi)/2):.2f})")
