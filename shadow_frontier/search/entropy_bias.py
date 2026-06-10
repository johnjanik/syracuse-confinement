#!/usr/bin/env python3
"""The entropy-bias squeeze: h(eps) = max entropy of a letter law on {1..K}
with mean = log2(3) and ord-3 shadow bias >= eps. Compare with ln 2 (band capacity)."""
import numpy as np
from scipy.optimize import minimize
import math
LOG23=math.log2(3.0); LN2=math.log(2.0)
K=30
z=np.exp(2j*np.pi/3)
G=sum(2.0**-b*z**-b for b in range(1,200))
bs=np.arange(1,K+1)
zv=z**(-bs.astype(float))
def neg_entropy(p):
    p=np.clip(p,1e-300,1)
    return float(np.sum(p*np.log(p)))
def solve(eps, omega):
    # constraints: sum p = 1; sum p*b = LOG23; Re(omega*(sum p z^-b - G)) >= eps
    cons=[{'type':'eq','fun':lambda p: p.sum()-1},
          {'type':'eq','fun':lambda p: p@bs-LOG23},
          {'type':'ineq','fun':lambda p: float(np.real(omega*(p@zv-G)))-eps}]
    p0=np.zeros(K); p0[0]=2-LOG23; p0[1]=LOG23-1
    p0=0.9*p0+0.1/K
    r=minimize(neg_entropy,p0,constraints=cons,bounds=[(0,1)]*K,
               method='SLSQP',options={'maxiter':800,'ftol':1e-12})
    return (-r.fun if r.success else np.nan), r
print(f"band capacity ln2 = {LN2:.4f} nats; h(0) check:")
# h(0): max entropy with mean log2 3 (geometric tilt)
h0,_=solve(0.0,1.0)
print(f"  h(0) = {h0:.4f} nats  ({h0/LN2:.3f} x ln2)  -> window exponent theta(0) = {h0/LN2:.3f}")
print(f"{'eps':>6} {'h(eps)':>8} {'theta=h/ln2':>11}  (theta<1 => biased banded windows repeat at Y^theta << Y)")
for eps in (0.05,0.10,0.15,0.20,0.25,0.30,0.35,0.40,0.45,0.50):
    best=-1
    for ang in np.linspace(0,2*np.pi,12,endpoint=False):
        h,_=solve(eps,np.exp(1j*ang))
        if not np.isnan(h): best=max(best,h)
    print(f"{eps:>6.2f} {best:>8.4f} {best/LN2:>11.3f}")
