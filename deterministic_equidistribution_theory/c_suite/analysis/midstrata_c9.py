"""c=9 mid-strata audit: Fubini spectrum E[#{a: nu(a)=v}]/phi per shell d,
vs probabilistic (4/7)^{v-d} and deterministic 3^{-(v-d)} predictions.
Window of interest: (c+d)/2 < v < c-1."""
import numpy as np
rng=np.random.default_rng(53)
c=9; m=c; K=c+5; MOD=3**K; Q=3**c; PHI=2*3**(c-1)
U=np.array([a for a in range(Q) if a%3],np.int64); phi=len(U)
def v3v(x):
    v=np.zeros(x.shape,np.int64); y=x%MOD
    z=y==0; v[z]=K; act=~z
    for _ in range(K):
        d=act&(y%3==0)
        if not d.any(): break
        y[d]//=3; v[d]+=1; act=d
    return np.minimum(v,K)
def henselinv(u):
    x=np.where(u%3==1,1,2).astype(np.int64)
    for _ in range(5): x=(x*((2-u*x)%MOD))%MOD
    return x%MOD
def consts(b):
    C={1:1}; P=1
    for i in range(1,m):
        P=(P*pow(2,int(b[i-1]),MOD))%MOD; C[i+1]=(3*C[i]+P)%MOD
    return C
spec={}; counts={}
NP=2500; done=0; tried=0
while done<NP and tried<60000:
    tried+=1
    b1=np.minimum(rng.geometric(0.5,m),40); b2=np.minimum(rng.geometric(0.5,m),40)
    C1,C2=consts(b1),consts(b2)
    vs=[]
    for i in range(2,m):
        dd=(C1[i]-C2[i])%MOD
        if dd:
            x=dd; vv=0
            while x%3==0: x//=3; vv+=1
            vs.append(i+vv)
    if not vs: continue
    d=min(vs)
    if d>c-2 or d<3: continue   # d=2 singleton-rigid, skip; need d>=3
    done+=1
    L=np.zeros(phi,np.int64)
    for i in range(2,m):
        t3M=pow(3,i,MOD)
        num=(t3M*((C2[i]-C1[i])%MOD))%MOD
        den=((t3M*U)%MOD+C1[i])%MOD*(((t3M*U)%MOD+C2[i])%MOD)%MOD
        L=(L+num*henselinv(den))%MOD
    nu=v3v(L)
    counts[d]=counts.get(d,0)+1
    for v in range(d,c+2):
        spec[(d,v)]=spec.get((d,v),0)+int((nu==v).sum())
    spec[(d,'deep')]=spec.get((d,'deep'),0)+int((nu>=c+2).sum())
print(f"c={c}, pairs={done}; spectrum E[#(nu=v)]/phi per shell:")
for d in sorted(counts):
    n=counts[d]
    print(f"d={d} (n={n}):  halfthr={(c+d)/2:.1f}")
    row=[]
    for v in range(d,c+2):
        f=spec.get((d,v),0)/(n*phi)
        h=v-d
        row.append(f"v={v}:{f:.2e} [(4/7)^h={4**h/7**h:.1e}|3^-h={3.0**-h:.1e}]")
    print("   "+"  ".join(row[:5]))
    print("   "+"  ".join(row[5:]))
    print(f"   deep(>={c+1}): {spec.get((d,'deep'),0)/(n*phi):.2e}")
