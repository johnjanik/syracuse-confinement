"""Deep-stratum descent: for class-IV pairs, compare |sum over deep strata of chi(R)|
against the deep-stratum measure: cross-cell cancellation factor."""
import numpy as np
rng=np.random.default_rng(31)
c=7; m=c; K=c+5; MOD=3**K; Q=3**c; PHI=2*3**(c-1)
dlog={}; p=1
for j in range(PHI): dlog[p]=j; p=(p*2)%Q
U=np.array([a for a in range(Q) if a%3],np.int64); phi=len(U)
chi_of=np.zeros(Q,complex)
for a in U: chi_of[a]=np.exp(2j*np.pi*dlog[int(a)]/PHI)
invQ=np.zeros(Q,np.int64)
for a in U: invQ[a]=pow(int(a),-1,Q)
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
res=[]
tried=0
while len(res)<200 and tried<200000:
    tried+=1
    b1=np.minimum(rng.geometric(0.5,m),40); b2=np.minimum(rng.geometric(0.5,m),40)
    C1,C2=consts(b1),consts(b2)
    vs=[(i+int(v3v(np.array([C1[i]-C2[i]])))) for i in range(2,m) if (C1[i]-C2[i])%MOD]
    if not vs: continue
    d=min(vs)
    if d>c-2 or d<2: continue
    # vectorized over all units: nu(a) and chi(R(a))
    L=np.zeros(phi,np.int64); r=np.ones(phi,np.int64)
    for i in range(2,m):
        t3M=pow(3,i,MOD); t3Q=pow(3,i,Q)
        num=(t3M*((C2[i]-C1[i])%MOD))%MOD
        den=((t3M*U)%MOD+C1[i])%MOD*(((t3M*U)%MOD+C2[i])%MOD)%MOD
        L=(L+num*henselinv(den))%MOD
        r=r*((t3Q*U+C1[i]%Q)%Q)%Q*invQ[(t3Q*U+C2[i]%Q)%Q]%Q
    nu=v3v(L)
    if not (nu>=c-1).any(): continue   # need genuine class IV
    ph=chi_of[r]
    thr=(c+d)//2
    deep=nu>thr
    mdeep=int(deep.sum())
    if mdeep==0: continue
    Sdeep=ph[deep].sum(); S=ph.sum()
    res.append((d,mdeep,abs(Sdeep),abs(S)))
res=np.array(res)
canc=res[:,2]/res[:,1]
print(f"n={len(res)} class-IV pairs (c=7): deep-stratum cancellation |S_deep|/m_deep:")
print(f"  mean={canc.mean():.3f} median={np.median(canc):.3f} q90={np.quantile(canc,0.9):.3f} max={canc.max():.3f}")
print(f"  m_deep: mean={res[:,1].mean():.1f} max={res[:,1].max():.0f}  (phi={phi})")
print(f"  |S_total| vs m_deep: mean ratio={(res[:,3]/res[:,1]).mean():.3f}")
print(f"  |S_total|/phi: mean={(res[:,3]/phi).mean():.4f}")
