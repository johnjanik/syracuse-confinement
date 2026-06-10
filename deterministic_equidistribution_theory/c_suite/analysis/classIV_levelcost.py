"""dc_27 sec 10: class-IV degeneracy audit organized around the proof.
P[h >= r | d_nom = d] for r=1,2,3, grouped by nominal shell d; plus
a-independence check of the FIRST degeneracy level (h>=1 should be a word event)."""
import numpy as np
c=7; m=c; K=c+4; MOD=3**K
rng=np.random.default_rng(13)
N=2_000_000
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
b1=np.minimum(rng.geometric(0.5,(N,m)),50).astype(np.int64)
b2=np.minimum(rng.geometric(0.5,(N,m)),50).astype(np.int64)
p2=np.array([pow(2,int(x),MOD) for x in range(51)],np.int64)
C1=np.ones(N,np.int64);C2=np.ones(N,np.int64);P1=np.ones(N,np.int64);P2v=np.ones(N,np.int64)
Cs1=np.zeros((N,m-1),np.int64);Cs2=np.zeros((N,m-1),np.int64)
for i in range(1,m):
    P1=(P1*p2[b1[:,i-1]])%MOD; P2v=(P2v*p2[b2[:,i-1]])%MOD
    C1=(3*C1+P1)%MOD; C2=(3*C2+P2v)%MOD
    Cs1[:,i-1]=C1; Cs2[:,i-1]=C2          # Cs[:,i-1] = C_{i+1}
# interior i=2..m-1 -> Cs[:,0..m-3]
ii=np.arange(2,m)
dC=(Cs1[:,0:m-2]-Cs2[:,0:m-2])%MOD
vi=np.where(dC==0,K,ii[None,:]+v3v(dC))
dnom=vi.min(axis=1)
# d_true at 6 units a
aprobe=np.array([1,2,4,5,7,8],np.int64)
t3=np.array([pow(3,int(i),MOD) for i in range(m)],np.int64)
h=np.zeros((N,len(aprobe)),np.int64)
L=np.zeros((N,len(aprobe)),np.int64)
for idx,i in enumerate(range(2,m)):
    num=(t3[i]*((Cs2[:,idx]-Cs1[:,idx])%MOD))%MOD
    for j,a in enumerate(aprobe):
        den=((t3[i]*a+Cs1[:,idx])%MOD)*((t3[i]*a+Cs2[:,idx])%MOD)%MOD
        L[:,j]=(L[:,j]+num*henselinv(den))%MOD
dtrue=v3v(L)
hh=dtrue-dnom[:,None]
# a-independence of first level: 1{h>=1} same across all probes?
first=hh>=1
agree=(first.all(axis=1)|(~first).any(axis=1)&(~first).all(axis=1))
mismatch=(first.any(axis=1)&~first.all(axis=1)).mean()
print(f"a-independence of first degeneracy level: P[mixed across a] = {mismatch:.2e}  (should be ~0)")
print(f"\nP[h>=r | d_nom=d]   (c={c}, N={N}, first probe a=1; word-level event for r=1)")
print(f"{'d':>3} {'n':>8} {'P[h>=1]':>9} {'P[h>=2]':>9} {'P[h>=3]':>9}   3^-r: 0.333 0.111 0.037")
h0=hh[:,0]
for d in range(2,c+1):
    sel=dnom==d
    n=int(sel.sum())
    if n<2000: continue
    p1=(h0[sel]>=1).mean(); p2_=(h0[sel]>=2).mean(); p3=(h0[sel]>=3).mean()
    print(f"{d:>3} {n:>8} {p1:>9.4f} {p2_:>9.4f} {p3:>9.4f}")
# conditional ratios (the level-cost law): P[h>=r+1]/P[h>=r]
sel=(dnom<=c-2)
print(f"\noverall (d_nom<=c-2): P[h>=1]={ (h0[sel]>=1).mean():.4f}, P[h>=2|h>=1]={(h0[sel]>=2).sum()/max((h0[sel]>=1).sum(),1):.4f}, P[h>=3|h>=2]={(h0[sel]>=3).sum()/max((h0[sel]>=2).sum(),1):.4f}")
