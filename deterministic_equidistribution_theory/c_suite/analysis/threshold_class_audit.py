"""dc_20 sec 8: exact four-class decomposition of the G = T^c (T^c)* Schur row sum
at threshold m=c, c=4, full word enumeration on the sup row.
Classes per word pair (w,w'), decided by the complete source sum S = sum_a chi(R_{w,w'}(a)):
  I    nonstationary (d_nom<=c-2, nondegenerate)  -> S = 0 exactly
  III  locked (all interior Delta C_i = 0)        -> |S| = phi
  S/U  stationary-unlocked (d_nom>=c-1, not locked)
  IV   degenerate (d_nom<=c-2 but d_true>=c-1 somewhere)
"""
import numpy as np
import sys
c=int(sys.argv[1]) if len(sys.argv)>1 else 4
k,m = 1,c
BMAX=int(sys.argv[2]) if len(sys.argv)>2 else 14
Q=3**c; PHI=2*3**(c-1); K=c+3; MOD=3**K
dlog={}; p=1
for j in range(PHI): dlog[p]=j; p=(p*2)%Q
U=np.array([a for a in range(Q) if a%3],np.int64); phi=len(U)
chiU=np.exp(2j*np.pi*k*np.array([dlog[int(a)] for a in U])/PHI)
chi_of=np.zeros(Q,complex)
for a,ch in zip(U,chiU): chi_of[a]=ch
invQ=np.zeros(Q,np.int64)
for a in U: invQ[a]=pow(int(a),-1,Q)

# ---- enumerate words ----
g=np.indices((BMAX,)*m).reshape(m,-1).T+1     # words (b1..b4), shape (Nw,4)
Nw=len(g)
pw=(0.5**g).prod(axis=1)
C=np.ones((Nw,m),np.int64)                    # C[:,i-1] = C_i, i=1..m
P2=np.ones(Nw,np.int64); B=np.zeros(Nw,np.int64)
Bint=np.zeros((Nw,m-1),np.int64)              # B_i for i=1..m-1
for i in range(1,m):
    P2=(P2*pow(2,1,MOD)**0)*0+ (P2*np.array([pow(2,int(x),MOD) for x in range(BMAX+1)])[g[:,i-1]])%MOD
    B+=g[:,i-1]; Bint[:,i-1]=B
    C[:,i]=(3*C[:,i-1]+P2)%MOD
Bm=B+g[:,m-1]
inv2=pow(2,-1,Q)
i2=np.array([pow(inv2,j,Q) for j in range(PHI)],np.int64)
endpt=((C[:,m-1]%Q)*i2[Bm%PHI])%Q             # C[:,m-1] = C_m already
# ---- build T, G; find sup row ----
den=1-0.5**PHI
T=np.zeros((2*phi,2*phi),complex)
idx={int(a):i for i,a in enumerate(U)}
for aii,a in enumerate(U):
    t3=(3*int(a)+1)%Q
    for ap in U:
        b0=dlog[(t3*int(invQ[ap]))%Q]%PHI
        if b0==0: b0=PHI
        W0=0.5**b0/den
        for tau in (0,1):
            T[idx[int(ap)]*2+(tau+b0)%2, aii*2+tau]+=W0*chiU[aii]
Tm=np.linalg.matrix_power(T,m); G=Tm@Tm.conj().T
rows=np.abs(G).sum(axis=0)
xi0=int(rows.argmax()); x0=int(U[xi0//2]); sig0=xi0%2
print(f"sup row: x0={x0} sigma={sig0}, matrix row sum={rows[xi0]:.4f}, R_G^(1/2m)={rows[xi0]**(1/(2*m)):.4f}")
rowmask=endpt==x0
wrow=np.where(rowmask)[0]
ordr=np.argsort(-pw[wrow]); wrow=wrow[ordr]
cov=pw[wrow].cumsum()/pw[rowmask].sum()
ntop=int(np.searchsorted(cov,0.995))+1
wrow=wrow[:ntop]
print(f"row words: {rowmask.sum()}, using top {ntop} (99.5% of row mass {pw[rowmask].sum():.5f})")

def v3v(x):
    v=np.zeros(x.shape,np.int64); y=x.copy()
    z=y==0; v[z]=K; act=~z
    for _ in range(K):
        d=act&(y%3==0)
        if not d.any(): break
        y[d]//=3; v[d]+=1; act=d
    return np.minimum(v,K)

aU=U.astype(np.int64)
acc={'I':0.0,'III':0.0,'SU0':0.0,'SU1':0.0,'IV':0.0}
cnt={kk:0 for kk in acc}
for w in wrow:
    dC=(C[w,:m-1][None,:]-C[:,:m-1])%MOD       # (Nw, m-1) interior i=1..m-1... careful: C[:,0..m-2]=C_1..C_{m-1}
    vi=np.where(dC==0,K,np.arange(1,m)[None,:]+v3v(dC))
    dnom=vi.min(axis=1)
    locked=(dC==0).all(axis=1)
    stat=(dnom>=c-1)&~locked
    nonstat=dnom<=c-2
    # exact S for all non-class-I candidates: locked, stat, and nonstat (to find degenerate)
    # ratio R(a) = prod_i (3^i a + C_i(w))/(3^i a + C_i(w')) mod Q ; vectorize over (w', a)
    cand=np.where(locked|stat|nonstat)[0]      # everything; but S for nonstat mostly 0 - compute to catch IV
    # chunked exact S
    Sabs=np.zeros(Nw)
    CH=4096
    for lo in range(0,len(cand),CH):
        sel=cand[lo:lo+CH]
        r=np.ones((len(sel),phi),np.int64)
        for i in range(1,m):
            t3=pow(3,i,Q)
            nume=(t3*aU+C[w,i-1]%Q)%Q
            deno=(t3*aU[None,:]+(C[sel,i-1]%Q)[:,None])%Q
            r=r*nume[None,:]%Q*invQ[deno]%Q
        Sabs[sel]=np.abs(chi_of[r].sum(axis=1))
    dBm=Bm[w]-Bm
    twist=(dBm%PHI)!=0
    pp=pw[w]*pw
    m_I=nonstat&(Sabs<1e-9); m_IV=nonstat&~m_I
    acc['I']+=0.0;                    cnt['I']+=int(m_I.sum())
    acc['III']+=(pp*Sabs)[locked].sum();    cnt['III']+=int(locked.sum())
    acc['SU0']+=(pp*Sabs)[stat&~twist].sum(); cnt['SU0']+=int((stat&~twist).sum())
    acc['SU1']+=(pp*Sabs)[stat&twist].sum();  cnt['SU1']+=int((stat&twist).sum())
    acc['IV']+=(pp*Sabs)[m_IV].sum();  cnt['IV']+=int(m_IV.sum())
tot=sum(acc.values())
print(f"\nabs class masses (R~ = sum pp'|S|), row ({x0},{sig0}):")
for kk in ('I','III','SU0','SU1','IV'):
    print(f"  {kk:>4}: R~={acc[kk]:.4f}  share={acc[kk]/tot:.3f}  rate^(1/2m)={acc[kk]**(1/(2*m)) if acc[kk]>0 else 0:.4f}  npairs={cnt[kk]}")
print(f"  total R~={tot:.4f}  rate={tot**(1/(2*m)):.4f}   (matrix row sum with cancellation: {rows[xi0]:.4f}, rate {rows[xi0]**(1/(2*m)):.4f})")
