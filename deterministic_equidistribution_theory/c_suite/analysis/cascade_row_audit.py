"""dc_21 sec 5-7: heavy-row (x=-1) cascade audit at threshold m=c.
Classes on G-row pairs: III locked; II cascade\locked split by beta in {1/2,1}
(two-point formula S=(phi/2)[chi(R(1))+chi(R(2))], exact); IV degenerate (subsampled).
Reports: abs/signed cascade row sums, Lambda_c, p1 channel rate, off-rep multiplicity."""
import numpy as np, sys
c=int(sys.argv[1]); BMAX=int(sys.argv[2]); m=c; k=1
Q=3**c; PHI=2*3**(c-1); K=c+4; MOD=3**K
rng=np.random.default_rng(5)
dlog={}; p=1
for j in range(PHI): dlog[p]=j; p=(p*2)%Q
U=[a for a in range(Q) if a%3]; phi=len(U)
chi_of=np.zeros(Q,complex)
for a in U: chi_of[a]=np.exp(2j*np.pi*k*dlog[a]/PHI)
invQ=np.zeros(Q,np.int64)
for a in U: invQ[a]=pow(int(a),-1,Q)
chi2=np.exp(2j*np.pi*k*np.arange(PHI)*dlog[2]/PHI)  # chi(2)^j
# words
g=(np.indices((BMAX,)*m).reshape(m,-1).T+1).astype(np.int64)
Nw=len(g); pw=(0.5**g).prod(axis=1)
p2tab=np.array([pow(2,int(x),MOD) for x in range(BMAX*m+1)],np.int64)
C=np.ones((Nw,m),np.int64); P2=np.ones(Nw,np.int64); B=np.zeros(Nw,np.int64)
SB=np.zeros(Nw,np.int64)   # sum_{i=1}^{m-1} B_i
for i in range(1,m):
    P2=(P2*p2tab[g[:,i-1]])%MOD; B+=g[:,i-1]; SB+=B
    C[:,i]=(3*C[:,i-1]+P2)%MOD          # C[:,i] = C_{i+1}
Bm=B+g[:,m-1]
inv2=pow(2,-1,Q); i2=np.array([pow(inv2,j,Q) for j in range(PHI)],np.int64)
endpt=((C[:,m-1]%Q)*i2[Bm%PHI])%Q
x0=Q-1
rowmask=endpt==x0
wrow=np.where(rowmask)[0]; wrow=wrow[np.argsort(-pw[wrow])]
covfull=pw[rowmask].sum()
ntop=int(np.searchsorted(pw[wrow].cumsum()/covfull,0.995))+1
wrow=wrow[:ntop]
print(f"c={c} BMAX={BMAX}: {Nw} words; row x=-1 mass={covfull:.5f}, top {ntop} words (99.5%)")
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
ii=np.arange(2,m)                       # interior positions with dC possibly nonzero
t3Q=np.array([pow(3,int(i),Q) for i in range(m)],np.int64)
t3M=np.array([pow(3,int(i),MOD) for i in range(m)],np.int64)
aprobe=np.array([a for a in [1,2,4,5,7,8] if a%3],np.int64)[:6]
ent_sgn=np.zeros((Q,2),complex)         # signed entries II+III, cols=(endpoint w', parity blk)
ent_abs=np.zeros((Q,2))                  # abs cascade mass per column
rowmass=np.bincount(endpt,weights=pw,minlength=Q)
print(f"row-mass: x=-1 share={rowmass[Q-1]:.5f}, mean={rowmass[rowmass>0].mean():.6f}, sup={rowmass.max():.5f} at x={rowmass.argmax()} (-1 is {Q-1})")
acc=dict(III=0.0, IIh=0.0, II1=0.0, IV=0.0); cnt=dict(III=0,IIh=0,II1=0,IV=0)
offrep_cnt=0; offrep_mass=0.0; iv_sampled_wt=0.0; iv_total_wt=0.0
chk=[]
for w in wrow:
    dC=(C[w,1:m-1][None,:]-C[:,1:m-1])%MOD       # i=2..m-1
    vi=np.where(dC==0,K,ii[None,:]+v3v(dC)); dnom=vi.min(axis=1)
    locked=(dC==0).all(axis=1)
    casc=(dnom>=c-1)
    cascNL=casc&~locked
    nonstat=~casc
    pp=pw[w]*pw
    # two-point S for cascade (incl locked) : S=(phi/2)(chi(R(1))+chi(R(2)))*chi(2)^{SB'-SB}
    sel=np.where(casc)[0]
    Rv=np.ones((len(sel),2),np.int64)
    for i in range(2,m):
        for j,a in enumerate((1,2)):
            nume=(t3Q[i]*a+C[w,i-1]%Q)%Q
            deno=(t3Q[i]*a+(C[sel,i-1]%Q))%Q
            Rv[:,j]=Rv[:,j]*nume%Q*invQ[deno]%Q
    ph2=chi2[(SB[sel]-SB[w])%PHI]
    Sc=0.5*phi*(chi_of[Rv[:,0]]+chi_of[Rv[:,1]])*ph2
    Sabs=np.abs(Sc)/phi                          # in {1/2,1}
    lk=locked[sel]; b1=(~lk)&(Sabs>0.75); bh=(~lk)&(Sabs<=0.75)
    acc['III']+=(pp[sel]*Sabs*phi)[lk].sum();  cnt['III']+=int(lk.sum())
    acc['II1']+=(pp[sel]*Sabs*phi)[b1].sum();  cnt['II1']+=int(b1.sum())
    acc['IIh']+=(pp[sel]*Sabs*phi)[bh].sum();  cnt['IIh']+=int(bh.sum())
    # off-representative: cascade pair with B_i' != B_i for some i<=c-3
    Bint_w=np.cumsum(g[w,:m-1]); Bint=np.cumsum(g[:,:m-1],axis=1)
    if c>=5:
        offr=cascNL & (Bint[:,:c-3]!=Bint_w[None,:c-3]).any(axis=1)
        offrep_cnt+=int(offr.sum()); offrep_mass+=pp[offr].sum()
    # signed entries for II+III
    cols=endpt[sel]; blk=(Bm[sel]-Bm[w])%2
    np.add.at(ent_sgn,(cols,blk),pp[sel]*Sc)
    np.add.at(ent_abs,(cols,blk),pp[sel]*np.abs(Sc))
    # class IV: nonstat & degenerate (probe), exact S on subsample
    selN=np.where(nonstat)[0] if len(sys.argv)<=3 else np.array([],np.int64)
    L=np.zeros((len(selN),len(aprobe)),np.int64)
    for i in range(2,m):
        num=(t3M[i]*((C[selN,i-1]-C[w,i-1])%MOD))%MOD
        for j,a in enumerate(aprobe):
            den=((t3M[i]*a+C[w,i-1])%MOD)*((t3M[i]*a+C[selN,i-1])%MOD)%MOD
            L[:,j]=(L[:,j]+num*henselinv(den))%MOD
    deg=(v3v(L)>=c-1).any(axis=1)
    dsel=selN[deg]; iv_total_wt+=pp[dsel].sum()
    if len(dsel)>4000: dsel=rng.choice(dsel,4000,replace=False)
    if len(dsel):
        aU=np.array(U,np.int64)
        Sd=np.zeros(len(dsel),complex)
        CH=600
        for lo in range(0,len(dsel),CH):
            ss=dsel[lo:lo+CH]
            r=np.ones((len(ss),phi),np.int64)
            for i in range(2,m):
                nume=(t3Q[i]*aU+C[w,i-1]%Q)%Q
                deno=(t3Q[i]*aU[None,:]+(C[ss,i-1]%Q)[:,None])%Q
                r=r*nume[None,:]%Q*invQ[deno]%Q
            Sd[lo:lo+CH]=(chi_of[r].sum(axis=1))
        iv_sampled_wt+=pw[dsel].sum()*pw[w]
        acc['IV']+=(pw[w]*pw[dsel]*np.abs(Sd)).sum()
        cnt['IV']+=int(deg.sum())
    # sanity: two-point vs direct on a few cascade pairs
    if len(chk)<30 and len(sel)>5:
        aU=np.array(U,np.int64)
        for s_ in sel[:2]:
            r=np.ones(phi,np.int64)
            for i in range(2,m):
                r=r*((t3Q[i]*aU+C[w,i-1]%Q)%Q)%Q*invQ[(t3Q[i]*aU+C[s_,i-1]%Q)%Q]%Q
            chk.append(abs(abs(chi_of[r].sum())-abs(0.5*phi*(chi_of[Rv[sel.tolist().index(s_),0]]+chi_of[Rv[sel.tolist().index(s_),1]]))))
# scale class IV to full weight
if iv_sampled_wt>0: acc['IV']*= iv_total_wt/iv_sampled_wt
R_casc_abs=acc['IIh']+acc['II1']+acc['III']
R_sgn=np.abs(ent_sgn).sum()
print(f"two-point check max err: {max(chk) if chk else -1:.2e}")
print(f"classes (abs, heavy row): III={acc['III']:.4f}  II(b=1/2)={acc['IIh']:.4f}  II(b=1)={acc['II1']:.4f}  IV~={acc['IV']:.4f}")
print(f"counts: III={cnt['III']} IIh={cnt['IIh']} II1={cnt['II1']} IV={cnt['IV']}")
p1=acc['II1']/(acc['II1']+acc['IIh']) if acc['II1']+acc['IIh']>0 else 0
print(f"R_cascade_abs(-1)={R_casc_abs:.4f}  Lambda_c={R_casc_abs**(1/(2*c)):.4f}   (with IV: {(R_casc_abs+acc['IV'])**(1/(2*c)):.4f})")
print(f"R_cascade_sgn(-1)={R_sgn:.4f}  rate={R_sgn**(1/(2*c)):.4f}   sgn/abs={R_sgn/R_casc_abs:.3f}")
print(f"p1 (beta=1 mass share within II)={p1:.3f}   off-rep: n={offrep_cnt}, mass={offrep_mass:.2e}")
topcol=ent_abs.max(); print(f"top transition (column) share of R_casc_abs: {topcol/R_casc_abs:.3f}; top-10 share: {np.sort(ent_abs.ravel())[-10:].sum()/R_casc_abs:.3f}")
