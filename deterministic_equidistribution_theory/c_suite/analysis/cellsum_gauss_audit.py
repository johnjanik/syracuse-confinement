"""dc_28 sec 7: Postnikov/Gauss audit on class-IV degenerate cells, c=7.
Records v3(L1), v3(L2) vs nondegenerate prediction d+i_min, and exact cell sums
|S_C| / 3^{l/2} on degenerate cells."""
import numpy as np
rng=np.random.default_rng(23)
c=7; m=c; K=c+5; MOD=3**K; Q=3**c; PHI=2*3**(c-1)
dlog={}; p=1
for j in range(PHI): dlog[p]=j; p=(p*2)%Q
U=[a for a in range(Q) if a%3]; phi=len(U)
chi_of=np.zeros(Q,complex)
for a in U: chi_of[a]=np.exp(2j*np.pi*dlog[a]/PHI)
invQ=np.zeros(Q,np.int64)
for a in U: invQ[a]=pow(int(a),-1,Q)
def v3(x):
    x%=MOD
    if x==0: return K
    v=0
    while x%3==0: x//=3; v+=1
    return v
def consts(b):
    C={1:1}; P=1
    for i in range(1,m):
        P=(P*pow(2,int(b[i-1]),MOD))%MOD; C[i+1]=(3*C[i]+P)%MOD
    return C
def L12(a,C1,C2):
    L1=0; L2=0
    for i in range(2,m):
        dC=(C2[i]-C1[i])%MOD
        den=((pow(3,i,MOD)*a+C1[i])%MOD)*((pow(3,i,MOD)*a+C2[i])%MOD)%MOD
        ui=pow(den,-1,MOD)
        t1=(pow(3,i,MOD)*dC)%MOD*ui%MOD
        L1=(L1+t1)%MOD
        sf=(2*pow(3,i,MOD)*a+C1[i]+C2[i])%MOD
        L2=(L2-t1*pow(3,i,MOD)%MOD*sf%MOD*ui)%MOD
    return L1%MOD,L2%MOD
def ratio(a,C1,C2):
    r=1
    for i in range(2,m):
        r=r*((pow(3,i,Q)*a+C1[i]%Q)%Q)%Q*invQ[(pow(3,i,Q)*a+C2[i]%Q)%Q]%Q
    return r
stats=[]; cellchecks=[]
tried=0
while len(stats)<300 and tried<250000:
    tried+=1
    b1=np.minimum(rng.geometric(0.5,m),40); b2=np.minimum(rng.geometric(0.5,m),40)
    C1,C2=consts(b1),consts(b2)
    vs=[(i+v3(C1[i]-C2[i])) for i in range(2,m) if (C1[i]-C2[i])%MOD]
    if not vs: continue
    d=min(vs)
    if d>c-2 or d<2: continue
    # find degenerate a0 (nu >= c-1) by scanning a few units
    found=None
    for a0 in U[::7]:
        L1,_=L12(a0,C1,C2)
        if v3(L1)>=c-1: found=a0; break
    if found is None: continue
    a0=found
    L1,L2=L12(a0,C1,C2)
    I=[i for i in range(2,m) if (C1[i]-C2[i])%MOD and i+v3(C1[i]-C2[i])==d]
    imin=min(I) if I else -1
    w2=v3(L2)
    stats.append(w2-(d+imin))
    # exact cell sum on the maximal quadratic cell: choose q with 2q+v3(L2)>=c > q+... use q=ceil((c-v3(L2))/2)
    if len(cellchecks)<60 and w2<c:
        q=max(1,(c-w2+1)//2); l=c-q
        if l>=1 and l<=6:
            S=sum(chi_of[ratio((a0+3**q*t)%Q if (a0+3**q*t)%3 else (a0+3**q*t+3**q)%Q,C1,C2)] for t in range(3**l))
            # careful: a0+3^q t stays unit automatically (a0 unit, q>=1)
            S=sum(chi_of[ratio((a0+3**q*t)%Q,C1,C2)] for t in range(3**l))
            cellchecks.append(abs(S)/3**(l/2))
st=np.array(stats)
print(f"class-IV points: n={len(st)}; v3(L2)-(d+i_min): P[=0]={(st==0).mean():.3f} P[=1]={(st==1).mean():.3f} P[=2]={(st==2).mean():.3f} P[>=3]={(st>=3).mean():.3f}")
cc=np.array(cellchecks)
print(f"exact cell sums |S_C|/3^(l/2): n={len(cc)}, values: min={cc.min():.3f} median={np.median(cc):.3f} max={cc.max():.3f}")
print("histogram:", np.round(np.quantile(cc,[0.1,0.25,0.5,0.75,0.9]),3))
