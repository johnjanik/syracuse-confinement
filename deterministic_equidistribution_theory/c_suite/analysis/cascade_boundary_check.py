"""Check: cascade pairs at exact boundary depth have S=0 (nondegenerate);
surviving class-II mass = deeper cascade (+ degenerate boundary).
c=5, m=c. Cascade <=> t1=0 mod 6, t2=0 mod 2. Deeper <=> t1=0 mod 18, t2=0 mod 6, t3=0 mod 2."""
import numpy as np
c,m=5,5
Q=3**c; PHI=2*3**(c-1); K=c+3; MOD=3**K
rng=np.random.default_rng(7)
dlog={}; p=1
for j in range(PHI): dlog[p]=j; p=(p*2)%Q
U=[a for a in range(Q) if a%3]; phi=len(U)
chi={a: np.exp(2j*np.pi*dlog[a]/PHI) for a in U}
invQ={a: pow(a,-1,Q) for a in U}
def consts(b):
    C=[None,1]; P=1
    for i in range(1,m):
        P=(P*pow(2,int(b[i-1]),MOD))%MOD
        C.append((3*C[-1]+P)%MOD)
    return C   # C[1..m-1] interior (C[i]=C_i)
def exact_S(C1,C2):
    S=0
    for a in U:
        r=1
        for i in range(1,m):
            r=r*((pow(3,i,Q)*a+C1[i])%Q)%Q*invQ[(pow(3,i,Q)*a+C2[i])%Q]%Q
        S+=chi[r]
    return abs(S)/phi
res={'boundary':[], 'deeper':[]}
n_locked=0; tries=0
while (len(res['boundary'])<800 or len(res['deeper'])<800) and tries<400000:
    tries+=1
    b1=np.minimum(rng.geometric(0.5,m),40); b2=np.minimum(rng.geometric(0.5,m),40)
    B1=b1.cumsum(); B2=b2.cumsum()
    t=B1-B2
    casc = (t[0]%6==0) and (t[1]%2==0)
    if not casc: continue
    if (b1[:m-1]==b2[:m-1]).all(): n_locked+=1; continue
    deeper = (t[0]%18==0) and (t[1]%6==0) and (t[2]%2==0)
    key='deeper' if deeper else 'boundary'
    if len(res[key])>=800: continue
    C1,C2=consts(b1),consts(b2)
    if all((C1[i]-C2[i])%MOD==0 for i in range(1,m)): n_locked+=1; continue  # C-locked despite b mismatch
    res[key].append(exact_S(C1,C2))
for key in ('boundary','deeper'):
    v=np.array(res[key])
    z=(v<1e-9).mean()
    print(f"{key:>9}: n={len(v)}  frac(S=0)={z:.3f}  mean|S|/phi={v.mean():.4f}  "
          f"nonzero |S|/phi: mean={v[v>1e-9].mean() if (v>1e-9).any() else 0:.3f}  max={v.max():.3f}")
print(f"(locked skipped: {n_locked}, tries {tries})")
