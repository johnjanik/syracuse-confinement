"""dc_30 Tracks A/B/C: periodic-word shadows; window deviation vs descent; trap lifting."""
import numpy as np
from itertools import combinations
import random
random.seed(7)

# ---------- Track A: periodic words ----------
print("=== Track A: periodic words, p<=7 ===")
zeta3=np.exp(2j*np.pi/3); zeta9=np.exp(2j*np.pi/9)
def G(z): return (1/(2*z))/(1-1/(2*z))   # E_geom[z^{-b}] = sum 2^-b z^-b
hits=[]
for p in range(1,8):
    Bmin=int(np.floor(p*np.log2(3)))+1
    for B in range(Bmin,2*p+4):
        # compositions of B into p parts >=1 via stars and bars
        for cuts in combinations(range(1,B),p-1):
            parts=[]; prev=0
            for cpos in cuts+(B,):
                parts.append(cpos-prev); prev=cpos
            A=0; Bj=0
            for j in range(p):
                A+=3**(p-1-j)*2**Bj; Bj+=parts[j]
            den=2**B-3**p
            if den>0 and A%den==0:
                x=A//den
                hits.append((p,tuple(parts),x))
print(f"integer positive cycles found (p<=7): {len(hits)}")
for p,w,x in hits[:10]: print(f"  p={p} word={w} x={x}")
# shadow detection for sample periodic words (rational cycles): smallest detecting character order
print("shadow detection (|cycle avg - G| for ord-3 char, z=zeta3):")
for w in [(2,),(1,3),(3,1),(4,),(1,1,4),(2,2),(1,2,3),(5,1),(2,3),(1,1,1,5)]:
    avg=np.mean([zeta3**(-b) for b in w])
    d3=abs(avg-G(zeta3))
    avg9=np.mean([zeta9**(-b) for b in w])
    d9=abs(avg9-G(zeta9))
    print(f"  w={str(w):>12}: |D(ord3)|={d3:.4f}  |D(ord9)|={d9:.4f}  {'TRIVIAL-CYCLE word' if set(w)=={2} else 'detected' if max(d3,d9)>1e-12 else 'INVISIBLE?!'}")

# ---------- Track B: orbit windows ----------
print("\n=== Track B: window deviation vs descent (large orbits) ===")
def orbit_letters(x0,maxn=4000):
    xs=[x0]; bs=[]
    x=x0
    for _ in range(maxn):
        y=3*x+1; b=0
        while y%2==0: y//=2; b+=1
        bs.append(b); x=y; xs.append(x)
        if x==1: break
    return xs,bs
M=64; H=64
Ggeom3=G(zeta3); Ggeom9=G(zeta9)
rows=[]
for trial in range(60):
    x0=random.randrange(10**14,10**15)*2+1
    xs,bs=orbit_letters(x0)
    if len(bs)<M+H+10: continue
    for start in range(0,len(bs)-M-H,M//2):
        w=bs[start:start+M]
        D3=abs(np.mean([zeta3**(-b) for b in w])-Ggeom3)
        D9=abs(np.mean([zeta9**(-b) for b in w])-Ggeom9)
        D=max(D3,D9)
        meanb=np.mean(w)
        desc=int(min(xs[start+1:start+M+H+1])<xs[start])
        rows.append((D,meanb,desc))
rows=np.array(rows)
print(f"windows={len(rows)}; base descent rate={rows[:,2].mean():.3f}")
for lo,hi in [(0,0.1),(0.1,0.2),(0.2,0.3),(0.3,1.0)]:
    sel=(rows[:,0]>=lo)&(rows[:,0]<hi)
    if sel.sum()>5:
        print(f"  deviation in [{lo},{hi}): n={sel.sum():5d}  P[descent]={rows[sel,2].mean():.3f}  mean-letter={rows[sel,1].mean():.3f}")
# phase-only vs mean-visible split among high-deviation windows
hi=rows[rows[:,0]>0.2]
if len(hi)>0:
    mv=np.abs(hi[:,1]-2)>0.25
    print(f"high-deviation windows: n={len(hi)}, mean-visible (|mean-2|>0.25): {mv.mean():.2f}, descent|mean-visible={hi[mv,2].mean() if mv.any() else float('nan'):.3f}, descent|phase-only={hi[~mv,2].mean() if (~mv).any() else float('nan'):.3f}")
