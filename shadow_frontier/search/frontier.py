#!/usr/bin/env python3
"""Shadow Frontier search tool.

Subcommands:
  pilot      -- generate calibrated+biased high-complexity candidates,
                test 2-adic realizability (ghost signature), extract
                mixed-tower traps, run Karp max-plus certificates.
  rank       -- exponent-vector rank diagnostic (Target 1) on orbit windows.
"""
import argparse, math, random, json, sys
import numpy as np

LOG23 = math.log2(3.0)

# ---------- candidate generation (Q3-aware) ----------
def biased_letter_law(eps_sign=+1, eps=0.12):
    """Letters {1,2,4}: solve for law with mean=log2(3) and ord-3 bias shifted.
    zeta3-bias of law p: sum p_b z^{-b}, z=e(2pi i/3). Returns dict b->prob."""
    # parametrize p4 = t; mean: p1+2p2+4t = LOG23, p1+p2+t = 1
    # => p1 = 2 - LOG23 + 2t ... solve: p2 = 1 - p1 - t
    best=None
    z=np.exp(2j*np.pi/3)
    G=sum(2.0**-b*z**-b for b in range(1,60))
    for t in np.linspace(0,0.12,200):
        p1=2-LOG23+2*t
        p2=1-p1-t
        if p2<0 or p1<0: continue
        law={1:p1,2:p2,4:t}
        D=abs(sum(p*z**-b for b,p in law.items())-G)
        if best is None or abs(D- eps)<abs(best[1]-eps):
            best=(law,D)
    return best

def gen_word(law, M, rng):
    bs=list(law.keys()); ps=np.array([law[b] for b in bs])
    w=rng.choice(bs, size=M, p=ps/ps.sum())
    return [int(b) for b in w]

def calibrate(w):
    """Adjust word to keep |sum(b - log2 3)| <= 2 by greedy letter swaps."""
    w=list(w); S=sum(w)-LOG23*len(w)
    i=0
    while abs(S)>2 and i<len(w):
        if S>2 and w[i]>1: S-=w[i]-1; w[i]=1
        elif S<-2 and w[i]==1: S+=1; w[i]=2
        i+=1
    return w

# ---------- diagnostics ----------
def complexity(w,p):
    return len({tuple(w[i:i+p]) for i in range(len(w)-p+1)})

def bias(w,r=2):
    z=np.exp(2j*np.pi/3)
    G=sum(2.0**-b*z**-b for b in range(1,60))
    return abs(np.mean([z**(-b) for b in w])-G)

# ---------- 2-adic realizability (ghost test) ----------
def realize(bs):
    r,Mb=1,1
    A=0;B=0;P3=1
    for b in bs:
        need=B+b; mod=1<<(need+1)
        c=(3*A+(1<<B))%mod
        coef=(3*P3)%mod
        x0=(pow(coef,-1,mod)*(((1<<need)-c)%mod))%mod
        if need+1>Mb:
            assert (x0-r)%(1<<Mb)==0
            r=x0;Mb=need+1
        A=3*A+(1<<B);P3*=3;B+=b
    return r,Mb

# ---------- mixed-tower trap + Karp ----------
def karp(nv,edges,wts):
    INF=-1e18
    dp=np.full((nv+1,nv),INF); dp[0,:]=0.0
    for k in range(1,nv+1):
        for (u,v,i) in edges:
            if dp[k-1][u]>INF/2 and dp[k-1][u]+wts[i]>dp[k][v]:
                dp[k][v]=dp[k-1][u]+wts[i]
    best=-np.inf
    for vtx in range(nv):
        if dp[nv][vtx]<=INF/2: continue
        m=min((dp[nv][vtx]-dp[k][vtx])/(nv-k) for k in range(nv) if dp[k][vtx]>INF/2)
        best=max(best,m)
    return best

def mixed_trap_certificate(word, x0, a_max=4, b_max=3, eps=None):
    """Extract residue-edge trap over Z/(2^a 3^b) along the realized prefix; Karp over lambda grid.
    Returns (level, margin) of the first certifying level, or None."""
    z=np.exp(2j*np.pi/3)
    G=sum(2.0**-bb*z**-bb for bb in range(1,60))
    D=np.mean([z**(-bb) for bb in word])-G
    if eps is None: eps=abs(D)
    if eps<1e-9: return None
    om=np.conj(D/abs(D))
    for a in range(2,a_max+1):
        for b3 in range(2,b_max+1):
            Q=(1<<a)*3**b3
            # trace residues
            xs=[x0%Q]; x=x0
            for bb in word:
                x=(3*x+1)//(1<<bb) if (3*x+1)%(1<<bb)==0 else None
                if x is None: break
                xs.append(x%Q)
            if x is None: continue
            verts=sorted(set(xs)); vid={v:i for i,v in enumerate(verts)}
            edges=[];g=[];ph=[]
            seen=set()
            for i,bb in enumerate(word):
                key=(xs[i],bb)
                if key in seen: continue
                seen.add(key)
                edges.append((vid[xs[i]],vid[xs[i+1]],len(g)))
                g.append(LOG23-bb)
                ph.append(float(np.real(om*(z**(-bb)-G))))
            g=np.array(g);ph=np.array(ph)
            best=min((karp(len(verts),edges,g+lam*ph)-lam*eps,lam) for lam in np.linspace(0,25,51))
            if best[0]<0:
                return ((a,b3),best[0])
    return None

# ---------- exponent-vector rank (Target 1 diagnostic) ----------
def expvec_rank(word,p):
    """Z-rank of differences of exponent vectors (B_{i,j}, p-1-j) across block identities."""
    vecs=[]
    for i in range(0,len(word)-p,max(1,(len(word)-p)//40)):
        B=0
        for j in range(p):
            vecs.append((B,p-1-j)); B+=word[i+j]
    V=np.array(vecs,dtype=float)
    V=V-V[0]
    return np.linalg.matrix_rank(V,tol=1e-9)

# ---------- pilot ----------
def pilot(n=200, M=300, seed=1):
    rng=np.random.default_rng(seed)
    law,D0=biased_letter_law()
    print(f"letter law {law} (achieved bias {D0:.3f})")
    stats={"ghost":0,"cert":0,"alive":0}
    rows=[]
    for trial in range(n):
        w=calibrate(gen_word(law,M,rng))
        p=16
        P=complexity(w,p); Dw=bias(w)
        if Dw<0.05: continue
        r,Mb=realize(w)
        # ghost signature: least rep has ~full bit-length and no stabilization on half prefix
        r2,_=realize(w[:M//2])
        stable=(r2==r)
        if not stable and r.bit_length()> int(0.8*Mb):
            stats["ghost"]+=1; verdict="ghost"
        else:
            cert=mixed_trap_certificate(w,r if r.bit_length()<60 else r%(1<<40)|1)
            if cert: stats["cert"]+=1; verdict=f"cert@{cert[0]}"
            else: stats["alive"]+=1; verdict="ALIVE?"
        rows.append({"trial":trial,"bias":round(float(Dw),3),"P16":P,
                     "meanb":round(float(np.mean(w)),3),"verdict":verdict})
    print(json.dumps(stats,indent=0))
    alive=[r for r in rows if r["verdict"]=="ALIVE?"]
    print(f"candidates tested={len(rows)}, ghosts={stats['ghost']}, certified={stats['cert']}, alive={len(alive)}")
    for r in alive[:5]: print("  ALIVE:",r)
    return rows,stats

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("cmd",choices=["pilot","rank"])
    ap.add_argument("--n",type=int,default=200)
    ap.add_argument("--M",type=int,default=300)
    a=ap.parse_args()
    if a.cmd=="pilot": pilot(a.n,a.M)
    elif a.cmd=="rank":
        rng=np.random.default_rng(2)
        law,_=biased_letter_law()
        w=calibrate(gen_word(law,a.M,rng))
        for p in (8,12,16): print(f"p={p}: expvec rank={expvec_rank(w,p)} (ambient 2)")
