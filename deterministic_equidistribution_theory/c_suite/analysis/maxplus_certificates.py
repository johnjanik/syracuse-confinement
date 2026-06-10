"""dc_31 sec 8: max-plus certificate search.
Trap H in G_r: vertices U_{3^r}, edges (a,b)->S_b(a), labels g(b)=log2(3)-b,
phi(b)=Re(omega(z^{-b}-G)). Certificate exists iff inf_{lambda>=0} (P_H(lambda)-lambda*eps)<0,
P_H = max cycle mean of g+lambda*phi (Karp)."""
import numpy as np, random
random.seed(3)
LOG23=np.log2(3.0)
def G(z): return (1/(2*z))/(1-1/(2*z))
def karp_max_cycle_mean(V,edges,w):
    # edges: list of (u,v,idx); w: weight per edge index
    n=len(V); INF=-1e18
    dp=np.full((n+1,n),INF); dp[0,:]=0.0
    for k in range(1,n+1):
        for (u,v,i) in edges:
            if dp[k-1][u]>INF/2 and dp[k-1][u]+w[i]>dp[k][v]:
                dp[k][v]=dp[k-1][u]+w[i]
    best=-np.inf
    for vtx in range(n):
        if dp[n][vtx]<=INF/2: continue
        m=np.inf
        for k in range(n):
            if dp[k][vtx]>INF/2:
                m=min(m,(dp[n][vtx]-dp[k][vtx])/(n-k))
        best=max(best,m)
    return best
def build_trap(r,word_pairs):
    # word_pairs: list of (a mod 3^r, b); returns vertex list, edges, labels g, phi-placeholder b-values
    Q=3**r
    verts=sorted(set([a for a,b in word_pairs]+[((3*a+1)*pow(2,-b,Q))%Q for a,b in word_pairs]))
    vidx={v:i for i,v in enumerate(verts)}
    edges=[];gv=[];bv=[]
    seen=set()
    for a,b in word_pairs:
        a2=((3*a+1)*pow(2,-b,Q))%Q
        key=(a,b)
        if key in seen: continue
        seen.add(key)
        edges.append((vidx[a],vidx[a2],len(gv)))
        gv.append(LOG23-b); bv.append(b)
    return verts,edges,np.array(gv),np.array(bv)
def certify(edges,verts,gv,bv,z,eps,omega):
    phi=np.real(omega*(z**(-bv.astype(float))-G(z)))
    best=(np.inf,None)
    for lam in np.linspace(0,30,121):
        P=karp_max_cycle_mean(verts,edges,gv+lam*phi)
        val=P-lam*eps
        if val<best[0]: best=(val,lam)
    return best
zeta3=np.exp(2j*np.pi/3)
# --- observed phase-only high-deviation windows ---
def orbit(x0,maxn=12000):
    xs=[x0];bs=[];x=x0
    for _ in range(maxn):
        y=3*x+1;b=0
        while y%2==0: y//=2;b+=1
        bs.append(b);x=y;xs.append(x)
        if x==1: break
    return xs,bs
M=64; r=2; Q=3**r
print("=== observed phase-only high-deviation windows (r=2, ord-3 char) ===")
found=0
for trial in range(30):
    x0=random.randrange(10**79,10**80)*2+1
    xs,bs=orbit(x0)
    if len(bs)<M+10: continue
    for start in range(0,len(bs)-M,M):
        w=bs[start:start+M]
        D=np.mean([zeta3**(-b) for b in w])-G(zeta3)
        meanb=np.mean(w)
        if abs(D)>=0.18 and abs(meanb-2)<=0.25:
            omega=np.conj(D/abs(D)); eps=abs(D)
            wp=[(xs[start+i]%Q,w[i]) for i in range(M)]
            verts,edges,gv,bv=build_trap(r,wp)
            val,lam=certify(edges,verts,gv,bv,zeta3,eps,omega)
            print(f"  window: |D|={eps:.3f} mean-b={meanb:.2f} |H|={len(gv)}edges: min(P-lam*eps)={val:+.4f} at lam={lam:.2f}  {'CERTIFIED' if val<0 else 'NO CERT'}")
            found+=1
            if found>=8: break
    if found>=8: break
# --- synthetic traps ---
print("\n=== synthetic traps ===")
# (a) all b=1 (the -1 cycle shadow): trap from iterating a->(3a+1)/2 mod 9
wp=[]; a=1
for _ in range(20): wp.append((a,1)); a=((3*a+1)*pow(2,-1,Q))%Q
verts,edges,gv,bv=build_trap(r,wp)
D=zeta3**(-1.0)-G(zeta3); omega=np.conj(D/abs(D)); eps=abs(D)
val,lam=certify(edges,verts,gv,bv,zeta3,eps,omega)
print(f"  all-b=1 trap: eps={eps:.3f}: min(P-lam*eps)={val:+.4f}  {'CERTIFIED' if val<0 else 'NO CERT (as predicted: 2-adic tower must kill it)'}")
# (b) near-critical {1,2}-mixture, p(1)=0.415: random word with that law threaded through residues
p1=2-LOG23  # mean = 1*p+2(1-p)=log2 3 => p = 2-log2 3 = 0.415
random.seed(5); a=1; wp=[]
bsmix=[1 if random.random()<p1 else 2 for _ in range(4000)]
for b in bsmix: wp.append((a,b)); a=((3*a+1)*pow(2,-b,Q))%Q
Dm=np.mean([zeta3**(-b) for b in bsmix])-G(zeta3)
omega=np.conj(Dm/abs(Dm)); eps=abs(Dm)
verts,edges,gv,bv=build_trap(r,wp)
val,lam=certify(edges,verts,gv,bv,zeta3,eps,omega)
print(f"  critical {{1,2}}-mixture (mean=log2 3, eps={eps:.3f}): min(P-lam*eps)={val:+.4f}  {'CERTIFIED' if val<0 else 'NO CERT'}")
