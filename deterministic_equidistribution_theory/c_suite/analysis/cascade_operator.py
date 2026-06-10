"""dc_23 sec 4: the two-channel threshold cascade chain in scaled coordinates,
heavy-row (x=-1, b_i=1) conditioning, levels i=1..c-3, moduli M_i=2*3^{c-3-i}.
Scaled state tbar_i = t_i/M_i; transition tbar' = 3*tbar + xbar, X = M_i*xbar = 1-b',
weight (normalized by phi-growth 3 per level): 3 * (1/2) * 2^{-(1-M_i*xbar)}  [xbar<=0].
Channels: D = deeper-so-far (tbar_j = 0 mod 3 all j), B = broken. beta: D->1, B->1/2.
Reports rho-rate, lock share, off-rep path mass, channel masses, Perron profile."""
import numpy as np
T=10                       # |tbar| cutoff
S=2*T+1
def level_matrix(M):
    # K[(ch',tb'),(ch,tb)] ; tb index offset T
    K=np.zeros((2*S,2*S))
    for tb in range(-T,T+1):
        for tbp in range(-T,T+1):
            xb=tbp-3*tb
            if xb>0: continue
            X=M*xb            # = 1 - b'  => b' = 1 - X >= 1 ok
            w=3*0.5*2.0**(X-1)
            if w<1e-30: continue
            deeper_ok = (tbp%3==0)
            for ch in (0,1):  # 0=D,1=B
                chp = 0 if (ch==0 and deeper_ok) else 1
                K[chp*S+(tbp+T), ch*S+(tb+T)]+=w
    return K
print(f"{'c':>3} {'rate':>7} {'lock-share':>10} {'offrep':>8} {'D-mass':>7} {'R_model':>10} {'Lam_model':>9}")
for c in (5,6,7,8,10,12,15,20,25,30):
    v=np.zeros(2*S); v[0*S+T]=1.0      # start: tbar=0, channel D
    total=1.0; lockonly=1.0
    Ms=[2*3**(c-3-i) for i in range(1,c-2)]
    for M in Ms:
        K=level_matrix(M)
        v=K@v
        lockonly*=3*0.25               # pure lock path weight per level
        s=v.sum(); total*=1.0
    mass=v.sum()
    D=v[:S].sum(); B=v[S:].sum()
    beta_mass=1.0*D+0.5*B
    # tail levels (i=c-2,c-1: unconstrained, factor 3*(1/2)*1 each) and |S| prefactor folded as const
    R_model=beta_mass*(1.5**2)
    rate=mass**(1/len(Ms)) if len(Ms)>0 else float('nan')
    offrep=1-lockonly/mass
    print(f"{c:>3} {rate:>7.4f} {lockonly/mass:>10.4f} {offrep:>8.1e} {D/mass:>7.4f} {R_model:>10.3e} {R_model**(1/(2*c)):>9.4f}")
# Perron-profile at c=20: top right-vector of the bulk level matrix (large M)
Kb=level_matrix(2*3**8)
ev,V=np.linalg.eig(Kb)
i=np.argmax(np.abs(ev))
vec=np.abs(V[:,i]); vec/=vec.max()
print("\nbulk per-level matrix: rho =",f"{abs(ev[i]):.6f}")
print("Perron profile over tbar (D channel):", np.round(vec[:S][T-3:T+4],6), "(tbar=-3..3)")
