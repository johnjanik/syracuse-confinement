"""dc_25 sec 9: levelwise audit of op:flat.
(a) Exact shells: Qtilde_L = 3^L Col_L(L) = sum_{u mod 3^L}|E_hat_L(u)|^2, per-level max.
(b) Transience of the expanding phase chain theta -> 3*2^{-b} theta (exact in t/3^L)."""
import numpy as np
def Ehat_all(L):
    Q=3**L; P=2*3**(L-1)
    pw=np.array([pow(2,r,Q) for r in range(P)],np.int64)
    G=np.array([2.0**(-(d if d>0 else P))/(1-2.0**(-P)) for d in range(P)])
    fG=np.fft.fft(G)
    us=np.arange(Q)
    out=np.zeros(Q)
    BATCH=max(1,int(2e7//P))
    for lo in range(0,Q,BATCH):
        ub=us[lo:lo+BATCH]
        a=np.zeros((len(ub),P),complex); a[:,0]=1.0
        for j in range(L):
            ph=np.exp(2j*np.pi*(((ub[:,None]*pow(3,L-1-j,Q))%Q)*pw[None,:]%Q)/Q)
            a=np.fft.ifft(np.fft.fft(a*ph,axis=1)*fG[None,:],axis=1)
        out[lo:lo+BATCH]=np.abs(a.sum(axis=1))**2
    return out
print(f"{'L':>2} {'Qtilde_L':>9} {'shell_L':>9} {'max|E|^2*3^L (prim)':>19} {'argmax':>7}")
prev=None
for L in range(1,8):
    E2=Ehat_all(L)
    Q=3**L
    Qt=E2.sum()
    prim=np.array([u for u in range(1,Q) if u%3])
    shell=E2[prim].sum()
    mx=E2[prim].max(); am=prim[E2[prim].argmax()]
    print(f"{L:>2} {Qt:>9.4f} {shell:>9.4f} {mx*3**L:>19.3f} {am:>7}")
# (b) transience: phase chain theta_k = t_k/3^{L-k}; weak region |theta| <= 3^{-2}
rng=np.random.default_rng(2)
print("\ntransience (chain theta->3*2^{-b}theta, exact; N_weak=#steps with |theta|<=1/9):")
print(f"{'L':>3} {'E[N_weak] u=1':>14} {'E[N_weak] u rnd':>15} {'theory L*log6(2)~':>16}")
for L in (6,8,10,12,16,20):
    QL=3**L
    for tag,uset in (("u1",[1]),("rnd",[int(x) for x in rng.integers(1,QL,40) if x%3][:30])):
        tot=0; n=0
        for u in uset:
            for _ in range(400 if tag=="u1" else 30):
                t=u; weak=0
                for k in range(L):
                    Qk=3**(L-k)
                    th=(t%Qk)/Qk; th=min(th,1-th)
                    if th<=1/9: weak+=1
                    b=int(rng.geometric(0.5))
                    t=(t*pow(2,-b,Qk))%Qk if Qk>1 else 0
                tot+=weak; n+=1
        if tag=="u1": e1=tot/n
        else: er=tot/n
    print(f"{L:>3} {e1:>14.2f} {er:>15.2f} {L*np.log(2)/np.log(6)*0+np.log(QL)/np.log(6):>16.2f}")
