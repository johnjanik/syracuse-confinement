#!/usr/bin/env python3
"""High-resolution (D, eps) phase diagram. Batched tilted strip transfers:
T(t,omega) = sum_b w_b(t,omega) * Shift_b; power iteration batched over tilts."""
import numpy as np, math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

LOG23=math.log2(3.0); LN2=math.log(2.0)
z=np.exp(2j*np.pi/3)
G=sum(2.0**-b*z**-b for b in range(1,200))
BMAX=20
GRID=0.025
Ds=np.arange(0.6,6.001,0.027)            # 200 D-values
eps_grid=np.linspace(0.0,0.6,150)        # 150 eps-values
ts=np.concatenate([[0.0],np.geomspace(0.2,20,39)])   # 40 tilts
omegas=np.exp(1j*np.linspace(0,2*np.pi,12,endpoint=False))
phis=np.array([[float(np.real(om*(z**(-b)-G))) for b in range(1,BMAX+1)] for om in omegas])  # (12,20)

RATE=np.full((len(eps_grid),len(Ds)),-9.0)
for di,D in enumerate(Ds):
    xs=np.arange(-D,D+1e-12,GRID); n=len(xs)
    # shift maps: for each b, target index array (or -1)
    idx=[]
    for b in range(1,BMAX+1):
        s2=xs+(LOG23-b)
        j=np.round((s2+D)/GRID).astype(int)
        ok=(s2>=-D-1e-9)&(s2<=D+1e-9)&(j>=0)&(j<n)
        j[~ok]=-1
        idx.append(j)
    lnlam=np.zeros((len(omegas),len(ts)))
    for oi in range(len(omegas)):
        W=np.exp(np.outer(ts,phis[oi]))           # (40,20)
        V=np.ones((len(ts),n))
        for it in range(110):
            V2=np.zeros_like(V)
            for bi in range(BMAX):
                j=idx[bi]; ok=j>=0
                V2[:,j[ok]]+=W[:,bi][:,None]*V[:,ok]
            nv=np.linalg.norm(V2,axis=1); nv[nv==0]=1
            V=V2/nv[:,None]
        lnlam[oi]=np.log(nv)
    # Legendre per eps
    for ei,eps in enumerate(eps_grid):
        RATE[ei,di]=np.max(np.min(lnlam-np.outer(np.ones(len(omegas)),ts*0)+0 - (ts*eps)[None,:],axis=1))
    if di%40==0: print(f"D={D:.2f} rate(0)={RATE[0,di]/LN2:.3f}")
np.savez('results/phase_diagram_hires.npz',Ds=Ds,eps=eps_grid,RATE=RATE)

TH=RATE/LN2
fig,ax=plt.subplots(figsize=(11,7))
cs=ax.contourf(Ds,eps_grid,TH,levels=np.linspace(0,1.6,33),cmap='RdBu_r')
cb=fig.colorbar(cs,ax=ax); cb.set_label(r'$\theta(D,\varepsilon)=\ln\lambda_{\rm eff}/\ln 2$')
bnd=ax.contour(Ds,eps_grid,TH,levels=[1.0],colors='k',linewidths=2.2)
ax.clabel(bnd,fmt={1.0:r'$\lambda_{\rm eff}=2$'},fontsize=9)
ax.contour(Ds,eps_grid,TH,levels=[1/(13.3+1)],colors='purple',linewidths=1.4,linestyles='--')
ax.text(0.63,0.025,r'$\theta=1/(\tau{+}1)$: full Baker exclusion',color='purple',fontsize=8,rotation=90)
ax.axvline(1.232,color='k',ls='--',lw=0.9,alpha=0.6)
ax.annotate(r'$D^*=1.232$',xy=(1.232,0.57),xytext=(1.45,0.575),fontsize=9,
            arrowprops=dict(arrowstyle='->',lw=0.8))
ax.text(0.83,0.30,'EXCLUDED\nany bias',fontsize=10,color='navy',ha='center',fontweight='bold')
ax.text(4.0,0.545,'EXCLUDED by bias',fontsize=10,color='navy',ha='center',fontweight='bold')
ax.text(4.0,0.12,'ALLOWED by counting\n(wide bands, low local bias)',fontsize=10,color='darkred',ha='center')
ax.scatter([3.4],[0.21],marker='d',s=60,color='crimson',zorder=5)
ax.annotate('pilot candidates',xy=(3.4,0.21),xytext=(4.3,0.26),fontsize=8,color='crimson',
            arrowprops=dict(arrowstyle='->',lw=0.7,color='crimson'))
ax.set_xlabel('strip half-width $D$  (band ratio $W=2^{2D}$)')
ax.set_ylabel(r'ord-3 shadow bias $\varepsilon$')
ax.set_title(r'The $(D,\varepsilon)$ phase diagram (200$\times$150 grid, 12 directions, 40 tilts, $\delta=0.025$)')
fig.tight_layout(); fig.savefig('viz/fig5_phase_diagram_hires.png',dpi=170)
print("wrote viz/fig5_phase_diagram_hires.png")
