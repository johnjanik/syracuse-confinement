#!/usr/bin/env python3
"""The (D, eps) phase diagram: lambda_eff(D, eps) = exponential growth rate of
strip-confined words (discrepancy half-width D) carrying ord-3 bias >= eps.
Legendre: rate(eps) = max_omega inf_{t>=0} [ln lambda_t(D,omega) - t*eps].
Phase boundary: lambda_eff = 2 (band capacity). Below: repetition forced."""
import numpy as np, math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

LOG23=math.log2(3.0); LN2=math.log(2.0)
z=np.exp(2j*np.pi/3)
G=sum(2.0**-b*z**-b for b in range(1,200))
BMAX=20

def lam_t(D, t, omega, grid=0.05):
    xs=np.arange(-D,D+1e-9,grid); n=len(xs)
    T=np.zeros((n,n))
    for b in range(1,BMAX+1):
        w=math.exp(t*float(np.real(omega*(z**(-b)-G))))
        shift=LOG23-b
        js=np.round((xs+shift+D)/grid).astype(int)
        ok=(xs+shift>=-D-1e-9)&(xs+shift<=D+1e-9)&(js>=0)&(js<n)
        for i in np.where(ok)[0]:
            T[js[i],i]+=w
    v=np.ones(n)
    for _ in range(120):
        v=T@v; nv=np.linalg.norm(v)
        if nv==0: return 0.0
        v/=nv
    return math.log(nv)

Ds=np.arange(0.6,6.01,0.27)
eps_grid=np.arange(0.0,0.62,0.04)
ts=np.concatenate([[0],np.geomspace(0.25,12,14)])
omegas=[np.exp(1j*a) for a in np.linspace(0,2*np.pi,8,endpoint=False)]
RATE=np.zeros((len(eps_grid),len(Ds)))
for di,D in enumerate(Ds):
    # precompute ln lambda_t for all (omega,t)
    LL={ (oi,ti): lam_t(D,t,om) for oi,om in enumerate(omegas) for ti,t in enumerate(ts) }
    for ei,eps in enumerate(eps_grid):
        best=-99
        for oi in range(len(omegas)):
            r=min(LL[(oi,ti)]-ts[ti]*eps for ti in range(len(ts)))
            best=max(best,r)
        RATE[ei,di]=best
    print(f"D={D:.2f} done; rate(eps=0)={RATE[0,di]:.3f} ({RATE[0,di]/LN2:.2f} ln2)")

np.savez('results/phase_diagram.npz', Ds=Ds, eps=eps_grid, RATE=RATE)

fig,ax=plt.subplots(figsize=(10,6.5))
TH=RATE/LN2   # in units of ln2: boundary at 1
cs=ax.contourf(Ds,eps_grid,TH,levels=np.arange(0,1.65,0.1),cmap='RdBu_r',alpha=0.85)
cb=fig.colorbar(cs,ax=ax); cb.set_label(r'$\theta(D,\varepsilon)=\ln\lambda_{\rm eff}/\ln 2$  (window exponent)')
bnd=ax.contour(Ds,eps_grid,TH,levels=[1.0],colors='k',linewidths=2.5)
ax.clabel(bnd,fmt={1.0:r'$\lambda_{\rm eff}=2$  PHASE BOUNDARY'},fontsize=9)
ax.axvline(1.232,color='k',ls='--',lw=1.0,alpha=0.7)
ax.annotate(r'$D^*=1.232$ (band ratio $2^{2D^*}\!\approx\!5.5$)',xy=(1.232,0.55),xytext=(1.5,0.56),
            fontsize=9,arrowprops=dict(arrowstyle='->',lw=0.8))
ax.text(0.72,0.30,'EXCLUDED\n(repetition forced:\ndwell $\\Rightarrow$ cycle)\nany bias',fontsize=10,
        color='navy',ha='center',fontweight='bold')
ax.text(4.0,0.50,'EXCLUDED by bias\n(biased words too few:\n$\\lambda_{\\rm eff}<2$)',fontsize=10,
        color='navy',ha='center',fontweight='bold')
ax.text(4.0,0.10,'ALLOWED by counting\n(counterexample windows must live here:\nwide bands, low local bias)',
        fontsize=10,color='darkred',ha='center')
# reference markers
ax.scatter([0.9],[0.45],marker='s',s=70,color='royalblue',zorder=5)
ax.annotate('Sturmian ($D<1$, dead)',xy=(0.9,0.45),xytext=(0.66,0.38),fontsize=8,color='royalblue')
ax.scatter([3.4],[0.21],marker='d',s=70,color='crimson',zorder=5)
ax.annotate('pilot candidates\n(window $D\\sim3.4$, $\\varepsilon\\approx0.21$)',xy=(3.4,0.21),
            xytext=(4.4,0.27),fontsize=8,color='crimson',arrowprops=dict(arrowstyle='->',lw=0.7,color='crimson'))
ax.set_xlabel('strip half-width $D$  (band ratio $W=2^{2D}$)')
ax.set_ylabel('ord-3 shadow bias $\\varepsilon$')
ax.set_title('The $(D,\\varepsilon)$ phase diagram: where banded windows are forced to repeat')
fig.tight_layout(); fig.savefig('viz/fig5_phase_diagram.png',dpi=140)
print("wrote viz/fig5_phase_diagram.png")
