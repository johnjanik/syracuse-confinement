# The exact phase-diagram engine: `vhires_phase.c` + render scripts

How to generate a high-resolution $(D,\varepsilon)$ phase diagram of any
window — e.g. to hunt for structure inside the candidate region.

## What the engine computes

`vhires_phase.c` computes `lnlam[D][omega][t]` = the exact growth rate
$\ln\lambda(D,\omega,t)$ of the tilted strip transfer, using the **exact
quantized state space**: $D$-confinement forces the partial sums $B_j$ into
the integer window around $j\log_2 3$ of size $\le\lfloor 2D\rfloor+1$, so
the rate is a Lyapunov average of small exact matrices along the rotation
orbit — **no grid discretization of the state variable**. Every feature you
see is arithmetic, not a rendering artifact (the old δ-grid scallops are
gone for good).

The $(D,\varepsilon)$ surface is then obtained in Python by the Legendre
transform $\theta(D,\varepsilon)=\max_\omega\min_t[\ln\lambda - t\varepsilon]/\ln 2$.
The exclusion boundary is the level set $\theta=1$ ($\lambda_{\rm eff}=2$).

## Build with compile-time overrides

```sh
cd shadow_frontier/search
gcc -O3 -march=native -fopenmp \
    -DND=3000 -DNT=400 -DP=4000 -DBURN=500 \
    -DDLO=1.20 -DDHI=4.20 \
    -DOUTBASE='"results/zoom_lnlam"' \
    -o zoom_phase vhires_phase.c -lm
cd ..            # run from the project root (OUTBASE is relative)
./search/zoom_phase
```

| flag | meaning | default |
|---|---|---|
| `-DDLO=`, `-DDHI=` | the $D$-window $[D_{\rm lo}, D_{\rm hi}]$ | 0.6, 6.0 |
| `-DND=` | number of $D$ grid points | 2000 |
| `-DNW=` | directions $\omega = e^{2\pi i k/N_W}$ | 24 |
| `-DNT=` | tilts: $t_0{=}0$, then geomspace(0.2, 20, NT−1) | 400 |
| `-DP=` | rotation-orbit length (boundary sharpness ~ 1/P) | 2800 |
| `-DBURN=` | burn-in steps excluded from the average | 400 |
| `-DOUTBASE='"path"'` | output basename (note the nested quotes) | `results/vhires_lnlam` |

Output: `OUTBASE.bin` — row-major `double[ND][NW][NT]` — plus an
`OUTBASE.meta` sidecar recording all parameters.

**Caveats.** (i) `MMAX=16` caps the window size: keep `DHI < 7.5`.
(ii) Runtime ≈ 90 s for 2000×24×400 at P=2800 on 24 cores, scaling
linearly in `ND·NW·NT·P` (and with $\lfloor 2D\rfloor^2$); the candidate-region
zoom (3000×24×400, P=4000) took ≈ 4 min. (iii) The `.bin` is large
(ND·NW·NT·8 bytes — 230 MB for the zoom): **gitignore it**, commit only the
compressed θ-surface npz and the PNG.

## Render: `phase_diagram_zoom.py`

Copy the script per window and edit the header block to **match the engine
flags exactly**:

```python
ND, NW, NT = 3000, 24, 400                      # must match -DND/-DNW/-DNT
Ds  = np.linspace(1.20, 4.20, ND)               # must match -DDLO/-DDHI/-DND
ts  = np.concatenate([[0.0], np.geomspace(0.2, 20.0, NT-1)])  # fixed grid
eps_grid = np.linspace(0.0, 0.60, 2000)         # free choice: eps is cheap
lnlam = np.fromfile('results/zoom_lnlam.bin').reshape(ND, NW, NT)
```

The ε-grid costs nothing (it only enters the Legendre post-processing), so
make it as fine as you like. The script also extracts $D^*$, the boundary
curve $\varepsilon^*(D)$, and the kink slope-jumps at $2D\in\mathbb Z$, and
writes a compressed `results/phase_diagram_<window>.npz` of the θ-surface.

## Sanity checks for any new window

1. **t=0 column is ω-independent**: `lnlam[:, :, 0]` must have zero spread
   across the ω axis.
2. **t=0 matches the exact counts**: $\theta(D,0)$ must agree with
   `exact_count.py` (e.g. θ(1.0)=0.828, θ(2.0)=1.258, $D^*=1.2463$).

## Hunting structure in the candidate region: recipes

The known arithmetic structure: the counting wall $D^*=1.24628$; boundary
kinks at $2D\in\mathbb Z$ (slope jumps −0.075 at D=1.5, −0.010 at 2.0/2.5,
−0.005 at 3.0); the binary ceiling $\varepsilon_{\rm bin}=0.449$ crossing
the boundary at D=2.4464. Promising micro-windows:

```sh
# 1. the D=1.5 kink, microscopic (does the corner have fine structure?)
gcc -O3 -march=native -fopenmp -DND=2000 -DNT=400 -DP=8000 -DBURN=1000 \
    -DDLO=1.45 -DDHI=1.55 -DOUTBASE='"results/kink15_lnlam"' \
    -o kink15_phase vhires_phase.c -lm

# 2. the ceiling crossing (boundary vs binary ceiling interplay)
gcc -O3 -march=native -fopenmp -DND=2000 -DNT=600 -DP=6000 -DBURN=800 \
    -DDLO=2.35 -DDHI=2.55 -DOUTBASE='"results/cross_lnlam"' \
    -o cross_phase vhires_phase.c -lm

# 3. deep interior of the candidate region (is the red zone featureless?)
gcc -O3 -march=native -fopenmp -DND=3000 -DNT=400 -DP=4000 \
    -DDLO=2.0 -DDHI=4.0 -DOUTBASE='"results/interior_lnlam"' \
    -o interior_phase vhires_phase.c -lm
```

Rendering tips for structure-hunting: tighten the color limits around the
local θ-range (`vmin/vmax`), add dense contour levels
(`np.arange(lo, hi, 0.005)`), and plot the gradient magnitude
`np.hypot(*np.gradient(TH))` — arithmetic features (window-size jumps,
resonances of the $\{j\log_2 3\}$ rotation, ceiling echoes from deeper
ghosts at $\varepsilon=|v-G|$ for other letter-support laws) appear as
level-set corners and gradient ridges. Raise `P` (and `BURN` ∝ P) before
trusting any feature smaller than ~1/P in θ; a real arithmetic feature
survives doubling `P`, a Lyapunov-average fluctuation halves.

## Candidate-search tools (`candidate_tools.py`, `candidate_image.py`, `candidate_checklist.py`)

A serious candidate image shows four simultaneous properties: banded height
(no downward trend), calibrated mean letter with nontrivial non-coboundary
shadow bias (D_3, D_9, D_27, D_5, D_11, D_13 — order-2/parity is exempt),
near-full factor diversity at the critical scale p = floor(log2 Y), and **no
mixed-tower max-plus descent certificate**: margin
inf_{lambda>=0}(P_H(lambda) - lambda*eps) >= 0 at all tested levels 2^a 3^b,
persisting under lifts.

```sh
# four-panel image + JSON diagnostics + six-step checklist for one candidate
python3 search/candidate_image.py --seed 687871 --steps 55 --out viz/cand_687871.png
python3 search/candidate_image.py --pilot 0 --out viz/cand_pilot000.png

# six-step checklist over a batch (120 pilots + champions + harvested
# ascending windows) + the (D,eps)->margin overlay on the phase diagram
python3 search/candidate_checklist.py     # writes viz/fig8_candidate_margins.png
```

The six checks: (1) C1 drift (mean b > log2(3)+eta = descent-forcing);
(2) repetition at critical p (collision distance < 2^{p+1} = rigidity
fires); (3) complexity ratio >= 0.9 (else low-complexity ghost); (4) a
non-coboundary character detects the bias; (5) Karp certificate margin at
levels 2^a 3^b (negative = descent certificate); (6) margin persists under
2- and 3-lifts (else finite artifact). Only windows surviving all six
deserve attention — and the two known ways to then kill them are OUTSIDE
the six: the ghost/realizability test (pilot words: full-bit-length least
representatives) and window transience (real ascending windows belong to
orbits that crash after the window).
