# The Frontier Program — working notes

## Surviving counterexample profile (post repetition-rigidity)

A critical pseudorandom subshift word: alphabet mostly {1,2} with sparse
≥3 corrections; mean calibrated to log₂3; persistent non-coboundary bias
ε at some level 3^r; factor complexity P(p) ≈ M−p+1 inside every banded
window at p ~ log₂Y; mixed-adically coherent; all periodic approximants
Baker-dead.

## Target 1 — Banded S-unit rigidity (analytic)

**Conjecture.** Fix W>1. There are A, κ>0 such that any no-descent
segment x_n..x_{n+M} ⊂ [Y, WY] with p = ⌊log₂Y⌋ satisfies one of:
(1) a repeated length-p block (⟹ integer cycle, dead by repetition
rigidity + Baker); (2) at most exp((1−κ)p) realizable distinct block
identities; (3) a mixed-level max-plus certificate.

Route: each block identity 2^{B}x' − 3^p x = A_{n,p} is a unit equation
with A a structured S-unit sum. Many identities with x, x' in a short
multiplicative interval ⟹ apply quantitative subspace/S-unit finiteness
(ESS 2002) to the normalized relations; the finitely many subspaces
correspond to linear exponent patterns = (eventually) repeated blocks.
Key diagnostic before proving: the Z-rank of exponent-vector differences
in high-deviation vs ordinary windows (rank collapse = traction).

## Target 2 — Band-crossing certificate (analytic)

**Conjecture.** For every W there is δ such that a no-descent crossing of
[Y, WY] in fewer than (1+δ)·log₂(W)/(2−log₂3) steps forces b=1-density
> 1/2 + δ on the crossing, which is 2-adically certificate-triggering
(the crossing word's realizability class converges to the negative ghost
x ≡ −1 mod 2^k unless interrupted by b ≥ 2 events that produce descent).

Route: quantify the all-ones exclusion (b≡1 forever ⟹ x = −1): a
crossing with b=1-density 1/2+δ over m steps forces x ≡ −1 mod 2^{f(δ)m}
on a positive fraction of the window — incompatible with positivity at
height Y once f(δ)m > log₂Y + O(1). [Sharpen: which mixed words of high
1-density are 2-adically near-ghost?]

## Target 3 — Mixed-tower certificate enumeration (computational)

For symbolic candidates passing all soft filters: extract residue-edge
traps over levels 2^a3^b (a ≤ A₀, b ≤ B₀), run Karp max-cycle-mean over
λ-grids, extract potentials Ψ when certificates exist, record the
(a,b)-level at which each candidate dies. Empirical target: every
candidate dies (ghost or certificate) — data for the rigidity theorems.

## Open questions log

- Q1: is the exponent-vector rank collapse real? (pilot: see results/)
- Q2: minimal (a,b) certificate level as a function of bias ε and mean
  deficit — is it uniformly bounded?
- Q3: can a calibrated word with bias ε have FULL de-Bruijn-like
  complexity at all scales simultaneously? (entropy vs bias tension:
  bias fixes a letter-marginal deviation; max-entropy subject to the
  marginal is a Markov measure — compute its complexity growth and
  whether repetition rigidity's threshold is met inside windows.)
