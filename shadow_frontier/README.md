# Shadow Frontier

Successor project to [Finite Spectral Shadows](../deterministic_equidistribution_theory/):
the exploration of what survives every filter of that program. By its
results, a Collatz counterexample must be a **high-complexity, calibrated,
phase-biased, mixed-adically coherent ghost** that resists every finite
max-plus certificate:

- mean letter → log₂3 (else C1 descent),
- persistent non-coboundary character bias (keystone arrow),
- nearly maximal length-p factor diversity in every banded window at
  p ≈ log₂(height) (repetition rigidity + Baker),
- coherent through the joint (2,3)-adic tower, certificate-free at every
  level 2^a3^b.

## The three targets (dc_next_steps)

1. **Banded S-unit rigidity** — many coherent block identities
   `2^{B_{i,p}} x_{i+p} − 3^p x_i = A_{i,p}` with all x in a band force
   the S-unit exponent vectors `(B_{i,j}, p−1−j)` into finitely many
   linear patterns (Evertse–Schlickewei–Schmidt territory); those
   patterns are repeated/periodic blocks, already dead.
2. **Band-crossing certificate** — orbits avoiding long banded windows
   cross bands fast, forcing b=1-density high enough to trigger 2-adic
   certificates (the x = −1 ghost direction).
3. **Mixed-tower certificate enumeration** — finite Karp/max-plus
   verification over 2^a3^b for traps extracted from symbolic candidates.

Final dichotomy: long banded windows ⟹ S-unit rigidity;
no long banded windows ⟹ band-crossing certificate.

## Layout

- `notes/PROGRAM.md` — the working analytic program (precise theorem targets).
- `search/frontier.py` — the symbolic search: candidate generation
  (calibrated + biased + high-complexity), 2-adic realizability (ghost
  test), mixed-tower trap extraction, Karp max-plus certificates,
  exponent-vector rank diagnostics.
- `results/` — pilot outputs and search logs.

Provenance: AIPM (`ailog`) from day one.
