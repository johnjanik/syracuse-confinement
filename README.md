# Diophantine Confinement in Syracuse Dynamics

A formal reduction of the Collatz conjecture to a Diophantine confinement problem,
machine-checked in Lean 4 with Mathlib.

The formalization identifies three forces that constrain Syracuse (3n+1) trajectories:

1. **Hensel attrition** (2-adic): consecutive dangerous steps decay as 2^{-d}
2. **Baker separation** (Archimedean): |p log 2 - q log 3| > C/q^5 prevents
   rational approximation of log_2(3)
3. **Denjoy-Koksma bound** (ergodic): Birkhoff sums over irrational rotations
   grow as O(t^{1/5}) via Rhin's irrationality measure

These forces combine to reduce the conjecture to a single open statement:
the deficit delta(n,t) = 3 nu_3(n,t) - t is bounded for every starting value n.

## Building the Lean formalization

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Internet connection (to fetch Mathlib on first build)

### Build

```bash
cd lean4
lake build
```

The first build downloads Mathlib and its compiled cache (~1.5 GB), then compiles
the project. Subsequent builds are incremental.

**Expected output:** `Build completed successfully (3112 jobs).`

### Toolchain

- Lean 4 v4.27.0
- Mathlib v4.27.0

## Project structure

```
lean4/
  CollatzLean.lean          -- Root module (36 imports)
  CollatzLean/
    Basic.lean              -- Collatz sequence, collatzReaches, CollatzConjecture
    Conclusion.lean         -- Main theorem: collatz_conjecture (from nu3_linear_bound)
    SublinearDrift.lean     -- Alternative path: collatz_via_denjoy_koksma

    -- Arithmetic core
    Baker.lean              -- Axiom A1: baker_two_three (Baker 1966)
    IrrationalityMeasure.lean -- Axiom A2: rhin_irrationality_measure (Rhin 1987)
    SteinerCycle.lean       -- Axiom A3: hercher_no_small_cycle (Hercher 2023)
    WeylEquidistribution.lean -- Axiom A4: weyl_equidistribution (Weyl 1916)
    DenjoyKoksma.lean       -- Axiom A5: denjoy_koksma_sublinear_birkhoff
    UniqueErgodicity.lean   -- Axiom A6: skew_product_uniquely_ergodic (Furstenberg 1961)

    -- Walk and deficit infrastructure
    Walk.lean               -- Walk = nu2 - log_2(3) * nu3
    HenselAttrition.lean    -- Deficit, Hensel decay, v2-danger runs
    DiophantineRepeller.lean -- Baker cell separation, finite_deficit_bound [sorry]
    Drift.lean              -- nu3_linear_bound [sorry], walk divergence

    -- Cycle elimination
    CorrectionRatio.lean    -- K-bound -> bounded -> periodic -> cycle = {1,2,4}
    CycleElimination.lean   -- Strict inequality for non-trivial cycles

    -- Skew product and ergodic theory
    SkewProduct.lean        -- Cocycle decomposition, fiber = walk
    CorrelationDecay.lean   -- Autocorrelation vanishing for d >= 2
    SolenoidMixing.lean     -- Solenoid infrastructure

    -- Supporting modules
    Parity.lean, Identity.lean, Torus.lean, SFT.lean, ...
```

## Axioms and sorrys

**6 axioms** (published theorems, axiomatized as external results):

| # | Name | Source | Content |
|---|------|--------|---------|
| A1 | `baker_two_three` | Baker 1966 | log_2(3) is transcendental with effective lower bound |
| A2 | `rhin_irrationality_measure` | Rhin 1987 | Irrationality measure mu(log_2(3)) <= 6 |
| A3 | `hercher_no_small_cycle` | Hercher 2023 | No non-trivial cycle with period sum < 80 |
| A4 | `weyl_equidistribution` | Weyl 1916 | Equidistribution of irrational rotations |
| A5 | `denjoy_koksma_sublinear_birkhoff` | Denjoy-Koksma | Sublinear Birkhoff sums for Diophantine rotations |
| A6 | `skew_product_uniquely_ergodic` | Furstenberg 1961 | Unique ergodicity of skew products with irrational cocycle |

**13 sorrys** (open proof obligations):

- **Critical path (2):** `nu3_linear_bound`, `finite_deficit_bound`
- **Denjoy-Koksma transfer (3):** `deficit_sublinear_bound`, `deficit_sublinear`, `deficit_sublinear_of_polynomial_bound`
- **Sublinear drift (2):** `three_delta3_le_p_of_sublinear`, `reaches_one_of_sublinear_deficit`
- **Weyl bridge (2):** `equidistribution_implies_deficit_bounded`, `nu3_linear_bound_from_weyl`
- **Growth estimates (3):** `blaschke_factor_le_ratio`, `rising_factorial_le_pow`, `poisson_jensen_blaschke`
- **Cycle (1):** `steiner_cycle_large`

## Computational data

The `c_scripts/` directory contains C programs for large-scale computation:

- **branch_locus.c** -- Branch counting on the (2,3)-torus grid, OpenMP parallelized
  with binary checkpoint/resume. Verified to N = 10 billion.
- **v2_danger.c** -- Two-pass analysis of v_2 = 1 dangerous runs, Hensel attrition
  statistics, and hopping correlation.
- **gpu_branch_kernel.cl / gpu_branch_host.c** -- OpenCL GPU-accelerated branch counting
  (1,768M nums/s convergence verification on RTX 5090).

## Papers

- `diophantine_confinement.pdf` -- Main paper
- `pedagogical_paper.pdf` -- Companion/pedagogical exposition

## License

MIT
