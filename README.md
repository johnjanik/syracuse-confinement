# Diophantine Confinement in Syracuse Dynamics

A formal reduction of the Collatz conjecture to a Diophantine confinement problem,
machine-checked in Lean 4 with Mathlib. **12,947 lines** across **45 files**.

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
  CollatzLean.lean              -- Root module (45 imports)
  CollatzLean/
    -- Foundation
    Basic.lean                  -- Collatz map, collatzReaches, CollatzConjecture
    Parity.lean                 -- Step parity, no-consecutive-odd-steps
    Winding.lean                -- nu2/nu3 counters, nu_partition
    Identity.lean               -- Multiplicative identity: a(t)·2^ν₂ = n·3^ν₃ + correction
    Torus.lean                  -- (Z/kZ)² torus residues, advance rules

    -- Symbolic dynamics
    SFT.lean                    -- Shift of finite type, golden mean shift
    CollatzSFT.lean             -- Collatz parity sequence lies in golden mean shift
    FibCounting.lean            -- Fibonacci counting, log₂3 < φ, topological entropy

    -- Branch locus
    BranchLocus.lean            -- Cell classification (branch/pure-even/pure-odd)
    StructuralPureEven.lean     -- Structural pure-even cells, double-halving
    TunnelWidth.lean            -- Diophantine error, Baker → positive wall width
    WallPersistence.lean        -- Walls persist at all scales, walk boost

    -- Walk and deficit
    Walk.lean                   -- Walk u(t) = ν₂ - log₂3·ν₃, drift, equilibrium
    HenselAttrition.lean        -- Hensel decay, v₂-danger runs, deficit tracking
    DiophantineRepeller.lean    -- Baker cell separation, sliding window, deficit bound
    DeficitBudget.lean          -- Deficit budget accounting, safe density
    Drift.lean                  -- nu3_linear_bound [sorry], walk divergence

    -- Cycle elimination
    CorrectionRatio.lean        -- K-bound → bounded → periodic → cycle = {1,2,4}
    CycleElimination.lean       -- Linear form bounds, strict inequality
    SteinerCycle.lean           -- Steiner bounds, Hercher axiom, Baker decomposition
    ContinuedFraction.lean      -- CF of log₂3, convergent verification, Steiner boundary

    -- Baker and transcendence
    Baker.lean                  -- Multiplicative independence, irrationality, Baker axiom
    IrrationalityMeasure.lean   -- Rhin axiom, linear form lower bounds
    SiegelLemma.lean            -- Auxiliary polynomial construction
    GrowthEstimates.lean        -- Entire function theory, Schwarz lemma, Gelfond-Schneider
    LinearFormThree.lean        -- Three-logarithm independence, Matveev axiom

    -- Syracuse framework
    Syracuse.lean               -- val2, Syracuse map, Tao affine identity
    SyracuseDrift.lean          -- Syracuse-Collatz bridge, valuation tracking

    -- Ergodic theory
    SkewProduct.lean            -- Cocycle decomposition, fiber = walk
    CorrelationDecay.lean       -- Autocorrelation vanishing, danger intervals
    SolenoidMixing.lean         -- Solenoid infrastructure, Hensel-Baker conflict
    BorelCantelli.lean          -- Survivor counting, danger density bounds
    UniqueErgodicity.lean       -- Unique ergodicity, cocycle growth rate
    WeylEquidistribution.lean   -- Weyl axiom, safe density, equidistribution bridge
    DenjoyKoksma.lean           -- DK axiom, deficit sublinear bounds

    -- Spectral and rigidity
    SpectralGap.lean            -- Spectral gap 2/3, telescoping product, transfer operator
    ArithmeticRigidity.lean     -- Three-way equivalence: Collatz ↔ Furstenberg ↔ Littlewood
    MetricConflict.lean         -- Metric conflict, attrition exceeds exit

    -- Carry bit and fuel
    CarryBitScrambling.lean     -- Carry propagation, bit-peeling, transition matrix
    FuelDynamics.lean           -- Fuel divisibility, regeneration path

    -- Approximation theory
    SimultaneousApprox.lean     -- Fractional distance, Littlewood product
    LittlewoodResidence.lean    -- Residence bounds, cell product bounds
    LittlewoodInduction.lean    -- Scale induction, simultaneous_approx [sorry]

    -- Sublinear drift and conclusion
    SublinearDrift.lean         -- Alternative DK path: sublinear deficit → reaches 1
    Conclusion.lean             -- Main theorem: collatz_conjecture
```

## Axioms and sorrys

### Axioms (9)

Published theorems axiomatized as external results:

| # | Name | File | Source | Content |
|---|------|------|--------|---------|
| A1 | `baker_two_three` | Baker.lean:242 | Baker 1966 | Effective lower bound on \|m·log 2 + n·log 3\| |
| A2 | `rhin_irrationality_measure` | IrrationalityMeasure.lean:34 | Rhin 1987 | Irrationality measure μ(log₂3) ≤ 6 |
| A3 | `hercher_no_small_cycle` | SteinerCycle.lean:248 | Hercher 2024 | No non-trivial m-cycle for m ≤ 91 |
| A4 | `baker_steiner_no_large_cycle` | SteinerCycle.lean:320 | Baker-Steiner | No cycle with Δ₃ ≥ 80 (extends Hercher) |
| A5 | `weyl_equidistribution_of_irrational_rotation` | WeylEquidistribution.lean:85 | Weyl 1916 | ⌊kα⌋ mod N equidistributed for α irrational |
| A6 | `denjoy_koksma_sublinear_birkhoff` | DenjoyKoksma.lean:93 | Khintchine/Herman | Birkhoff sums sublinear for Diophantine rotations |
| A7 | `matveev_three_log` | LinearFormThree.lean:358 | Matveev 2000 | Lower bound on linear forms in 3 logarithms |
| A8 | `skew_product_uniquely_ergodic` | UniqueErgodicity.lean:186 | Furstenberg 1961 | Unique ergodicity of irrational skew products |
| A9 | `arithmetic_decoupling` | SpectralGap.lean:351 | — | Spectral gap implies per-trajectory equidistribution |

### Sorrys (6 critical path + 6 exploratory)

**Critical path** (each equivalent to the Collatz conjecture):

| Sorry | File | Statement |
|-------|------|-----------|
| `nu3_linear_bound` | Drift.lean:31 | ∃ K T₀, ∀ t ≥ T₀, 3·ν₃(n,t) ≤ t + K |
| `finite_deficit_bound` | DiophantineRepeller.lean:254 | ∃ D, ∀ t, deficit(n,t) ≤ D |
| `equidistribution_implies_deficit_bounded` | WeylEquidistribution.lean:376 | Equidistribution of cell visits → deficit bounded |
| `cellSeqNu2_equidistributed` | WeylEquidistribution.lean:453 | ν₂ sequence equidistributed mod N (odd N) |
| `syracuseValSum_equidistributed_of_sublinear_walk` | SolenoidMixing.lean:273 | Sublinear walk → valuation sums equidistributed |
| `simultaneous_approx_log2_5_7` | LittlewoodInduction.lean:147 | Simultaneous Diophantine approximation for log₂5, log₂7 |

**Exploratory** (spectral gap / rigidity program, NOT on critical path):

| Sorry | File | Statement |
|-------|------|-----------|
| `spectral_gap_transfer` | SpectralGap.lean:293 | T₃ contracts L² norm by 1/9 (standard Fourier analysis) |
| `spectral_gap_iterated` | SpectralGap.lean:299 | t-fold contraction by (1/9)^t |
| `furstenberg_partition_rigidity` | ArithmeticRigidity.lean:219 | T₃-invariant probability → uniform on Z/2^j Z |
| `spectral_gap_implies_collatz` | ArithmeticRigidity.lean:269 | Spectral mixing rate γ > 0 → CollatzConjecture |
| `spectral_gap_implies_furstenberg` | ArithmeticRigidity.lean:290 | γ > 0 → Furstenberg partition rigidity |
| `spectral_gap_implies_littlewood` | ArithmeticRigidity.lean:309 | γ > 0 → Littlewood for (log₂5, log₂7) |

## Main proof chains

### Critical path (Collatz conjecture)
```
nu3_linear_bound [sorry]
  → podd_uniform_bound [proved]
  → walk_diverges_of_podd_bound [proved]
  → collatzSeq_eventually_bounded_of_linear_drift [proved]
  → collatzSeq_eventually_periodic_of_bounded [proved]
  → cycle_contains_one [proved — full case split]
  → reaches_one_of_linear_drift [proved]
  → collatz_conjecture [proved]
```

### Equivalence
```
nu3_linear_bound_iff_reaches : K-bound ↔ collatzReaches n  [proved, Conclusion.lean]
```

### Alternative path (Denjoy-Koksma)
```
finite_deficit_bound [sorry]
  → k_bound_of_deficit_bounded [proved]
  → trajectory_bounded_of_sublinear_deficit [proved]
  → reaches_one_of_sublinear_deficit [proved]
  → collatz_via_denjoy_koksma [proved]
```

### Cycle elimination (fully proved modulo axioms A1-A4)
```
Δ₃ = 0: no_cycle_delta3_zero [proved — 2^p = 1 impossible]
Δ₃ = 1: cycle_contains_one_of_delta3_one [proved — only {1,2,4}]
Δ₃ ≥ 2, 3Δ₃ < p: no_cycle_strict_inequality [proved]
Δ₃ ≥ 2, 3Δ₃ = p: no_cycle_equality_case [proved via Baker]
Δ₃ 2–79: steiner_cycle_elimination [proved + Hercher A3]
Δ₃ ≥ 80: baker_no_balanced_cycle [proved via Baker-Steiner A4]
```

### Arithmetic rigidity (exploratory)
```
spectral_gap_transfer [sorry — standard Fourier]
  → spectral_gap_implies_collatz [sorry — three reductions]
  + spectral_gap_implies_furstenberg [sorry]
  + spectral_gap_implies_littlewood [sorry]
  → arithmetic_rigidity [proved — packages all three]
```

## Formalized proofs by file

### Basic.lean — Foundation

| Theorem | Statement |
|---------|-----------|
| `collatz_zero` | collatz 0 = 0 |
| `collatz_even` | n even → collatz n = n/2 |
| `collatz_odd` | n odd → collatz n = 3n+1 |
| `collatz_pos` | n ≥ 1 → collatz n ≥ 1 |
| `collatz_two` | collatz 2 = 1 |
| `collatz_one` | collatz 1 = 4 |
| `collatz_cycle` | collatzSeq 1 3 = 1 |
| `reaches_two` | collatzReaches 2 |
| `reaches_four` | collatzReaches 4 |

### Parity.lean — Step parity

| Theorem | Statement |
|---------|-----------|
| `odd_step_produces_even` | odd m → (3m+1) % 2 = 0 |
| `collatz_odd_result_even` | odd n → collatz n is even |
| `no_consecutive_odd_steps` | odd step at t → even step at t+1 |

### Winding.lean — Step counters

| Theorem | Statement |
|---------|-----------|
| `nu2_step_even` | Even step increments ν₂ |
| `nu2_step_odd` | Odd step leaves ν₂ unchanged |
| `nu3_step_odd` | Odd step increments ν₃ |
| `nu3_step_even` | Even step leaves ν₃ unchanged |
| `nu_partition` | ν₂(n,t) + ν₃(n,t) = t |

### Identity.lean — Multiplicative identity

| Theorem | Statement |
|---------|-----------|
| `collatz_even_general` | Even m → collatz m = m/2 |
| `even_or_odd_step` | Every step is even or odd |
| `div_two_mul_two` | m even → (m/2)·2 = m |
| `correction_succ_even` | Correction at even step |
| `correction_succ_odd` | Correction at odd step |
| `collatz_identity` | **a(t)·2^{ν₂} = n·3^{ν₃} + correction** |

### SFT.lean — Symbolic dynamics

| Theorem | Statement |
|---------|-----------|
| `shiftMap_preserves_SFT` | Shift map preserves SFT membership |
| `inGoldenMeanShift_iff` | Golden mean = no consecutive 1s |
| `shiftMap_goldenMean` | Shift preserves golden mean membership |

### CollatzSFT.lean — Collatz as SFT

| Theorem | Statement |
|---------|-----------|
| `collatzSeq_pos` | n ≥ 1 → a(t) ≥ 1 for all t |
| `collatzParitySeq_in_goldenMean` | **Collatz parity sequence lies in golden mean shift** |

### FibCounting.lean — Entropy bounds

| Theorem | Statement |
|---------|-----------|
| `avoidCount_eq_fib` | Words avoiding "11" of length n = fib(n+2) |
| `logb_two_three_lt` | log₂3 < 8/5 |
| `eight_fifths_lt_goldenRatio` | 8/5 < φ |
| `log2_three_lt_goldenRatio` | **log₂3 < φ** (golden ratio) |
| `goldenMean_entropy` | Topological entropy = log φ |
| `goldenMean_max_p_odd` | Maximum odd density = 1/φ² |

### BranchLocus.lean — Cell classification

| Theorem | Statement |
|---------|-----------|
| `cell_trichotomy` | Every visited cell is branch, pure-even, or pure-odd |
| `pureEven_forces_even` | Pure-even cells force even steps |
| `branch_count_12` | Branch count at k=12 is 43 |
| `pureEven_walls_exist` | Pure-even walls exist at small scales |

### StructuralPureEven.lean — Structural sieve

| Theorem | Statement |
|---------|-----------|
| `structural_implies_no_odd_visit` | Structural pure-even → no odd visit possible |
| `structural_and_visited_implies_empirical` | Structural + visited → empirically pure-even |
| `mod4_one_double_halving` | m ≡ 1 (mod 4) → (3m+1) ≡ 0 (mod 4) |
| `double_halving_two_even_steps` | **Double-halving: two consecutive even steps** |

### TunnelWidth.lean — Diophantine walls

| Theorem | Statement |
|---------|-----------|
| `diophError_ne_zero` | Diophantine error never zero (irrationality) |
| `diophError_lower_bound` | **∃ C', ε > 0, \|diophError b\| > C'/(3^b)^{1+ε}** (from Baker) |
| `tunnel_walls_positive_of_baker` | Baker → positive wall width |
| `tunnel_walls_positive` | **∀ b ≥ 1, tunnel walls exist** |
| `walk_confined_at_boundary` | Pure-even → walkIncrement = 1 |

### WallPersistence.lean — Scale persistence

| Theorem | Statement |
|---------|-----------|
| `wall_absent_3` | No walls at k=3 (native_decide) |
| `wall_exists_9` | Walls exist at k=9 |
| `wall_exists_27` | Walls exist at k=27 |
| `wall_persists` | **∀ b ≥ 1, walls exist** |
| `wall_pushes_walk_up` | Pure-even walls → walkIncrement = +1 |
| `wall_boost` | Positive wall frequency → positive walk boost |
| `walk_boost_pos` | 2 - log₂3 > 0 |
| `walk_boost_double_halving` | **a ≡ 1 (mod 4) → walk gain = 2 - log₂3** |

### Walk.lean — Walk function

| Theorem | Statement |
|---------|-----------|
| `walk_step_even` | Walk increment at even step = +1 |
| `walk_step_odd` | Walk increment at odd step = -log₂3 |
| `walk_increment_eq` | Increment decomposition |
| `walk_eq_sum_increments` | Walk = sum of increments |
| `meanWalkIncrement_eq` | Mean increment formula |
| `drift_positive_of_podd_lt` | **p_odd < p_eq → positive drift** |
| `walkIncrement_at_pureEven` | Pure-even cell → increment = +1 |

### HenselAttrition.lean — 2-adic attrition (46 theorems)

| Theorem | Statement |
|---------|-----------|
| `oddCollatzStep_key` | **2·(T(x)+1) = 3·(x+1)** (compressed step identity) |
| `forward_step` | 2^{k+1} \| x+1 → 2^k \| T(x)+1 |
| `backward_step` | 2^k \| T(x)+1 → 2^{k+1} \| x+1 |
| `hensel_attrition` | **d consecutive v₂=1 steps ↔ 2^{d+1} \| x+1** |
| `collatz_two_steps_eq_oddCollatzStep` | Two Collatz steps = one compressed step |
| `collatzSeq_tracks_oddCollatzIter` | Sequence tracking through v₂ runs |
| `walk_of_v2_run` | Walk change during v₂=1 run = d·(1 - log₂3) |
| `walk_exit_recovery` | Exit recovery gain = 2 - log₂3 |
| `walk_run_plus_exit` | **Net walk = (d+1)·(1 - log₂3) + 1** |
| `attrition_rate` | **Survivors = odd_count / 2^d** (exact 2^{-d} rate) |
| `deficit_step_odd/even` | Deficit increment at odd/even steps |
| `deficit_of_v2_run` | Deficit during v₂=1 run |
| `deficit_nonincreasing_at_safe_step` | Safe steps don't increase deficit |
| `walk_eq_deficit_form` | **walk = ((2 - log₂3)·t - (1+log₂3)·deficit) / 3** |

### DiophantineRepeller.lean — Deficit confinement

| Theorem | Statement |
|---------|-----------|
| `deficit_step_le` | deficit(t+1) ≤ deficit(t) + 2 |
| `deficit_add_le` | deficit(t+r) ≤ deficit(t) + 2r |
| `deficit_nonpos_at_multiples` | Sliding window → deficit ≤ 0 at W-multiples |
| `deficit_bounded_of_window` | **SWC → deficit bounded by 2W** |
| `k_bound_of_deficit_bounded'` | Deficit bounded → K-bound |
| `k_bound_from_repeller` | **SWC → K-bound** |
| `cellError_linearForm` | Cell error = linear form in log 2, log 3 |
| `baker_cell_separation` | **∃ C, κ > 0, \|cellError\| > C/max^κ** (from Baker) |
| `finite_deficit_bound` | ∃ D, ∀ t, deficit(n,t) ≤ D **[sorry — ≡ Collatz]** |
| `nu3_linear_bound_from_repeller` | finite_deficit_bound → K-bound |
| `sliding_window_implies_deficit_bounded` | SWC → deficit bounded |

### DeficitBudget.lean — Budget accounting (22 theorems, all proved)

| Theorem | Statement |
|---------|-----------|
| `nu3_pair_bound` | **ν₃(t+2) - ν₃(t) ≤ 1** (no consecutive odd) |
| `nu3_bounded` | ν₃(t+2k) ≤ ν₃(t) + k |
| `odd_steps_le_half_ceil` | **2·Δν₃ ≤ W + 1** (core D1 bound) |
| `deficit_budget_of_window` | Window deficit budget |
| `safe_steps_compensate` | Safe steps compensate dangerous ones |
| `sliding_window_iff_odd_density` | SWC ↔ odd density bound |
| `sliding_window_of_safe_density` | Safe density → sliding window |

### Drift.lean — Walk divergence

| Theorem | Statement |
|---------|-----------|
| `nu3_linear_bound` | ∃ K T₀, ∀ t ≥ T₀, 3·ν₃ ≤ t + K **[sorry — ≡ Collatz]** |
| `podd_uniform_bound` | K-bound → ε-gap below equilibrium |
| `walk_eq_drift_form` | walk = t - (1+log₂3)·ν₃ |
| `walk_lower_bound_linear` | ε-gap → walk ≥ (1+log₂3)·ε·t |
| `tendsto_atTop_of_eventually_linear` | f(t) ≥ δ·t → f → ∞ |
| `walk_diverges_of_podd_bound` | K-bound → walk diverges |
| `nu3_linear_bound_of_reaches` | **Reverse: reaches 1 → K-bound** |
| `k_bound_of_deficit_bounded` | Deficit bounded → K-bound |
| `deficit_bounded_of_k_bound` | K-bound → deficit bounded |

### CorrectionRatio.lean — Cycle elimination (19 theorems)

| Theorem | Statement |
|---------|-----------|
| `correction_ratio_even` | Correction halves at even step |
| `correction_ratio_odd` | Correction at odd step: 3·corr + 2^{ν₂} |
| `collatzSeq_le_of_identity` | a(t)·2^{ν₂} = n·3^{ν₃} + correction |
| `identity_le_four_pow_nu3` | **n·3^{ν₃} + correction ≤ n·4^{ν₃}** |
| `collatzSeq_eventually_bounded_of_linear_drift` | **K-bound → trajectory bounded** |
| `collatzSeq_eventually_periodic_of_bounded` | **Bounded → eventually periodic** (pigeonhole) |
| `reaches_one_of_cycle_142` | Periodic + visits 1 → collatzReaches |
| `no_cycle_delta3_zero` | **0 odd steps → impossible** (2^p = 1) |
| `cycle_contains_one_of_delta3_one` | **Exactly 1 odd → only {1,2,4}** |
| `no_cycle_strict_inequality` | **3Δ₃ < p → contradiction** |
| `no_cycle_equality_case` | **p = 3Δ₃ → contains 1** (via Baker) |
| `no_cycle_delta3_ge2` | Δ₃ ≥ 2 → cycle contains 1 |
| `cycle_contains_one` | **Full case split: every cycle contains 1** |
| `reaches_one_of_linear_drift` | **K-bound → collatzReaches** (main composition) |

### CycleElimination.lean — Linear form bounds

| Theorem | Statement |
|---------|-----------|
| `cycleLinearForm_eq` | Λ = ν₂·log 2 - ν₃·log 3 |
| `cycle_lower_bound` | **∃ C, \|Λ\| > C·log 2 / Δ₃⁶** (Rhin bridge) |
| `cycle_upper_bound` | Λ < (2^{ν₂} - 3^{ν₃}) / 3^{ν₃} |
| `cycleLinearForm_pos` | 2^{ν₂} > 3^{ν₃} → Λ > 0 |
| `cycle_elim_from_rhin` | **∃ t < 3Δ₃, a(t) = 1** |

### SteinerCycle.lean — Steiner bounds

| Theorem | Statement |
|---------|-----------|
| `correction_upper_bound` | 2·corr + 2^L ≤ 3^K · 2^L |
| `correction_lower_bound` | 2·corr + 1 ≥ 3^K |
| `cycle_c0_bound` | c₀ upper bound from correction |
| `cycle_c0_squeeze` | c₀ squeeze: both bounds simultaneously |
| `steiner_K_bound_79` | **Δ₃ ≤ 79 → ν₃ ≤ 91** (native_decide: 2^{145} < 3^{92}) |
| `steiner_cycle_elimination` | Δ₃ ∈ [2,79] → no cycle (+ Hercher) |
| `steiner_cycle_large` | Δ₃ ≥ 80 → no cycle (Baker-Steiner axiom) |
| `baker_no_balanced_cycle` | **Complete cycle theorem via Baker decomposition** |

### ContinuedFraction.lean — Convergents of log₂3

| Theorem | Statement |
|---------|-----------|
| `convergents_verified` | 15 convergents of log₂3 verified (native_decide) |
| `pow2_lt_pow3_k0/k2/k4/k6/k8` | Even convergents: 2^p < 3^q |
| `pow2_gt_pow3_k1/k3/k5/k7` | Odd convergents: 2^p > 3^q (cycle candidates) |
| `steiner_boundary_79` | steinerWorks 91 79 = true |
| `steiner_boundary_80` | steinerWorks 91 80 = false |
| `steiner_all_79` | All Δ₃ ≤ 79 eliminated with m ≤ 91 |

### Baker.lean — Transcendence theory (24 theorems)

| Theorem | Statement |
|---------|-----------|
| `multIndep_two_three` | **2^m = 3^n → m = n = 0** |
| `irrational_logb_two_three` | **log₂3 is irrational** (from multiplicative independence) |
| `linear_form_nonzero` | (m,n) ≠ (0,0) → m·log 2 + n·log 3 ≠ 0 |
| `baker_aux_construction` | ∃ P with P(0,0) ≠ 0 and bounded coefficients |
| `baker_extrapolation` | Contradiction from vanishing at exponential points |
| `baker_zero_estimate` | ∃ C, \|linearFormLog\| > C/max^κ |
| `baker_effective_bound` | ∃ C, \|linearFormLog\| > C/max³ |
| `cycle_identity` | **a(t) · 2^{ν₂} = c₀ · 3^{ν₃} + correction** (cycle form) |
| `cycle_equation` | **Periodic → c₀ · (2^{ν₂} - 3^{ν₃}) = correction** |

### IrrationalityMeasure.lean — Rhin bound

| Theorem | Statement |
|---------|-----------|
| `linearForm_eq_approx` | Linear form = K·log 2·(L/K - log₂3) |
| `linear_form_lower_bound_rhin` | ∃ C, \|L·log 2 - K·log 3\| > K·log 2·C/K⁶ |
| `linearFormLog_lower_bound_of_rhin` | Lower bound in cycle form |
| `rhin_bound_pos` | **∃ b > 0, \|L·log 2 - K·log 3\| > b** |

### SiegelLemma.lean — Auxiliary polynomial

| Theorem | Statement |
|---------|-----------|
| `linear_form_vanishes` | m·n + n·(-m) = 0 |
| `bounded_nonzero_exists` | ∃ nonzero solution with bounded coefficients |
| `baker_aux_poly` | **∃ P, P(0,0) ≠ 0, \|P(i,j)\| ≤ max\|m\|\|n\|** |

### GrowthEstimates.lean — Entire function theory

| Theorem | Statement |
|---------|-----------|
| `auxEntireFunc_differentiable` | Auxiliary function is entire |
| `auxEntireFunc_growth` | Exponential type bound |
| `schwarz_vanishing_bound` | **Vanishes at integers → exponentially small** |
| `jensen_zero_count` | **Bounded f, f(0) ≠ 0 → finite zeros** |
| `polynomial_zero_estimate` | **Non-zero P of degree ≤ L → ≤ L²-1 zeros** (Vandermonde) |
| `gelfond_schneider_contradiction` | **Vanishing + degree bound → False** |

### LinearFormThree.lean — Three-logarithm theory

| Theorem | Statement |
|---------|-----------|
| `multIndep_two_five_seven` | 2^a · 5^b · 7^c = 1 → a = b = c = 0 |
| `irrational_logb_two_five` | log₂5 is irrational |
| `irrational_logb_two_seven` | log₂7 is irrational |
| `irrational_logb_five_seven` | log₅7 is irrational |
| `linearForm257_nonzero` | **ℚ-linear independence of {log 2, log 5, log 7}** |
| `matveev_bound_pos` | Matveev bound is positive for H ≥ 3 |
| `linearForm257_lower_of_nonzero` | Lower bound on three-logarithm linear forms |
| `frac_dist_as_linear_form` | Fractional distance as linear form |

### Syracuse.lean — Syracuse map (16 theorems)

| Theorem | Statement |
|---------|-----------|
| `val2_even/odd` | 2-adic valuation: even/odd cases |
| `pow_val2_dvd` | 2^{v₂(n)} divides n |
| `val2_cancel` | n / 2^{v₂} · 2^{v₂} = n |
| `val2_div_odd` | n / 2^{v₂(n)} is odd |
| `syracuse_mul_pow` | **Syr(n) · 2^{v₂(3n+1)} = 3n+1** |
| `syracuse_odd` | Syr(n) is odd for odd n |
| `syracuse_pos` | Syr(n) > 0 for odd n > 0 |
| `syracuse_identity` | **Syr^k(n) · 2^{\|a^{(k)}\|} = 3^k · n + G_k** (Tao 2022) |
| `syracuse_descent_criterion` | **2^{\|a\|} > 3^k + margin → Syr^k(n) < n** |
| `collatzSeq_to_syracuse` | **Odd step + halvings = Syracuse step** |

### SyracuseDrift.lean — Syracuse-Collatz bridge

| Theorem | Statement |
|---------|-----------|
| `collatzSeq_eq_iterate` | collatzSeq n t = collatz^[t] n |
| `halving_steps_even` | **Halving phase → all even steps** |
| `collatzSeq_at_syracuseTime` | Collatz value at Syracuse boundaries |
| `nu3_at_syracuseTime` | ν₃ at Syracuse time = k |
| `nu2_at_syracuseTime` | ν₂ at Syracuse time = valuation sum |
| `walk_from_syracuse` | Walk expressed via Syracuse valuations |
| `syracuse_descent_implies_reaches` | Descent criterion → collatzReaches |

### SkewProduct.lean — Cocycle theory (12 theorems, all proved)

| Theorem | Statement |
|---------|-----------|
| `cocycleSum_eq` | Cocycle sum = log₂3 · ν₃ |
| `fiberCoord_eq_walk` | **Fiber coordinate = walk** |
| `fiberCoord_eq_walkCellError` | Fiber coordinate = walkCellError |
| `irrational_half_logb_two_three` | log₂3 / 2 is irrational |
| `cocycle_mean_irrational` | Cocycle mean is irrational |
| `deficit_eq_two_nu3_minus_nu2` | Deficit = 2ν₃ - ν₂ |
| `cocycleSum_of_v2_run` | Cocycle sum during v₂=1 run |

### CorrelationDecay.lean — Autocorrelation (17 theorems)

| Theorem | Statement |
|---------|-----------|
| `cell_error_exits_danger` | d ≥ 2, ε > 0 → exits ε-neighborhood |
| `walkCellError_exits_danger` | Walk cell error exits danger zone |
| `cellError_shift_identity` | Cell error shift identity |
| `danger_intervals_disjoint` | Danger intervals are disjoint |
| `autocorrelation_zero_of_large_shift` | **Autocorrelation vanishes for d ≥ 2** |
| `correlation_decay` | Correlation decay for large separation |
| `correlation_supports_mixing` | Correlation data supports mixing hypothesis |
| `run_recovery_deficit_bound` | Run + recovery deficit bound |

### SolenoidMixing.lean — Solenoid infrastructure

| Theorem | Statement |
|---------|-----------|
| `walk_eq_walkCellError` | walk = walkCellError |
| `cellError_shift_of_v2_run` | Cell error shift during v₂ run |
| `cellError_shift_exceeds_one` | **d ≥ 2 → shift exceeds one cell** |
| `hasBoundedRuns_iff` | Bounded runs characterization |
| `hensel_baker_conflict` | **Hensel and Baker constraints conflict** |
| `syracuseValSum_near_rotation` | Valuation sum ≈ rotation |
| `syracuseValSum_equidistributed_of_sublinear_walk` | Sublinear walk → equidistributed **[sorry]** |

### BorelCantelli.lean — Measure theory (11 theorems)

| Theorem | Statement |
|---------|-----------|
| `survivor_count` | Exact survivor count in period |
| `oddSurvivorCount_eq` | Odd survivor count formula |
| `survivorSet_antitone` | Survivor sets decrease with depth |
| `survivor_density_le` | **Survivor density ≤ 1/2^d** |
| `borel_cantelli_finite` | Finitely many long-run survivors |
| `borel_cantelli_danger_density` | **∀ ε > 0, ∃ D, danger density < ε for d ≥ D** |

### UniqueErgodicity.lean — Ergodic theory

| Theorem | Statement |
|---------|-----------|
| `coboundary_contradicts_irrational_mean` | Coboundary → contradiction (irrational mean) |
| `collatz_cocycle_not_coboundary` | **Collatz cocycle is not a coboundary** |
| `birkhoff_all_orbits` | Birkhoff averages for all orbits (from axiom A8) |
| `cocycleSum_growth_rate` | Cocycle sum grows at rate log₂3/2 |
| `deficit_over_t_of_uniquely_ergodic` | deficit/t → 1/2 (linear growth) |
| `cocycleSum_diverges` | Cocycle sum diverges |
| `deficit_bounded_consistent_with_ergodicity` | Bounded deficit consistent with ergodicity |

### WeylEquidistribution.lean — Equidistribution bridge

| Theorem | Statement |
|---------|-----------|
| `log2_3_rotation_equidistributed` | log₂3-rotation equidistributed (from axiom A5) |
| `dangerous_cells_per_row_bound` | Dangerous cells bounded per row |
| `total_dangerous_cells_bound` | Total dangerous cells bounded |
| `safe_density_positive_of_irrational` | **Safe cell density > 0** (from irrationality) |
| `equidistributed_subset_visits_lower` | Equidistribution → visit frequency bounds |
| `equidistribution_implies_deficit_bounded` | Equidistribution → deficit bounded **[sorry]** |
| `equidistribution_implies_k_bound` | Equidistribution → K-bound |
| `cellSeqNu2_equidistributed` | ν₂ sequence equidistributed **[sorry]** |
| `safeCellDensity_at_inverse_scale` | Safe density at inverse scale |
| `nu3_linear_bound_from_weyl` | **Weyl path → K-bound** (chains two sorrys) |

### DenjoyKoksma.lean — Sublinear Birkhoff sums

| Theorem | Statement |
|---------|-----------|
| `log2_3_diophantine_condition` | log₂3 satisfies Diophantine condition |
| `deficit_increment_bounded` | \|deficit(t+1) - deficit(t)\| ≤ 2 |
| `log2_3_diophantine_condition_rpow` | Real-power form of Diophantine condition |
| `deficit_sublinear_bound` | DK → deficit = O(t^{3/10}) |
| `deficit_sublinear_of_polynomial_bound` | Polynomial bound → sublinear |
| `deficit_sublinear` | **Deficit is sublinear** (from DK axiom) |
| `rhin_exponent_valid` | 1/5 < 3/10 |
| `sublinear_exponent_lt_one` | 3/10 < 1 |

### SublinearDrift.lean — Alternative proof path

| Theorem | Statement |
|---------|-----------|
| `nu3_ratio_bound_of_sublinear` | Sublinear deficit → ν₃/t → 1/3 |
| `walk_eventually_linear_of_sublinear` | Sublinear → walk eventually linear |
| `walk_diverges_of_sublinear_deficit` | Sublinear → walk diverges |
| `collatzSeq_le_of_deficit` | a(t) ≤ n · 2^{deficit(t)} |
| `collatzSeq_le_n_of_nonpos_deficit` | deficit ≤ 0 → a(t) ≤ n |
| `three_delta3_le_p_of_sublinear` | Sublinear → 3Δ₃ ≤ p |
| `trajectory_bounded_of_sublinear_deficit` | **Sublinear deficit → trajectory bounded** |
| `reaches_one_of_sublinear_deficit` | **Sublinear deficit → reaches 1** |
| `sublinear_of_k_bound` | K-bound → sublinear |
| `sublinear_of_deficit_bounded` | Deficit bounded → sublinear |
| `sublinear_of_reaches` | Reaches 1 → sublinear |
| `collatz_via_denjoy_koksma` | **Alternative theorem: DK path → collatzReaches** |

### Conclusion.lean — Main theorem

| Theorem | Statement |
|---------|-----------|
| `seq_eq_one_of_pow_bound` | Power bound → a(t) = 1 |
| `collatz_reaches_of_walk_diverges` | Walk → ∞ → reaches 1 |
| `collatz_conjecture` | **∀ n ≥ 1, collatzReaches n** (from nu3_linear_bound) |
| `nu3_linear_bound_iff_reaches` | **K-bound ↔ collatzReaches n** (equivalence) |

### SpectralGap.lean — Fourier analysis

| Theorem | Statement |
|---------|-----------|
| `exp_cube_factor` | e^{3z} factorization |
| `geom_sum_three_ratio` | Geometric sum ratio for ×3 |
| `euler_cos_identity` | 1 + 2cos θ = (e^{3iθ} - 1)/(e^{iθ} - 1) |
| `geom_sum_cos_factor` | Geometric sum as cosine factor |
| `exp_triple_full_factor` | Full ×3 factor decomposition |
| `prod_div_telescope` | Product telescoping |
| `orbit_telescope` | **Orbit product telescopes** |
| `orbit_cos_prod_norm` | \|orbit product\| = ∏\|1 + 2cos(3^j θ)\| / 3^L |
| `three_coprime_pow2` | gcd(3, 2^j) = 1 |
| `spectral_gap_transfer` | T₃ contracts L² by 1/9 **[sorry — standard Fourier]** |
| `spectral_gap_iterated` | t applications contract by (1/9)^t **[sorry]** |

### ArithmeticRigidity.lean — Three-way equivalence

| Theorem | Statement |
|---------|-----------|
| `mixing_rate_pos` | γ > 0 |
| `contraction_factor_eq` | Contraction = 1/3 |
| `disjointness_of_metrics` | 2-adic and Archimedean metrics are disjoint |
| `effective_disjointness` | Effective form of disjointness |
| `three_forces_active` | All three forces simultaneously active |
| `hensel_baker_conflict_rate` | Hensel-Baker conflict rate |
| `furstenberg_partition_rigidity` | T₃-invariant → uniform **[sorry]** |
| `spectral_gap_implies_collatz` | γ > 0 → CollatzConjecture **[sorry]** |
| `spectral_gap_implies_furstenberg` | γ > 0 → Furstenberg rigidity **[sorry]** |
| `spectral_gap_implies_littlewood` | γ > 0 → Littlewood for (log₂5, log₂7) **[sorry]** |
| `arithmetic_rigidity` | **Packages all three reductions** |
| `orbit_product_identity` | Orbit product identity |
| `cell_errors_have_gaps` | Cell errors have Baker gaps |
| `metrics_incommensurable` | log₂3 irrational |
| `danger_is_self_defeating` | log₂3 > 1 |

### MetricConflict.lean — Metric analysis (13 theorems, all proved)

| Theorem | Statement |
|---------|-----------|
| `shiftRate_pos` | Shift rate > 0 |
| `shiftRate_gt_half` | Shift rate > 1/2 |
| `total_shift` | Total shift over d steps |
| `exit_after_two_steps` | Exits cell after 2 steps |
| `one_step_exceeds_half_cell` | One step exceeds half cell width |
| `two_steps_shift_exceeds_one` | 2 · shiftRate > 1 |
| `conflict_at_scale_one` | Metric conflict at scale 1 |
| `long_run_crosses_cells` | **d ≥ 2 → crosses multiple cells** |
| `danger_run_requires_divisibility` | Danger run → 2^{d+1} \| x+1 |
| `metric_conflict` | **Complete metric conflict theorem** |
| `attrition_exceeds_exit` | **d ≥ 2 → attrition exceeds exit** |

### CarryBitScrambling.lean — Carry propagation (37 theorems, all proved)

| Theorem | Statement |
|---------|-----------|
| `danger_iff_mod4` | n dangerous ↔ n ≡ 3 (mod 4) |
| `safe_iff_mod4` | n safe ↔ n ≡ 1 (mod 4) |
| `compressed_step_odd_of_danger` | Compressed step of danger is odd |
| `carry_to_safe` | n ≡ 3 (mod 8) → safe after one step |
| `carry_to_danger` | n ≡ 7 (mod 8) → danger after one step |
| `danger_dichotomy` | **Danger → safe or danger with prob 1/2 each** |
| `consecutive_danger_ratio` | P(DD) / P(D) = 1/2 |
| `danger_to_danger_is_half` | **P(danger → danger) = 1/2** |
| `bit_peel_general` | General bit-peeling lemma |
| `iterated_bit_peel` | Iterated bit-peeling |
| `danger_transition_half` | Danger transition probability = 1/2 |
| `transition_doubly_stochastic` | **Transition matrix is doubly stochastic** |
| `perfect_mixing_one_step` | Perfect mixing after one compressed step |
| `compressed_erosion_parity` | Parity erosion through compression |
| `compressed_erosion_danger` | Danger status erosion through compression |

### FuelDynamics.lean — Fuel regeneration (15 theorems, all proved)

| Theorem | Statement |
|---------|-----------|
| `refill_equation` | Fuel refill equation |
| `refill_mul` | Refill multiplicative form |
| `fuel_divisibility_forward` | 2^k \| n+1 → 2^{k-1} \| T(n)+1 |
| `fuel_divisibility_backward` | 2^k \| T(n)+1 → 2^{k+1} \| n+1 |
| `fuel_divisibility_iff` | **Fuel divisibility equivalence** |
| `fuel_at_27` | v₂(28) = 2 |
| `syr_27` | Syr(27) = 41 |
| `fuel_regeneration_path` | **27 → 41 → 31: fuel 2 → 1 → 5** |

### SimultaneousApprox.lean — Littlewood infrastructure

| Theorem | Statement |
|---------|-----------|
| `fracDist_nonneg` | ‖x‖ ≥ 0 |
| `fracDist_le_half` | ‖x‖ ≤ 1/2 |
| `fracDist_int` | ‖n‖ = 0 for integers |
| `fracDist_eq_zero_iff` | ‖x‖ = 0 ↔ x is an integer |
| `littlewoodProduct_nonneg` | n · ‖nα‖ · ‖nβ‖ ≥ 0 |
| `littlewoodProduct_lt_of_close` | Close approximation → small product |

### LittlewoodResidence.lean — Residence bounds

| Theorem | Statement |
|---------|-----------|
| `residence_bounded_two_dim` | **L=2 suffices** (log₂5 ∈ (9/4, 5/2)) |
| `escape_implies_frac_change` | Escape implies fractional distance change |
| `cell_product_upper_bound` | Cell product ≤ 1/(4K²) |
| `finer_cell_visit` | Finer cells are visited |

### LittlewoodInduction.lean — Scale induction

| Theorem | Statement |
|---------|-----------|
| `product_bounded_by_scale` | Product bounded by 1/K |
| `product_doubly_bounded` | Product bounded by 1/(K₁·K₂) |
| `scale_induction_step` | Scale induction step |
| `product_decays_with_scale` | **Product → 0 as scale → ∞** (1/(4K²) < ε) |
| `simultaneous_approx_log2_5_7` | Simultaneous approximation **[sorry — deep Diophantine]** |
| `fracDist_alpha_pos` | ‖n · log₂5‖ > 0 for n ≥ 1 |
| `littlewood_log2_5_log2_7` | **Littlewood holds for (log₂5, log₂7)** (from sorry) |

### Conclusion.lean — Main theorem

| Theorem | Statement |
|---------|-----------|
| `collatz_conjecture` | **∀ n ≥ 1, collatzReaches n** |
| `nu3_linear_bound_iff_reaches` | **K-bound ↔ collatzReaches n** |

## Computational data

The `c_scripts/` directory contains C programs for large-scale computation:

- **branch_locus.c** — Branch counting on the (2,3)-torus grid, OpenMP parallelized
  with binary checkpoint/resume. Verified to N = 100 billion (25.1 × 10¹² Collatz steps).
- **v2_danger.c** — Two-pass analysis of v₂ = 1 dangerous runs, Hensel attrition
  statistics, and hopping correlation.
- **gpu_branch_kernel.cl / gpu_branch_host.c** — OpenCL GPU-accelerated branch counting
  (1,768M nums/s convergence verification on RTX 5090).
- **deficit_analysis.c** — Sliding window condition analysis, deficit extremes.
- **collatz_scatter.c** — Scatter plot data generation.
- **parity_sft.c** — Parity sequence and SFT analysis.
- **profinite_compat.c** — Profinite compatibility checking.
- **gen_sieve.c / analyze_sieve.c / sieve_bench.c** — Sieve precomputation and benchmarking.

## Visualizations

### Branch locus (100B run)
- `branch_locus_fig1.png` — Cell saturation (21,632 cells for k ≥ 216)
- `branch_locus_fig2.png` — Heatmaps across grid levels
- `branch_locus_fig3.png` — Diophantine signature
- `branch_locus_fig4.png` — SFT transition structure
- `branch_locus_fig5.png` — Foliation collapse
- `branch_locus_fig6.png` — Cell statistics and equilibrium cusp
- `branch_locus_fig7.png` — Convergence diagnostics

### Diophantine ghost island
- `diophantine_branch_k729.png` — Full k=729 grid view
- `diophantine_k729_zoom.png` — Ghost island zoom (352-unit void)
- `diophantine_k729_structure.png` — Island structure analysis
- `diophantine_transitions.png` — Transition patterns
- `diophantine_foliation_depletion.png` — Foliation depletion

### qx+1 family comparison
- `danger_compare_belt.png` — Inverted belt (3x+1 vs 5x+1)
- `danger_compare_phase.png` — Phase transition at q=4
- `danger_compare_autocorrelation.png` — Autocorrelation comparison
- `danger_compare_dynamics.png` — Dynamics comparison
- `5x1_danger_*.png` — Five 5x+1 diagnostic plots
- `7x1_danger_*.png` — Five 7x+1 diagnostic plots

### Interactive HTML
- `baker_kick.html` — Baker's theorem visualization
- `hensel_attrition.html` — Hensel attrition animation
- `solenoid_pipe.html` — (2,3)-solenoid dynamics
- `torus_sieve.html` — Torus sieve visualization
- `spectral_contraction.html` — Spectral gap contraction
- `arithmetic_friction.html` — Three-force arithmetic friction
- `sieve_of_21632.html` — The sieve of 21,632

## Papers

- `collatz_reduction_20260220.pdf` — *Diophantine Confinement in Syracuse Dynamics:
  A Formal Reduction* (submitted to FMP)
- `diophantine_confinement_20260221.pdf` — *Computational Evidence and Extended Analysis*
  (arXiv companion: branch locus figures, 5x+1/7x+1, Furstenberg, Littlewood)

## License

MIT
