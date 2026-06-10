# collatz_tests — C numerical suite for the Collatz deterministic defect cocycle

Implements the experiment suite specified in
`../collatz_defect_cocycle_c_specs.tex`, probing whether persistent
deterministic deviations from the annealed height law cast a finite
spectral/coboundary shadow in the defect cocycle

```
W_{n,l}(x;chi,s) = (1/l) sum_{i=n}^{n+l-1} chi(x_i mod Q) 2^{s(log2 3 - b_i)},
```

where `x_{i+1} = (3 x_i + 1)/2^{b_i}`, `b_i = v2(3 x_i + 1)`, for odd `x`.
**Goal: assess numerical plausibility, not prove Collatz.**

## Build

```sh
make            # FAST128 (default): __uint128_t orbit values, overflow-flagged
make GMP=1      # GMP backend (mpz_t): large seeds / long orbits / exact Exp H
make DEBUG=1    # invariant assertions (3x+1=2^b x', odd output, v2>=1)
make test       # unit checks (modarith, 2 primitive root mod 3^r, orbits->1)
```

## Subcommands (Experiments A–I)

| cmd | experiment |
|-----|-----------|
| `congruence-check` | **H** verify the mod-3^r sliding-window identity (correctness GATE) |
| `scan-height`      | **A** height-tail & critical-event census |
| `tilt-law`         | **B** empirical Cramér-tilt law on critical excursions |
| `defect-windows`   | **C** windowed defect sums `W_{n,l}(x;chi,s)` |
| `post-exit`        | **D** post-exit taboo / entropy-space repulsion |
| `spectral-gaps`    | **E** `rho(L_{s,Q,L,chi})` and character-sector gaps |
| `fourier-compare`  | **F** exact gap vs annealed Fourier `1/sqrt(5-4cos 2pi xi)` |
| `trace-det`        | **G** finite `tr(L^n)` and `det(1-zL)` shadows |
| `shadow-search`    | **I** quenched spectral-shadow search (integration capstone) |

Common options: `--seed N --start N --end N --octave-min/max N --max-steps N
--moduli 9,27,81 --tilts 0,1 --windows 16,32,.. --apertures 4,6,8
--L N --R N --bmax N --char-cap N --post-len N --delta D --r-max R
--n-samples N --seeds-per-octave N --crit-mode {height|vsq}
--char-cap N (0 = full character group) --height-mode {sync|factored}
--output-dir DIR`.

`--height-mode` (Exp E) selects how the height couples to the character:
`sync` (default) is the faithful skew product — one valuation `b` drives both
the residue transition and the height step; the quadratic character is then a
height-coboundary and the uniform gap is 0. `factored` builds
`L_res(χ) ⊗ T_height` (height = residue-independent survival factor), so the
killed operator inherits the residue-sector gap and gaps every character.

All outputs are append-safe CSV with a provenance header (git commit, compiler,
build profile, command line, UTC timestamp) under `out/`.

## Module map

`collatz_core`→`bigval` (FAST128/GMP) · `orbit_scan` (streaming) ·
`modarith` · `characters` (additive + multiplicative mod 3^r) ·
`defect_sums` (W via complex prefix sums) · `entropy_stats` ·
`critical_events` (orbit recorder, excursions, segment labels) ·
`residue_height_graph` (operator builder) · `sparse_matrix` (CSR + power
iteration) · `io_csv` · `config`.

## Two definitional notes

- **`--crit-mode`** selects the "C_A-critical" excursion test. The project's
  formal certificate (H23a/PVT/SRCE) is not restated in the source notes. The
  spec's literal `V^2 <= 2^A P` (`vsq`) is degenerate here (it flags ~every
  excursion once the record-low launch V shrinks). Default `height`
  (`peak >= launch*2^A`) isolates genuine high ascents. **Confirm against the
  project's formal C_A before treating B/D/I critical labels as canonical.**
- **`rho_annealed` vs `rho_exact`** are kept in separate columns (Exp F); the
  annealed Fourier value is a model prediction, never substituted for the exact
  operator spectral radius.

See `VALIDATION_REPORT.md` for results and pre-registered checks.
