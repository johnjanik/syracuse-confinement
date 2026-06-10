
shadow_frontier/ — the new project, with AIPM provenance from its first action:

- README — the mission: the surviving counterexample class (high-complexity, calibrated, phase-biased, mixed-adically coherent,
certificate-resistant), the three targets, and the final dichotomy: long banded windows ⟹ S-unit rigidity; no long banded windows ⟹ band-crossing
certificate.
- notes/PROGRAM.md — the analytic working document with precise conjecture statements for Target 1 (banded S-unit rigidity, with the ESS/subspace
route and the rank-collapse diagnostic), Target 2 (band-crossing certificate, with the quantified all-ones-exclusion route: b=1-density ½+δ over m
steps forces x ≡ −1 mod 2^{f(δ)m} against positivity), Target 3 (mixed-tower enumeration) — plus an open-questions log, including Q3, which I think
is the sharpest analytic question to start with: the entropy-vs-bias tension — the max-entropy law subject to a biased letter marginal is Markov, so
does any biased word family actually achieve the near-full complexity that repetition rigidity demands?
- search/frontier.py — the full pipeline: candidate generation (letter law on {1,2,4} solving mean = log₂3 with prescribed ord-3 bias), calibration,
factor complexity, the 2-adic realizability ghost test, mixed-tower trap extraction with Karp max-plus certificates over 2^a3^b, and the
exponent-vector rank diagnostic.

First result (pilot 001)

120/120 calibrated, biased, high-complexity candidates are 2-adic ghosts — full-bit-length least representatives, no prefix stabilization, none
positive-realizable, none even surviving to the certificate stage. The reversed search direction dc_next_steps prescribed is working exactly as
hoped: the surviving symbolic class shows the same ghost signature as the Sturmian class that's now a theorem.

Suggested opening moves for the new program

1. Q3 first (analytic, possibly provable with existing tools): compute the complexity growth of the max-entropy-given-bias Markov measures and check
whether they can meet the repetition-rigidity threshold inside banded windows — if not, the entire biased class is squeezed between rigidity and the
bias requirement.
2. The rank diagnostic on realized orbit windows (Target 1's empirical fork): high-deviation vs ordinary windows from genuine orbits.
3. The band-crossing lemma (Target 2): the quantified all-ones exclusion looks like the most provable-next-theorem in the file.

Whenever you're ready — and with a critique series for this one, history suggests it'll go somewhere worth going.


Starting from a conjectural defect cocycle, it built and validated a nine-experiment suite; classified the coboundaries exactly (Cob = ⟨χ₂⟩); proved
strict gaps, conductor collapse, and ejection; survived roughly ten exact marginal coincidences, each broken by a named mechanism (the pinning
constant C₀, the shell constant 3C₁, the level constant 4/7, the grading lemmas, the root-ball law); proved the uniform finite spectral gap
$\sup_c\gamma_c(0)<1$; proved the keystone arrow; absorbed cycle elimination into the shadow framework via linear forms in logarithms; and ended with
genuinely new mathematics — repetition rigidity, by which repeated valuation blocks are exact cycles, killing every Sturmian and
subexponential-complexity ghost unconditionally. What remains is stated with precision and without inflation: the quenched shadow exclusion, with its
surviving class characterized and the S-unit/subspace frontier named as the next tool.


The remaining obstruction is a **joint (2)-/(3)-adic deterministic rigidity problem**: after the finite spectral theory, keystone arrow, cycle exclusion, calibrated-measure reduction, and repetition-rigidity/Baker arguments, any counterexample must be a positive Syracuse orbit whose valuation word is mean-critical,

[
\frac1N\sum_{n<N} b_n\approx \log_2 3,
]

yet carries a persistent finite non-coboundary two-point shadow bias

[
\frac1N\sum_{n<N}\chi'(x_{n+1})\overline{\chi'(3x_n+1)}
\not\to
\mathbb E_{\rm geom}[\chi'(2)^{-b}],
]

while avoiding descent and every max-plus certificate on the mixed tower (2^a3^b). Low-complexity calibrated ghosts are now excluded: repeated length-(p) blocks inside a banded window force an actual integer cycle, and Baker/linear-forms bounds eliminate such cycles beyond the verified range. Thus the only surviving counterexample profile is a **high-complexity, randomness-mimicking, mixed-adically coherent valuation sequence**: locally diverse enough to avoid repetition rigidity, phase-biased enough to trigger the keystone shadow, calibrated enough to avoid mean-visible descent, and projectively coherent in both the (2)-adic realization tower and the (3)-adic shadow tower. Proving Collatz in this framework amounts to showing that no such object is positive-realizable: either high-complexity banded windows must satisfy an (S)-unit/subspace rigidity principle that forces repetition, periodicity, or a max-plus descent certificate, or orbits that avoid long banded windows must acquire enough (2)-adic (b=1)-bias to be forced into a ghost/certificate.


