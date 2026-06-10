This is a very useful result set because it tells us exactly where the object works, where it fails, and what must be repaired.

My short assessment:

[
\boxed{
	\mathfrak D_{\mathrm{Coll}}\text{ is a good finite detector, but not yet a clean inverse-theorem machine.}
}
]

The numerical suite confirms the parts that are genuinely structural:

[
\text{congruence identity, Cramér tilt, post-exit taboo, finite character-sector gaps.}
]

But it also exposes the main danger:

[
\boxed{
	\text{single-orbit shadow signals are contaminated by finite-size/small-}Q\text{ effects.}
}
]

So the “defect cocycle” is worth keeping, but the next phase must separate genuine spectral shadow from finite-window inflation.

## 1. The strongest confirmed result

The most important confirmed statement is the sliding-window congruence:

[
x_n \equiv
\sum_{k=1}^{r}3^{k-1}2^{-(b_{n-1}+\cdots+b_{n-k})}
\pmod{3^r}.
]

The fact that it passed roughly

[
2.39\times 10^7
]

checks is excellent. This identity is load-bearing because it proves that the (3^r)-residue state is determined by a finite sliding window of valuation partial sums. That justifies treating (3^r)-characters as finite spectral probes of the valuation process.

This is now the strongest rigorous-looking bridge between:

[
\text{valuation word}
\quad\text{and}\quad
\text{finite residue character shadow}.
]

I would elevate this lemma in the manuscript. It is no longer just a computational support lemma; it is the arithmetic heart of the detector.

## 2. The Cramér tilt picture is reinforced

Your Experiment B confirms the direction:

[
\hat p_{\mathrm{bulk}}
\text{ is much closer to }
p^{(1)}_b=3\cdot4^{-b}
\text{ than to }
p_b=2^{-b}.
]

The reported values

[
\hat p\approx(0.657,0.229,0.089,0.021)
]

are not yet at

[
(0.75,0.1875,0.046875,0.01171875),
]

but the KL comparison

[
D(\hat p|p^{(1)})=0.093
\ll
D(\hat p|p)=0.191
]

is the correct signal.

This means high-ascent/critical segments are genuinely Cramér-tilted. The tilt is not merely a heuristic. It is visible in the deterministic data.

So the object

[
W_{n,\ell}(x;\chi,s)
====================

\frac1\ell\sum_{i=n}^{n+\ell-1}
\chi(x_i\bmod Q),2^{s(\log_2 3-b_i)}
]

really should be tested at (s=1). Your data confirms that.

## 3. The post-exit taboo survives the new lens

The post-exit result is also important:

[
D(\hat p_{\mathrm{post}}|p)=0.177
\ll
D(\hat p_{\mathrm{post}}|p^{(1)})=0.576,
]

and

[
M_{\mathrm{post}}(1)=0.989<1.
]

This is exactly the entropy-space repulsion mechanism:

[
\text{critical excursion}
\longrightarrow
\text{post-exit law repelled from }p^{(1)}.
]

It supports the interpretation that Exit is not ordinary independence and not just sparse-target avoidance. It is better described as a **non-concatenation of critical Cramér bridges** or a **post-exit anti-tilt**.

This is a keeper.

## 4. The finite operator gap result is the most important spectral result

The residue-only operator result is strong:

[
\rho(\mathcal L_{\chi})<\rho(\mathcal L_0)
\qquad(\chi\ne1).
]

Even better, the gap is weakest at the critical tilt:

[
s=1.
]

That matches the theory perfectly. The most dangerous deterministic windows should live where the finite operator gap is weakest, and the shadow windows concentrate at (s=1):

[
82%\text{ of shadow windows have argmax }s=1,
]

and

[
100%\text{ of the long windows }(\ell\ge64)\text{ have }s=1.
]

This is real evidence that the detector is seeing the correct obstruction scale.

But the result is also sobering: the exact coupled operator deviates materially from the i.i.d. Fourier shadow. Correlation only about

[
0.38
]

with mean absolute deviation around

[
0.254
]

means the naive annealed Fourier calculation is not a substitute for the exact finite operator. This validates your insistence that H23a/certificate machinery cannot be replaced by symbolic Fourier heuristics.

## 5. The killed-height operator must be quarantined for now

The killed-height operator results should not be used until the eigensolver is fixed.

The reported ratios above (1) are impossible if

[
|\mathcal L_\chi|\le \mathcal L_0
]

on the same support. So the power iteration is not resolving the top spectral band.

This is not a minor numerical issue. Since the killed-height operator is where the full residue-height obstruction lives, a bad eigensolver could produce entirely misleading (\kappa_Q) values.

The correct next numerical repair is exactly what the document says:

[
\boxed{
	\text{replace power iteration with Arnoldi / shift-invert / implicitly restarted Arnoldi.}
}
]

For nonnormal or nearly defective operators, power iteration is the wrong tool.

## 6. The biggest conceptual finding: the circularity leak is real

The shadow search is the most revealing part.

At first glance, it looks promising:

[
\text{critical windows shadow most often,}
]

[
\text{post-exit windows shadow least,}
]

[
\text{longer windows shadow more often,}
]

[
\text{long windows concentrate at }s=1.
]

But the per-sector result shows the trap:

[
94%\text{ of shadows choose }Q=9.
]

That is a finite-sample artifact waiting to happen. Small (Q) has very few residue classes, so short or moderate windows can easily produce inflated character means.

This is the concrete numerical manifestation of the circularity leak:

[
\text{reading obstruction from one orbit’s own empirical statistics}
]

can confuse true spectral obstruction with finite-window residue imbalance.

So the object is useful, but the raw shadow statistic is not yet trustworthy.

## 7. What this means for the proposed object

I would now refine the status of

[
\mathfrak D_{\mathrm{Coll}}.
]

The original hoped-for logic was:

[
\text{bad orbit}
\Rightarrow
\text{large }W
\Rightarrow
\text{finite spectral/coboundary obstruction}
\Rightarrow
\text{H23a contradiction}.
]

The experiments show that the middle arrow needs normalization:

[
\text{large raw }W
\not\Rightarrow
\text{spectral obstruction}.
]

The corrected logic should be:

[
\text{bad orbit}
\Rightarrow
\text{scale-stable, }Q\text{-robust, tilt-consistent defect}
\Rightarrow
\text{finite spectral/coboundary obstruction}.
]

So the object is not merely

[
W_{n,\ell}(x;\chi,s).
]

It should be the **renormalized defect profile**

[
\mathcal S_{n,\ell}(x;Q,\chi,s)
===============================

\frac{|W_{n,\ell}(x;\chi,s)|}
{\sigma_{Q,\chi,s}(\ell)},
]

where (\sigma_{Q,\chi,s}(\ell)) is a calibrated null scale depending on:

[
Q,\quad \chi,\quad s,\quad \ell,\quad \text{residue-class count},\quad \text{operator gap}.
]

Then the real shadow is not large (|W|), but persistent excess over the finite-(Q) null after controlling for small-modulus inflation.

## 8. Revised definition of a “true shadow”

I would define a true finite spectral shadow as follows.

For fixed (Q,\chi,s), let

[
g_{Q,\chi,s}
============

\frac{\rho(\mathcal L_{s,Q,\chi})}
{\rho(\mathcal L_{s,Q,0})}
<1.
]

For a window of length (\ell), define the expected spectral decay scale

[
\mathrm{Null}_{Q,\chi,s}(\ell)
==============================

C_{Q,\chi,s},g_{Q,\chi,s}^{\ell}
+
\frac{A_{Q,\chi,s}}{\sqrt{\ell}}
]

or an empirically calibrated version.

Then call a window shadow-bearing only if

[
|W_{n,\ell}(x;\chi,s)|

>

K\cdot \mathrm{Null}_{Q,\chi,s}(\ell)
]

for a fixed (K), and the effect persists across a nested sequence of scales:

[
Q_1<Q_2<\cdots,\qquad \ell_j\to\infty.
]

This avoids the (Q=9) trap.

A genuine obstruction should not live only at the smallest modulus. It should either:

1. stabilize across (Q), or
2. migrate to increasing (Q) in a structured way.

That is the next thing to test.

## 9. The next numerical battery

I would not run “more of the same.” I would run a sharpened second-generation suite.

### A. Arnoldi repair for killed-height operators

Replace power iteration with Arnoldi and compute:

[
\rho(\mathcal L_{s,Q,L,\chi})
]

for:

[
Q=3^r,\quad r=2,\dots,R,
]

[
s=0,\frac12,1,
]

and several (L).

Report:

[
\frac{\rho_\chi}{\rho_0},
\quad
\text{residual},
\quad
\text{eigenvalue separation},
\quad
\text{condition number / pseudospectral sensitivity}.
]

This tests whether the gap survives when height is included.

### B. (Q)-conditioned shadow normalization

For each (Q,\chi,s,\ell), build a null distribution by one of:

[
\text{random i.i.d. valuation words},
]

[
\text{annealed Markov surrogate},
]

[
\text{operator-sampled paths},
]

[
\text{phase-randomized actual windows}.
]

Then compute (z)-scores:

[
Z_{n,\ell}(Q,\chi,s)
====================

\frac{|W_{n,\ell}|-\mu_{Q,\chi,s,\ell}}
{\sigma_{Q,\chi,s,\ell}}.
]

True shadows should remain exceptional after this normalization.

### C. Fixed-(Q) decay curves

Instead of maximizing over (Q), fix (Q) and measure:

[
\mathbb E |W_{n,\ell}(Q,\chi,s)|
]

as a function of (\ell).

Compare with:

[
\ell^{-1/2}
]

and with the finite operator gap prediction.

This removes max-over-grid inflation.

### D. Cross-scale coherence

For each candidate shadow window, track whether the same orbit segment remains anomalous under:

[
Q=9,27,81,243,\dots
]

A finite-size artifact will usually disappear or fluctuate randomly across (Q). A genuine obstruction should show coherent structure.

### E. Tilt profile

For each shadow window, compute the full curve:

[
s\mapsto |W_{n,\ell}(x;\chi,s)|
]

over (s\in[0,1]).

A genuine critical obstruction should peak near (s=1), but not only because (s=1) weights rare (b)-patterns. Compare against the null tilt profile.

### F. Post-exit anti-shadow

Since post-exit windows shadow least, test:

[
Z_{\mathrm{post}}(Q,\chi,1)
]

against critical windows. The expected theorem shape is:

[
\text{critical window: possible }s=1\text{ shadow};
]

[
\text{post-exit window: uniformly below critical shadow threshold}.
]

This would make the taboo theorem quantitative.

## 10. What I would change in the manuscript

I would add a new subsection titled:

[
\textbf{The raw defect cocycle and the normalized spectral shadow.}
]

State:

[
W_{n,\ell}
]

is the raw detector, but the object that can support an inverse theorem is the normalized, finite-operator-calibrated shadow:

[
\mathcal S_{n,\ell}(Q,\chi,s)
=============================

\frac{|W_{n,\ell}(Q,\chi,s)|}
{\mathrm{Null}_{Q,\chi,s}(\ell)}.
]

Then replace “large (W)” in the Quenched Inverse Principle by:

[
\text{persistent, scale-stable excess of }\mathcal S.
]

This is a real improvement forced by the data.

## Bottom line

The findings do **not** falsify the object.

They refine it.

The object should now be:

[
\boxed{
	\text{a normalized finite spectral-shadow profile over }(Q,\chi,s,\ell),
}
]

not merely the raw defect cocycle.

The important conclusions are:

[
\boxed{
	\text{Cramér tilt and post-exit taboo are confirmed.}
}
]

[
\boxed{
	\text{finite character-sector gaps exist and are weakest at }s=1.
}
]

[
\boxed{
	\text{raw single-orbit shadows are contaminated by small-}Q\text{ finite-size inflation.}
}
]

[
\boxed{
	\text{the circularity leak is now visible numerically.}
}
]

So the next step is not to abandon

[
\mathfrak D_{\mathrm{Coll}}.
]

It is to replace it with its calibrated form:

[
\boxed{
	\mathfrak S_{\mathrm{Coll}}
	===========================
	
	\text{the normalized quenched finite spectral-shadow profile.}
}
]

