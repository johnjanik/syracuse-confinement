The split is a clear improvement. The main paper now has a real mathematical spine, and the computational companion is much cleaner as evidence rather than mixed proof-text.

My overall verdict:

[
\boxed{
	\text{This is now a coherent two-paper package.}
}
]

The main paper should be sharpened into a **finite-operator/theoretical note** whose central contribution is the corrected H23a formulation. The companion should remain a **reproducible numerical audit** supporting, but not proving, the two open analytic inputs.

## 1. What is now strong

The split correctly separates:

[
\text{the object and rigorous finite identities}
]

from

[
\text{the numerical evidence and diagnostics}.
]

That was the right move. The main manuscript now has three genuinely useful mathematical pieces:

[
\boxed{
	\text{sliding-window congruence}}
]

[
\boxed{
	\chi_2(S(x))=(-1)^{v_2(3x+1)}}
]

[
\boxed{
	\text{faithful sync operator } \Rightarrow \text{ quotient by exact coboundary}}
]

The strongest conceptual sentence remains:

[
\boxed{
	\text{H23a is a gap for non-coboundary characters of the faithful sync operator, not all nontrivial characters.}
}
]

That is a real clarification. It is worth preserving as the main theorem-level message of the package.

## 2. The main paper: what to improve

### A. The title is good, but the abstract should say “conditional” earlier

The abstract currently says you “formulate the remaining quantitative gap as a precise conditional statement.” That is accurate, but I would make the proof status unmistakable earlier.

Suggested insertion near the end of the abstract:

```latex
The resulting constant-gap statement is conditional on two explicit finite
operator inputs: absence of further principal-unit coboundaries and conductor
monotonicity.  These are supported numerically in the companion but are not
proved here.
```

This prevents readers from thinking the constant gap is established.

### B. “The operator question is settled in form” is good; avoid “closed”

You already improved the language. Keep saying:

[
\text{settled in form}
]

not:

[
\text{closed}.
]

The operator has been identified, and the quotient has been identified. The proof of the quotient gap is still open.

### C. The inverse principle should be labeled even more explicitly as conjectural

Your “inverse principle” is the open keystone. It should not be adjacent to theorems without a strong status marker.

I would title it:

```latex
\section{The finite spectral shadow principle (conjectural)}
```

Then state:

[
\text{This is not proved in this note and is not implied by H23a.}
]

It is the “moon,” not the finite operator result. The current text is mostly clear, but this extra warning is worth adding.

### D. The sliding-window congruence is excellent

The proof is short, exact, and important. Keep it in the main text. This lemma is one of the few genuinely rigorous bridges:

[
\text{valuation word}
\longrightarrow
\text{finite }3^r\text{-residue character}.
]

I would add one sentence after the lemma:

```latex
This identity is independent of any randomness or annealed model.
It is the arithmetic reason that \(3^r\)-residue characters are legitimate
finite-window probes of the valuation word.
```

That will help readers understand why it belongs in the theoretical paper.

### E. The quadratic coboundary theorem is the centerpiece

The proof is clean and should remain in the main text. I would emphasize that the result is exact for every (r), every tilt, and every height discretization:

[
\rho(\mathcal L_{\chi_2})=\rho(\mathcal L_{\mathbf 1})
]

because it is an isospectral conjugacy, not a numerical phenomenon.

This is probably the main publishable/archivable fact in the note.

### F. The statement “residues are not uniform mod 3” needs careful wording

The corollary says:

[
\Pr(x\equiv1)=1/3,\qquad \Pr(x\equiv2)=2/3.
]

That probability is under the annealed valuation-pushforward law, not as an unconditional statement about integer residues. Clarify:

```latex
Under the annealed valuation law \(p_b=2^{-b}\), the induced one-step
pushforward distribution on residues mod \(3\) is \(1/3:2/3\).
```

Otherwise a reader may object that odd integer residues modulo (3) are not being sampled by Haar in that sentence.

### G. Conductor autonomy is useful but should specify the operator precisely

The proposition says the gap ratio of a conductor-(3^c) sector is independent of ambient (r). That is true for the reduced finite operator if the height component and allowed (b)-truncation are also independent of (r).

Add a phrase:

```latex
for the same height discretization, \(b\)-support/truncation, and synchronized
edge-weight convention.
```

Without that, someone may wonder whether (B_{\max}), killed boundaries, or exact edge multiplicities change with (r).

### H. The no-further-coboundaries conjecture needs a sharper proof target

This is now the most important analytic lemma.

You write that it reduces to the principal-unit functional equation

[
\psi(3a+1)=\psi(a^2)
\quad\text{on }C=1+3\mathbb Z/3^r\mathbb Z.
]

This is exactly where I would put proof energy. But the manuscript should derive that equation, not only state it. Add a short derivation sketch:

1. suppose a character (\chi) is a coboundary;
2. restrict to paired orbits/edges that cancel valuation parity;
3. eliminate the (\tau)-coordinate;
4. obtain a relation on principal units;
5. show it forces (\psi) trivial.

Even if the last step is still conjectural, the reduction will be clearer.

### I. Conductor monotonicity should be split into two possible targets

“Maximal gap ratio occurs at conductor (9)” is stronger than what you need. For the proof, you only need

[
\kappa_Q\gg 1/\operatorname{polylog}(Q).
]

So state two conjectures:

```latex
Conjecture A (polylog quotient gap).
...
Conjecture B (constant gap / conductor-9 extremality).
...
```

Then the proof path is less brittle. If conductor monotonicity is hard, a weaker block-minorization could still close the finite H23a leak.

## 3. Computational companion: what to improve

The companion is substantially better than before. It is honest about provisional criticality, separates exact and annealed gaps, and reports the Arnoldi repair. Good.

### A. Include exact command lines or a run manifest

You say outputs are append-only CSV with provenance headers. Excellent. The paper should include either:

[
\text{one exact command line per experiment}
]

or a pointer to a run manifest file name.

For archival reproducibility, a table like:

```latex
Exp H: ./collatz_tests --exp H --seed-min 3 --seed-max 1000000 --r-max 8 ...
```

would be valuable.

### B. Add matrix-size data for operator experiments

For Experiments E/F, include:

[
#\text{states},\quad #\text{nonzeros},\quad B_{\max},\quad L,\quad R.
]

This matters because the spectral result is the core computational claim. Readers need to know the scale of the matrices.

### C. Arnoldi validation is good but needs one more check

You say residuals are (<8\times10^{-11}) and no Wielandt violations. Add:

[
\text{left/right residuals or backward error}
]

if available, and whether complex conjugate eigenpairs are recovered correctly.

For nonnormal matrices, a tiny residual is good but not always enough. At least include:

[
\frac{|\mathcal L v-\lambda v|}{|\mathcal L||v|}
]

and maybe a note that repeated runs with different Krylov dimensions agree.

### D. “Constant by conductor” in the companion should be softened

In the E/F finding box, the phrase:

[
\text{constant by conductor}
]

could read too much like a proof. Make it:

[
\text{observed constant by conductor}
]

or:

[
\text{conductor-organized and ambient-(r)-independent in tested range}.
]

### E. Experiment I should be marked as diagnostic, not evidence for the inverse principle

The companion already says the per-sector signal is confounded by small-(Q) inflation. That is good. I would sharpen the interpretation:

[
\boxed{
	\text{Experiment I does not validate the inverse principle.}
}
]

It validates that raw (W)-shadows are contaminated and need normalization. The main value of I is negative/diagnostic.

### F. Add a “negative findings” table

This would make the companion more trustworthy. For example:

[
\begin{array}{l|l}
	\text{Attempt} & \text{Outcome}\
	\hline
	\text{raw (W)-shadow} & \text{small-(Q) inflation}\
	\text{factored operator} & \text{breaks quadratic coboundary}\
	\text{power iteration} & \text{spurious ratios (>1)}\
	\text{literal (V^2\le2^A P)} & \text{degenerate critical label}
\end{array}
]

This is one of the strongest parts of your program: you do not hide dead ends.

## 4. How to proceed with the proof

There are now three proof tasks. They should be attacked in this order.

## Task 1: prove no further coboundaries

This is the most local and most likely to fall.

Target:

[
\text{Cob}(\mathcal L^{\mathrm{sync}})=\langle\chi_2\rangle.
]

Equivalently, no principal-unit character is a coboundary.

You already have the claimed reduction to:

[
\psi(3a+1)=\psi(a^2)
\quad
\text{on }C=1+3\mathbb Z/3^r\mathbb Z.
]

Work (3)-adically. Write

[
a=1+3u.
]

Then

[
3a+1=4+9u
=1+3(1+3u)
\quad\text{modulo }3^r,
]

after identifying (4\equiv1\pmod3), and

[
a^2=(1+3u)^2=1+6u+9u^2.
]

Pass to the logarithm on principal units:

[
\log:1+3\mathbb Z/3^r\mathbb Z
\to
3\mathbb Z/3^r\mathbb Z.
]

A principal-unit character is of the form

[
\psi(1+3u)=
\exp\left(\frac{2\pi i, k, \log(1+3u)}{3^r}\right)
]

up to the usual conductor normalization.

The equation

[
\psi(3a+1)=\psi(a^2)
]

becomes a linear congruence condition on

[
\log(3a+1)-2\log(a).
]

Show that the subgroup generated by

[
{\log(3a+1)-2\log(a):a\in C}
]

is the whole principal-unit additive group. Then every (\psi) killing it is trivial.

That would prove no further coboundaries.

This is now a very concrete finite (3)-adic algebra lemma. I would try to prove it first.

## Task 2: prove a polylog or constant gap

Once no further coboundaries is proved, the next target is cancellation.

Do not start by proving conductor-9 extremality. Start with the weaker theorem:

[
\kappa_Q\gg\frac1{(\log Q)^A}.
]

Use a block-minorization argument.

For each nontrivial principal-unit character (\chi), find a short block family (\mathcal W) such that endpoint residues contain a full coset of a subgroup (H) on which (\chi) is nontrivial. Then

[
\sum_{u\in H}\chi(uh)=0.
]

If the block mass is bounded below by (\alpha_Q), then

[
\kappa_Q\gg \alpha_Q.
]

The numerics suggest (\alpha_Q) may actually be constant after quotienting (\chi_2), but even

[
\alpha_Q\gg 1/\operatorname{polylog}(Q)
]

would be excellent.

A plausible proof route:

1. Use small valuation blocks (b\in{1,2,3}).
2. Compute the induced maps on principal units:
[
a\mapsto (3a+1)2^{-b}.
]
3. Show their commutators generate a nontrivial principal-unit subgroup at every conductor.
4. Use character orthogonality on that subgroup.
5. Bound the mass of the corresponding block family.

This is the finite (p)-adic analogue of Doeblin cancellation.

## Task 3: connect height/killing to the residue gap

After residue cancellation is proved, carry it to the full synchronized residue-height operator.

The problem is distortion:

[
w_s(w)=2^{s\sum_i(\log_2 3-b_i)}\prod_i2^{-b_i}.
]

For paired cancellation blocks, show

[
\frac{w_s(w_1)}{w_s(w_2)}
\in[C^{-1},C]
]

uniformly for (s\in[0,1]), or arrange exact same (b)-multisets so weights are equal.

The cleanest construction is to use block pairs/families with identical valuation multisets but different residue endpoints. Then height weights are exactly equal and cancellation is pure.

So for the proof of Task 2, prefer block families with the same valuation multiset whenever possible.

## 5. What not to focus on next

I would not spend more proof effort on:

[
\text{raw single-orbit shadow statistics}
]

until the finite operator theorem is proved. Experiment I already showed the circularity leak. Raw (W)-shadows are diagnostic, not foundational.

I would also not try to prove the full quenched inverse arrow yet. The finite operator side is now well-posed and much more accessible:

[
\text{no more coboundaries}
+
\text{polylog/constant quotient gap}.
]

Finish that first. Then return to:

[
\text{bad orbit}\Rightarrow\text{finite spectral shadow}.
]

## 6. Suggested next manuscript revision

For the main paper, add a “Proof Roadmap” subsection after the refined H23a target:

```latex
The remaining proof breaks into three independent finite statements:
(1) no additional coboundaries;
(2) principal-unit cancellation giving \(\kappa_Q\gg 1/\mathrm{polylog}(Q)\);
(3) height/killing distortion control.
Only after these are proved does one return to the global inverse principle.
```

For the computational companion, add an “Evidence-to-theorem map”:

[
\begin{array}{c|c|c}
	\text{Experiment} & \text{supports} & \text{proof target}\
	\hline
	H & sliding congruence & \text{proved lemma}\
	E/F & quotient gap & \text{Task 2}\
	I & raw shadow contamination & \text{normalization needed}\
	B/D & Cramér/post-exit structure & \text{context only}
\end{array}
]

## Bottom line

The split is the right structure. The main paper is now strongest when read as:

[
\boxed{
	\text{a finite spectral formulation and corrected H23a target.}
}
]

The companion is strongest when read as:

[
\boxed{
	\text{a reproducible audit showing why this is the right finite operator and quotient.}
}
]

To proceed with the proof, focus narrowly:

[
\boxed{
	\text{Prove no further coboundaries first.}
}
]

Then:

[
\boxed{
	\text{Prove principal-unit cancellation / polylog quotient gap.}
}
]

Only then return to the global quenched inverse arrow.
