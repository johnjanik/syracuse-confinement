My main critique is that the manuscript is currently trying to be three things at once: a theoretical note, a computational report, and an appendix proving the corrected operator formulation. The mathematical content is good, but the proof-status boundaries need to be made sharper.

## Overall assessment

The strongest sentence in the paper is essentially:

[
\boxed{
	\text{H23a is not a gap for all nontrivial characters; it is a gap for all non-coboundary characters of the faithful sync operator.}
}
]

That is a genuine clarification. The quadratic character computation is not a nuisance; it is the structural correction that makes the operator honest.

The best technical contribution is the proof that

[
\chi_2(S(x))=(-1)^{b(x)}
]

and hence the quadratic character is valuation parity in disguise. This justifies quotienting it out rather than treating it as an obstruction. That is the right mathematical diagnosis.

The main remaining weakness is that the manuscript sometimes states “constant gap” language more strongly than the proof currently supports. You do say monotonicity in conductor is open, but the theorem environment still reads as if the constant gap is proved.

## Major issue 1: downgrade `Theorem 10.3` unless monotonicity is proved

The section

[
\text{“The sync quotient gap: a constant, by conductor”}
]

contains:

[
\textbf{Theorem [Sync quotient gap is constant].}
]

But the proof status says the remaining input is monotonicity in conductor. Therefore this should not be a theorem yet.

Right now the logic is:

[
\text{conductor reduction proved}
]

[
\text{conductor-}9\text{ gap computed}
]

[
\text{higher-conductor monotonicity observed numerically}
]

[
\Rightarrow \kappa_Q=\kappa_0.
]

The third arrow is still open. So the theorem should become one of:

[
\textbf{Conditional Theorem}
]

or

[
\textbf{Numerical Conjecture / Gap Target}
]

or

[
\textbf{Proposition + Conjecture}
]

A clean rewrite:

[
\textbf{Proposition.}
]
Conductor-(3^c) sectors are (r)-autonomous, hence their gap ratios are independent of ambient (Q=3^r) once (r\ge c).

[
\textbf{Conjecture.}
]
Among non-coboundary sectors, the maximal ratio occurs at conductor (9).

[
\textbf{Conditional Corollary.}
]
If the conductor monotonicity conjecture holds, then

[
\kappa_Q^{\mathrm{sync}/\mathrm{cob}}\ge\kappa_0\approx0.0931
]

for all (Q=3^r).

That would make the status exact.

## Major issue 2: the coboundary classification lemma is not proved

You state:

[
\text{A character }\chi\text{ is a coboundary iff }\chi\in\langle\chi_2\rangle.
]

But the manuscript itself says the uniqueness direction is still left as the lemma and reduces to a principal-unit functional equation. That is not a proof.

This is not just a formal issue: this lemma is the conceptual hinge of the quotient. The forward direction is proved:

[
\chi_2\text{ is a coboundary}.
]

The reverse direction is still open unless the functional equation

[
\psi(3a+1)=\psi(a^2)
]

is actually solved for all (r).

So revise the status:

[
\textbf{Proposition.}
]
(\langle\chi_2\rangle) is contained in the coboundary group.

[
\textbf{Conjecture / Lemma to prove.}
]
No principal-unit character is a coboundary.

Then the quotient gap theorem becomes conditional on both:

1. no additional coboundary characters;
2. conductor monotonicity / principal-unit cancellation.

That is still good. It gives a precise proof target.

## Major issue 3: clarify source-character versus edge-character convention

The theorem

[
\frac{d(a',\tau')}{d(a,\tau)}=\chi_2(a)
]

is correct under your convention that the twist is carried on the **source** residue.

But many transfer-operator conventions twist by the endpoint, or by the edge multiplier. Since the exact coboundary depends on this convention, state it explicitly before the theorem:

> Throughout this appendix the multiplicative character twist is placed on the source vertex (a). With endpoint twisting the coboundary formula is conjugate but takes a different form.

This will prevent confusion.

## Major issue 4: (\Omega_Q) changes identity

Earlier the manuscript speaks of characters of (\Omega_Q), then later specializes to multiplicative characters of

[
U_Q=(\mathbb Z/3^r\mathbb Z)^\times.
]

Those are not the same unless (\Omega_Q) is defined as the unit group at this stage. Since the quadratic coboundary is specifically a multiplicative-character phenomenon modulo (3^r), make the specialization explicit.

Suggested sentence near the beginning:

> In Parts IV and Appendix A, the residue space is specialized to (U_{3^r}=(\mathbb Z/3^r\mathbb Z)^\times), and all characters are multiplicative unless explicitly stated otherwise. The additive-character experiments in earlier sections are diagnostic only and are not the final H23a vehicle.

This is important because Experiment C mentions additive characters, while the final operator vehicle uses multiplicative characters.

## Major issue 5: the critical-event labels are still not canonical

You already note the caveat:

[
V^2\le2^A P
]

is degenerate in practice, and the suite uses both `vsq` and `height`, with `height` default.

This is a serious issue for Experiments B, D, and I. The conclusions about “critical windows,” “post-exit taboo,” and “critical excursions shadow most often” should be labeled as conditional on the working definition of criticality.

I would strengthen the caveat:

> The conclusions involving labels `critical_C_A`, `high_ascent`, and `post_exit` are exploratory until the formal (C_A)-critical certificate is fixed. They should not be used as theorem evidence in the current form.

Otherwise a reader may treat the post-exit result as more canonical than it is.

## Major issue 6: the Quenched Inverse Principle still overconcludes

The final line of the principle says:

[
\text{Hence every integer orbit equidistributes relative to the annealed residue law.}
]

This is too strong as a conclusion from the stated finite-character contradiction. At best, if the principle and H23a gap hold, you rule out persistent **non-coboundary finite spectral shadows**. That is not identical to full equidistribution unless you prove that every violation of the annealed law produces such a shadow.

That is exactly the keystone. So I would change the final sentence to:

> Hence every orbit satisfying the hypotheses of the inverse principle has no persistent non-coboundary finite spectral shadow. If every bounded-deficit or large-deviation failure produces such a shadow, then the relevant quenched obstruction is excluded.

This preserves the open arrow.

## What is genuinely strong

The following should be highlighted more prominently:

### 1. The sliding-window congruence lemma

This is the load-bearing arithmetic identity:

[
x_n \equiv
\sum_{k=1}^{r}
3^{k-1}
2^{-(b_{n-1}+\cdots+b_{n-k})}
\pmod{3^r}.
]

You should move the proof of this lemma into the main text, not just state it. It is short and important. It shows that finite (3^r)-residue characters are finite sliding-window observables of the valuation process. That is one of the few rigorous bridges from valuation word to residue shadow.

### 2. The quadratic coboundary proof

This is the strongest clean theorem in the document. It deserves to be in the main body or at least introduced as a central result before the computational assessment.

The identity

[
S(x)\equiv (-1)^b\pmod3
]

is simple, memorable, and structurally decisive.

### 3. The distinction between `sync` and `factored`

This is excellent and should be made more prominent. It says the operator must be faithful:

[
\text{same }b\text{ drives residue and height}.
]

The factored operator breaks the coboundary artificially and therefore is not the true H23a vehicle. That is an important methodological lesson.

## Suggested reorganization

I would reorganize the manuscript into four parts:

### Part I: The object and the open inverse principle

Keep this, but tighten the conclusion and definitions.

### Part II: Rigorous finite identities

Move here:

1. sliding-window congruence;
2. quadratic coboundary;
3. source-twist convention;
4. residue-only versus sync/factored distinction.

This gives the manuscript a real theorem core before the experiments.

### Part III: Numerical experiments

Report A–I after the rigorous identities. Make `critical` labels explicitly provisional.

### Part IV: The refined H23a target

State:

[
\text{proved: conductor autonomy;}
]

[
\text{proved: quadratic character is a coboundary;}
]

[
\text{open: no other coboundaries;}
]

[
\text{open: conductor monotonicity/principal-unit cancellation;}
]

[
\text{conditional: constant sync quotient gap.}
]

This will make the status transparent.

## Specific wording changes

Replace:

> “This closes the operator question.”

with:

> “This identifies the correct operator and the correct quotient. The remaining operator theorem is the quantitative non-coboundary gap on that quotient.”

Replace:

> “the gap is present, (Q)-uniform, and in fact constant”

with:

> “the computed gap is (Q)-uniform after conductor reduction, and the data suggest a constant gap governed by conductor (9). Proving this reduces to the conductor monotonicity/principal-unit cancellation statement.”

Replace:

> “every character of order (>2) stays gapped”

with:

> “every tested character of order (>2) stays gapped; analytically this reduces to ruling out principal-unit coboundaries and proving cancellation.”

Unless you prove it.

## LaTeX / compilation notes

The file compiles, but repeated runs still report cross-reference warnings such as missing appendix anchors. This is probably caused by `\part`/appendix interactions and unnumbered section references. Not mathematically serious, but worth cleaning before sharing.



## Bottom line

This is a strong manuscript, but its status labels need tightening.

The real achievements are:

[
\boxed{
	\text{the correct H23a operator is the faithful sync operator;}
}
]

[
\boxed{
	\text{the quadratic character is an exact coboundary, not an obstruction;}
}
]

[
\boxed{
	\text{H23a must be stated on the non-coboundary quotient;}
}
]

[
\boxed{
	\text{the remaining finite-operator task is principal-unit cancellation / conductor monotonicity.}
}
]

The remaining open pieces are:

[
\boxed{
	\text{prove no additional coboundaries;}
}
]

[
\boxed{
	\text{prove conductor monotonicity or at least }\kappa_Q\gg1/\operatorname{polylog}(Q);
}
]

[
\boxed{
	\text{prove the quenched inverse arrow: bad orbit }\Rightarrow\text{ finite spectral shadow.}
}
]

That is a good place to be. The manuscript should make exactly that status impossible to misunderstand.
