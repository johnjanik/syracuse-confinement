**mathematics of deterministic equidistribution, sparse targets, inverse theorems, and the normality barrier**.

One correction first: Tao’s relevant Collatz paper is from 2019/2020, not 2022. Its exact limitation is the right frontier marker: it proves an **almost-all** result using estimates for a skew random walk on (\mathbb Z/3^n), not a pointwise theorem for every orbit. ([arXiv][1])

Below is the reading list I would actually use.

# 0. The Collatz-specific frontier

Start here because it tells you precisely what current methods can and cannot do.

## Terence Tao, *Almost all orbits of the Collatz map attain almost bounded values*

This is the modern benchmark. Tao proves that for any (f(N)\to\infty),

[
\operatorname{Col}_{\min}(N)\le f(N)
]

for almost all (N), in logarithmic density. The proof uses an approximate transport property for a Syracuse random variable and Fourier analysis of a skew random walk on (\mathbb Z/3^n). This is exactly the annealed/average side of your obstruction. ([arXiv][1])

Read it with one question in mind:

[
\text{Where does the proof lose the fixed initial integer?}
]

That loss is essentially your “quenched” wall.

## Bernstein–Lagarias, *The (3x+1) conjugacy map*

This is foundational for the (2)-adic/parity-vector viewpoint. It studies the (3x+1) conjugacy map on (\mathbb Z_2), the induced permutations modulo (2^n), and the relationship with shift-like (2)-adic dynamics. ([Semantic Scholar][2])

Read this as the natural coordinate system for your valuation cocycle.

## Terras, Everett, Lagarias survey material

Not contemporary, but necessary background: parity vectors, stopping times, density-one results, and probabilistic heuristics. Use these only to situate Tao and your work; they will not solve the quenched obstruction.

# 1. Deterministic normality and the “single orbit realizes randomness” barrier

Your final obstruction is structurally closer to normality of explicit numbers than to ordinary ergodic theory.

## Bugeaud, *Expansions of algebraic numbers*

This is a survey of what is known about (b)-ary expansions of algebraic numbers. The striking point is negative: even for algebraic irrational numbers, we are far from proving normality. ([irma.math.unistra.fr][3])

This is the philosophical analogue of your obstruction:

[
\text{a.e. normality is easy;}
\qquad
\text{a specific deterministic object is hard.}
]

## Adamczewski–Bugeaud, *On the complexity of algebraic numbers I*

This proves that an irrational algebraic number cannot have a low-complexity base-(b) expansion, and that irrational automatic numbers are transcendental. It does **not** prove normality, but it is a prototype of an inverse theorem:

[
\text{too much structure in digits}
\Rightarrow
\text{arithmetic impossibility}.
]

That is exactly the kind of theorem you want for valuation sequences. ([adamczewski.perso.math.cnrs.fr][4])

**Why it matters for you:** it suggests the right form of a future theorem may be weaker than full normality but strong enough: rule out low-complexity valuation sequences or persistent sparse-target clustering.

# 2. Dynamical Borel–Cantelli and shrinking targets

This is the closest named field to your desired theorem, but current results typically require mixing/decay of correlations and give a.e. conclusions.

## Chernov–Kleinbock, *Dynamical Borel–Cantelli lemmas for Gibbs measures*

Canonical source for dynamical Borel–Cantelli in systems with Gibbs/mixing structure. It is useful precisely because it shows what hypotheses you lack. ([arXiv][5])

## Athreya, *Logarithm laws and shrinking target properties*

A readable survey linking shrinking targets, recurrence, geometry, and Diophantine approximation. Good orientation before reading more technical work. ([Springer][6])

## Dolgopyat–Fayad–Liu, *Multiple Borel–Cantelli lemma in dynamics and multilog law for recurrence*

This is modern and closer to your “clustered hits” issue. They study multiple occurrences of rare events on the same time scale and obtain Poisson/log-law conclusions under exponential mixing of all orders. ([AIMS][7])

**Why it matters:** it tells you how clustered rare events are handled when mixing exists. Your system lacks the needed mixing, so this becomes a template for what a Collatz-specific replacement would have to prove.

## Kleinbock–Zheng, *Dynamical Borel–Cantelli lemma for recurrence under Lipschitz twists*

Useful because it unifies shrinking targets and recurrence through a generalized framework. Again, it is measure-preserving/a.e., but the formalism may help you state your deterministic analogue. ([arXiv][8])

# 3. Measure rigidity and (\times2,\times3)

This is the theory that almost applies — and fails for the exact structural reason you identified: not enough independent (\times3)-entropy.

## Furstenberg (\times2,\times3) conjecture and positive-entropy rigidity

Read a survey first. The current survey literature explains Rudolph, Host, Parry, Lyons, and the positive-entropy case of Furstenberg’s conjecture. ([arXiv][9])

What to extract:

[
\text{positive entropy under two independent commuting actions}
\Rightarrow
\text{Lebesgue/Haar rigidity}.
]

Your system has (\times2)-richness but only rank-one (\times3) motion, so the theorem does not bite. That failure is structurally important.

## Einsiedler–Katok–Lindenstrauss / Lindenstrauss measure rigidity

Read selectively, not exhaustively. The lesson is the same: higher-rank diagonal action + entropy gives rigidity. Your system is too rank-one.

## Hochman–Shmerkin, *Local entropy averages and projections of fractal measures*

This is very relevant as method, not because (C_6) is a fixed fractal target. Hochman–Shmerkin use local entropy averages to prove projection and dimension results, including Furstenberg-type consequences for (\times m,\times n) invariant sets. ([arXiv][10])

**Why it matters for you:** local entropy averages are one of the few tools that turn multiscale structure into quantitative conclusions. If a future Collatz theorem uses entropy rather than single characters, this is one of the conceptual ancestors.

# 4. Inverse theorems: equidistribution failure implies structure

This is probably the most important direction.

## Green–Tao, *The quantitative behaviour of polynomial orbits on nilmanifolds*

This is the cleanest available model for the theorem-shape you want:

[
\text{failure of equidistribution}
\Rightarrow
\text{explicit low-complexity obstruction}.
]

Green–Tao prove a quantitative version of Leibman’s theorem: finite polynomial nilorbits either equidistribute quantitatively or are controlled by lower-complexity algebraic structure. ([annals.math.princeton.edu][11])

This does not apply directly to Collatz, because the accelerated Collatz cocycle is not a polynomial nilorbit. But the **logical shape** is exactly right.

Your desired theorem would be:

[
\text{failure of valuation/height sparse-target law}
\Rightarrow
\text{affine }2\text{-adic coboundary / low-complexity obstruction}.
]

## Green–Tao–Ziegler inverse theory for Gowers norms

Read after Green–Tao nilmanifolds if needed. The lesson is: large correlation with structured tests forces nilpotent structure. You probably need a Collatz analogue where “structured tests” are (2)-adic affine characters or height-cocycle targets.

## Bourgain’s entropy/sum-product toolkit

Not one paper, but a methodology. Tao’s “Exploring the toolkit of Jean Bourgain” is a good guide to Bourgain-style arguments: discretized sum-product, entropy growth, flattening, and spectral gaps. ([arXiv][12])

This may matter because your obstruction smells like:

[
\text{repeated sparse hits}
\Rightarrow
\text{failure of entropy growth}
\Rightarrow
\text{hidden approximate algebraic structure}.
]

# 5. Homogeneous dynamics and quantitative nondivergence

This is a possible future route, but only if someone builds an (S)-arithmetic homogeneous encoding of the Collatz cocycle.

## Kleinbock–Margulis, *Flows on homogeneous spaces and Diophantine approximation on manifolds*

This is the basic quantitative nondivergence machine: it controls time spent near cusp/rational degeneracies for homogeneous flows. ([arXiv][13])

For you, the analogy is:

[
\text{large valuation/height excursion}
\sim
\text{cusp excursion}.
]

But there is no known (G/\Gamma) model for Collatz that makes this literal.

## Kelmer, *Shrinking targets for discrete time flows on hyperbolic manifolds*

This is useful because it handles shrinking targets for homogeneous flows and establishes logarithm laws/hitting estimates. ([arXiv][13])

Again: relevant as a blueprint only if a homogeneous encoding is found.

# 6. Thermodynamic formalism, pressure, and large deviations

This is now central because your corrected (C_6) picture is governed by the height cocycle

[
M(s)=\frac{3^s}{2^{1+s}-1}.
]

You should read pressure/large-deviation material with the aim of translating:

[
M(s)
\quad\leadsto\quad
\text{Cramér tilt, height tail, conditioned excursion law}.
]

## Standard references

Read one standard source on thermodynamic formalism and one on large deviations:

* Parry–Pollicott, *Zeta functions and the periodic orbit structure of hyperbolic dynamics*.
* Denker–Keller–Urbanski or Pesin-style accounts of pressure and multifractal spectra.
* Dembo–Zeitouni, *Large Deviations Techniques and Applications*.

For your purpose, you only need the part that says:

[
\Pr(h\ge H)\sim e^{-I(H)}
]

and conditioned paths are governed by a tilted measure.

## Branching random walk / killed random walk

Your R3 correction shows the spine scale is diffusive:

[
1-\rho_L^{\mathrm{spine}}\asymp L^{-2}.
]

So read killed random walk and branching random walk with absorption:

* Addario-Berry–Broutin–Reed / Aïdékon-type killed branching random walk literature.
* Hu–Shi on branching random walks and derivative martingales.
* Kyprianou’s branching random walk and Lévy process material.

The point is not Collatz; it is the mechanism:

[
\text{critical branching + killed strip}
\Rightarrow
\text{finite depth with diffusive scale}.
]

# 7. (p)-adic and affine-dynamical foundations

This is the local language for your system.

## Bernstein–Lagarias again

Essential for (2)-adic conjugacy and finite mod-(2^n) structure. ([cr.yp.to][14])

## Monks, *The autoconjugacy of the (3x+1) function*

Useful for understanding symmetries of parity vectors and (2)-adic transforms. ([ACM Digital Library][15])

## Rozier / Terracol-style parity sequence studies

Recent work on parity sequences and induced (2)-adic dynamics may help formalize the affine-cocycle framework. Search this line, but keep it secondary.

# 8. What not to over-prioritize

## Schmidt games / absolute winning

Interesting for target-avoidance sets, but probably not central. It proves large sets of avoiding initial points, whereas you need every positive integer orbit.

## Fractal dimension of (C_6)

After your latest corrections, this should not drive the program. (C_6) is not primarily a low-dimensional (2)-adic fractal. It is a pressure/large-deviation level set.

## Pure Baker theory

Baker and (p)-adic linear forms are useful for excluding near-cycles and (S)-unit relations, but they do not give the deterministic Borel–Cantelli theorem you need.

# Recommended reading order

If I were designing a six-month reading program, I would do this:

## Month 1: Collatz and normality frontier

1. Tao, *Almost all orbits of the Collatz map attain almost bounded values*.
2. Bernstein–Lagarias, *The (3x+1) conjugacy map*.
3. Bugeaud, *Expansions of algebraic numbers*.
4. Adamczewski–Bugeaud, *On the complexity of algebraic numbers I*.

Goal: understand the pointwise/quenched barrier.

## Month 2: Dynamical Borel–Cantelli and shrinking targets

1. Chernov–Kleinbock.
2. Athreya survey.
3. Dolgopyat–Fayad–Liu.
4. Kleinbock–Zheng.

Goal: understand what mixing gives and why you lack it.

## Month 3: Inverse theorems and structural obstructions

1. Green–Tao nilmanifold paper.
2. Basic Gowers inverse theorem expositions.
3. Tao’s Bourgain toolkit note.

Goal: learn the architecture of “failure of randomness implies structure.”

## Month 4: (\times2,\times3) rigidity and local entropy

1. Furstenberg (\times2,\times3) survey.
2. Hochman–Shmerkin.
3. Selected Rudolph–Johnson / Host material.

Goal: understand why positive entropy/rank hypotheses matter.

## Month 5: Pressure and killed-walk machinery

1. Thermodynamic formalism / pressure.
2. Dembo–Zeitouni large deviations.
3. Killed random walk / branching random walk absorption papers.

Goal: put (M(s)=3^s/(2^{1+s}-1)) and R3 on standard footing.

## Month 6: Try to write the new theorem

The theorem to write is:

[
\boxed{
	\textbf{Deterministic sparse large-deviation theorem for the accelerated Collatz height cocycle.}
}
]

In a weak form:

[
\text{persistent violation of the Cramér large-deviation law}
\Rightarrow
\text{finite affine/character obstruction}.
]

Then compare that obstruction with H23a/certificate machinery.

# Final classification

Your obstruction sits between existing fields:

[
\begin{array}{lll}
	\text{Normality of explicit numbers} & \text{same pointwise barrier} & \text{no general method} \
	\text{Dynamical Borel--Cantelli} & \text{right target language} & \text{requires mixing/a.e.} \
	\text{Measure rigidity} & \text{right entropy language} & \text{requires higher rank} \
	\text{Green--Tao inverse theory} & \text{right proof architecture} & \text{wrong ambient system} \
	\text{Thermodynamic formalism} & \text{right pressure object} & \text{usually annealed/Gibbs} \
	\text{(2)-adic affine dynamics} & \text{right local coordinate} & \text{no sparse-target theorem}
\end{array}
]

So the most honest reading-list thesis is:

[
\boxed{
	\text{Develop a Collatz-specific inverse theorem: deterministic failure of the Cramér/Haar law must force a finite affine obstruction.}
}
]

That is the mathematics your program is pointing toward.

[1]: https://arxiv.org/abs/1909.03562 "Almost all orbits of the Collatz map attain almost bounded values"
[2]: https://www.semanticscholar.org/paper/The-3x-%2B-1-Conjugacy-Map-Bernstein-Lagarias/56dfdf65e1d03de836f6cf5c92b5c5876abe8145 "The 3x + 1 Conjugacy Map"
[3]: https://irma.math.unistra.fr/~bugeaud/travaux/FFNT.pdf "Expansions of algebraic numbers - IRMA, Strasbourg"
[4]: https://adamczewski.perso.math.cnrs.fr/ComplexityI.pdf "On the complexity of algebraic numbers I. Expansions in ..."
[5]: https://arxiv.org/abs/math/9912178 "Dynamical Borel-Cantelli lemmas for Gibbs measures - math"
[6]: https://link.springer.com/article/10.1007/s12044-009-0044-x "Logarithm laws and shrinking target properties - Springer Nature"
[7]: https://www.aimsciences.org/article/doi/10.3934/jmd.2022009 "Multiple Borel–Cantelli Lemma in dynamics and MultiLog ..."
[8]: https://arxiv.org/abs/2205.12366 "Dynamical Borel-Cantelli Lemma for Recurrence under Lipschitz Twists"
[9]: https://arxiv.org/html/2110.05989v15 "Furstenberg's Times 2, Times 3 Conjecture (a Short Survey)"
[10]: https://arxiv.org/abs/0910.1956 "Local entropy averages and projections of fractal measures"
[11]: https://annals.math.princeton.edu/2012/175-2/p02 "The quantitative behaviour of polynomial orbits on nilmanifolds"
[12]: https://arxiv.org/abs/2009.06736 "[2009.06736] Exploring the toolkit of Jean Bourgain"
[13]: https://arxiv.org/abs/1702.01025 "Shrinking targets for discrete time flows on hyperbolic manifolds"
[14]: https://cr.yp.to/papers/3x1conjmap-19960215-retypeset20220326.pdf "THE 3x + 1 CONJUGACY MAP Daniel J. Bernstein, Jeffrey C ..."
[15]: https://dl.acm.org/doi/abs/10.1016/s0012-365x%2803%2900125-0 "The autoconjugacy of the 3x+1 function"
