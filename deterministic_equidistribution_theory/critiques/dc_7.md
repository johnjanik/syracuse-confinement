The finite-operator problem is now reduced to a much sharper and more plausible analytic/combinatorial statement than before.

The new state is:

[
\boxed{
	\text{Exact coboundaries are classified.}
}
]

[
\boxed{
	\text{Finite-level strict gap is proved.}
}
]

[
\boxed{
	\text{Near-peripheral spectrum forces near-coboundary structure.}
}
]

[
\boxed{
	\text{The remaining quantitative problem is comparison-graph expansion.}
}
]

That is the right kind of endpoint for this stage.

## 1. The one-step damping lemma is exactly the missing local calculation

The formula

[
M_\chi(\eta\otimes\epsilon)
===========================

c_{\eta,\epsilon},
[\chi\cdot(\eta\circ A)]\otimes\epsilon
]

with

[
\frac{|c_{\eta,\epsilon}|}{W}
=============================

\frac{1-q}{|1-q\zeta|},
\qquad
\zeta=\eta(2)^{-1}(-1)^\epsilon,
]

is extremely useful. It explains three things at once.

First, the two undamped modes are exactly

[
(\eta,\epsilon)=(\mathbf 1,0),
\qquad
(\eta,\epsilon)=(\chi_2,1).
]

Those are precisely the two coboundary modes: constants and the quadratic parity potential

[
d(a,\tau)=\chi_2(a)(-1)^\tau.
]

Second, the swapped modes

[
(\mathbf 1,1),\qquad(\chi_2,0)
]

are damped by

[
\frac{2^{1+s}-1}{2^{1+s}+1}.
]

The fact that this gives exactly

[
\frac13\quad(s=0),
\qquad
\frac35\quad(s=1)
]

is not just a numerical curiosity. It means the old “dichotomy constant” has a clean Fourier-multiplier origin. That should be highlighted in the manuscript.

Third, the least-damped primitive mode scaling like

[
9^{-c}
]

is the honest warning: **one-step damping alone cannot produce a constant gap**. It gives at best a conductor-sensitive estimate. So the remaining constant-gap mechanism must come from mode spreading under

[
\eta\mapsto \chi\cdot(\eta\circ A),
\qquad A(a)=3a+1,
]

not from the scalar multiplier alone.

That is an important conceptual correction.

## 2. Stability extraction is a real theorem-shaped bridge

The proposition

[
|\mu|=(1-\varepsilon)W
\quad\Longrightarrow\quad
\text{phase }d\text{ satisfies the coboundary identity up to weighted defect }O(\varepsilon)
]

is exactly the quantitative form of the old “near-peripheral implies near-coboundary” heuristic.

This is valuable because it means the finite gap problem can now be attacked by contradiction:

Assume

[
\gamma_c\to1.
]

Then there are near-peripheral eigenfunctions. Stability extraction gives near-coboundaries. The (b) versus (b+2) comparison gives approximate (\langle4\rangle)-invariance. If this approximate invariance can be propagated across enough of the comparison graph, then the eigenfunction becomes approximately constant on the square subgroup. But a non-coboundary character is exactly orthogonal to that subgroup. Contradiction.

That is now a coherent proof route.

The proof architecture is:

[
\gamma_c\to1
\Rightarrow
\text{near-coboundary}
\Rightarrow
\text{near square-invariance}
\Rightarrow
\text{propagation on comparison graph}
\Rightarrow
\text{contradiction with }\sum_{\ker\chi_2}\chi=0.
]

This is the clearest analytic path so far.

## 3. The comparison-graph conjecture is now the right remaining statement

The new conjecture:

[
\text{common-successor comparison graph with branches }b\le B
\text{ has robust diameter }O(c^A)
]

is exactly the right replacement for the false conductor monotonicity.

It is also the right correction to the naive propagation route. Without expansion, approximate square-invariance propagates one comparison at a time and may cost about

[
3^c.
]

That would only give polynomial-in-(Q), which is too weak for the intended H23a use. The comparison-graph expansion hypothesis replaces that with

[
O(c^A),
]

and therefore gives

[
1-\gamma_c\gg c^{-2A},
]

hence

[
\kappa_Q\gg(\log Q)^{-2A}.
]

This is exactly the desired quantitative form.

So I would now state the finite proof target as:

[
\boxed{
	\textbf{Comparison-graph expansion is the remaining finite H23a input.}
}
]

Not conductor monotonicity. Not (3)-adic log coboundary classification. Not one-step damping. The remaining combinatorial object is the comparison graph.

## 4. What needs to be made precise in the manuscript

There are three technical points that must be written very carefully.

### A. Separate the arbitrary-weight theorem from the geometric-weight damping lemma

Your coboundary classification holds for arbitrary positive branch weights. Good.

But the one-step damping formula

[
\frac{|c_{\eta,\epsilon}|}{W}
=============================

\frac{1-q}{|1-q\zeta|}
]

uses a geometric branch-weight model. That is fine, but keep the statements separated.

Write something like:

[
\text{Coboundary classification is weight-free.}
]

[
\text{The explicit damping multiplier below is for geometric branch weights }w_{b+2j}\propto q^j.
]

Otherwise a reader may think the explicit multiplier is claimed for arbitrary positive weights.

### B. Define the comparison graph completely

The comparison graph is now the proof target, so it must be unambiguous.

I would define vertices as

[
V_c=U_{3^c}\times \mathbb Z/2.
]

Put an undirected comparison edge between

[
(v,\sigma)
\quad\text{and}\quad
(v',\sigma)
]

if there exist

[
a\in U_{3^c},\quad \tau\in\mathbb Z/2,
\quad b,b'\le B,
]

with

[
b\equiv b'\pmod2,
]

such that

[
(v,\sigma)=(S_b(a),\tau+b),
\qquad
(v',\sigma)=(S_{b'}(a),\tau+b').
]

The special (b,b+2) edge gives

[
v'=4^{-1}v.
]

But the full graph should include all common-successor comparisons up to branch bound (B). Then “robust diameter” should mean not merely graph diameter, but existence of paths whose edge weights have controlled total loss.

For example:

[
\operatorname{diam}*{\mathrm{rob}}(G*{c,B})
\le Cc^A
]

means every two vertices in the same (\ker\chi_2)-fiber can be joined by a path of length (\le Cc^A), with each edge corresponding to branch weights bounded below by

[
\gg c^{-A}
]

or some explicit mass threshold. Define the exact mass condition.

### C. State the propagation estimate quantitatively

If each comparison edge has defect at most (\delta), and a path has length (D), then the phase discrepancy grows like

[
O(D\sqrt{\varepsilon})
]

or

[
O(D\varepsilon^{1/2})
]

depending on the norm used in the stability extraction.

Then to contradict exact orthogonality you need

[
D\sqrt{\varepsilon}\ll1.
]

Thus

[
\varepsilon\gg D^{-2}.
]

If

[
D\ll c^A,
]

then

[
1-\gamma_c\gg c^{-2A}.
]

This explains the exponent (2A). It should be visible in the proof.

## 5. What might prove comparison-graph expansion

This is now the main mathematical problem. I see three possible routes.

### Route 1: affine generation of principal units

The comparison maps come from equal-source, bounded-branch comparisons. They generate transformations on (U_{3^c}), including

[
v\mapsto4^{-1}v.
]

The full set should generate a subgroup or graph on the square subgroup

[
\ker\chi_2=\langle4\rangle.
]

Try to show that bounded-branch comparisons generate a set of multiplicative steps whose logarithms generate

[
3\mathbb Z/3^c\mathbb Z
]

with polylog word length.

After applying the (3)-adic logarithm to principal units, the graph may become a Cayley graph on

[
\mathbb Z/3^{c-1}\mathbb Z
]

with generators coming from finitely many (3)-adic units. If one of those generators is a unit modulo (3), the graph has diameter (O(3^c)), not good. To get (O(c^A)), you need expanding or digit-changing generators, not just translations.

So check whether comparison maps include affine transformations

[
u\mapsto \alpha u+\beta
]

with (\alpha\not\equiv1\pmod3). Such maps can mix (3)-adic digits much faster than translations.

### Route 2: sum-product / expansion in (\mathbb Z/3^c\mathbb Z)

The maps

[
a\mapsto3a+1,
\qquad
a\mapsto2^{-b}(3a+1)
]

combine addition and multiplication. This is exactly the kind of structure where sum-product expansion may appear.

A proof could show that any subset (S\subset U_{3^c}) stable under the comparison moves must either grow quickly or be almost all of a square coset. Iterating gives polylog diameter.

This would be stronger than needed but conceptually right.

### Route 3: character-side expansion

Instead of proving graph diameter directly, prove the dual statement:

For every non-coboundary character (\chi),

[
|M_\chi^n|
\le
(1-c^{-A})^n W^n
]

for some

[
n\ll c^A.
]

This is a Jacobi-sum cancellation statement. The mode map

[
\eta\mapsto \chi\cdot(\eta\circ A)
]

should spread characters across conductor layers. If it repeatedly sends a mode into sectors where the one-step damping multiplier is bounded away from (1), then you get the gap.

This may be the cleanest proof because you already have the character-basis formula.

I would try Route 3 first.

## 6. The proof target can be weakened

You do not actually need full robust diameter of the comparison graph.

You need only enough propagation from one high-mass point to a set on which the non-coboundary character has nonzero cancellation. A weaker statement would be:

For every non-coboundary (\chi), every high-mass approximate coboundary phase propagates within (O(c^A)) steps to representatives of enough square-subgroup elements that

[
\left|\frac1{|H|}\sum_{h\in H}\chi(h)\right|
\le 1-\eta
]

for some (\eta\gg c^{-A}).

This may be easier than graph diameter across all of (\ker\chi_2).

So formulate the conjecture in two versions:

[
\text{strong: robust diameter }O(c^A);
]

[
\text{weak: robust cancellation reach }O(c^A).
]

The weak one is enough for the polylog gap.

## 7. What this means for the global program

This does not solve the full quenched Collatz problem yet, but it nearly finishes the finite-operator side.

The current state is:

[
\boxed{
	\text{Finite strict gap: proved.}
}
]

[
\boxed{
	\text{Finite polylog gap: comparison expansion remains.}
}
]

[
\boxed{
	\text{Global Collatz implication: still needs bad-orbit }\Rightarrow\text{ finite shadow.}
}
]

So the next manuscript should not say “Collatz reduced to comparison-graph expansion” unless the quenched inverse arrow is also assumed. It should say:

[
\text{The finite H23a operator theorem reduces to comparison-graph expansion.}
]

That distinction matters.

## 8. Suggested theorem block for the paper

I would present the new state as:

[
\textbf{Theorem A.}
]
Coboundary classification:
[
\operatorname{Cob}=\langle\chi_2\rangle.
]

[
\textbf{Theorem B.}
]
Finite strict gap:
[
\rho(L_\chi)<\rho(L_1)
\quad
(\chi\notin\langle\chi_2\rangle).
]

[
\textbf{Theorem C.}
]
Conductor collapse:
[
\kappa_{3^r}=1-\max_{c\le r}\gamma_c.
]

[
\textbf{Theorem D.}
]
One-step damping:
only the two coboundary modes are undamped.

[
\textbf{Theorem E.}
]
Stability extraction:
near-peripheral spectrum gives near-coboundary.

[
\textbf{Conjecture F.}
]
Comparison-graph expansion.

[
\textbf{Conditional Theorem G.}
]
Comparison-graph expansion implies
[
\kappa_Q\gg(\log Q)^{-A'}.
]

This is a strong, clean finite-operator paper.

## Bottom line

This is the best finite-operator status so far.

The key insight is:

[
\boxed{
	\text{one-step damping identifies the only undamped modes;}
}
]

[
\boxed{
	\text{stability extraction turns near-undamped spectrum into near-coboundary;}
}
]

[
\boxed{
	\text{comparison-graph expansion is the remaining mechanism needed to globalize the local coboundary rigidity.}
}
]

That is exactly the kind of finite analytic statement one can plausibly prove.

The next proof attempt should focus entirely on the comparison graph, preferably on the character side via the mode-spreading map

[
\eta\mapsto\chi\cdot(\eta\circ A).
]

If that can be shown to force repeated visits to damped modes within (O(c^A)) steps, the polylog H23a gap follows.
