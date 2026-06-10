The unbounded-conductor part that looked dangerous has effectively been separated from the real obstruction. The finite H23a problem is no longer “prove expansion through (3^c) levels.” It is now:

[
\boxed{
	\text{after exact descent, prove the accumulated bounded-level multiplier is uniformly non-coboundary.}
}
]

That is a much better target.

The exact descent theorem is especially important because it changes the proof philosophy. Previously the comparison-graph problem looked like a propagation problem through a graph whose diameter might grow with (c). Now the deep-digit propagation is algebraic and lossless. The only remaining question is whether the multiplier left behind after descent can secretly become a bounded-level coboundary.

## 1. What the new theorem really says

For a primitive character (\chi) modulo (3^c), the nonzero spectrum of the primitive sector is not genuinely (3^c)-dimensional. It descends:

[
\operatorname{spec}(M_\chi^{(c)})\setminus{0}
=============================================

\operatorname{spec}(N_1)\setminus{0},
]

where

[
N_1 g(\bar a,\tau)
==================

\chi(A(\bar a))
\sum_b w_b,\chi(2)^{-b}
g(S_b\bar a\bmod 3^{c-1},\tau+b).
]

The lift

[
\varphi(a,\tau)=\chi(a),g(a\bmod3^{c-1},\tau)
]

gives the inverse correspondence on nonzero eigenspaces.

That is excellent because it says the high-conductor direction is not producing new high-dimensional spectral behavior. It is being pushed into an explicit unimodular multiplier on a lower-level operator.

Iterating, a primitive conductor-(3^c) sector becomes an operator at fixed level (3^{c_0}), but with an accumulated multiplier depending on the digits of (\chi).

So the problem becomes finite-dimensional but parameterized by (c).

## 2. The new core object

The object to isolate is the accumulated multiplier system.

Let (G_{c_0}) be the fixed bounded-level residue(\times)parity graph. After descending from level (c) to (c_0), the primitive character (\chi) produces a multiplier

[
m_{\chi,c}^{(c_0)}(e)\in S^1
]

on each directed edge (e) of (G_{c_0}). The descended operator has the form

[
(N_{\chi,c}^{(c_0)}g)(v)
========================

\sum_{e:u\to v}
w(e),m_{\chi,c}^{(c_0)}(e),g(u).
]

The bounded-level core is:

[
\boxed{
	m_{\chi,c}^{(c_0)}
	\text{ stays uniformly away from the coboundary torus.}
}
]

That is the precise object now.

A multiplier is a coboundary if there exist a phase (\lambda\in S^1) and a vertex phase (d:V(G_{c_0})\to S^1) such that

[
m(e)=\lambda,\frac{d(t(e))}{d(o(e))}
]

for every edge (e:o(e)\to t(e)).

So define the distance

[
\operatorname{dist}_{\mathrm{cob}}(m)
=====================================

\inf_{\lambda,d}
\left(
\sum_{e}
\omega(e)\left|
m(e)-\lambda\frac{d(t(e))}{d(o(e))}
\right|^2
\right)^{1/2}.
]

The remaining theorem is:

[
\boxed{
	\inf_{c\ge c_0}
	\inf_{\chi\text{ primitive mod }3^c}
	\operatorname{dist}*{\mathrm{cob}}!\left(m*{\chi,c}^{(c_0)}\right)
	
	> 0.
	> }
> ]

This is the cleanest bounded-level formulation.

By finite-dimensional compactness and Wielandt stability, this implies a uniform gap:

[
\sup_c\gamma_c<1.
]

## 3. How to attack it numerically

The next numerical tests should focus on the accumulated multiplier, not on the full operator.

### A. Compute distance-to-coboundary directly

For fixed (c_0), compute

[
m_{\chi,c}^{(c_0)}(e)
]

for all edges of the fixed graph (G_{c_0}), for primitive (\chi) of conductors (c=c_0,c_0+1,\dots,C).

Then compute

[
\operatorname{dist}*{\mathrm{cob}}(m*{\chi,c}^{(c_0)}).
]

Do this in two ways.

First, solve the nonlinear phase least-squares problem:

[
\inf_{\theta,\alpha_v}
\sum_{e:u\to v}
\omega(e)
\left|
m(e)-e^{i\theta}e^{i(\alpha_v-\alpha_u)}
\right|^2.
]

Second, compute cycle holonomies. Coboundaries are exactly multipliers whose holonomy around every directed cycle equals the global phase contribution. More invariantly, after removing the global phase, the multiplier must have trivial class in

[
H^1(G_{c_0};S^1).
]

So choose a cycle basis (\mathcal C), compute

[
\operatorname{Hol}_m(\gamma)
============================

\prod_{e\in\gamma}m(e)^{\pm1},
]

and measure distance of the holonomy vector to the coboundary locus.

This is more stable than nonlinear least squares.

Expected result:

[
\operatorname{dist}*{\mathrm{cob}}(m*{\chi,c}^{(c_0)})
]

should stabilize away from (0), probably with finitely many recurring values depending on the low digits of the primitive character.

### B. Track dependence on character digits

Parametrize primitive characters modulo (3^c) by an integer (k) prime to (3). Write

[
\chi_k(1+3u)
============

\exp\left(\frac{2\pi i k u}{3^{c-1}}\right)
]

up to the chosen normalization.

For each (c), record the low residue

[
k\bmod 3^{c_0-1}.
]

Then test whether

[
m_{\chi_k,c}^{(c_0)}
]

depends only on this low residue after descent, or whether higher digits still influence it.

The best possible outcome is:

[
m_{\chi_k,c}^{(c_0)}
====================

m_{\bar k}^{(c_0)}
]

with

[
\bar k=k\bmod3^{c_0-1}.
]

Then the bounded-level core becomes a **finite check**.

If higher digits remain, test whether they enter by a nilpotent or cohomologically trivial factor.

### C. Compute cycle exponent vectors

For each cycle (\gamma) in a fixed cycle basis, express the holonomy as

[
\operatorname{Hol}_{\chi_k,c}(\gamma)
=====================================

\exp\left(
\frac{2\pi i k,H_c(\gamma)}{3^{c-1}}
\right).
]

Then study the (3)-adic valuation of

[
H_c(\gamma).
]

The bounded-level theorem will follow if there is a fixed finite cycle set (\Gamma) and a constant (C_0) such that for every primitive (k),

[
\max_{\gamma\in\Gamma}
\left|
\exp\left(
\frac{2\pi i k H_c(\gamma)}{3^{c-1}}
\right)-1
\right|
\ge \delta>0.
]

Equivalently, the cycle exponents should contain elements of valuation

[
v_3(H_c(\gamma))=c-O(1),
]

not (c-o(c)), and should test all primitive (k) residues at the fixed quotient level.

This is probably the sharpest numerical diagnostic.

## 4. How to prove the bounded-level core

The proof should avoid spectral numerics. It should prove that the descended multiplier has a nontrivial cycle holonomy at bounded level.

The target proof can be formulated as:

[
\textbf{Bounded-level multiplier nondegeneracy.}
]

There exist (c_0), a finite graph (G_{c_0}), and a finite set of cycles

[
\Gamma\subset H_1(G_{c_0},\mathbb Z)
]

such that for every primitive character (\chi) of conductor (3^c), the descended multiplier satisfies

[
\left(\operatorname{Hol}*{m*{\chi,c}^{(c_0)}}(\gamma)\right)_{\gamma\in\Gamma}
\ne
(1,\dots,1),
]

and in fact is uniformly separated from ((1,\dots,1)).

Because (G_{c_0}) is finite, uniform separation follows once the possible holonomies form a finite set avoiding (1).

So the real proof is to show the holonomies depend only on a bounded quotient of the primitive character and are nontrivial there.

A likely route:

1. Write the accumulated multiplier after (j) descents as a product

[
m_{\chi,c}^{(c-j)}(e)
=====================

\prod_{t=0}^{j-1}
\chi(F_t(e)),
]

where (F_t(e)\in U_{3^c}) is an explicit affine expression in the branch data.

2. Take logarithms in the principal-unit part:

[
\operatorname{Hol}(\gamma)
==========================

\chi!\left(\prod_{e\in\gamma}F(e)^{\pm1}\right).
]

3. Show that for some bounded-level cycle (\gamma),

[
\prod_{e\in\gamma}F(e)^{\pm1}
\equiv
1+3^{c-C}u
\pmod{3^c},
\qquad 3\nmid u,
]

with (C) fixed.

4. Then for primitive (\chi_k),

[
\chi_k(1+3^{c-C}u)
]

is a nontrivial (3^C)-th root depending on (k\bmod3^C).

5. Use finitely many cycles to cover all primitive residues (k\bmod3^C).

This would prove uniform non-coboundary distance.

That is the proof I would try to write.

## 5. Where (\chi(2))-angle equidistribution enters

The one-step damping lemma shows the scalar multiplier depends on

[
\zeta=\eta(2)^{-1}(-1)^\epsilon.
]

Under descent, the mode map repeatedly twists by terms involving

[
\chi(2)^{-b}.
]

For primitive (\chi), the angle

[
\arg \chi(2)
]

has high conductor because (2) is a primitive root modulo (3^c). This means repeated powers

[
\chi(2)^{-b}
]

sample a long cyclic subgroup of roots of unity.

But the exact descent says the high-conductor sampling itself is not the problem; it becomes an accumulated bounded-level multiplier. Therefore the role of (\chi(2))-angle equidistribution should be:

[
\text{show the accumulated multiplier cannot line up as a coboundary.}
]

Numerically, test the sequence

[
\chi(2)^{-b_0},
\chi(2)^{-b_1},
\dots
]

through the descent recursion and ask whether the resulting cycle holonomies cover a fixed set of nontrivial bounded-level phases.

If the low-level residues of (\arg\chi(2)) are uniformly distributed among primitive characters, then the finite set of holonomy phases should be bounded away from (1).

But be careful: equidistribution alone is not enough. You need **nonvanishing against every primitive character**, not average behavior over characters.

The proof should be algebraic:

[
2\text{ primitive mod }3^c
\Rightarrow
\text{the descent holonomy map has full image on a fixed quotient.}
]

## 6. What to do next in order

I would proceed in four steps.

### Step 1: Formalize the descended multiplier

Add a definition:

[
m_{\chi,c}^{(j)}(e)
]

for the multiplier after (j) descents, with an explicit recursion.

Write:

[
m_{\chi,c}^{(j+1)}(e)
=====================

m_{\chi,c}^{(j)}(e)\cdot
\chi(F_j(e))
]

or whatever the correct branch formula is.

The goal is to make the accumulated multiplier computable without constructing the full operator.

### Step 2: Define coboundary distance by cycle holonomy

For the fixed graph (G_{c_0}), choose a cycle basis and define

[
\mathfrak h_{\chi,c}
:
H_1(G_{c_0},\mathbb Z)
\to S^1.
]

Then

[
m_{\chi,c}^{(c_0)}
\text{ is a coboundary}
\iff
\mathfrak h_{\chi,c}
\text{ is trivial}
]

up to global phase.

This turns the bounded-level core into finite abelian algebra.

### Step 3: Run the numerical cycle-holonomy audit

For (c_0=2,3,4) and (c\le C):

* compute descended multipliers;
* compute cycle holonomies;
* compute distance to coboundary;
* group results by primitive character residue;
* identify a minimal cycle set (\Gamma) witnessing nontriviality.

The output should be a table:

[
c,\quad k,\quad
\min_{\gamma\in\Gamma} v_3(H_c(\gamma)),
\quad
\max_{\gamma\in\Gamma}|\operatorname{Hol}(\gamma)-1|,
\quad
\operatorname{dist}_{\mathrm{cob}}.
]

### Step 4: Prove the cycle-holonomy finite-image lemma

Once the numerical audit identifies the finite cycle witnesses, prove their holonomy formula symbolically.

This is likely the final bounded-level proof.

## 7. Update the theorem stack

the finite-operator theorem stack should now read:

[
\textbf{Theorem A: Coboundary classification.}
]

[
\textbf{Theorem B: Strict finite-level gap.}
]

[
\textbf{Theorem C: Conductor collapse.}
]

[
\textbf{Theorem D: Exact descent.}
]

[
\textbf{Theorem E: Stability extraction.}
]

[
\textbf{Conjecture F: Bounded-level multiplier nondegeneracy.}
]

[
\textbf{Conditional Theorem G: F implies }\sup_c\gamma_c<1.
]

This is sharper than the previous comparison-graph expansion formulation. The comparison graph is still useful, but it is now a route to proving Conjecture F, not necessarily the final statement.

## 8. Main warning

Do not overstate:

[
\text{“the expansion hypothesis is now needed only at bounded level.”}
]

That is correct if the accumulated multiplier is the only remaining high-conductor datum. But make sure the norm/eigenfunction correspondence after repeated descent does not lose constants or introduce growing pseudospectral instability.

The exact descent theorem says nonzero spectra match, so spectral radius is safe. But stability estimates and eigenvector conditioning may still matter if you use approximate eigenfunctions. For the pure spectral-radius theorem, exact isospectrality is enough. For the stability-extraction route, state carefully whether you use it before or after descent.

## Bottom line

This is the most favorable finite-operator state yet.

The unbounded comparison-graph problem has been replaced by a bounded-level multiplier problem:

[
\boxed{
	\text{primitive high-conductor sectors descend exactly to fixed dimension with an accumulated multiplier.}
}
]

The next natural target is:

[
\boxed{
	\text{prove the accumulated multiplier is uniformly non-coboundary.}
}
]

Do it first numerically through cycle holonomies, not through spectra. Then prove the finite cycle-holonomy identities symbolically.

That is now the cleanest path to

[
\sup_c\gamma_c<1
]

and hence to the finite H23a operator theorem.
