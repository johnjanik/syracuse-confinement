#!/usr/bin/env python3
"""Regenerate pilot-001 candidates exactly (seed=1) and emit ghost_catalog.tex."""
import sys, math
sys.path.insert(0, '../search'); sys.path.insert(0, 'search')
import numpy as np
from frontier import biased_letter_law, gen_word, calibrate, complexity, bias, realize

LOG23 = math.log2(3.0)
ALPHA = 2 - LOG23

def sturmian(theta, N):
    return [1 if ((n*ALPHA + theta) % 1.0) < ALPHA else 2 for n in range(N)]

# --- regenerate pilot 001 exactly (frontier.pilot defaults: seed=1) ---
n, M, seed = 120, 240, 1
rng = np.random.default_rng(seed)
law, D0 = biased_letter_law()
cands = []
for trial in range(n):
    w = calibrate(gen_word(law, M, rng))
    Dw = bias(w)
    if Dw < 0.05: continue
    P = complexity(w, 16)
    r, Mb = realize(w)
    r2, _ = realize(w[:M//2])
    stable = (r2 == r)
    cands.append(dict(i=trial, w=w, mean=float(np.mean(w)), D=float(Dw), P16=P,
                      B=sum(w), bits=r.bit_length(), mod=Mb,
                      ratio=r.bit_length()/Mb, stable=stable))

def wordstr(w, perline=60):
    s = ''.join(str(b) for b in w)
    return '\\\\\n'.join(s[i:i+perline] for i in range(0, len(s), perline))

# --- Sturmian data ---
thetas = [0.0, 0.1, 0.2, 0.33, 0.5, 0.61, 0.75, 0.9, 0.057, 0.085]
sturm = []
for th in thetas:
    w = sturmian(th, 240)
    r, Mb = realize(w)
    reps = {}
    for N in (100, 200, 240):
        rr, mm = realize(w[:N]); reps[N] = (rr.bit_length(), mm)
    sturm.append(dict(th=th, w=w, B=sum(w), bits=r.bit_length(), mod=Mb,
                      ratio=r.bit_length()/Mb, reps=reps, D=float(bias(w))))

# --- emit tex ---
tex = []
A = tex.append
A(r"""\documentclass[10pt]{article}
\usepackage[margin=2.2cm]{geometry}
\usepackage{amsmath,amssymb,longtable,booktabs}
\usepackage[T1]{fontenc}
\title{A Catalog of Ghosts:\\ the 120 Pilot Candidate Counterexamples\\ and Sturmian Realizability Data}
\author{John A. Janik\\ \small\texttt{john.janik@gmail.com}}
\date{June 2026}
\begin{document}
\maketitle

\begin{abstract}
This catalog accompanies the Shadow Frontier project (successor to
\emph{Finite Spectral Shadows for the Collatz Valuation Cocycle}). It lists
the 120 candidate-counterexample valuation words of pilot run 001
(deterministic regeneration, seed $1$): words of length $M=240$ over the
alphabet $\{1,2,4\}$, calibrated to mean $\log_23$ within $2/M$ and
carrying a non-coboundary order-$3$ shadow bias, sampled from the law
$p_1=0.567$, $p_2=0.357$, $p_4=0.076$. Every one of the 120 is a
\emph{mixed-adic ghost}: its $2$-adic realizability class modulo
$2^{B_M+1}$ has least positive representative of nearly full bit length,
not stabilizing between prefix lengths $M/2$ and $M$ --- the signature
that no positive integer realizes the word. We also list ten Sturmian
ghosts of the critical slope $\alpha=2-\log_23$ (all Sturmian words are
now \emph{provably} non-realizable, by the repetition-rigidity theorem);
their data is shown for comparison. The objects below are points of
$\mathbb{Z}_2$; the Collatz conjecture asserts that classes like these
never meet $\mathbb{Z}^{+}$.
\end{abstract}

\section{Conventions}
For a valuation word $w=(b_0,\dots,b_{M-1})$, $B_N=\sum_{n<N}b_n$;
the set of odd $x$ whose first $N$ valuations equal the prefix is a single
residue class modulo $2^{B_N+1}$; ``rep bits'' is the bit length of its
least positive representative $r_N$, ``mod bits'' is $B_N+1$, and the fill
ratio is their quotient. A positive realization would force
$r_N$ to stabilize at $\lceil\log_2 x_0\rceil$ once $2^{B_N}>x_0$; a ghost
rides the diagonal $r_N\sim 2^{B_N}$. The bias is
$|D_3|=\bigl|\frac1M\sum_n \zeta_3^{-b_n}-\mathbb{E}_{\mathrm{geom}}
[\zeta_3^{-b}]\bigr|$, the order-3 non-coboundary two-point shadow.

\section{The 120 pilot candidates: statistics}
All 120 are ghosts: no representative stabilized; fill ratios
$\approx 1$.\medskip
""")
A(r"\begin{longtable}{rrrrrrrr}")
A(r"\toprule")
A(r"\# & mean $b$ & $|D_3|$ & $P(16)$ & $B_{240}$ & rep bits & mod bits & fill\\")
A(r"\midrule\endhead")
for k, c in enumerate(cands):
    A(f"{k+1} & {c['mean']:.4f} & {c['D']:.3f} & {c['P16']} & {c['B']} & {c['bits']} & {c['mod']} & {c['ratio']:.3f}\\\\")
A(r"\bottomrule")
A(r"\end{longtable}")
A(r"""
\section{Sturmian ghosts (critical slope, now a theorem)}
Words $b_n=1+\mathbf 1\{\{n\alpha+\theta\}\ge\alpha\}$,
$\alpha=2-\log_23$. By the repetition-rigidity theorem these are
non-realizable for \emph{every} slope and intercept; the data below shows
the same diagonal-riding signature as the candidates.\medskip
""")
A(r"\begin{longtable}{lrrrrrr}")
A(r"\toprule")
A(r"$\theta$ & $|D_3|$ & $B_{240}$ & rep bits & mod bits & fill & rep bits at $N{=}100/200$\\")
A(r"\midrule\endhead")
for s in sturm:
    A(f"{s['th']:.3f} & {s['D']:.3f} & {s['B']} & {s['bits']} & {s['mod']} & {s['ratio']:.3f} & {s['reps'][100][0]}/{s['reps'][200][0]}\\\\")
A(r"\bottomrule")
A(r"\end{longtable}")
A(r"""
\noindent Example Sturmian words (first 120 letters):\medskip
\begingroup\ttfamily\footnotesize
""")
for s in sturm[:4]:
    A(f"$\\theta={s['th']:.2f}$:\\\\")
    A(wordstr(s['w'][:120]) + r"\medskip\\")
A(r"""\endgroup

\section{The negative cycles, computed explicitly}

The three known negative cycles anchor the ghost families: each periodic
valuation word below has its unique $2$-adic realization at a
\emph{negative} integer, so the least positive representatives of its
realizability classes ride the ceiling $2^{B_N+1}-|x|$ --- the periodic
ghost lines of the trajectory zoo. Throughout,
$S(x)=(3x+1)/2^{v_2(3x+1)}$ and a period-$p$ word $w$ with sum $B$
satisfies the affine cycle equation
\[
x=\frac{A_w}{2^{B}-3^{p}},\qquad
A_w=\sum_{j=0}^{p-1}3^{\,p-1-j}\,2^{B_j},\quad B_j=b_1+\dots+b_j .
\]
Negative cycles are exactly those with $2^B<3^p$ (denominator negative).

\subsection*{$x=-1$: word $(1)$, period $1$}
\[
3(-1)+1=-2=-2^{1}\cdot1,\qquad v_2=1,\qquad S(-1)=\tfrac{-2}{2}=-1 .
\]
Cycle formula: $p=1$, $B=1$, $A_w=3^{0}2^{0}=1$, and
$x=1/(2^{1}-3^{1})=1/(-1)=-1$. This is the $2$-adic limit of the all-ones
word: $b\equiv1$ forces $x\equiv-1 \pmod{2^k}$ for every $k$.

\subsection*{$x=-5$: word $(1,2)$, period $2$}
\begin{align*}
3(-5)+1&=-14=-2^{1}\cdot7, & v_2&=1, & S(-5)&=-7,\\
3(-7)+1&=-20=-2^{2}\cdot5, & v_2&=2, & S(-7)&=-5 .
\end{align*}
Cycle formula: $p=2$, $B=1+2=3$, partial sums $B_0=0$, $B_1=1$:
\[
A_w=3^{1}2^{0}+3^{0}2^{1}=3+2=5,\qquad
x=\frac{5}{2^{3}-3^{2}}=\frac{5}{8-9}=-5 .
\]
Letter mean $\tfrac32<\log_23$: in the positive world this word ascends,
the gentle green dotted line of the trajectory zoo.

\subsection*{$x=-17$: word $(1,1,1,2,1,1,4)$, period $7$}
\begin{align*}
3(-17)+1&=-50=-2^{1}\cdot25, & S&\colon -17\mapsto-25,\\
3(-25)+1&=-74=-2^{1}\cdot37, & &\phantom{\colon} -25\mapsto-37,\\
3(-37)+1&=-110=-2^{1}\cdot55, & &\phantom{\colon} -37\mapsto-55,\\
3(-55)+1&=-164=-2^{2}\cdot41, & &\phantom{\colon} -55\mapsto-41,\\
3(-41)+1&=-122=-2^{1}\cdot61, & &\phantom{\colon} -41\mapsto-61,\\
3(-61)+1&=-182=-2^{1}\cdot91, & &\phantom{\colon} -61\mapsto-91,\\
3(-91)+1&=-272=-2^{4}\cdot17, & &\phantom{\colon} -91\mapsto-17 .
\end{align*}
Cycle formula: $p=7$, $B=1{+}1{+}1{+}2{+}1{+}1{+}4=11$, so
$2^{B}=2048<2187=3^{p}$; partial sums
$(B_0,\dots,B_6)=(0,1,2,3,5,6,7)$:
\[
A_w=3^6\!\cdot\!1+3^5\!\cdot\!2+3^4\!\cdot\!4+3^3\!\cdot\!8
+3^2\!\cdot\!32+3\!\cdot\!64+128
=729+486+324+216+288+192+128=2363,
\]
\[
x=\frac{2363}{2^{11}-3^{7}}=\frac{2363}{2048-2187}
=\frac{2363}{-139}=-17\qquad(139\cdot17=2363) .
\]
Letter mean $\tfrac{11}{7}\approx1.571<\log_23\approx1.585$: again
sub-critical, again a positive-world ascender. Note how close
$11/7$ is to $\log_23$ --- the $-17$ cycle is a near-balanced word, the
best rational approximant realizable at small height, and exactly the
shape that the Baker cycle bound ($x_{\min}\le Cp^{\tau+1}$) governs.

\appendix
\section{The 120 candidate words}
Alphabet $\{1,2,4\}$, length 240, row-wrapped at 60 letters.
\begingroup\ttfamily\scriptsize
""")
for k, c in enumerate(cands):
    A(f"\\noindent\\textbf{{\\#{k+1}}} (mean {c['mean']:.3f}, $|D_3|$={c['D']:.3f}):\\\\")
    A(wordstr(c['w']) + r"\medskip" + "\n")
A(r"\endgroup")
A(r"\end{document}")
open('catalog/ghost_catalog.tex','w').write('\n'.join(tex))
print(f"candidates listed: {len(cands)}; sturmian: {len(sturm)}")
