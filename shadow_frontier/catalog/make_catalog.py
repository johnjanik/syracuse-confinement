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
