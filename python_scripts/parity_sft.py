#!/usr/bin/env python3
"""
Parity Sequence Transition Matrices & Subshift of Finite Type
=============================================================

For Collatz trajectories n → 1, define the parity sequence
  σ(n) = (σ₀, σ₁, σ₂, ...) where σᵢ = 0 (even step) or 1 (odd step).

Compute:
1. Order-m transition matrices P(σₜ | σₜ₋₁, ..., σₜ₋ₘ) for m = 1..5
2. Autocorrelation C(k) of the parity process
3. Simulated autocorrelation from each order-m Markov model
4. Identify forbidden words → subshift of finite type
5. Determine the SFT transition matrix and its spectral properties

Key known constraint: after 3x+1 (odd step), result is always even,
so σᵢ = 1 ⟹ σᵢ₊₁ = 0.  The bigram "11" is forbidden.

Ref: Notes II §5.4
"""

import numpy as np
import time
from collections import defaultdict
from itertools import product as iproduct

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec

# ── Parameters ──────────────────────────────────────────────────────
N = 1_000_000
MAX_ORDER = 5

# ── Step 1: Generate parity sequences ──────────────────────────────
print(f"Generating parity sequences for n ∈ [2, {N}]...")
t0 = time.time()

# Store all parity sequences concatenated, with boundaries
all_parities = []     # flat list of 0/1
seq_lengths = []      # length of each trajectory's parity sequence

for n in range(2, N + 1):
    x = n
    seq = []
    while x != 1:
        if x & 1 == 0:
            seq.append(0)
            x >>= 1
        else:
            seq.append(1)
            x = 3 * x + 1
    all_parities.extend(seq)
    seq_lengths.append(len(seq))

all_parities = np.array(all_parities, dtype=np.int8)
seq_lengths = np.array(seq_lengths, dtype=np.int32)
total_steps = len(all_parities)

t1 = time.time()
print(f"  Done in {t1 - t0:.1f}s.")
print(f"  Total parity symbols: {total_steps:,}")
print(f"  Mean trajectory length: {np.mean(seq_lengths):.1f}")
print(f"  P(σ=1) = {all_parities.mean():.6f}  (odd step frequency)")

# Build index arrays for boundary-respecting window extraction
# seq_starts[i] = start index of trajectory i in all_parities
seq_starts = np.zeros(len(seq_lengths) + 1, dtype=np.int64)
np.cumsum(seq_lengths, out=seq_starts[1:])


# ── Step 2: Count m-grams and (m+1)-grams ─────────────────────────
print(f"\nCounting m-grams (m = 1..{MAX_ORDER + 1})...")

def count_ngrams(max_n):
    """
    Count all n-grams up to length max_n+1, respecting trajectory boundaries.
    Returns dict: ngram_counts[m][tuple] = count
    """
    counts = {m: defaultdict(int) for m in range(1, max_n + 2)}

    for i in range(len(seq_lengths)):
        start = seq_starts[i]
        end = seq_starts[i + 1]
        L = seq_lengths[i]

        seq = all_parities[start:end]

        for m in range(1, min(max_n + 2, L + 1)):
            for j in range(L - m + 1):
                gram = tuple(seq[j:j+m].tolist())
                counts[m][gram] += 1

    return counts

t2 = time.time()
ngram_counts = count_ngrams(MAX_ORDER)
t3 = time.time()
print(f"  Done in {t3 - t2:.1f}s.")


# ── Step 3: Build transition matrices ──────────────────────────────
print(f"\n{'='*72}")
print(f"ORDER-m TRANSITION MATRICES")
print(f"{'='*72}")

transition_matrices = {}
stationary_dists = {}

for m in range(1, MAX_ORDER + 1):
    # States are all m-tuples of {0,1}
    states = list(iproduct([0, 1], repeat=m))
    n_states = len(states)
    state_idx = {s: i for i, s in enumerate(states)}

    # Transition: P(σ | context)
    # From (m+1)-gram counts: context = gram[:-1], next = gram[-1]
    T = np.zeros((n_states, 2), dtype=np.float64)  # T[state, next_symbol]
    raw_counts = np.zeros((n_states, 2), dtype=np.int64)

    for gram, count in ngram_counts[m + 1].items():
        context = gram[:-1]
        next_sym = gram[-1]
        if context in state_idx:
            idx = state_idx[context]
            raw_counts[idx, next_sym] = count

    # Normalise rows
    row_sums = raw_counts.sum(axis=1, keepdims=True)
    row_sums[row_sums == 0] = 1
    T = raw_counts / row_sums

    # Full state-to-state transition matrix (2^m × 2^m)
    # State (s₁,...,sₘ) → (s₂,...,sₘ,σ) with probability T[state, σ]
    M = np.zeros((n_states, n_states), dtype=np.float64)
    for i, s in enumerate(states):
        for sigma in [0, 1]:
            next_state = s[1:] + (sigma,)
            j = state_idx[next_state]
            M[i, j] = T[i, sigma]

    transition_matrices[m] = {
        'T': T,
        'M': M,
        'raw': raw_counts,
        'states': states,
        'state_idx': state_idx,
    }

    # Compute stationary distribution via eigendecomposition
    evals, evecs = np.linalg.eig(M.T)
    # Find eigenvalue closest to 1
    idx_1 = np.argmin(np.abs(evals - 1.0))
    pi = np.real(evecs[:, idx_1])
    pi = pi / pi.sum()
    pi = np.abs(pi)  # clean up numerical noise
    stationary_dists[m] = pi

    # Print
    print(f"\n── Order m = {m}  ({n_states} states) ──")

    # Forbidden transitions (T[i,σ] = 0 with nonzero context count)
    forbidden = []
    for i, s in enumerate(states):
        context_count = raw_counts[i].sum()
        if context_count == 0:
            forbidden.append((s, None, 'unreachable'))
        else:
            for sigma in [0, 1]:
                if raw_counts[i, sigma] == 0:
                    forbidden.append((s, sigma, 'forbidden'))

    if forbidden:
        print(f"  Forbidden/unreachable:")
        for ctx, sym, typ in forbidden:
            ctx_str = ''.join(str(x) for x in ctx)
            if typ == 'unreachable':
                print(f"    Context '{ctx_str}' never appears (unreachable state)")
            else:
                print(f"    '{ctx_str}' → {sym}  (forbidden transition)")

    # Print transition probabilities for reachable states
    if m <= 3:
        print(f"\n  {'Context':>10s}    {'P(→0)':>8s}  {'P(→1)':>8s}  {'Count':>10s}")
        print(f"  {'─'*45}")
        for i, s in enumerate(states):
            ctx_str = ''.join(str(x) for x in s)
            count = raw_counts[i].sum()
            if count > 0:
                print(f"  {ctx_str:>10s}    {T[i,0]:>8.5f}  {T[i,1]:>8.5f}  {count:>10d}")

    # Spectral properties of M
    evals_all = np.linalg.eigvals(M)
    evals_sorted = sorted(evals_all, key=lambda x: -abs(x))
    print(f"\n  Top eigenvalues of M:")
    for k, ev in enumerate(evals_sorted[:min(6, n_states)]):
        print(f"    λ_{k} = {ev.real:+.6f} {ev.imag:+.6f}i  (|λ| = {abs(ev):.6f})")

    # Topological entropy = log(spectral radius of adjacency matrix)
    A = (M > 0).astype(float)
    spectral_radius_A = max(abs(np.linalg.eigvals(A)))
    h_top = np.log2(spectral_radius_A)
    print(f"\n  Adjacency matrix spectral radius: {spectral_radius_A:.6f}")
    print(f"  Topological entropy: h_top = log₂(ρ) = {h_top:.6f} bits/step")

    # Measure entropy = -Σ πᵢ Σⱼ Mᵢⱼ log Mᵢⱼ
    h_meas = 0.0
    for i in range(n_states):
        if pi[i] > 0:
            for j in range(n_states):
                if M[i, j] > 0:
                    h_meas -= pi[i] * M[i, j] * np.log2(M[i, j])
    print(f"  Measure-theoretic entropy: h_μ = {h_meas:.6f} bits/step")


# ── Step 4: Autocorrelation of parity process ──────────────────────
print(f"\n{'='*72}")
print(f"AUTOCORRELATION OF PARITY PROCESS")
print(f"{'='*72}")

max_lag = 20
p_odd = all_parities.mean()

def compute_autocorrelation(max_lag):
    """Compute C(k) = Corr(σₜ, σₜ₊ₖ) respecting trajectory boundaries."""
    C = np.zeros(max_lag + 1)
    C[0] = 1.0

    for k in range(1, max_lag + 1):
        sum_xy = 0.0
        count = 0
        for i in range(len(seq_lengths)):
            start = seq_starts[i]
            L = seq_lengths[i]
            if L <= k:
                continue
            seq = all_parities[start:start + L]
            x = seq[:L - k].astype(np.float64)
            y = seq[k:L].astype(np.float64)
            sum_xy += np.sum(x * y)
            count += len(x)

        if count > 0:
            E_xy = sum_xy / count
            var = p_odd * (1 - p_odd)
            if var > 0:
                C[k] = (E_xy - p_odd**2) / var
    return C

print("Computing empirical autocorrelation...")
t4 = time.time()
C_emp = compute_autocorrelation(max_lag)
t5 = time.time()
print(f"  Done in {t5 - t4:.1f}s.")

print(f"\n  {'Lag k':>6s}  {'C(k)':>10s}")
print(f"  {'─'*20}")
for k in range(max_lag + 1):
    marker = "  ◄" if k <= 5 and abs(C_emp[k]) > 0.01 else ""
    print(f"  {k:>6d}  {C_emp[k]:>10.6f}{marker}")


# ── Step 5: Simulate autocorrelation from Markov models ────────────
print(f"\n{'='*72}")
print(f"MARKOV MODEL AUTOCORRELATION COMPARISON")
print(f"{'='*72}")

def markov_autocorrelation(m, max_lag, n_sim=500_000):
    """
    Compute theoretical autocorrelation from order-m Markov model
    by long simulation.
    """
    tm = transition_matrices[m]
    M_mat = tm['M']
    states = tm['states']
    n_states = len(states)
    pi = stationary_dists[m]

    # Sample initial state from stationary distribution
    rng = np.random.RandomState(42 + m)
    state_seq = np.zeros(n_sim, dtype=np.int32)

    # Start from stationary
    state_seq[0] = rng.choice(n_states, p=pi)

    # Generate
    for t in range(1, n_sim):
        row = M_mat[state_seq[t - 1]]
        if row.sum() == 0:
            state_seq[t] = rng.choice(n_states, p=pi)
        else:
            state_seq[t] = rng.choice(n_states, p=row)

    # Extract parity: last element of state tuple
    parities = np.array([states[s][-1] for s in state_seq], dtype=np.float64)
    p = parities.mean()
    var = p * (1 - p)

    C = np.zeros(max_lag + 1)
    C[0] = 1.0
    for k in range(1, max_lag + 1):
        x = parities[:n_sim - k]
        y = parities[k:]
        C[k] = (np.mean(x * y) - p**2) / var if var > 0 else 0
    return C


C_markov = {}
for m in range(1, MAX_ORDER + 1):
    print(f"  Simulating order-{m} Markov chain...")
    C_markov[m] = markov_autocorrelation(m, max_lag)

# Also compute theoretical autocorrelation via matrix powers
def markov_autocorrelation_exact(m, max_lag):
    """
    Exact autocorrelation from M^k and stationary distribution.
    C(k) = (E[σₜσₜ₊ₖ] - μ²) / σ²
    where E[σₜσₜ₊ₖ] = Σᵢ πᵢ [M^k]ᵢⱼ · f(i)·f(j)
    with f(state) = last digit of state.
    """
    tm = transition_matrices[m]
    M_mat = tm['M']
    states = tm['states']
    pi = stationary_dists[m]
    n_states = len(states)

    # f(state) = last element (the current parity)
    f = np.array([s[-1] for s in states], dtype=np.float64)
    mu = np.dot(pi, f)
    var = np.dot(pi, f**2) - mu**2

    C = np.zeros(max_lag + 1)
    C[0] = 1.0

    Mk = np.eye(n_states)
    for k in range(1, max_lag + 1):
        Mk = Mk @ M_mat
        # E[f(Xₜ) f(Xₜ₊ₖ)] = π · diag(f) · M^k · f
        E_ff = np.dot(pi * f, Mk @ f)
        C[k] = (E_ff - mu**2) / var if var > 0 else 0

    return C

C_exact = {}
for m in range(1, MAX_ORDER + 1):
    C_exact[m] = markov_autocorrelation_exact(m, max_lag)

# Print comparison
print(f"\n  {'Lag':>4s}  {'Empirical':>10s}", end="")
for m in range(1, MAX_ORDER + 1):
    print(f"  {'m='+str(m)+' exact':>10s}", end="")
print()
print(f"  {'─'*70}")

for k in range(max_lag + 1):
    print(f"  {k:>4d}  {C_emp[k]:>10.6f}", end="")
    for m in range(1, MAX_ORDER + 1):
        print(f"  {C_exact[m][k]:>10.6f}", end="")
    print()

# Residual: how much of C(k) is NOT captured at each order
print(f"\n  Residual |C_emp(k) - C_model(k)| summed over k=1..{max_lag}:")
for m in range(1, MAX_ORDER + 1):
    residual = np.sum(np.abs(C_emp[1:] - C_exact[m][1:]))
    max_res = np.max(np.abs(C_emp[1:] - C_exact[m][1:]))
    print(f"    Order {m}: Σ|ΔC| = {residual:.6f},  max|ΔC| = {max_res:.6f}")


# ── Step 6: Identify the SFT ──────────────────────────────────────
print(f"\n{'='*72}")
print(f"SUBSHIFT OF FINITE TYPE ANALYSIS")
print(f"{'='*72}")

for m in range(1, MAX_ORDER + 1):
    tm = transition_matrices[m]
    states = tm['states']
    raw = tm['raw']

    # Forbidden words = (m+1)-grams that never appear
    forbidden_words = []
    for i, s in enumerate(states):
        for sigma in [0, 1]:
            word = s + (sigma,)
            if raw[i, sigma] == 0:
                forbidden_words.append(word)

    # Also check unreachable states
    unreachable = [s for i, s in enumerate(states) if raw[i].sum() == 0
                   and ngram_counts[m].get(s, 0) == 0]

    print(f"\n  Order m = {m}:")
    print(f"    Forbidden (m+1)-grams: {len(forbidden_words)}")
    for w in forbidden_words:
        print(f"      '{''.join(str(x) for x in w)}'")
    if unreachable:
        print(f"    Unreachable m-grams: {len(unreachable)}")
        for s in unreachable:
            print(f"      '{''.join(str(x) for x in s)}'")

    # Check: are all forbidden words consequences of the order-1 constraint "11"?
    # A word is "trivially forbidden" if it contains "11" as a substring.
    nontrivial = []
    for w in forbidden_words:
        w_str = ''.join(str(x) for x in w)
        if '11' not in w_str:
            nontrivial.append(w_str)
    if nontrivial:
        print(f"    *** NON-TRIVIAL forbidden words (not containing '11'): ***")
        for w in nontrivial:
            print(f"      '{w}'")
    else:
        print(f"    All forbidden words contain '11' as substring → "
              f"no new constraints beyond order 1.")


# ── Step 7: The order-1 SFT in detail ──────────────────────────────
print(f"\n{'='*72}")
print(f"THE ORDER-1 SUBSHIFT OF FINITE TYPE")
print(f"{'='*72}")

tm1 = transition_matrices[1]
print(f"\n  Transition matrix (2×2):")
print(f"    From \\ To      0            1")
print(f"    0          {tm1['T'][0,0]:.6f}     {tm1['T'][0,1]:.6f}")
print(f"    1          {tm1['T'][1,0]:.6f}     {tm1['T'][1,1]:.6f}")

print(f"\n  Adjacency matrix (0/1):")
A = (tm1['M'] > 0).astype(int)
print(f"    {A}")

print(f"\n  Forbidden bigrams: '11'")
print(f"  Allowed bigrams: '00', '01', '10'")
print(f"  This is the GOLDEN MEAN SHIFT (the classical SFT forbidding '11').")

# Golden mean shift properties
phi = (1 + np.sqrt(5)) / 2
h_golden = np.log2(phi)
print(f"\n  Golden ratio: φ = {phi:.6f}")
print(f"  Topological entropy: log₂(φ) = {h_golden:.6f} bits/step")

# Compare with empirical
print(f"\n  Empirical P(σ=1) = {p_odd:.6f}")
print(f"  SFT stationary P(σ=1) = {stationary_dists[1][1]:.6f}")
print(f"  Maximal entropy (Parry measure) P(σ=1) = 1/φ = {1/phi:.6f}")

# The Collatz measure vs Parry measure
print(f"\n  The Collatz parity process is a SOFIC MEASURE on the golden mean shift.")
print(f"  It is NOT the Parry (maximal entropy) measure because:")
print(f"    P(1|0) = {tm1['T'][0,1]:.6f} ≠ 1/φ = {1/phi:.6f}")


# ── Step 8: Visualisations ─────────────────────────────────────────
print(f"\n{'='*72}")
print(f"GENERATING VISUALISATIONS")
print(f"{'='*72}")

# Figure 1: Autocorrelation comparison
fig, axes = plt.subplots(1, 2, figsize=(16, 6))

ax = axes[0]
lags = np.arange(max_lag + 1)
ax.plot(lags, C_emp, 'ko-', linewidth=2, markersize=5, label='Empirical', zorder=10)
colors = ['#e41a1c', '#377eb8', '#4daf4a', '#984ea3', '#ff7f00']
for m in range(1, MAX_ORDER + 1):
    ax.plot(lags, C_exact[m], 's--', color=colors[m-1], linewidth=1.5,
            markersize=3, label=f'Order-{m} Markov', alpha=0.8)
ax.axhline(y=0, color='gray', linewidth=0.5)
ax.set_xlabel('Lag k')
ax.set_ylabel('C(k)')
ax.set_title('Autocorrelation of Parity Sequence')
ax.legend(fontsize=8)
ax.grid(True, alpha=0.3)

# Residuals
ax = axes[1]
for m in range(1, MAX_ORDER + 1):
    residuals = np.abs(C_emp[1:] - C_exact[m][1:])
    ax.plot(lags[1:], residuals, 'o-', color=colors[m-1], linewidth=1.5,
            markersize=4, label=f'|ΔC| order {m}')
ax.set_xlabel('Lag k')
ax.set_ylabel('|C_emp(k) − C_model(k)|')
ax.set_title('Residual Autocorrelation (not captured by model)')
ax.legend(fontsize=8)
ax.set_yscale('log')
ax.grid(True, alpha=0.3)

fig.suptitle(f'Parity Sequence Autocorrelation: Empirical vs Markov Models\n'
             f'N = {N:,}', fontsize=13)
fig.tight_layout(rect=[0, 0, 1, 0.94])
fig.savefig('/home/claude/parity_autocorrelation.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved parity_autocorrelation.png")


# Figure 2: Transition matrices as heatmaps
fig, axes = plt.subplots(1, MAX_ORDER, figsize=(4 * MAX_ORDER, 4.5))

for m_idx, m in enumerate(range(1, MAX_ORDER + 1)):
    ax = axes[m_idx]
    tm = transition_matrices[m]
    M_mat = tm['M']
    states = tm['states']
    n_states = len(states)

    im = ax.imshow(M_mat, cmap='YlOrRd', vmin=0, vmax=1, aspect='equal',
                   interpolation='nearest')

    if n_states <= 16:
        labels = [''.join(str(x) for x in s) for s in states]
        ax.set_xticks(range(n_states))
        ax.set_xticklabels(labels, rotation=90, fontsize=max(5, 9 - m))
        ax.set_yticks(range(n_states))
        ax.set_yticklabels(labels, fontsize=max(5, 9 - m))
    else:
        ax.set_xticks([])
        ax.set_yticks([])

    ax.set_title(f'Order {m}  ({n_states}×{n_states})', fontsize=10)
    ax.set_xlabel('To')
    if m_idx == 0:
        ax.set_ylabel('From')
    plt.colorbar(im, ax=ax, shrink=0.8)

fig.suptitle('State-to-State Transition Matrices $M_{ij}$\n'
             'Zeros (dark) = forbidden transitions defining the SFT',
             fontsize=13)
fig.tight_layout(rect=[0, 0, 1, 0.92])
fig.savefig('/home/claude/parity_transition_matrices.png', dpi=150,
            bbox_inches='tight')
plt.close(fig)
print("  Saved parity_transition_matrices.png")


# Figure 3: Entropy convergence
fig, ax = plt.subplots(1, 1, figsize=(8, 5))

h_tops = []
h_meass = []
for m in range(1, MAX_ORDER + 1):
    M_mat = transition_matrices[m]['M']
    A = (M_mat > 0).astype(float)
    rho = max(abs(np.linalg.eigvals(A)))
    h_top = np.log2(rho)
    h_tops.append(h_top)

    pi = stationary_dists[m]
    states = transition_matrices[m]['states']
    h_m = 0.0
    for i in range(len(states)):
        if pi[i] > 0:
            for j in range(len(states)):
                if M_mat[i, j] > 0:
                    h_m -= pi[i] * M_mat[i, j] * np.log2(M_mat[i, j])
    h_meass.append(h_m)

orders = range(1, MAX_ORDER + 1)
ax.plot(orders, h_tops, 'o-', color='firebrick', linewidth=2,
        markersize=6, label='Topological entropy $h_{top}$')
ax.plot(orders, h_meass, 's-', color='steelblue', linewidth=2,
        markersize=6, label='Measure entropy $h_\\mu$')
ax.axhline(y=np.log2(phi), color='firebrick', linestyle='--', alpha=0.4,
           label=f'log₂(φ) = {np.log2(phi):.4f} (golden mean shift)')
ax.set_xlabel('Markov order m')
ax.set_ylabel('Entropy (bits/step)')
ax.set_title('Entropy Convergence with Markov Order')
ax.legend()
ax.grid(True, alpha=0.3)
ax.set_xticks(list(orders))

fig.tight_layout()
fig.savefig('/home/claude/parity_entropy.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved parity_entropy.png")


# Figure 4: The golden mean shift graph
fig, ax = plt.subplots(figsize=(6, 4))

# Draw the SFT graph: states 0, 1
# Edges: 0→0, 0→1, 1→0
ax.set_xlim(-0.5, 2.5)
ax.set_ylim(-0.8, 1.2)

# State circles
circle0 = plt.Circle((0.5, 0.3), 0.3, fill=False, linewidth=2, color='steelblue')
circle1 = plt.Circle((1.5, 0.3), 0.3, fill=False, linewidth=2, color='coral')
ax.add_patch(circle0)
ax.add_patch(circle1)
ax.text(0.5, 0.3, '0\n(even)', ha='center', va='center', fontsize=11,
        fontweight='bold', color='steelblue')
ax.text(1.5, 0.3, '1\n(odd)', ha='center', va='center', fontsize=11,
        fontweight='bold', color='coral')

# Self-loop 0→0
angle = np.linspace(0.3, 2*np.pi - 0.3, 50)
r = 0.25
cx, cy = 0.5, 0.85
ax.plot(cx + r*np.cos(angle), cy + r*np.sin(angle), 'steelblue', linewidth=1.5)
ax.annotate('', xy=(cx + r*np.cos(-0.3), cy + r*np.sin(-0.3)),
            xytext=(cx + r*np.cos(-0.1), cy + r*np.sin(-0.1)),
            arrowprops=dict(arrowstyle='->', color='steelblue', lw=1.5))
p0 = transition_matrices[1]['T'][0, 0]
ax.text(0.5, 1.18, f'P = {p0:.3f}', ha='center', fontsize=9, color='steelblue')

# Edge 0→1
ax.annotate('', xy=(1.2, 0.38), xytext=(0.8, 0.38),
            arrowprops=dict(arrowstyle='->', color='purple', lw=1.5))
p01 = transition_matrices[1]['T'][0, 1]
ax.text(1.0, 0.52, f'P = {p01:.3f}', ha='center', fontsize=9, color='purple')

# Edge 1→0
ax.annotate('', xy=(0.8, 0.22), xytext=(1.2, 0.22),
            arrowprops=dict(arrowstyle='->', color='green', lw=1.5))
ax.text(1.0, 0.02, f'P = 1.000', ha='center', fontsize=9, color='green')

# Forbidden edge 1→1 (X)
ax.text(1.85, 0.85, '✗  1→1', fontsize=12, color='red', fontweight='bold')
ax.text(1.85, 0.7, 'FORBIDDEN', fontsize=8, color='red')

ax.set_aspect('equal')
ax.axis('off')
ax.set_title('The Golden Mean Shift: Collatz Parity SFT\n'
             'After an odd step (3x+1), next step must be even (÷2)',
             fontsize=11)

fig.tight_layout()
fig.savefig('/home/claude/golden_mean_shift.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved golden_mean_shift.png")


# ── Copy to outputs ────────────────────────────────────────────────
import shutil
for f in ['parity_autocorrelation.png', 'parity_transition_matrices.png',
          'parity_entropy.png', 'golden_mean_shift.png']:
    shutil.copy2(f'/home/claude/{f}', f'/mnt/user-data/outputs/{f}')
shutil.copy2('/home/claude/parity_sft.py', '/mnt/user-data/outputs/parity_sft.py')

print(f"\nDone.")
