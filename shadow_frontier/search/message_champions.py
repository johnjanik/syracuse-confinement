#!/usr/bin/env python3
"""Compose messages whose forced continuation survives long.

Naive spelling (ASCII bit 0 -> b=1, bit 1 -> b=2) makes the script a
{1,2}-prefix; 'forced survival' = how many more letters the carry
cascade keeps in {1,2} after the script ends (the automaton's own
composition). This is the champion problem restricted to ASCII moves.
"""
import sys, os, math, itertools
sys.path.insert(0, 'search')
from frontier import realize

def spell(msg):
    bits = ''.join(f"{ord(c):08b}" for c in msg)
    return realize([1 if c == '0' else 2 for c in bits])[0], len(bits)

def depth12(x, cap=4000):
    d = 0
    while d < cap:
        t = 3 * x + 1
        b = (t & -t).bit_length() - 1
        if b > 2: return d
        x = t >> b; d += 1
    return cap

def forced(msg):
    r, L = spell(msg)
    return depth12(r) - L, r, L

# ---- 1. English dictionary ----
best_words = []
dictpath = '/usr/share/dict/words'
if os.path.exists(dictpath):
    words = [w.strip() for w in open(dictpath, errors='ignore')
             if 3 <= len(w.strip()) <= 8 and w.strip().isalpha()]
    for w in words:
        f, r, L = forced(w)
        best_words.append((f, w, r))
    best_words.sort(reverse=True)
    print(f"dictionary ({len(words)} words 3-8 letters), top forced survival:")
    for f, w, r in best_words[:8]:
        print(f"  {w!r}: script {8*len(w)}, forced +{f}, integer {r}")
else:
    print("no system dictionary found")

# ---- 2. all 2-char printable ASCII ----
P = [chr(c) for c in range(33, 127)]
best2 = max(((forced(a+b)[0], a+b) for a in P for b in P))
f2, m2 = best2
r2, L2 = spell(m2)
print(f"\nbest 2-char printable: {m2!r}: script {L2}, forced +{f2}, integer {r2}")

# ---- 3. greedy composition: GHOST + chosen tail ----
msg = "GHOST"
print(f"\ngreedy composition from {msg!r}:")
for step in range(7):
    f0, _, _ = forced(msg)
    cand = max(((forced(msg + c)[0], c) for c in P))
    msg += cand[1]
    print(f"  + {cand[1]!r} -> {msg!r}: forced +{cand[0]}")
fF, rF, LF = forced(msg)
print(f"\nfinal composition: {msg!r}")
print(f"  integer {rF} ({rF.bit_length()} bits)")
print(f"  script {LF} letters, forced continuation +{fF}, "
      f"total {LF+fF} {{1,2}}-letters")
print(f"  random-message expectation for the forced part: ~3 letters "
      f"(geometric 3/4); best-of-N search wins ~log_{{4/3}}(N)")
