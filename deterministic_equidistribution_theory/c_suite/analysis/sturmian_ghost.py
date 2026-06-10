"""dc_32 sec 6: test balanced critical Sturmian valuation words for positive realizability.
b_n(theta) = 1 + 1{frac(n*alpha+theta) >= alpha}, alpha = 2-log2(3).
Prefix determines x mod 2^{B_N+1}; ghost <=> least positive rep wanders ~2^{B_N}."""
from math import log2, floor
ALPHA=2-log2(3)
def word(theta,N):
    return [1 if ((n*ALPHA+theta)%1.0)<ALPHA else 2 for n in range(N)]
def realize(bs):
    # returns (r, M): the class x = r mod 2^M realizing the valuation prefix bs
    # iterate: maintain (r, M); x_n = (3^n x + A_n)/2^{B_{n-1}}; condition v2(3 x_n + 1) = b_n
    r,Mbits=1,1   # x odd
    A=0; B=0; P3=1  # x_n = (P3*x + A)/2^B
    for n,b in enumerate(bs):
        # numerator Num(x) = 3*(P3 x + A) + 2^B = 3 P3 x + 3A + 2^B ; need v2 = B + b exactly
        need=B+b
        mod=1<<(need+1)
        c=(3*A+(1<<B))%mod
        coef=(3*P3)%mod
        # solve coef*x + c = 2^need * odd  mod 2^{need+1}: coef odd
        inv=pow(coef,-1,mod)
        # x = inv*(2^need - c) mod 2^{need+1} gives numerator = 2^need mod 2^{need+1}: odd quotient ok
        x0=(inv*(((1<<need)-c)%mod))%mod
        # combine with current class: x = r mod 2^Mbits AND x = x0 mod 2^{need+1}
        m2=need+1
        if m2>Mbits:
            assert (x0 - r) % (1<<Mbits) == 0, "inconsistent nested classes"
            r=x0; Mbits=m2
        # advance affine data
        A=3*A+(1<<B); P3*=3; B+=b
    return r,Mbits
print(f"{'theta':>6} {'N':>5} {'B_N':>5} {'least-rep bits':>14} {'ratio r/2^M':>12} {'stabilized?':>11}")
import random
random.seed(2)
for theta in [0.0,0.1,0.2,0.33,0.5,0.61,0.75,0.9]+[random.random() for _ in range(4)]:
    reps={}
    for N in (100,200,400,800):
        bs=word(theta,N)
        r,M=realize(bs)
        reps[N]=(r,M)
    stab = reps[100][0]==reps[200][0]==reps[400][0]
    r,M=reps[800]
    print(f"{theta:6.3f} {800:>5} {sum(word(theta,800)):>5} {r.bit_length():>14} {r/(1<<M):>12.6f} {'YES <-- POSITIVE CANDIDATE' if stab else 'no (ghost)':>11}")
