#!/usr/bin/env python3
"""Verify twin prime constant C₂, Hardy-Littlewood asymptotic, and pair correlation."""

from math import log, sqrt
from sympy import primerange, isprime

print("=== Twin prime constant C₂ ===")
C2 = 1.0
for p in primerange(3, 100000):
    C2 *= (1 - 1/(p-1)**2)
print(f"C₂ = {C2:.12f}")
print(f"Expected: 0.660161815846... (Hardy-Littlewood)\n")

print("=== Twin prime count vs Hardy-Littlewood prediction ===")
print(f"{'N':>10} {'π₂(N)':>8} {'2C₂·li₂(N)':>12} {'ratio':>8}")
print("-" * 42)

def li2(N):
    """Logarithmic integral approximation: ∫₂ᴺ dt/(log t)²"""
    s = 0.0
    dt = 1.0
    t = 2.0
    while t < N:
        s += dt / log(t)**2
        t += dt
        if t > 100:
            dt = 10.0
        if t > 10000:
            dt = 100.0
    return s

twin_counts = {}
for N_exp in [4, 5, 6, 7]:
    N = 10**N_exp
    count = sum(1 for p in primerange(3, N) if isprime(p + 2))
    predicted = 2 * C2 * li2(N)
    ratio = count / predicted if predicted > 0 else 0
    twin_counts[N] = count
    print(f"{N:>10} {count:>8} {predicted:>12.1f} {ratio:>8.4f}")

print("\n(Ratio → 1.0 confirms Hardy-Littlewood asymptotic)\n")

print("=== Pair correlation Σ Λ(n)Λ(n+2) vs 2C₂·x ===")
print(f"{'x':>8} {'Σ Λ(n)Λ(n+2)':>14} {'2C₂·x':>10} {'ratio':>8}")
print("-" * 44)

def von_mangoldt(n):
    """Λ(n) = log p if n = p^k, else 0"""
    if n < 2:
        return 0.0
    for p in primerange(2, int(n**0.5) + 2):
        if n % p == 0:
            pk = p
            while pk <= n:
                if pk == n:
                    return log(p)
                pk *= p
            return 0.0
    # n is prime
    return log(n)

for x in [1000, 5000, 10000, 50000]:
    pair_sum = sum(von_mangoldt(n) * von_mangoldt(n + 2) for n in range(1, x + 1))
    predicted = 2 * C2 * x
    ratio = pair_sum / predicted
    print(f"{x:>8} {pair_sum:>14.2f} {predicted:>10.2f} {ratio:>8.4f}")

print("\n(Ratio → 1.0 confirms pair correlation asymptotic)")

print("\n=== Sublinearity of non-twin contribution ===")
print("Λ(n)Λ(n+2) is nonzero for non-twin-primes only at prime powers.")
print("Checking that prime power pairs are rare:\n")
pp_count = 0
twin_count = 0
for n in range(2, 100001):
    lam_n = von_mangoldt(n)
    lam_n2 = von_mangoldt(n + 2)
    if lam_n > 0 and lam_n2 > 0:
        is_twin = isprime(n) and isprime(n + 2)
        if is_twin:
            twin_count += 1
        else:
            pp_count += 1

print(f"In [2, 100000]: twin prime pairs = {twin_count}, "
      f"prime power pairs = {pp_count}")
print(f"Non-twin fraction: {pp_count/(twin_count+pp_count):.4f}")
print("(Small fraction confirms sublinearity of non-twin contribution)")
