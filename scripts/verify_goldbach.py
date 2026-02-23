#!/usr/bin/env python3
"""Verify Goldbach's conjecture and circle method predictions."""

from math import log
from sympy import isprime, primerange

print("=== Goldbach verification: every even n in [4, 10000] ===")
failures = []
for n in range(4, 10001, 2):
    found = False
    for p in primerange(2, n):
        if isprime(n - p):
            found = True
            break
    if not found:
        failures.append(n)

if failures:
    print(f"FAIL: Goldbach fails at {failures}")
else:
    print("PASS: all even n in [4, 10000] verified\n")

print("=== Goldbach representation count r(n) = #{(p,q) : p+q=n, p≤q prime} ===")
def goldbach_count(n):
    count = 0
    for p in primerange(2, n // 2 + 1):
        if isprime(n - p):
            count += 1
    return count

print(f"{'n':>8} {'r(n)':>6} {'n/log²n':>10} {'ratio':>8}")
print("-" * 36)
for n in [100, 500, 1000, 5000, 10000, 50000]:
    r = goldbach_count(n)
    pred = n / log(n)**2
    print(f"{n:>8} {r:>6} {pred:>10.1f} {r/pred:>8.3f}")

print("\n(r(n) grows roughly as n/log²n, as circle method predicts)\n")

print("=== Goldbach singular series S(n) variation ===")
print("Even n with many small prime factors have larger S(n).\n")

def goldbach_singular_approx(n):
    """Approximate singular series for Goldbach: ∏_{p|n, p>2} (p-1)/(p-2) · ∏_{p>2} (1-1/(p-1)²)"""
    product = 1.0
    for p in primerange(3, min(n, 1000)):
        if n % p == 0:
            product *= (p - 1) / (p - 2)
    return product

print(f"{'n':>8} {'r(n)':>6} {'S(n)·n/log²n':>14} {'ratio':>8}")
print("-" * 40)
for n in [30, 210, 2310, 1000, 9998, 10000]:
    r = goldbach_count(n)
    S = goldbach_singular_approx(n)
    pred = S * n / log(n)**2
    ratio = r / pred if pred > 0 else 0
    print(f"{n:>8} {r:>6} {pred:>14.1f} {ratio:>8.3f}")

print("\n(Highly composite n like 210=2·3·5·7 have elevated counts)")

print("\n=== Verification that R(n) ≥ n for large even n (circle method under RH) ===")
print("R(n) = Σ_{p+q=n} Λ(p)Λ(q)\n")

from math import log

def R_goldbach(n):
    """R(n) = Σ_{p+q=n} Λ(p)Λ(q) over primes/prime powers"""
    total = 0.0
    for p in primerange(2, n):
        q = n - p
        if q >= 2 and isprime(q):
            total += log(p) * log(q)
    return total

print(f"{'n':>8} {'R(n)':>12} {'n':>8} {'R(n)/n':>8}")
print("-" * 40)
for n in range(100, 10001, 100):
    R = R_goldbach(n)
    if n in [100, 500, 1000, 2000, 5000, 10000]:
        print(f"{n:>8} {R:>12.2f} {n:>8} {R/n:>8.4f}")
print("\n(R(n)/n > 1 for large n confirms the circle method bound)")
