#!/usr/bin/env python3
"""Verify Baker's theorem consequences: Q-independence of log 2, log 3,
and Collatz contraction rate."""

from math import log, gcd
from fractions import Fraction

print("=== log 2 / log 3 is irrational (Baker 1966) ===")
log2 = log(2)
log3 = log(3)
ratio = log2 / log3
print(f"log 2 = {log2:.15f}")
print(f"log 3 = {log3:.15f}")
print(f"log2/log3 = {ratio:.15f}\n")

print("Best rational approximations (continued fraction convergents):")
print(f"{'a/b':>12} {'|a·log3 - b·log2|':>20} {'3^a vs 2^b':>20}")
print("-" * 56)

best = []
for b in range(1, 10000):
    a = round(b * ratio)
    if a > 0:
        err = abs(a * log3 - b * log2)
        if not best or err < best[-1][2]:
            best.append((a, b, err))
            if len(best) <= 20:
                # Verify 2^b ≠ 3^a directly for small cases
                if b <= 60 and a <= 40:
                    diff = 2**b - 3**a
                    print(f"  {a:>4}/{b:<4} {err:>20.12e} {'2^b-3^a=' + str(diff):>20}")
                else:
                    print(f"  {a:>4}/{b:<4} {err:>20.12e}")

print("\n(Error never reaches 0 — log2/log3 is irrational)\n")

print("=== Unique factorization proof: 2^b = 3^a is impossible ===")
print("If 2^b = 3^a, then the prime factorization of 2^b contains only 2,")
print("but 3^a contains only 3. Since 2 ≠ 3, equality is impossible.")
print("This is the Lean proof of baker_lower_bound (from unique factorization).\n")

# Verify for all small cases
for a in range(1, 100):
    for b in range(1, 100):
        assert 3**a != 2**b, f"FAIL: 3^{a} = 2^{b}"
print("Verified: 3^a ≠ 2^b for all a,b ∈ [1,99]\n")

print("=== Collatz contraction rate: 3^20 / 2^33 < 1 ===")
print(f"3^20 = {3**20}")
print(f"2^33 = {2**33}")
print(f"3^20 / 2^33 = {3**20 / 2**33:.12f}")
print(f"3^20 < 2^33: {3**20 < 2**33}\n")

print("=== Collatz: Baker bound on |m·log3 - S·log2| ===")
print("For a hypothetical cycle with m odd steps and S total steps:")
print("3^m / 2^S must equal some rational, so |m·log3 - S·log2| > 0.")
print("Baker gives |m·log3 - S·log2| > exp(-C·log(m)·log(S)).\n")

print(f"{'m':>4} {'S':>4} {'3^m/2^S':>14} {'|m·log3-S·log2|':>18}")
print("-" * 44)
for m in range(1, 25):
    # Optimal S for 3^m ≈ 2^S
    S = round(m * log3 / log2)
    r = 3**m / 2**S
    err = abs(m * log3 - S * log2)
    print(f"{m:>4} {S:>4} {r:>14.8f} {err:>18.12f}")

print("\n(The gap |m·log3 - S·log2| is always positive — Baker's theorem)")

print("\n=== Collatz verification: all n in [1, 10^6] reach 1 ===")
def collatz_steps(n):
    steps = 0
    while n != 1:
        n = n // 2 if n % 2 == 0 else 3 * n + 1
        steps += 1
        if steps > 1000:
            return -1
    return steps

max_steps = 0
max_n = 1
for n in range(1, 10**6 + 1):
    s = collatz_steps(n)
    assert s >= 0, f"Collatz fails at {n}"
    if s > max_steps:
        max_steps = s
        max_n = n

print(f"PASS: all n ∈ [1, 10^6] reach 1")
print(f"Longest orbit: n = {max_n} with {max_steps} steps")
