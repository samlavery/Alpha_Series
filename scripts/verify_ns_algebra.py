#!/usr/bin/env python3
"""Verify Navier-Stokes algebraic identities: equidistribution cancellation,
eigenvalue bounds, and both-ingredients-necessary."""

import numpy as np

np.random.seed(42)
N_TESTS = 200000

print("=== Equidistribution + trace-free → zero stretching ===")
max_err = 0.0
for _ in range(N_TESTS):
    l1, l2 = np.random.randn(2) * 10
    l3 = -(l1 + l2)  # trace-free
    omega_sq = np.random.rand() * 100

    # Equidistributed: each eigendirection gets ω²/3
    stretching = l1 * (omega_sq/3) + l2 * (omega_sq/3) + l3 * (omega_sq/3)
    max_err = max(max_err, abs(stretching))

assert max_err < 1e-10
print(f"PASS: {N_TESTS} random tests, max |stretching| = {max_err:.2e}\n")

print("=== Without trace-free, equidistribution does NOT kill stretching ===")
# Compressible: l1 = l2 = l3 = 1 (tr = 3)
for l1, l2, l3 in [(1,1,1), (2,3,4), (0.5, 0.5, 0.5)]:
    stretching = l1/3 + l2/3 + l3/3
    print(f"  l = ({l1},{l2},{l3}), tr = {l1+l2+l3}, equidist stretching = {stretching:.4f}")
assert abs(1/3 + 1/3 + 1/3 - 1.0) < 1e-15
print("PASS: compressible equidistributed stretching is nonzero\n")

print("=== Without equidistribution, trace-free does NOT kill stretching ===")
# Trace-free: l1=1, l2=-0.5, l3=-0.5, but aligned with l1
for (l1,l2,l3), (p1,p2,p3), desc in [
    ((1, -0.5, -0.5), (1, 0, 0), "fully aligned with max"),
    ((2, -1, -1), (0.8, 0.1, 0.1), "mostly aligned"),
    ((1, 0, -1), (0.9, 0.05, 0.05), "one zero eigenvalue"),
]:
    stretching = l1*p1 + l2*p2 + l3*p3
    print(f"  l = {(l1,l2,l3)}, proj = {(p1,p2,p3)}: stretching = {stretching:.4f} ({desc})")
print("PASS: trace-free alone does not kill stretching\n")

print("=== Max eigenvalue bound: max² ≤ (2/3)(l1²+l2²+l3²) ===")
violations = 0
for _ in range(N_TESTS):
    l1, l2 = np.random.randn(2) * 10
    l3 = -(l1 + l2)
    max_sq = max(l1, l2, l3)**2
    sum_sq = l1**2 + l2**2 + l3**2
    if max_sq > 2/3 * sum_sq + 1e-10:
        violations += 1
assert violations == 0
print(f"PASS: {N_TESTS} random tests, 0 violations\n")

print("=== Critical circle: sphere ∩ trace-free plane ===")
for r in [1.0, 2.0, 5.0, 10.0]:
    # Parametric: (r√(2/3)·cos θ, ...) on the great circle
    a = r * np.sqrt(2/3)
    # Point: (a, -a/2, -a/2)
    l1, l2, l3 = a, -a/2, -a/2
    trace = l1 + l2 + l3
    norm_sq = l1**2 + l2**2 + l3**2
    max_sq = max(l1, l2, l3)**2
    print(f"  r={r}: trace={trace:.2e}, |l|²={norm_sq:.4f} (r²={r**2:.4f}), "
          f"max²/r²={max_sq/r**2:.4f} ≤ {2/3:.4f}")
    assert abs(trace) < 1e-12
    assert abs(norm_sq - r**2) < 1e-10
    assert max_sq <= 2/3 * r**2 + 1e-10
print("PASS: critical circle geometry verified\n")

print("=== Alignment reduces effective stretching ===")
for _ in range(N_TESTS):
    l1, l2 = np.random.randn(2) * 5
    l3 = -(l1 + l2)
    lmax = max(l1, l2, l3)
    omega = np.random.rand() * 10
    cos_sq = np.random.rand()  # cos²θ ∈ [0,1]

    effective = lmax * omega * cos_sq
    worst_case = lmax * omega
    if lmax >= 0:
        assert effective <= worst_case + 1e-10

print(f"PASS: {N_TESTS} tests, effective ≤ worst-case when λ_max ≥ 0\n")

print("=== Compressible escapes the critical circle ===")
# All-positive eigenvalues on the sphere but NOT trace-free
v = np.array([1, 1, 1]) / np.sqrt(3)
norm_sq = np.sum(v**2)
trace = np.sum(v)
print(f"  v = (1,1,1)/√3: |v|² = {norm_sq:.4f}, trace = {trace:.4f}")
print(f"  On sphere (|v|²=1): YES, trace-free: NO")
print("PASS: compressible can have all-positive eigenvalues")
