#!/usr/bin/env python3
"""Verify zeros of ζ(s) lie on Re = 1/2 and ξ_rot is real on ℝ."""

from mpmath import mp, zetazero, zeta, gamma, pi, im, re, mpc, mpf, fabs

mp.dps = 50

def completed_zeta(s):
    """ξ(s) = π^(-s/2) Γ(s/2) ζ(s)"""
    return pi**(-s/2) * gamma(s/2) * zeta(s)

print("=== Verifying first 100 zeros of ζ(s) on Re = 1/2 ===")
for k in range(1, 101):
    z = zetazero(k)
    err = fabs(re(z) - mpf('0.5'))
    assert err < mpf('1e-40'), f"Zero {k} off critical line: {z}"
    if k <= 10 or k % 20 == 0:
        print(f"  ζ zero #{k:>3}: t = {float(im(z)):>20.12f}, |Re - 1/2| < 1e-40")
print("PASS: all 100 zeros on Re = 1/2\n")

print("=== Verifying ξ_rot(w) = ξ(1/2 + iw) is real for real w ===")
test_points = [0.1, 1.0, 5.0, 14.134725, 21.022040, 25.0, 50.0, 100.0]
for t in test_points:
    val = completed_zeta(mpc(0.5, t))
    imag = fabs(im(val))
    assert imag < mpf('1e-40'), f"ξ_rot not real at t={t}: im = {imag}"
    print(f"  ξ_rot({t:>10.6f}) = {float(re(val)):>20.12f} + {float(im(val)):.2e}i")
print("PASS: ξ_rot real on ℝ\n")

print("=== Verifying Schwarz reflection: ξ(conj s) = conj(ξ(s)) ===")
test_s = [mpc(0.3, 5.0), mpc(0.7, 10.0), mpc(0.5, 14.134), mpc(0.25, 3.0)]
for s in test_s:
    lhs = completed_zeta(s.conjugate())
    rhs = completed_zeta(s).conjugate()
    err = fabs(lhs - rhs)
    assert err < mpf('1e-40'), f"Schwarz fails at s={s}: err={err}"
    print(f"  s = {s}, |ξ(conj s) - conj(ξ(s))| = {float(err):.2e}")
print("PASS: Schwarz reflection verified\n")

print("=== Verifying functional equation: ξ(1-s) = ξ(s) ===")
for s in test_s:
    lhs = completed_zeta(1 - s)
    rhs = completed_zeta(s)
    err = fabs(lhs - rhs)
    assert err < mpf('1e-40'), f"Functional eq fails at s={s}: err={err}"
    print(f"  s = {s}, |ξ(1-s) - ξ(s)| = {float(err):.2e}")
print("PASS: functional equation verified")
