#!/bin/bash
# Run all verification scripts. Requires: pip install mpmath sympy numpy
set -e
DIR="$(cd "$(dirname "$0")" && pwd)"

echo "========================================"
echo "  Numerical Verification Suite"
echo "========================================"
echo ""

for script in \
    verify_baker.py \
    verify_ns_algebra.py \
    verify_goldbach.py \
    verify_twin_primes.py \
    verify_zeta_zeros.py \
    verify_grh_zeros.py
do
    echo "========================================"
    echo "  Running: $script"
    echo "========================================"
    python3 "$DIR/$script"
    echo ""
done

echo "========================================"
echo "  All verification scripts completed."
echo "========================================"
