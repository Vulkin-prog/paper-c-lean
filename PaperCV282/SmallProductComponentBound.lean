import PaperC.Combinatorics.CanonicalResidualPrimeProduct
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The residual-component budget of a small prime product

The canonical certificate has exactly `c#` distinct prime labels and each
label exceeds `B=L+1`. Thus `(B+1)^c# <= P#`. This finite observation controls
every fixed power of the component factor on `P# <= M` without counting
certificate populations or using a critical relation between `2^B` and `M`.
-/

namespace PaperC.V282.SmallProductComponentBound

open CanonicalResidualComponents ResidualComponentCounts
open scoped BigOperators

noncomputable section

/-- Distinct prime representatives give the exact component-count exponent. -/
theorem base_pow_componentCount_le_primeProduct
    {A x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) :
    (L + 2) ^ canonicalResidualComponentCount A x y L ≤
      canonicalResidualPrimeProduct (A := A) (L := L)
        (show 1 ≤ x by omega) (show 1 ≤ y by omega) := by
  let primes := canonicalResidualCertificatePrimes (A := A) (L := L)
    (show 1 ≤ x by omega) (show 1 ≤ y by omega)
  have hcard : primes.card = canonicalResidualComponentCount A x y L :=
    canonicalResidualPrimeProduct_factorCount hx hy
  have hfactor : ∀ p ∈ primes, L + 2 ≤ p := by
    intro p hp
    have hlarge := prime_large_of_mem_canonicalResidualCertificatePrimes
      (show 1 ≤ x by omega) (show 1 ≤ y by omega) hp
    exact Nat.succ_le_iff.mpr hlarge.2
  rw [← hcard]
  change (L + 2) ^ primes.card ≤ ∏ p ∈ primes, p
  calc
    (L + 2) ^ primes.card = ∏ _p ∈ primes, (L + 2) := by simp
    _ ≤ ∏ p ∈ primes, p := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hfactor

/-- Logarithmic form of the same finite small-product budget. -/
theorem componentCount_mul_log_le_log_of_smallProduct
    {M A x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hproduct : canonicalResidualPrimeProduct (A := A) (L := L)
      (show 1 ≤ x by omega) (show 1 ≤ y by omega) ≤ M) :
    (canonicalResidualComponentCount A x y L : ℝ) * Real.log (L + 2 : ℝ) ≤
      Real.log M := by
  have hpow : (L + 2) ^ canonicalResidualComponentCount A x y L ≤ M :=
    (base_pow_componentCount_le_primeProduct hx hy).trans hproduct
  have hlog := Real.log_le_log
    (by positivity : (0 : ℝ) < ((L + 2) ^ canonicalResidualComponentCount A x y L : ℕ))
    (by exact_mod_cast hpow : (((L + 2) ^ canonicalResidualComponentCount A x y L : ℕ) : ℝ) ≤ M)
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Real.log_pow] using hlog

/-- Every fixed moment of the component factor is at most the ambient scale once the base allows it. -/
theorem two_pow_componentCount_pow_le_of_smallProduct
    {M A x y L k : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) (hbase : 2 ^ k ≤ L + 2)
    (hproduct : canonicalResidualPrimeProduct (A := A) (L := L)
      (show 1 ≤ x by omega) (show 1 ≤ y by omega) ≤ M) :
    (2 ^ canonicalResidualComponentCount A x y L) ^ k ≤ M := by
  calc
    (2 ^ canonicalResidualComponentCount A x y L) ^ k =
        (2 ^ k) ^ canonicalResidualComponentCount A x y L := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (L + 2) ^ canonicalResidualComponentCount A x y L :=
      Nat.pow_le_pow_left hbase _
    _ ≤ canonicalResidualPrimeProduct (A := A) (L := L)
        (show 1 ≤ x by omega) (show 1 ≤ y by omega) :=
      base_pow_componentCount_le_primeProduct hx hy
    _ ≤ M := hproduct

end
end PaperC.V282.SmallProductComponentBound
