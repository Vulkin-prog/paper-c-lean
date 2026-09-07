import PaperC.Arithmetic.PolynomialZoneLargePrimes

/-! # The uniform Laishram--Shorey input actually used in E.2

This is a separate bibliographic boundary from the weaker, historical
Corollary 1. The published equation (14), p.331, explicitly makes its
threshold depend only on epsilon, uniformly over all n>k. It follows in
the source from Theorem 2 and PNT. Its proof is not claimed here.

Primary source: https://www.impan.pl/shop/en/publication/transaction/download/product/83314
Laishram and Shorey, Acta Arithmetica 113 (2004), 327--341,
DOI 10.4064/aa113-4-3, equation (14), p.331.
-/

namespace PaperC.V282.LaishramUniformInput

open LaishramShoreyInput PolynomialZoneLargePrimes

/-- Published uniform equation (14), passed explicitly as a theorem argument. -/
def UniformPrimeDivisorStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ kzero : ℕ,
    ∀ k : ℕ, kzero ≤ k → 2 ≤ k → ∀ n : ℕ, k < n →
      (2 - epsilon) * (PrimesUpTo.count k : ℝ) ≤
        ((consecutiveProduct n k).primeFactors.card : ℝ)

/-- Removing primes at most k leaves the required uniform number of large species. -/
theorem uniform_large_prime_species (hLS : UniformPrimeDivisorStatement)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ kzero : ℕ, ∀ k : ℕ, kzero ≤ k → 2 ≤ k → ∀ n : ℕ, k < n →
      (1 - epsilon) * (PrimesUpTo.count k : ℝ) ≤
        ((largePrimeFactors k n k).card : ℝ) := by
  obtain ⟨kzero,hbound⟩ := hLS epsilon hepsilon
  refine ⟨kzero,fun k hk hk2 n hkn => ?_⟩
  have hLSbound := hbound k hk hk2 n hkn
  have hremove := primeFactors_card_sub_primeCount_le_largePrimeFactors_card k n k
  have htotal : (consecutiveProduct n k).primeFactors.card ≤
      PrimesUpTo.count k + (largePrimeFactors k n k).card := by omega
  have hreal : ((consecutiveProduct n k).primeFactors.card : ℝ) ≤
      (PrimesUpTo.count k : ℝ) + ((largePrimeFactors k n k).card : ℝ) := by
    exact_mod_cast htotal
  linarith

end PaperC.V282.LaishramUniformInput
