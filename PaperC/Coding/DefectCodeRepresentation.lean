import PaperC.Arithmetic.DefectParitySupport
import PaperC.Coding.DefectCodeRunge

/-!
# Instantiating the defect-code coverage hypothesis

This file discharges the arithmetic coverage hypothesis left explicit in
`DefectCodeRank`.  Each selected integer is supplied with its representation

`f i = s i * (a i)^2`,

and the finite list `smallPrime` is assumed to contain every prime divisor of
each `s i`.  These are exactly the data used in Proposition 3.2.
-/

namespace PaperC
namespace DefectCodeRepresentation

open scoped BigOperators

/--
A kernel word selects a square product directly from the representations
`f i = s i * (a i)^2` and coverage of the divisors of `s i`.
-/
theorem square_product_of_defectRepresentations
    {m r : ℕ}
    (smallPrime : Fin r → ℕ)
    (f s a : Fin m → ℕ)
    (hrep : ∀ i, f i = s i * (a i) ^ 2)
    (hs : ∀ i, s i ≠ 0)
    (ha : ∀ i, a i ≠ 0)
    (hsmall : ∀ i p, Nat.Prime p → p ∣ s i →
      ∃ j : Fin r, smallPrime j = p)
    (x : Fin m → F₂)
    (hx :
      x ∈ LinearMap.ker
        (DefectCodeRank.augmentedParityMap smallPrime f)) :
    ∃ q : ℕ,
      ∏ i ∈ HammingBound.wordSupport x, f i = q ^ 2 := by
  apply DefectCodeRank.square_product_of_mem_ker_augmentedParityMap
    smallPrime f
  · intro i
    rw [hrep i]
    exact mul_ne_zero (hs i) (pow_ne_zero 2 (ha i))
  · intro i p hp
    exact DefectParitySupport.parityCoverage_of_eq_mul_sq
      smallPrime (hs i) (ha i) (hrep i) (hsmall i) p hp
  · exact hx

/--
The complete finite bridge from a represented defect-code word to the
translated Runge inputs, with no residual parity-coverage hypothesis.
-/
theorem kernelWord_translatedRungeInput_of_defectRepresentations
    {m r U R : ℕ}
    (smallPrime : Fin r → ℕ)
    (f s a : Fin m → ℕ)
    (hrep : ∀ i, f i = s i * (a i) ^ 2)
    (hs : ∀ i, s i ≠ 0)
    (ha : ∀ i, a i ≠ 0)
    (hsmall : ∀ i p, Nat.Prime p → p ∣ s i →
      ∃ j : Fin r, smallPrime j = p)
    (hinjective : Function.Injective f)
    (hlower : ∀ i, U ≤ f i)
    (hupper : ∀ i, f i ≤ U + R)
    (x : Fin m → F₂)
    (hx :
      x ∈ LinearMap.ker
        (DefectCodeRank.augmentedParityMap smallPrime f)) :
    let S := HammingBound.wordSupport x
    let selected : {i // i ∈ S} → ℕ := fun i ↦ f i
    Function.Injective
        (RungeTranslation.translatedShift U selected) ∧
      (∀ i,
        |RungeTranslation.translatedShift U selected i| ≤ R) ∧
      ∃ q : ℤ,
        (∏ i,
          ((U : ℤ) +
            RungeTranslation.translatedShift U selected i)) = q ^ 2 := by
  apply DefectCodeRunge.kernelWord_translatedRungeInput
    smallPrime f
  · intro i
    rw [hrep i]
    exact mul_ne_zero (hs i) (pow_ne_zero 2 (ha i))
  · intro i p hp
    exact DefectParitySupport.parityCoverage_of_eq_mul_sq
      smallPrime (hs i) (ha i) (hrep i) (hsmall i) p hp
  · exact hinjective
  · exact hlower
  · exact hupper
  · exact hx

end DefectCodeRepresentation
end PaperC
