import PaperC.Algebra.RungeBound
import PaperC.Coding.DefectCodeProposition

/-!
# Applying the quantitative Runge lemma to the defect code

This file turns the explicit bound in `RungeBound.quantitative_runge` into
the absence of short square-product words required by the defect-code
argument.  It then exposes the volume and length conclusions directly from
the arithmetic representations.
-/

namespace PaperC
namespace RungeDefectApplication

open Finset

/--
If `U` is larger than the quantitative Runge bound at every
`1 ≤ k ≤ t`, no Runge square-product datum of those sizes exists.
-/
theorem noShortRungeSquare_of_growth
    {U R t : ℕ}
    (hR : 1 ≤ R)
    (hU : 2 * R ≤ U)
    (hgrowth :
      ∀ k, 1 ≤ k → k ≤ t →
        (128 * (2 * k) * R) ^ (4 * k) < U) :
    DefectCodeDistance.NoShortRungeSquare U R t := by
  intro k hk hkt γ hγinjective hγbounded
  rintro ⟨q, hq⟩
  have hbound :
      U ≤ (128 * (2 * k) * R) ^ (4 * k) :=
    RungeBound.quantitative_runge
      hk hR hU γ (by simpa using hγbounded) hγinjective q hq
  exact (not_lt_of_ge hbound) (hgrowth k hk hkt)

/-- Monotonicity of the explicit Runge scale in its size parameter. -/
theorem rungeScale_mono
    {R k t : ℕ} (hR : 1 ≤ R) (hk : 1 ≤ k) (hkt : k ≤ t) :
    (128 * (2 * k) * R) ^ (4 * k) ≤
      (128 * (2 * t) * R) ^ (4 * t) := by
  have hbase :
      128 * (2 * k) * R ≤ 128 * (2 * t) * R := by
    exact Nat.mul_le_mul_right R
      (Nat.mul_le_mul_left 128 (Nat.mul_le_mul_left 2 hkt))
  calc
    (128 * (2 * k) * R) ^ (4 * k) ≤
        (128 * (2 * t) * R) ^ (4 * k) :=
      Nat.pow_le_pow_left hbase (4 * k)
    _ ≤ (128 * (2 * t) * R) ^ (4 * t) := by
      apply Nat.pow_le_pow_right
      · have ht : 1 ≤ t := hk.trans hkt
        positivity
      · omega

/--
Endpoint form: it is enough to compare `U` with the single Runge scale at
`t`; monotonicity supplies all smaller values of `k`.
-/
theorem noShortRungeSquare_of_endpoint_growth
    {U R t : ℕ}
    (hR : 1 ≤ R)
    (hU : 2 * R ≤ U)
    (hgrowth : (128 * (2 * t) * R) ^ (4 * t) < U) :
    DefectCodeDistance.NoShortRungeSquare U R t := by
  apply noShortRungeSquare_of_growth hR hU
  intro k hk hkt
  exact (rungeScale_mono hR hk hkt).trans_lt hgrowth

/--
The exact Hamming-volume inequality, with the quantitative Runge growth
condition substituted for the abstract no-short-square hypothesis.
-/
theorem defectCode_volume_le_two_pow_of_growth
    {m r U R t : ℕ}
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
    (hR : 1 ≤ R)
    (hU : 2 * R ≤ U)
    (hgrowth :
      ∀ k, 1 ≤ k → k ≤ t →
        (128 * (2 * k) * R) ^ (4 * k) < U)
    (hrows : r + 1 ≤ m) :
    (∑ j ∈ Finset.range (t + 1), m.choose j) ≤ 2 ^ (r + 1) := by
  apply
    DefectCodeProposition.defectCode_volume_le_two_pow_of_representations
      smallPrime f s a hrep hs ha hsmall hinjective hlower hupper
  · exact noShortRungeSquare_of_growth hR hU hgrowth
  · exact hrows

/--
The finite length bound, with the quantitative Runge growth condition
substituted for the abstract no-short-square hypothesis.
-/
theorem defectCode_length_lt_of_growth
    {m r U R t : ℕ}
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
    (hR : 1 ≤ R)
    (hU : 2 * R ≤ U)
    (hgrowth :
      ∀ k, 1 ≤ k → k ≤ t →
        (128 * (2 * k) * R) ^ (4 * k) < U)
    (ht : 1 ≤ t)
    (htm : 2 * t ≤ m)
    (hrows : r + 1 ≤ m) :
    m < 2 * t * 2 ^ ((r + 1) / t + 1) := by
  apply
    DefectCodeProposition.defectCode_length_lt_of_representations
      smallPrime f s a hrep hs ha hsmall hinjective hlower hupper
  · exact noShortRungeSquare_of_growth hR hU hgrowth
  · exact ht
  · exact htm
  · exact hrows

/--
Volume inequality under the single endpoint comparison
`(128 * (2*t) * R)^(4*t) < U`.
-/
theorem defectCode_volume_le_two_pow_of_endpoint_growth
    {m r U R t : ℕ}
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
    (hR : 1 ≤ R)
    (hU : 2 * R ≤ U)
    (hgrowth : (128 * (2 * t) * R) ^ (4 * t) < U)
    (hrows : r + 1 ≤ m) :
    (∑ j ∈ Finset.range (t + 1), m.choose j) ≤ 2 ^ (r + 1) := by
  apply
    DefectCodeProposition.defectCode_volume_le_two_pow_of_representations
      smallPrime f s a hrep hs ha hsmall hinjective hlower hupper
  · exact noShortRungeSquare_of_endpoint_growth hR hU hgrowth
  · exact hrows

/--
Length estimate under the single endpoint comparison
`(128 * (2*t) * R)^(4*t) < U`.
-/
theorem defectCode_length_lt_of_endpoint_growth
    {m r U R t : ℕ}
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
    (hR : 1 ≤ R)
    (hU : 2 * R ≤ U)
    (hgrowth : (128 * (2 * t) * R) ^ (4 * t) < U)
    (ht : 1 ≤ t)
    (htm : 2 * t ≤ m)
    (hrows : r + 1 ≤ m) :
    m < 2 * t * 2 ^ ((r + 1) / t + 1) := by
  apply
    DefectCodeProposition.defectCode_length_lt_of_representations
      smallPrime f s a hrep hs ha hsmall hinjective hlower hupper
  · exact noShortRungeSquare_of_endpoint_growth hR hU hgrowth
  · exact ht
  · exact htm
  · exact hrows

end RungeDefectApplication
end PaperC
