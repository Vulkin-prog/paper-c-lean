import PaperC.Arithmetic.RungeTranslation
import PaperC.Coding.DefectCodeRank

/-!
# From a defect-code word to the translated Runge data

This file certifies the exact bridge between the binary code in
Proposition 3.2 and the input of Lemma 3.1.

A word in the kernel of the augmented parity matrix selects:

* an even number of entries;
* a square product, under the explicit small-prime coverage hypothesis;
* distinct translated shifts in `[0, R]`, when the original entries are
  distinct and belong to `[U, U + R]`.

No quantitative Runge bound is asserted here.  That remaining analytic
statement is precisely what must turn a short nonzero kernel word into a
contradiction.
-/

namespace PaperC
namespace DefectCodeRunge

open scoped BigOperators

/--
A nonzero defect-code kernel word selects `2 * k` entries for some `k ≥ 1`.
This packages the parity condition `d = 2k ≥ 2` in Lemma 3.1.
-/
theorem kernelWord_support_card_eq_two_mul
    {m r : ℕ}
    (smallPrime : Fin r → ℕ) (f : Fin m → ℕ)
    (x : Fin m → F₂)
    (hx :
      x ∈ LinearMap.ker
        (DefectCodeRank.augmentedParityMap smallPrime f))
    (hx0 : x ≠ 0) :
    ∃ k : ℕ,
      1 ≤ k ∧ (HammingBound.wordSupport x).card = 2 * k := by
  classical
  have heven : Even (HammingBound.wordSupport x).card := by
    rw [HammingBound.card_wordSupport]
    exact DefectCodeRank.defectCode_kernelWord_even
      smallPrime f x hx
  have hpositive : 0 < (HammingBound.wordSupport x).card := by
    by_contra hnot
    have hempty : HammingBound.wordSupport x = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hnot)
    apply hx0
    funext i
    by_contra hi
    change x i ≠ (0 : F₂) at hi
    have himem : i ∈ HammingBound.wordSupport x := by
      simp [HammingBound.wordSupport, hi]
    rw [hempty] at himem
    simp at himem
  obtain ⟨k, hk⟩ := heven
  refine ⟨k, ?_, ?_⟩
  · omega
  · simpa [two_mul] using hk

/--
The entries selected by a defect-code kernel word satisfy the translated
Runge hypotheses: injective bounded shifts and a square product at the base
point.
-/
theorem kernelWord_translatedRungeInput
    {m r U R : ℕ}
    (smallPrime : Fin r → ℕ) (f : Fin m → ℕ)
    (hf0 : ∀ i, f i ≠ 0)
    (hcover : ∀ i p, parityVec (f i) p ≠ 0 →
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
      ∃ a : ℤ,
        (∏ i,
          ((U : ℤ) +
            RungeTranslation.translatedShift U selected i)) = a ^ 2 := by
  classical
  dsimp only
  let S := HammingBound.wordSupport x
  let selected : {i // i ∈ S} → ℕ := fun i ↦ f i
  have hselectedInjective : Function.Injective selected := by
    intro i j hij
    apply Subtype.ext
    exact hinjective hij
  have hselectedLower : ∀ i, U ≤ selected i := by
    intro i
    exact hlower i
  have hselectedUpper : ∀ i, selected i ≤ U + R := by
    intro i
    exact hupper i
  have hsquareFinset :
      ∃ q : ℕ, ∏ i ∈ S, f i = q ^ 2 := by
    simpa [S] using
      DefectCodeRank.square_product_of_mem_ker_augmentedParityMap
        smallPrime f hf0 hcover x hx
  have hsquare :
      ∃ q : ℕ, ∏ i, selected i = q ^ 2 := by
    obtain ⟨q, hq⟩ := hsquareFinset
    refine ⟨q, ?_⟩
    change ∏ i : {i // i ∈ S}, f i = q ^ 2
    rw [Finset.prod_coe_sort]
    exact hq
  exact RungeTranslation.translatedRungeInput
    hselectedInjective hselectedLower hselectedUpper hsquare

end DefectCodeRunge
end PaperC
