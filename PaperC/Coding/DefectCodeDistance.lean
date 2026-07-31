import PaperC.Coding.DefectCodeRepresentation
import Mathlib.Data.Fintype.EquivFin

/-!
# From the finite Runge obstruction to the defect-code distance

This file closes the logical gap between the arithmetic Runge input attached
to a kernel word and the minimum-weight hypothesis used by the Hamming bound.

If every square-product datum of size `2 * k`, for `1 ≤ k ≤ t`, with
injective shifts bounded by `R` is impossible, then every nonzero word in the
kernel of the augmented parity map has weight strictly larger than `2 * t`.
-/

namespace PaperC
namespace DefectCodeDistance

open scoped BigOperators

/--
There is no Runge square-product datum based at `U`, with shifts bounded by
`R`, whose half-cardinality lies in `[1, t]`.
-/
def NoShortRungeSquare (U R t : ℕ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → k ≤ t →
    ∀ γ : Fin (2 * k) → ℤ,
      Function.Injective γ →
      (∀ i, |γ i| ≤ R) →
      ¬ ∃ q : ℤ, ∏ i, ((U : ℤ) + γ i) = q ^ 2

/--
Reindex translated Runge data on a finite support of cardinality `2 * k`
by the standard type `Fin (2 * k)`.
-/
theorem reindex_translatedRungeInput
    {α : Type*} {S : Finset α} {U R k : ℕ}
    (selected : S → ℕ)
    (hcard : S.card = 2 * k)
    (hinjective :
      Function.Injective
        (RungeTranslation.translatedShift U selected))
    (hbounded :
      ∀ i, |RungeTranslation.translatedShift U selected i| ≤ R)
    (hsquare :
      ∃ q : ℤ,
        (∏ i,
          ((U : ℤ) +
            RungeTranslation.translatedShift U selected i)) = q ^ 2) :
    ∃ γ : Fin (2 * k) → ℤ,
      Function.Injective γ ∧
      (∀ i, |γ i| ≤ R) ∧
      ∃ q : ℤ, (∏ i, ((U : ℤ) + γ i)) = q ^ 2 := by
  classical
  let e : Fin (2 * k) ≃ S :=
    (Finset.equivFinOfCardEq hcard).symm
  let γ : Fin (2 * k) → ℤ :=
    fun i ↦ RungeTranslation.translatedShift U selected (e i)
  refine ⟨γ, ?_, ?_, ?_⟩
  · exact hinjective.comp e.injective
  · intro i
    exact hbounded (e i)
  · obtain ⟨q, hq⟩ := hsquare
    refine ⟨q, ?_⟩
    have hreindex :=
      e.prod_comp
        (fun i : S ↦
          (U : ℤ) +
            RungeTranslation.translatedShift U selected i)
    exact (by simpa [γ] using hreindex.trans hq)

/--
The reusable distance bridge for Proposition 3.2.

The hypotheses `hrep`, `hs`, `ha`, and `hsmall` supply the square product
selected by a kernel word.  Injectivity and interval membership supply the
translated shifts.  `hRunge` rules out every possible nonzero word of weight
at most `2 * t`.
-/
theorem minWeightAbove_augmentedParityMap_of_noShortRungeSquare
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
    (hRunge : NoShortRungeSquare U R t) :
    HammingBound.MinWeightAbove
      (LinearMap.ker
        (DefectCodeRank.augmentedParityMap smallPrime f))
      (2 * t) := by
  classical
  intro c hc
  let x : Fin m → F₂ := (c : Fin m → F₂)
  have hxker :
      x ∈ LinearMap.ker
        (DefectCodeRank.augmentedParityMap smallPrime f) :=
    c.property
  have hx0 : x ≠ 0 := by
    intro hx
    apply hc
    apply Subtype.ext
    exact hx
  obtain ⟨k, hk1, hcard⟩ :=
    DefectCodeRunge.kernelWord_support_card_eq_two_mul
      smallPrime f x hxker hx0
  have hnorm :
      hammingNorm x = 2 * k := by
    rw [← HammingBound.card_wordSupport]
    exact hcard
  by_contra hnot
  have hweight_le :
      hammingNorm x ≤ 2 * t :=
    Nat.le_of_not_gt hnot
  have hkt : k ≤ t := by
    omega
  let S := HammingBound.wordSupport x
  let selected : S → ℕ := fun i ↦ f i
  have hinput :
      Function.Injective
          (RungeTranslation.translatedShift U selected) ∧
        (∀ i,
          |RungeTranslation.translatedShift U selected i| ≤ R) ∧
        ∃ q : ℤ,
          (∏ i,
            ((U : ℤ) +
              RungeTranslation.translatedShift U selected i)) = q ^ 2 := by
    simpa only [S, selected] using
      (DefectCodeRepresentation.kernelWord_translatedRungeInput_of_defectRepresentations
          smallPrime f s a hrep hs ha hsmall hinjective hlower hupper
          x hxker)
  have hScard : S.card = 2 * k := by
    simpa only [S] using hcard
  obtain ⟨γ, hγinjective, hγbounded, hγsquare⟩ :=
    reindex_translatedRungeInput selected hScard
      hinput.1 hinput.2.1 hinput.2.2
  exact hRunge k hk1 hkt γ hγinjective hγbounded hγsquare

end DefectCodeDistance
end PaperC
