import PaperCV282.IidWordCosts
import PaperCV282.IidWordInfinite

/-! # The actual iid word field compared with the same independent Poisson target -/
namespace PaperC.V282.IidWordPoisson

open IidWordField IidWordDependency IidWordCosts IidWordInfinite
open DictionaryFieldModel DictionaryFieldTransfer WordOverlapSum SectionTwelveMoments
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput
open scoped BigOperators NNReal

noncomputable section

/-- Distance of the true iid coordinate field to its site-and-word product Poisson target. -/
def iidPoissonDistance (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) : ℝ :=
  massTotalVariation (iidFieldLaw N L W) (poissonFieldMass (allWordRates N L W (dyadicBlock N)))

theorem iidPoissonDistance_nonneg (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    0 ≤ iidPoissonDistance N L W := massTotalVariation_nonneg _ _

/-- Finite iid process comparison with actual local costs and no arithmetic input. -/
theorem iidPoissonDistance_le (hAGG : ProcessAGGStatement) {N L : ℕ}
    (W : Finset (Fin (L+1) → F₂)) (hW : W.Nonempty) (hN : 1 ≤ N) :
    iidPoissonDistance N L W ≤
      4 * ((N : ℝ) * (dictionaryRate L W : ℝ) * overlapWeight W +
        (N : ℝ) * (L+1 : ℝ) * (dictionaryRate L W : ℝ)^2) := by
  have h := process_totalVariation_le hAGG (iidUniformPMF (dyadicCutoff N L + 1))
    (iidFieldIndicator N L W) (iidWordGraph N L W) (hasExactDependencyGraph_iidWordField W hN)
  rw [iidField_rates_eq] at h
  have hOne := bOne_iid_le N L W
  have hTwo := bTwo_iid_le W hW hN
  change iidPoissonDistance N L W ≤ _ at h
  nlinarith

/-- The printed iid error is O(Lambda*Omega+Lambda^2*B/N), with absolute constant4. -/
theorem iidPoissonDistance_le_normalized (hAGG : ProcessAGGStatement) {N L : ℕ}
    (W : Finset (Fin (L+1) → F₂)) (hW : W.Nonempty) (hN : 1 ≤ N) :
    iidPoissonDistance N L W ≤
      4 * (((N : ℝ) * (dictionaryRate L W : ℝ)) * overlapWeight W +
        ((N : ℝ) * (dictionaryRate L W : ℝ))^2 * (L+1 : ℝ) / N) := by
  apply (iidPoissonDistance_le hAGG W hW hN).trans_eq
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp

/-- The same exact comparison for the word field in the full infinite iid source. -/
theorem infinite_iid_poisson_distance_le (hAGG : ProcessAGGStatement) {N L : ℕ}
    (W : Finset (Fin (L+1) → F₂)) (hW : W.Nonempty) (hN : 1 ≤ N) :
    massTotalVariation (infiniteIidFieldLaw N L W) (poissonFieldMass (allWordRates N L W (dyadicBlock N))) ≤
      4 * (((N : ℝ) * (dictionaryRate L W : ℝ)) * overlapWeight W +
        ((N : ℝ) * (dictionaryRate L W : ℝ))^2 * (L+1 : ℝ) / N) := by
  rw [infiniteIidFieldLaw_eq_iidFieldLaw]
  exact iidPoissonDistance_le_normalized hAGG W hW hN

end
end PaperC.V282.IidWordPoisson
