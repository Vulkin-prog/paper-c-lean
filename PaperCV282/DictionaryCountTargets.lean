import PaperCV282.DictionaryFieldStatistics
import PaperCV282.DictionaryFieldRates
import PaperCV282.PoissonFieldAggregation

/-!
# Exact scalar and vector targets for dictionary occurrence counts

The statistics are applied to the complete actual site-and-word field.
Their Poisson targets are proved by aggregation, so every word count has
its stated mean and the entire vector has the independent product law.
-/

namespace PaperC.V282.DictionaryCountTargets

open DictionaryFieldModel DictionaryFieldTransfer DictionaryFieldRates DictionaryFieldInfinite
open DictionaryFieldStatistics InfiniteRademacher InfiniteConditionalWords InfiniteWordTransfer
open ConditionalStartProbability ConditionalAGGAverage SectionThirteenCouplings
open SectionThirteenFiniteBound FiniteFieldPoissonCoupling FiniteFieldTotalVariation
open ScalarSteinInput PoissonFieldMeasure PoissonFieldAggregation MassPushforward
open MeasureTheory
open scoped BigOperators NNReal

noncomputable section

/-- Total occurrences of dictionary words on a deterministic set of sites. -/
def maskedDictionaryCount {N L : ℕ} (W : Finset (Fin (L+1) → F₂)) (mask : Finset ℕ)
    (k : DictionaryIndex N L W → ℕ) : ℕ := by
  classical
  exact ∑ i, if i.1.val ∈ mask then k i else 0

def maskedDictionaryTargetRate (L : ℕ) (W : Finset (Fin (L+1) → F₂)) (mask : Finset ℕ) : ℝ≥0 :=
  mask.card * dictionaryRate L W

/-- Vector of individual word counts, retaining all word labels. -/
def dictionaryWordCounts {N L : ℕ} (W : Finset (Fin (L+1) → F₂))
    (k : DictionaryIndex N L W → ℕ) : {b // b ∈ W} → ℕ := fun b => ∑ x, k (x,b)

def individualWordCountRate (N L : ℕ) : ℝ≥0 := N * wordRate L

theorem maskedDictionaryTargetRate_coe (L : ℕ) (W : Finset (Fin (L+1) → F₂)) (mask : Finset ℕ) :
    (maskedDictionaryTargetRate L W mask : ℝ) = mask.card * W.card / (2:ℝ)^(L+1) := by
  simp only [maskedDictionaryTargetRate,NNReal.coe_mul,NNReal.coe_natCast,dictionaryRate_coe]
  ring

theorem individualWordCountRate_coe (N L : ℕ) :
    (individualWordCountRate N L : ℝ) = N / (2:ℝ)^(L+1) := by
  simp only [individualWordCountRate,NNReal.coe_mul,NNReal.coe_natCast,wordRate_coe]
  ring

/-- Sum of the selected coordinate rates is exactly the masked mean. -/
theorem sum_masked_dictionary_rates {N L : ℕ} (W : Finset (Fin (L+1) → F₂))
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    (∑ i : DictionaryIndex N L W, if i.1.val ∈ mask then wordRate L else 0) =
      maskedDictionaryTargetRate L W mask := by
  classical
  apply NNReal.coe_injective
  push_cast
  simp only [apply_ite,NNReal.coe_zero]
  rw [sum_dictionaryIndex_site N L W (fun x => if x ∈ mask then (wordRate L : ℝ) else 0),
    ← Finset.sum_filter]
  have hf : (dyadicBlock N).filter (fun x => x ∈ mask) = mask := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hx => ⟨hmask hx,hx⟩⟩
  rw [hf]
  simp only [Finset.sum_const,nsmul_eq_mul,maskedDictionaryTargetRate_coe,wordRate_coe]
  ring

/-- The scalar image of the full product field has precisely the claimed Poisson mean. -/
theorem pushforward_dictionary_count_target {N L : ℕ} (W : Finset (Fin (L+1) → F₂))
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    pushforwardMass (maskedDictionaryCount W mask)
      (poissonFieldMass (allWordRates N L W (dyadicBlock N))) =
        poissonMass (maskedDictionaryTargetRate L W mask) := by
  classical
  rw [allWordRates_full_eq]
  have h := pushforward_poissonFieldMass_sum (fun _ : DictionaryIndex N L W => wordRate L)
    (Finset.univ.filter (fun i => i.1.val ∈ mask))
  simp only [Finset.sum_filter] at h
  rw [sum_masked_dictionary_rates W mask hmask] at h
  exact h

/-- Exact independent product of the Poisson word-count laws. -/
theorem pushforward_dictionary_word_counts_target (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    pushforwardMass (dictionaryWordCounts W)
      (poissonFieldMass (allWordRates N L W (dyadicBlock N))) =
        poissonFieldMass (fun _ : {b // b ∈ W} => individualWordCountRate N L) := by
  classical
  rw [allWordRates_full_eq]
  have h := pushforward_poissonFieldMass_column_sums
    (fun _ : {x // x ∈ dyadicBlock N} × {b // b ∈ W} => wordRate L)
    (fun _ => Finset.univ)
  unfold dictionaryWordCounts
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,
    TouchingPairs.card_dyadicBlock,nsmul_eq_mul,individualWordCountRate] using h

/-- Actual source count law compared to its exact scalar Poisson target. -/
theorem infinite_dictionary_count_distance_le {N L : ℕ} (W : Finset (Fin (L+1) → F₂))
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    massTotalVariation
      (fun b => (infiniteRademacherMeasure {omega |
        maskedDictionaryCount W mask (infiniteDictionaryField N L W omega) = b}).toReal)
      (poissonMass (maskedDictionaryTargetRate L W mask)) ≤ dictionaryDistance N L W := by
  rw [← pushforward_dictionary_count_target W mask hmask]
  exact infinite_statistic_distance_le W _

/-- Actual source vector compared to the product of independent Poisson count laws. -/
theorem infinite_dictionary_word_counts_distance_le (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    massTotalVariation
      (fun b => (infiniteRademacherMeasure {omega |
        dictionaryWordCounts W (infiniteDictionaryField N L W omega) = b}).toReal)
      (poissonFieldMass (fun _ : {b // b ∈ W} => individualWordCountRate N L)) ≤
        dictionaryDistance N L W := by
  rw [← pushforward_dictionary_word_counts_target N L W]
  exact infinite_statistic_distance_le W _

/-- Averaged true conditional count laws obey the same full-field bound. -/
theorem average_dictionary_count_distance_le {N L Y : ℕ} (W : Finset (Fin (L+1) → F₂))
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      massTotalVariation
        (fun b => (infiniteRademacherMeasure
          ({omega | maskedDictionaryCount W mask (infiniteDictionaryField N L W omega) = b} ∩
            infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal /
          (infiniteRademacherMeasure (infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal)
        (poissonMass (maskedDictionaryTargetRate L W mask))) ≤ dictionaryConditionalDistance N L Y W := by
  rw [← pushforward_dictionary_count_target W mask hmask]
  exact average_source_statistic_distance_le W _

end
end PaperC.V282.DictionaryCountTargets
