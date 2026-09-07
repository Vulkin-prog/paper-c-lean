import PaperCV282.MacroscopicFirstMoment

/-!
# Macroscopic dictionary first moments in the infinite source model

The complete window defect weight also controls prescribed words.
The threshold is independent of the position mask, dictionary size and
individual words, so dictionaries may vary with the ambient scale.
-/

namespace PaperC.V282.MacroscopicWordFirstMoment

open MeasureTheory InfiniteRademacher InfiniteWordFirstMoment InfiniteWordTransfer
open MacroscopicGeometry MacroscopicFirstMoment
open scoped BigOperators

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- Even the sum of absolute individual word-probability errors has the uniform macroscopic bound. -/
theorem sum_abs_word_probability_error_le_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ s : Finset ℕ, s ⊆ macroscopicStarts M delta → ∀ W : Finset (Fin (L + 1) → F₂),
        (∑ x ∈ s, ∑ b ∈ W, |infiniteWordProbability x (L + 1) b - 1 / (2 : ℝ) ^ (L + 1)|) ≤
          ((W.card : ℝ) / (2 : ℝ) ^ (L + 1)) * (M : ℝ) ^ (1 / (2 : ℝ) + epsilon) := by
  obtain ⟨Mmass, hmass⟩ := sum_fullDefectWeight_le_half_power_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Mmass 2, ?_⟩
  intro M hM L hlo hhi s hs W
  have hpos : ∀ x ∈ s, 2 ≤ x := fun x hx =>
    (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc (by omega) hdelta (hs hx))).1
  exact (sum_abs_wordProbability_sub_baseline_le (L + 1) s W hpos).trans
    (mul_le_mul_of_nonneg_left (hmass M (by omega) L hlo hhi s hs) (by positivity))

/-- The dictionary probability sum keeps its actual cardinality in both baseline and error. -/
theorem macroscopic_word_probability_sum_le_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ s : Finset ℕ, s ⊆ macroscopicStarts M delta → ∀ W : Finset (Fin (L + 1) → F₂),
        |wordProbabilitySum (L + 1) s W - (s.card : ℝ) * (W.card : ℝ) / (2 : ℝ) ^ (L + 1)| ≤
          ((W.card : ℝ) / (2 : ℝ) ^ (L + 1)) * (M : ℝ) ^ (1 / (2 : ℝ) + epsilon) := by
  obtain ⟨Mmass, hmass⟩ := sum_fullDefectWeight_le_half_power_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Mmass 2, ?_⟩
  intro M hM L hlo hhi s hs W
  have hpos : ∀ x ∈ s, 2 ≤ x := fun x hx =>
    (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc (by omega) hdelta (hs hx))).1
  exact (abs_wordProbabilitySum_sub_baseline_le (L + 1) s W hpos).trans
    (mul_le_mul_of_nonneg_left (hmass M (by omega) L hlo hhi s hs) (by positivity))

/-- The macroscopic extension of the summed word corollary, as a genuine source-model expectation. -/
theorem corollary_two_six_macroscopic_expectation
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ s : Finset ℕ, s ⊆ macroscopicStarts M delta → ∀ W : Finset (Fin (L + 1) → F₂),
        |(∫ omega, wordOccurrenceCount (L + 1) s W omega ∂infiniteRademacherMeasure) -
          (s.card : ℝ) * (W.card : ℝ) / (2 : ℝ) ^ (L + 1)| ≤
          ((W.card : ℝ) / (2 : ℝ) ^ (L + 1)) * (M : ℝ) ^ (1 / (2 : ℝ) + epsilon) := by
  obtain ⟨Mzero, hzero⟩ := macroscopic_word_probability_sum_le_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨Mzero, ?_⟩
  intro M hM L hlo hhi s hs W
  rw [integral_wordOccurrenceCount]
  exact hzero M hM L hlo hhi s hs W

end
end PaperC.V282.MacroscopicWordFirstMoment
