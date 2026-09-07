import PaperCV282.ConditionedCountableLaw

/-! # Sharp conditioning of arbitrary probability laws

Total variation is the supremum over measurable events, with probability
normalization (no factor two). The conditioning denominator is the larger
of the two actual event probabilities.
-/
namespace PaperC.V282.SharpConditioning

open MeasureTheory ProbabilityTheory InfiniteMassCoupling FiniteFieldTotalVariation
open ConditionedCountableLaw

noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

def measureTotalVariation (μ ν : Measure α) : ℝ :=
  sSup {r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r = |μ.real A - ν.real A|}

theorem variation_set_nonempty (μ ν : Measure α) :
    Set.Nonempty {r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r = |μ.real A - ν.real A|} :=
  ⟨0, ∅, MeasurableSet.empty, by simp⟩

theorem variation_set_bddAbove (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove {r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r = |μ.real A - ν.real A|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨A, _, rfl⟩
  have hm := measureReal_mono (μ := μ) (Set.subset_univ A)
  have hn := measureReal_mono (μ := ν) (Set.subset_univ A)
  simp only [probReal_univ] at hm hn
  exact abs_sub_le_iff.mpr ⟨by linarith [measureReal_nonneg (μ := ν) (s := A)],
    by linarith [measureReal_nonneg (μ := μ) (s := A)]⟩

theorem discrepancy_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set α) (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ measureTotalVariation μ ν :=
  le_csSup (variation_set_bddAbove μ ν) ⟨A, hA, rfl⟩

theorem measureTotalVariation_le_iff (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (r : ℝ) :
    measureTotalVariation μ ν ≤ r ↔ ∀ A : Set α, MeasurableSet A → |μ.real A - ν.real A| ≤ r := by
  constructor
  · intro h A hA
    exact (discrepancy_le μ ν A hA).trans h
  · intro h
    apply csSup_le (variation_set_nonempty μ ν)
    rintro t ⟨A, hA, rfl⟩
    exact h A hA

theorem measureTotalVariation_nonneg (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ measureTotalVariation μ ν := by
  simpa using discrepancy_le μ ν ∅ MeasurableSet.empty

theorem measureTotalVariation_le_one (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    measureTotalVariation μ ν ≤ 1 :=
by
  apply (measureTotalVariation_le_iff μ ν 1).mpr
  intro A _
  have hm := measureReal_mono (μ := μ) (Set.subset_univ A)
  have hn := measureReal_mono (μ := ν) (Set.subset_univ A)
  simp only [probReal_univ] at hm hn
  exact abs_sub_le_iff.mpr ⟨by linarith [measureReal_nonneg (μ := ν) (s := A)],
    by linarith [measureReal_nonneg (μ := μ) (s := A)]⟩

theorem measureTotalVariation_comm (μ ν : Measure α) :
    measureTotalVariation μ ν = measureTotalVariation ν μ := by
  unfold measureTotalVariation
  congr 1
  ext r
  simp only [abs_sub_comm]

theorem measureTotalVariation_map_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → β} (hf : Measurable f) :
    measureTotalVariation (μ.map f) (ν.map f) ≤ measureTotalVariation μ ν := by
  letI instProbabilityLocal1 : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI instProbabilityLocal2 : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro A hA
  simp only [Measure.real, Measure.map_apply hf hA]
  exact discrepancy_le μ ν (f ⁻¹' A) (hf hA)

theorem cond_real_apply (μ : Measure α) (B : Set α) (hB : MeasurableSet B) (A : Set α) :
    (cond μ B).real A = μ.real (B ∩ A) / μ.real B := by
  simp only [Measure.real, cond_apply hB, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

theorem normalized_difference_le {a b p q ε : ℝ}
    (ha : 0 ≤ a) (haq : a ≤ q) (hq : 0 < q) (hp : 0 < p) (hqp : q ≤ p)
    (hba : b - a ≤ ε) (hcom : (p - b) - (q - a) ≤ ε) :
    |a / q - b / p| ≤ ε / p := by
  apply abs_sub_le_iff.mpr
  constructor
  · apply (le_div_iff₀ hp).mpr
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    apply (sub_le_iff_le_add).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hq).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hqp) (sub_nonneg.mpr haq)]
  · apply (le_div_iff₀ hp).mpr
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    rw [div_mul_eq_mul_div]
    have hle : a ≤ a * p / q := (le_div_iff₀ hq).mpr
      (mul_le_mul_of_nonneg_left hqp ha)
    linarith

theorem conditioning_ordered_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (B : Set α) (hB : MeasurableSet B) {ε : ℝ}
    (htv : measureTotalVariation μ ν ≤ ε)
    (hq : 0 < μ.real B) (hp : 0 < ν.real B) (hqp : μ.real B ≤ ν.real B) :
    measureTotalVariation (cond μ B) (cond ν B) ≤ ε / ν.real B := by
  letI instProbabilityLocal3 : IsProbabilityMeasure (cond μ B) := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos μ hq)
  letI instProbabilityLocal4 : IsProbabilityMeasure (cond ν B) := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos ν hp)
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro A hA
  rw [cond_real_apply μ B hB, cond_real_apply ν B hB]
  have hAB := (discrepancy_le μ ν (B ∩ A) (hB.inter hA)).trans htv
  have hBC := (discrepancy_le μ ν (B \ A) (hB.diff hA)).trans htv
  have hm : μ.real (B \ A) = μ.real B - μ.real (B ∩ A) := by
    linarith [measureReal_sdiff_add_inter (μ := μ) (s := B) hA]
  have hn : ν.real (B \ A) = ν.real B - ν.real (B ∩ A) := by
    linarith [measureReal_sdiff_add_inter (μ := ν) (s := B) hA]
  rw [hm, hn] at hBC
  exact normalized_difference_le (measureReal_nonneg (μ := μ) (s := B ∩ A))
    (measureReal_mono (μ := μ) Set.inter_subset_left) hq hp hqp
    (abs_sub_le_iff.mp hAB).2 (abs_sub_le_iff.mp hBC).2

/-- Lemma 6.2, with the sharp denominator and positivity of the actual event. -/
theorem lemma_six_two (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (B : Set α) (hB : MeasurableSet B) {ε : ℝ}
    (htv : measureTotalVariation μ ν ≤ ε) (hε : ε < ν.real B) :
    0 < μ.real B ∧
    measureTotalVariation (cond μ B) (cond ν B) ≤ ε / max (ν.real B) (μ.real B) ∧
    ε / max (ν.real B) (μ.real B) ≤ ε / ν.real B := by
  have he : 0 ≤ ε := (measureTotalVariation_nonneg μ ν).trans htv
  have hp : 0 < ν.real B := lt_of_le_of_lt he hε
  have hdiff := (discrepancy_le μ ν B hB).trans htv
  have hq : 0 < μ.real B := by
    have h := (abs_sub_le_iff.mp hdiff).2
    linarith
  refine ⟨hq, ?_, ?_⟩
  · rcases le_total (μ.real B) (ν.real B) with h | h
    · rw [max_eq_left h]
      exact conditioning_ordered_le μ ν B hB htv hq hp h
    · rw [max_eq_right h, measureTotalVariation_comm]
      apply conditioning_ordered_le ν μ B hB _ hp hq h
      rwa [measureTotalVariation_comm]
  · exact div_le_div_of_nonneg_left he hp (le_max_left _ _)

end
end PaperC.V282.SharpConditioning
