import PaperCV282.D4ClosurePointLaws
import PaperCV282.PoissonQuantitativeMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The centered target has infinite mass towards negative levels -/
namespace PaperC.V282.D4ClosureInfiniteMass

open MeasureTheory ProbabilityTheory Filter
open D4ClosurePointMeasure D4ClosurePointLaws D4ClosureIntegerLevels
open PoissonQuantitativeMoments
open scoped Topology NNReal ENNReal

noncomputable section

theorem negativeLevelRate_tendsto (theta : ℝ) :
    Tendsto (fun k : ℕ => (integerLevelRate theta (-(k : ℤ)) : ℝ)) atTop atTop := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h : Tendsto (fun k : ℕ => theta+(k : ℝ)-1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hnat.eventually_ge_atTop (b-theta+1)] with k hk
    linarith
  convert (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp h using 1
  ext k
  change (2 : ℝ)^(theta-((-(k : ℤ) : ℤ) : ℝ)-1) = (2 : ℝ)^(theta+(k : ℝ)-1)
  congr 1
  push_cast
  ring

theorem poisson_small_count_le (rate : ℝ≥0) (K : ℕ)
    (hr : 0<(rate : ℝ)) (hK : 2*(K : ℝ)≤(rate : ℝ)) :
    (poissonMeasure rate).real {n : ℕ | n≤K} ≤4/(rate : ℝ) := by
  calc
    _ ≤ (poissonMeasure rate).real {n : ℕ | (rate : ℝ)/2≤|(n : ℝ)-(rate : ℝ)|} := by
      apply measureReal_mono (μ := poissonMeasure rate) ?_ (measure_ne_top _ _)
      intro n hn
      have hnR : (n : ℝ)≤K := by exact_mod_cast hn
      have hneg : (n : ℝ)-(rate : ℝ)≤0 := by linarith
      simp only [Set.mem_setOf_eq,abs_of_nonpos hneg]
      linarith
    _ ≤ (rate : ℝ)/((rate : ℝ)/2)^2 := poisson_outer_tail rate _ (by positivity)
    _ = 4/(rate : ℝ) := by field_simp; ring

theorem total_mass_small_probability (theta : ℝ) (K : ℕ) :
    (integerSpatialSampleMeasure theta) {sample | integerPointMeasure sample Set.univ≤(K : ℝ≥0∞)}=0 := by
  let B : Set IntegerSpatialSample := {sample | integerPointMeasure sample Set.univ≤(K : ℝ≥0∞)}
  have hbound : ∀ᶠ k : ℕ in atTop,
      (integerSpatialSampleMeasure theta).real B ≤4/(integerLevelRate theta (-(k : ℤ)) : ℝ) := by
    filter_upwards [(negativeLevelRate_tendsto theta).eventually_ge_atTop (2*(K : ℝ)+1)] with k hk
    have he : B ⊆ {sample : IntegerSpatialSample | (sample (-(k : ℤ))).1≤K} := by
      intro sample hs
      have hl := measure_mono (μ := integerPointMeasure sample)
        (show Set.univ ×ˢ ({-(k : ℤ)} : Set ℤ) ⊆ Set.univ from Set.subset_univ _)
      rw [integerPointMeasure_level] at hl
      exact_mod_cast hl.trans hs
    have hrow : (integerSpatialSampleMeasure theta).real
        {sample : IntegerSpatialSample | (sample (-(k : ℤ))).1≤K} =
        (poissonMeasure (integerLevelRate theta (-(k : ℤ)))).real {n : ℕ | n≤K} := by
      have h := (hasLaw_integer_coordinate theta (-(k : ℤ))).fun_comp (hasLaw_integerSpatialCounts theta)
      rw [measureReal_def,measureReal_def,← h.map_eq,
        Measure.map_apply_of_aemeasurable h.aemeasurable ((Set.to_countable _).measurableSet)]
      rfl
    exact (measureReal_mono he).trans (hrow.trans_le
      (poisson_small_count_le _ K (by linarith) (by linarith)))
  have ht : Tendsto (fun k : ℕ => 4/(integerLevelRate theta (-(k : ℤ)) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (negativeLevelRate_tendsto theta)
  have hz : (integerSpatialSampleMeasure theta).real B=0 :=
    le_antisymm (ge_of_tendsto ht hbound) measureReal_nonneg
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top _ _)

/-- Local finiteness coexists with infinite total mass. The divergence is already
forced by the rows at negative integer levels. -/
theorem ae_integerPointMeasure_univ_top (theta : ℝ) :
    ∀ᵐ sample ∂integerSpatialSampleMeasure theta, integerPointMeasure sample Set.univ=⊤ := by
  have hall : ∀ᵐ sample ∂integerSpatialSampleMeasure theta,
      ∀ K : ℕ, ¬ integerPointMeasure sample Set.univ≤(K : ℝ≥0∞) := by
    apply ae_all_iff.mpr
    intro K
    apply ae_iff.mpr
    simpa only [not_not] using total_mass_small_probability theta K
  filter_upwards [hall] with sample hs
  by_contra h
  obtain ⟨K,hK⟩ := ENNReal.exists_nat_gt h
  exact hs K hK.le

end
end PaperC.V282.D4ClosureInfiniteMass
