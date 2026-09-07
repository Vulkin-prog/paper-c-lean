import PaperCV282.PoissonQuantitativeTailExterior

/-! # Relative moderate deviations for the actual Poisson upper tail -/
namespace PaperC.V282.PoissonQuantitativeModerate

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open PoissonQuantitativeLattice PoissonQuantitativeTailCells PoissonQuantitativeTailCutoff
open PoissonQuantitativeTailExterior PoissonQuantitativeMills PoissonQuantitativeCDFGeometry

open scoped NNReal

noncomputable section

def moderateConstant : ℝ :=
  (moderateCentralConstant+11530)*exp (3/2)*sqrt (2*π)

theorem poisson_tail_truncation_error (rate : ℝ≥0) (t : ℝ) :
    |(poissonMeasure rate).real (Ici ⌈(rate : ℝ)+sqrt rate*t⌉₊)-
      (poissonMeasure rate).real (moderateTailAtoms rate t)|≤
        (poissonMeasure rate).real (Ici (centralTailTop rate)) := by
  have h := probability_difference_le_errors (poissonMeasure rate)
    (Ici ⌈(rate : ℝ)+sqrt rate*t⌉₊) (moderateTailAtoms rate t)
    (Ici (centralTailTop rate)) ∅ (by
      intro n hn
      by_cases hk : n≤centralTailTop rate
      · exact Or.inl (Finset.mem_Icc.mpr ⟨hn,hk⟩)
      · exact Or.inr (le_of_lt (lt_of_not_ge hk))) (by
      intro n hn
      exact Or.inl (Finset.mem_Icc.mp hn).1)
  simpa using h

theorem gaussian_tail_cells_error {rate t : ℝ} (hr : 4096≤rate) (ht : 0≤t)
    (hcubic : t^3/sqrt rate≤1) :
    |(gaussianReal 0 1).real (⋃n∈moderateTailAtoms rate t,latticeCell rate n)-normalTail t|≤
      (5/sqrt rate)*exp (-t^2/2) := by
  have hc := moderate_cells_cover (by linarith : 16≤rate) ht
  have h := probability_difference_le_errors (gaussianReal 0 1)
    (Ici t) (⋃n∈moderateTailAtoms rate t,latticeCell rate n)
    (Ico t (t+1/sqrt rate)∪Ici (latticePoint rate (centralTailTop rate))) ∅
    hc.2 (by intro x hx;exact Or.inl (hc.1 hx))
  simp only [measureReal_empty,add_zero] at h
  have hround := gaussian_threshold_rounding_le (by linarith : 0<rate) ht
  have hext := gaussian_moderate_exterior_le hr ht hcubic
  have hu := measureReal_union_le (μ := gaussianReal 0 1)
    (Ico t (t+1/sqrt rate)) (Ici (latticePoint rate (centralTailTop rate)))
  rw [abs_sub_comm]
  exact h.trans (hu.trans ((add_le_add hround hext).trans_eq (by unfold normalTail at *;ring)))

theorem poisson_moderate_absolute_error (rate : ℝ≥0) (hr : (4096 : ℝ)≤rate) (t : ℝ)
    (ht : 0≤t) (hcubic : t^3/sqrt rate≤1) :
    |(poissonMeasure rate).real (Ici ⌈(rate : ℝ)+sqrt rate*t⌉₊)-normalTail t|≤
      ((moderateCentralConstant*((1+t^3)/(1+t))+5765)/sqrt rate)*exp (-t^2/2) := by
  have hp := poisson_tail_truncation_error rate t
  have hf := finite_tail_probability_error rate (by linarith : 1≤rate) t ht
    ((moderate_parameter_bound hr ht hcubic).trans (by nlinarith [sqrt_nonneg (rate : ℝ)] : sqrt (rate : ℝ)/8≤sqrt rate/2))
    hcubic (moderateTailAtoms rate t) (fun n hn => mem_moderateTailAtoms (by linarith) ht hn)
  have hg := gaussian_tail_cells_error hr ht hcubic
  have he := poisson_moderate_exterior_le rate hr t ht hcubic
  have htri := (abs_sub_le ((poissonMeasure rate).real (Ici ⌈(rate : ℝ)+sqrt rate*t⌉₊))
    ((poissonMeasure rate).real (moderateTailAtoms rate t)) (normalTail t)).trans
      (add_le_add (hp.trans he)
        ((abs_sub_le ((poissonMeasure rate).real (moderateTailAtoms rate t))
          ((gaussianReal 0 1).real (⋃n∈moderateTailAtoms rate t,latticeCell rate n))
          (normalTail t)).trans (add_le_add hf hg)))
  exact htri.trans_eq (by ring)

theorem one_add_le_cubic (t : ℝ) (ht : 0≤t) : 1+t≤2*(1+t^3) := by
  by_cases h : t≤1
  · nlinarith [pow_nonneg ht 3]
  · have h1 : 1≤t := le_of_lt (lt_of_not_ge h)
    have hh := mul_nonneg (show 0≤t^2-1 by nlinarith) ht
    nlinarith

/-- The displayed relative error in D.1, with an explicit universal constant. -/
theorem poisson_moderate_relative_error (rate : ℝ≥0) (hr : (4096 : ℝ)≤rate) (t : ℝ)
    (ht : 0≤t) (hcubic : t^3/sqrt rate≤1) :
    |(poissonMeasure rate).real (Ici ⌈(rate : ℝ)+sqrt rate*t⌉₊)/normalTail t-1|≤
      moderateConstant*((1+t^3)/sqrt rate) := by
  have hp := normalTail_pos t ht
  have hs : 0<sqrt (rate : ℝ) := by positivity
  have htp : 0<1+t := by positivity
  have hpi : 0<sqrt (2*π) := by positivity
  have hm := normalTail_lower t ht
  have h := poisson_moderate_absolute_error rate hr t ht hcubic
  conv_lhs => rw [← div_self (ne_of_gt hp),← sub_div,abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have hc : 0≤moderateCentralConstant := by
    unfold moderateCentralConstant PoissonQuantitativeTailSum.tailSummationConstant
    positivity
  have hnum : moderateCentralConstant*((1+t^3)/(1+t))+5765≤
      (moderateCentralConstant+11530)*((1+t^3)/(1+t)) := by
    have hw := one_add_le_cubic t ht
    have hw' : 1≤2*((1+t^3)/(1+t)) := by
      rw [← mul_div_assoc]
      exact (le_div_iff₀ htp).mpr (by simpa using hw)
    nlinarith
  have hconst : 0≤moderateConstant*((1+t^3)/sqrt (rate : ℝ)) := by
    unfold moderateConstant
    positivity
  have hmul := mul_le_mul_of_nonneg_left hm hconst
  have he : exp (-t^2/2-3/2)=exp (-t^2/2)/exp (3/2) := by rw [exp_sub]
  have hid : moderateConstant*((1+t^3)/sqrt (rate : ℝ))*
      (exp (-t^2/2-3/2)/(sqrt (2*π)*(1+t)))=
      (((moderateCentralConstant+11530)*((1+t^3)/(1+t)))/sqrt rate)*exp (-t^2/2) := by
    rw [he]
    unfold moderateConstant
    field_simp
  rw [hid] at hmul
  exact h.trans ((mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hnum hs.le) (exp_pos _).le).trans hmul)

end
end PaperC.V282.PoissonQuantitativeModerate
