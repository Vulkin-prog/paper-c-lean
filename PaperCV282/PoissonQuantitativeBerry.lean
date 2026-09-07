import PaperCV282.PoissonQuantitativeCDFGeometry

/-! # An internal Berry--Esseen bound for the actual Poisson law

The proof sums effective local errors on a genuine moving lattice and controls
the exterior by the exact second moments. No normal approximation is an input.
-/
namespace PaperC.V282.PoissonQuantitativeBerry

open MeasureTheory ProbabilityTheory Real Set
open PoissonQuantitativeLocal PoissonQuantitativeLattice PoissonQuantitativeSummation
open PoissonQuantitativeCells PoissonQuantitativeCDFGeometry PoissonQuantitativeMoments
open scoped NNReal

noncomputable section

def berryConstant : ℝ := localSummationConstant+cellSummationConstant+21

theorem berryConstant_ge_four : 4≤berryConstant := by
  have h1 : 0≤localSummationConstant := by unfold localSummationConstant;positivity
  have h2 : 0≤cellSummationConstant := by unfold cellSummationConstant;positivity
  unfold berryConstant
  linarith

theorem poisson_CDF_central_error (rate : ℝ≥0) (hr : 0<rate) (t : ℝ) :
    |(poissonMeasure rate).real {n : ℕ | latticePoint rate n≤t}-
      (poissonMeasure rate).real (centralCDFAtoms rate t)|≤4/(rate : ℝ) := by
  have h1 : {n : ℕ | latticePoint rate n≤t} ⊆ (centralCDFAtoms rate t : Set ℕ) ∪
      {n : ℕ | (rate : ℝ)/2≤|(n : ℝ)-rate|} := by
    intro n hn
    by_cases hc : |(n : ℝ)-rate|≤(rate : ℝ)/2
    · exact Or.inl ((mem_centralCDFAtoms rate.coe_nonneg n).mpr ⟨hc,hn⟩)
    · exact Or.inr (le_of_not_ge hc)
  have h2 : (centralCDFAtoms rate t : Set ℕ)⊆{n : ℕ | latticePoint rate n≤t}∪∅ := by
    intro n hn
    exact Or.inl (((mem_centralCDFAtoms rate.coe_nonneg n).mp hn).2)
  have h := probability_difference_le_errors (poissonMeasure rate) _ _ _ _ h1 h2
  simp only [measureReal_empty,add_zero] at h
  have ht := poisson_outer_tail rate ((rate : ℝ)/2) (by positivity)
  have he : (rate : ℝ)/((rate : ℝ)/2)^2=4/(rate : ℝ) := by field_simp;ring
  rw [he] at ht
  exact h.trans ht

theorem central_CDF_sum_error (rate : ℝ≥0) (hr : 1≤rate) (t : ℝ) :
    |(poissonMeasure rate).real (centralCDFAtoms rate t)-
      (gaussianReal 0 1).real (centralCDFCells rate t)|≤
      (localSummationConstant+cellSummationConstant)/sqrt rate := by
  let s := centralCDFAtoms (rate : ℝ) t
  have hi := integrable_gaussianPDFReal (μ := 0) (v := 1)
  rw [← sum_measureReal_singleton,gaussian_real_eq_integral,centralCDFCells,
    integral_biUnion_finset (s := latticeCell (rate : ℝ)) s (fun _ _ => measurableSet_Ico)
      (fun i _ j _ hij => latticeCell_pairwise (by linarith : (0 : ℝ)<rate) hij)
      (fun _ _ => hi.integrableOn)]
  have hlocal := poisson_central_sum_error_le rate hr s (fun n hn =>
    ((mem_centralCDFAtoms rate.coe_nonneg n).mp hn).1)
  have hcell := density_cells_sum_error_le (rate := (rate : ℝ)) hr s
  have htri : (∑ n∈s,|(poissonMeasure rate).real {n}-∫ x in latticeCell rate n,gaussianPDFReal 0 1 x|)≤
      (∑ n∈s,|(poissonMeasure rate).real {n}-gaussianLatticeMass rate (latticePoint rate n)|)+
      (∑ n∈s,|gaussianLatticeMass rate (latticePoint rate n)-∫ x in latticeCell rate n,gaussianPDFReal 0 1 x|) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun n _ => abs_sub_le _ _ _
  rw [← Finset.sum_sub_distrib]
  have hsum := (Finset.abs_sum_le_sum_abs (s := s) (f := fun n =>
    (poissonMeasure rate).real {n}-∫ x in latticeCell rate n,gaussianPDFReal 0 1 x)).trans htri
  exact hsum.trans (by simpa only [add_div] using add_le_add hlocal hcell)

/-- Uniform Kolmogorov bound, including every positive real rate and every threshold. -/
theorem poisson_gaussian_CDF_error (rate : ℝ≥0) (hr : 0<rate) (t : ℝ) :
    |(poissonMeasure rate).real {n : ℕ | ((n : ℝ)-(rate : ℝ))/sqrt rate≤t}-
      (gaussianReal 0 1).real (Iic t)|≤berryConstant/sqrt rate := by
  by_cases hlarge : (16 : ℝ)≤rate
  · have h1 := poisson_CDF_central_error rate hr t
    have h2 := central_CDF_sum_error rate (by linarith : 1≤rate) t
    have h3 := gaussian_CDF_cell_error (t := t) hlarge
    have htri := (abs_sub_le
      ((poissonMeasure rate).real {n : ℕ | latticePoint rate n≤t})
      ((poissonMeasure rate).real (centralCDFAtoms rate t))
      ((gaussianReal 0 1).real (Iic t))).trans
        (add_le_add h1 ((abs_sub_le _ ((gaussianReal 0 1).real (centralCDFCells rate t)) _).trans (add_le_add h2 h3)))
    have hs : sqrt (rate : ℝ)≤rate := by nlinarith [sq_sqrt rate.coe_nonneg,sqrt_nonneg (rate : ℝ)]
    have hh : 20/(rate : ℝ)≤20/sqrt (rate : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hs
    change |(poissonMeasure rate).real {n : ℕ | latticePoint rate n≤t}-(gaussianReal 0 1).real (Iic t)|≤_
    apply htri.trans
    unfold berryConstant
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith only [hh]
  · have hp : 0<sqrt (rate : ℝ) := sqrt_pos.mpr hr
    have hs : sqrt (rate : ℝ)≤4 := by nlinarith [sq_sqrt rate.coe_nonneg]
    have hb : (1 : ℝ)≤berryConstant/sqrt rate := (le_div_iff₀ hp).mpr (by linarith [berryConstant_ge_four])
    apply le_trans _ hb
    have ha0 : 0≤(poissonMeasure rate).real {n : ℕ | ((n : ℝ)-(rate : ℝ))/sqrt rate≤t} := measureReal_nonneg
    have ha1 : (poissonMeasure rate).real {n : ℕ | ((n : ℝ)-(rate : ℝ))/sqrt rate≤t}≤1 := measureReal_le_one
    have hb0 : 0≤(gaussianReal 0 1).real (Iic t) := measureReal_nonneg
    have hb1 : (gaussianReal 0 1).real (Iic t)≤1 := measureReal_le_one
    exact abs_le.mpr ⟨by linarith,by linarith⟩

end
end PaperC.V282.PoissonQuantitativeBerry
