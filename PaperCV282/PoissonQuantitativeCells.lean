import PaperCV282.PoissonQuantitativeSummation

/-! # Gaussian cell discretization on the actual Poisson lattice -/
namespace PaperC.V282.PoissonQuantitativeCells

open MeasureTheory ProbabilityTheory Real Set PoissonQuantitativeLocal PoissonQuantitativeLattice

noncomputable section

theorem standard_density_derivative (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_pow 2 x).neg.div_const 2).exp).const_mul ((sqrt (2*π))⁻¹)
  have he : gaussianPDFReal 0 1=(fun y : ℝ => (sqrt (2*π))⁻¹*exp (-y^2/2)) := by
    funext y
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [he]
  convert! h using 1; simp only [Pi.neg_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one]; ring

theorem density_derivative_decay (x : ℝ) :
    |-x*gaussianPDFReal 0 1 x|≤6*exp (-x^2/3) := by
  have hpi : 1≤sqrt (2*π) := one_le_sqrt.mpr (by have h := pi_gt_three;linarith)
  have hp : (sqrt (2*π))⁻¹≤1 := inv_le_one_of_one_le₀ hpi
  have hx : |x|≤6*exp (x^2/6) := by
    have h := add_one_le_exp (x^2/6)
    have hh : |x|≤1+x^2 := by nlinarith [sq_abs x,sq_nonneg (|x|-1)]
    nlinarith
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,abs_mul,abs_neg,
    abs_of_nonneg (inv_nonneg.mpr (sqrt_nonneg (2*π))),abs_of_pos (exp_pos _)]
  calc
    _≤|x| *(1*exp (-x^2/2)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (exp_pos _).le) (abs_nonneg _)
    _≤(6*exp (x^2/6))*exp (-x^2/2) := by simpa using mul_le_mul_of_nonneg_right hx (exp_pos (-x^2/2)).le
    _=6*exp (-x^2/3) := by rw [mul_assoc,← exp_add];congr 1;ring

theorem density_cell_lipschitz {rate : ℝ} (hr : 1≤rate) (n : ℕ) {x : ℝ}
    (hx : x∈latticeCell rate n) :
    |gaussianPDFReal 0 1 x-gaussianPDFReal 0 1 (latticePoint rate n)|≤
      (6*exp (1/3)*exp (-(latticePoint rate n)^2/6))*(1/sqrt rate) := by
  have hs : 1≤sqrt rate := one_le_sqrt.mpr hr
  have hh : 1/sqrt rate≤1 := (div_le_one (by positivity)).mpr hs
  have hd (y : ℝ) (hy : y∈Icc (latticePoint rate n) (latticePoint rate n+1/sqrt rate)) :
      ‖-y*gaussianPDFReal 0 1 y‖≤6*exp (1/3)*exp (-(latticePoint rate n)^2/6) := by
    have hd0 : 0≤y-latticePoint rate n := sub_nonneg.mpr hy.1
    have hd1 : y-latticePoint rate n≤1 := by have h := hy.2;linarith
    have hd2 : (y-latticePoint rate n)^2≤1 := by nlinarith
    have hb : (latticePoint rate n)^2≤2*y^2+2 := by nlinarith [sq_nonneg (2*y-latticePoint rate n)]
    rw [Real.norm_eq_abs]
    apply (density_derivative_decay y).trans
    rw [mul_assoc,← exp_add]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith)) (by norm_num)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (standard_density_derivative y).hasDerivWithinAt) hd (convex_Icc _ _)
    (show x∈Icc (latticePoint rate n) (latticePoint rate n+1/sqrt rate) from ⟨hx.1,hx.2.le⟩)
    (show latticePoint rate n∈Icc (latticePoint rate n) (latticePoint rate n+1/sqrt rate) from ⟨le_rfl,by linarith [show 0≤1/sqrt rate by positivity]⟩)
  simp only [Real.norm_eq_abs] at h
  have hdist : |latticePoint rate n-x|≤1/sqrt rate := by
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hx.1)]
    have hh := hx.2
    linarith
  simpa only [abs_sub_comm] using h.trans (mul_le_mul_of_nonneg_left hdist (by positivity))

theorem density_cell_error_le {rate : ℝ} (hr : 1≤rate) (n : ℕ) :
    |gaussianLatticeMass rate (latticePoint rate n)-∫ x in latticeCell rate n,gaussianPDFReal 0 1 x|≤
      (6*exp (1/3))*(1/sqrt rate)^2*exp (-(latticePoint rate n)^2/6) := by
  have hi := integrable_gaussianPDFReal (μ := 0) (v := 1)
  have hc : IntegrableOn (fun _ : ℝ => gaussianPDFReal 0 1 (latticePoint rate n)) (latticeCell rate n) :=
    integrableOn_const (by rw [latticeCell,volume_Ico];exact ENNReal.ofReal_ne_top)
  have he : gaussianLatticeMass rate (latticePoint rate n)-∫ x in latticeCell rate n,gaussianPDFReal 0 1 x=
      ∫ x in latticeCell rate n,gaussianPDFReal 0 1 (latticePoint rate n)-gaussianPDFReal 0 1 x := by
    rw [integral_sub hc hi.integrableOn,setIntegral_const,latticeCell_volume (by linarith : 0<rate),smul_eq_mul,
      gaussianLatticeMass_eq_density (by linarith : 0<rate)]
    ring
  rw [he]
  have h := norm_setIntegral_le_of_norm_le_const
    (f := fun x : ℝ => gaussianPDFReal 0 1 (latticePoint rate n)-gaussianPDFReal 0 1 x)
    (C := (6*exp (1/3)*exp (-(latticePoint rate n)^2/6))*(1/sqrt rate))
    (by rw [latticeCell,volume_Ico];exact ENNReal.ofReal_lt_top : volume (latticeCell rate n)<⊤)
    (fun x hx => by simpa only [Real.norm_eq_abs,abs_sub_comm] using density_cell_lipschitz hr n hx)
  rw [Real.norm_eq_abs,latticeCell_volume (by linarith : 0<rate)] at h
  convert h using 1; ring

def cellSummationConstant : ℝ := 6*exp (1/3)*exp (1/6)*sqrt (12*π)

theorem density_cells_sum_error_le {rate : ℝ} (hr : 1≤rate) (s : Finset ℕ) :
    (∑ n∈s,|gaussianLatticeMass rate (latticePoint rate n)-∫ x in latticeCell rate n,gaussianPDFReal 0 1 x|)≤
      cellSummationConstant/sqrt rate := by
  have h := Finset.sum_le_sum (s := s) (fun n _ => density_cell_error_le hr n)
  rw [← Finset.mul_sum] at h
  have hs := mul_le_mul_of_nonneg_left (gaussian_lattice_sum_le hr s)
    (by positivity : 0≤6*exp (1/3)*(1/sqrt rate))
  have he : 6*exp (1/3)*(1/sqrt rate)*(1/sqrt rate)=6*exp (1/3)*(1/sqrt rate)^2 := by ring
  rw [← mul_assoc,he] at hs
  exact h.trans (by convert hs using 1; unfold cellSummationConstant; ring)

end
end PaperC.V282.PoissonQuantitativeCells
