import PaperCV282.PoissonQuantitativeCDFGeometry
import PaperCV282.PoissonQuantitativeTailLocal
import PaperCV282.PoissonQuantitativeTailSum

/-! # Summed true Poisson and Gaussian-cell errors in a moderate tail -/
namespace PaperC.V282.PoissonQuantitativeTailCells

open MeasureTheory ProbabilityTheory Real Set
open PoissonQuantitativeLocal PoissonQuantitativeLattice PoissonQuantitativeCells
open PoissonQuantitativeTailLocal PoissonQuantitativeTailSum
open scoped NNReal

noncomputable section

theorem gaussianPDF_antitone_nonneg {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    gaussianPDFReal 0 1 y≤gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith [pow_le_pow_left₀ hx hxy 2])) (by positivity)

theorem density_cell_positive_error {rate : ℝ} (hr : 1≤rate) (n : ℕ)
    (hz : 0≤latticePoint rate n) :
    |gaussianLatticeMass rate (latticePoint rate n)-∫ x in latticeCell rate n,gaussianPDFReal 0 1 x|≤
      (latticePoint rate n+1)*gaussianPDFReal 0 1 (latticePoint rate n)*(1/sqrt rate)^2 := by
  have hs : 1≤sqrt rate := one_le_sqrt.mpr hr
  have hh : 1/sqrt rate≤1 := (div_le_one (by positivity)).mpr hs
  have hpoint (x : ℝ) (hx : x∈latticeCell rate n) :
      |gaussianPDFReal 0 1 (latticePoint rate n)-gaussianPDFReal 0 1 x|≤
        ((latticePoint rate n+1)*gaussianPDFReal 0 1 (latticePoint rate n))*(1/sqrt rate) := by
    have hd (y : ℝ) (hy : y∈Icc (latticePoint rate n) (latticePoint rate n+1/sqrt rate)) :
        ‖-y*gaussianPDFReal 0 1 y‖≤(latticePoint rate n+1)*gaussianPDFReal 0 1 (latticePoint rate n) := by
      rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg (hz.trans hy.1),
        abs_of_nonneg (gaussianPDFReal_nonneg 0 1 y)]
      exact mul_le_mul (by have h := hy.2;linarith) (gaussianPDF_antitone_nonneg hz hy.1)
        (gaussianPDFReal_nonneg 0 1 y) (by positivity)
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ => (standard_density_derivative y).hasDerivWithinAt) hd (convex_Icc _ _)
      (show x∈Icc (latticePoint rate n) (latticePoint rate n+1/sqrt rate) from ⟨hx.1,hx.2.le⟩)
      (show latticePoint rate n∈Icc (latticePoint rate n) (latticePoint rate n+1/sqrt rate) from ⟨le_rfl,by linarith [show 0≤1/sqrt rate by positivity]⟩)
    simp only [Real.norm_eq_abs,abs_sub_comm (latticePoint rate n) x,
      abs_of_nonneg (sub_nonneg.mpr hx.1)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by have h := hx.2;linarith)
      (mul_nonneg (by positivity) (gaussianPDFReal_nonneg 0 1 _)))
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
    (C := ((latticePoint rate n+1)*gaussianPDFReal 0 1 (latticePoint rate n))*(1/sqrt rate))
    (by rw [latticeCell,volume_Ico];exact ENNReal.ofReal_lt_top : volume (latticeCell rate n)<⊤)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hpoint x hx)
  rw [Real.norm_eq_abs,latticeCell_volume (by linarith : 0<rate)] at h
  convert h using 1; ring

theorem density_tail_cell_error {rate t : ℝ} (hr : 1≤rate) (ht : 0≤t) (n : ℕ)
    (htz : t≤latticePoint rate n) :
    |gaussianLatticeMass rate (latticePoint rate n)-∫ x in latticeCell rate n,gaussianPDFReal 0 1 x|≤
      (2/(rate : ℝ))*exp (-t^2/2)*(1+(latticePoint rate n)^3)*exp (-((latticePoint rate n)^2-t^2)/3) := by
  have hz := ht.trans htz
  have hp : gaussianPDFReal 0 1 (latticePoint rate n)≤exp (-(latticePoint rate n)^2/2) := by
    have hpi : 1≤sqrt (2*π) := one_le_sqrt.mpr (by have h := pi_gt_three;linarith)
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    exact mul_le_of_le_one_left (exp_pos _).le (inv_le_one_of_one_le₀ hpi)
  have hpoly : latticePoint rate n+1≤2*(1+(latticePoint rate n)^3) := by
    by_cases h : latticePoint rate n≤1
    · nlinarith [pow_nonneg hz 3]
    · have h := le_self_pow₀ (le_of_not_ge h) (by norm_num : (3 : ℕ)≠0)
      linarith
  have he : exp (-(latticePoint rate n)^2/2)≤
      exp (-t^2/2)*exp (-((latticePoint rate n)^2-t^2)/3) := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by nlinarith [pow_le_pow_left₀ ht htz 2])
  have h := (density_cell_positive_error hr n hz).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul hpoly (hp.trans he)
      (gaussianPDFReal_nonneg 0 1 _) (by positivity)) (by positivity))
  have hsq : (1/sqrt rate)^2=1/rate := by rw [div_pow,sq_sqrt (by linarith : 0≤rate),one_pow]
  rw [hsq] at h
  simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using h

theorem poisson_tail_sum_error (rate : ℝ≥0) (hr : 1≤rate) (t : ℝ) (ht : 0≤t)
    (htop : t≤sqrt (rate : ℝ)/2) (s : Finset ℕ)
    (hs : ∀n∈s,t≤latticePoint rate n ∧ latticePoint rate n≤sqrt (rate : ℝ)/2) :
    (∑ n∈s,|(poissonMeasure rate).real {n}-gaussianLatticeMass rate (latticePoint rate n)|)≤
      (7*tailSummationConstant/sqrt rate)*((1+t^3)/(1+t))*exp (-t^2/2+2*t^3/sqrt rate) := by
  have hrp : (0 : ℝ)<rate := lt_of_lt_of_le zero_lt_one hr
  have hsp : 0<sqrt (rate : ℝ) := sqrt_pos.mpr hrp
  have hsum := Finset.sum_le_sum (s := s) (fun n hn => poisson_tail_local_error rate hr
    (show 0<n from by
      have hh := ht.trans (hs n hn).1
      have hh' := (le_div_iff₀ hsp).mp hh
      have hn' : (0 : ℝ)<n := by nlinarith
      exact_mod_cast hn') t ht (hs n hn).1 (hs n hn).2)
  simp_rw [sub_eq_add_neg,exp_add] at hsum
  have hfact : (∑ n∈s,(7/(rate : ℝ))*(1+(latticePoint rate n)^3)*
      (exp (-t^2/2)*exp (2*t^3/sqrt rate)*exp (-((latticePoint rate n)^2-t^2)/3)))=
      ((7/(rate : ℝ))*exp (-t^2/2+2*t^3/sqrt rate))*
        (∑ n∈s,(1+(latticePoint rate n)^3)*exp (-((latticePoint rate n)^2-t^2)/3)) := by
    rw [Finset.mul_sum,exp_add]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hw := weighted_tail_lattice_sum_le (rate := (rate : ℝ)) hr ht htop s (fun n hn => (hs n hn).1)
  have hm := mul_le_mul_of_nonneg_left hw
    (by positivity : 0≤(7/sqrt (rate : ℝ))*exp (-t^2/2+2*t^3/sqrt rate))
  have hsquare := sq_sqrt rate.coe_nonneg
  have hcoef : (7/sqrt (rate : ℝ))*(1/sqrt (rate : ℝ))=7/(rate : ℝ) := by
    rw [div_mul_div_comm,mul_one,← pow_two,hsquare]
  have hbound : ((7/(rate : ℝ))*exp (-t^2/2+2*t^3/sqrt rate))*
      (∑ n∈s,(1+(latticePoint rate n)^3)*exp (-((latticePoint rate n)^2-t^2)/3))≤
      (7*tailSummationConstant/sqrt rate)*((1+t^3)/(1+t))*exp (-t^2/2+2*t^3/sqrt rate) := by
    have hleft : (7/sqrt (rate : ℝ))*exp (-t^2/2+2*t^3/sqrt rate)*
        ((1/sqrt (rate : ℝ))*(∑ n∈s,(1+(latticePoint rate n)^3)*exp (-((latticePoint rate n)^2-t^2)/3)))=
        ((7/(rate : ℝ))*exp (-t^2/2+2*t^3/sqrt rate))*(∑ n∈s,(1+(latticePoint rate n)^3)*exp (-((latticePoint rate n)^2-t^2)/3)) := by
      calc
        _=((7/sqrt (rate : ℝ))*(1/sqrt (rate : ℝ)))*exp (-t^2/2+2*t^3/sqrt rate)*
            (∑ n∈s,(1+(latticePoint rate n)^3)*exp (-((latticePoint rate n)^2-t^2)/3)) := by ring
        _=_ := by rw [hcoef]
    rw [hleft] at hm
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hm
  apply le_trans _ hbound
  rw [← hfact]
  simpa only [sub_eq_add_neg,exp_add,neg_div,neg_mul,mul_neg,mul_assoc] using hsum


theorem rescale_lattice_bound {rate a b v : ℝ} (hr : 0<rate) (ha : 0≤a)
    (h : (1/sqrt rate)*v≤b) : (a/rate)*v≤(a/sqrt rate)*b := by
  have hs : 0<sqrt rate := sqrt_pos.mpr hr
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0≤a/sqrt rate)
  have he : (a/sqrt rate)*((1/sqrt rate)*v)=(a/rate)*v := by
    rw [← mul_assoc,div_mul_div_comm,mul_one,← pow_two,sq_sqrt hr.le]
  rwa [he] at hh

theorem density_tail_sum_error {rate t : ℝ} (hr : 1≤rate) (ht : 0≤t)
    (htop : t≤sqrt rate/2) (s : Finset ℕ) (hs : ∀n∈s,t≤latticePoint rate n) :
    (∑ n∈s,|gaussianLatticeMass rate (latticePoint rate n)-∫ x in latticeCell rate n,gaussianPDFReal 0 1 x|)≤
      (2*tailSummationConstant/sqrt rate)*((1+t^3)/(1+t))*exp (-t^2/2) := by
  have hsum := Finset.sum_le_sum (s := s) (fun n hn => density_tail_cell_error hr ht n (hs n hn))
  simp only [mul_assoc] at hsum
  rw [← Finset.mul_sum,← Finset.mul_sum] at hsum
  have hw := weighted_tail_lattice_sum_le hr ht htop s hs
  have h := rescale_lattice_bound (by linarith : 0<rate)
    (by positivity : 0≤2*exp (-t^2/2)) hw
  apply hsum.trans
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

def moderateCentralConstant : ℝ := (7*exp 2+2)*tailSummationConstant

/-- The actual finite upper-tail event and its genuine Gaussian cells. -/
theorem finite_tail_probability_error (rate : ℝ≥0) (hr : 1≤rate) (t : ℝ) (ht : 0≤t)
    (htop : t≤sqrt (rate : ℝ)/2) (hcubic : t^3/sqrt rate≤1) (s : Finset ℕ)
    (hs : ∀n∈s,t≤latticePoint rate n ∧ latticePoint rate n≤sqrt (rate : ℝ)/2) :
    |(poissonMeasure rate).real s-(gaussianReal 0 1).real (⋃n∈s,latticeCell rate n)|≤
      (moderateCentralConstant/sqrt rate)*((1+t^3)/(1+t))*exp (-t^2/2) := by
  have hi := integrable_gaussianPDFReal (μ := 0) (v := 1)
  rw [← sum_measureReal_singleton,PoissonQuantitativeCDFGeometry.gaussian_real_eq_integral,
    integral_biUnion_finset (s := latticeCell (rate : ℝ)) s (fun _ _ => measurableSet_Ico)
      (fun i _ j _ hij => latticeCell_pairwise (by linarith : (0 : ℝ)<rate) hij)
      (fun _ _ => hi.integrableOn),← Finset.sum_sub_distrib]
  have htri := (Finset.abs_sum_le_sum_abs (s := s) (f := fun n =>
    (poissonMeasure rate).real {n}-∫ x in latticeCell rate n,gaussianPDFReal 0 1 x)).trans
      (Finset.sum_le_sum (s := s) fun n _ => abs_sub_le ((poissonMeasure rate).real {n})
        (gaussianLatticeMass rate (latticePoint rate n)) _)
  rw [Finset.sum_add_distrib] at htri
  have h1 := poisson_tail_sum_error rate hr t ht htop s hs
  have h2 := density_tail_sum_error hr ht htop s (fun n hn => (hs n hn).1)
  have he : exp (-t^2/2+2*t^3/sqrt rate)≤exp (-t^2/2)*exp 2 := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by simp only [div_eq_mul_inv] at hcubic ⊢;nlinarith only [hcubic])
  have hp : 0≤(7*tailSummationConstant/sqrt (rate : ℝ))*((1+t^3)/(1+t)) := by
    unfold tailSummationConstant
    positivity
  have hh := htri.trans (add_le_add (h1.trans (mul_le_mul_of_nonneg_left he hp)) h2)
  exact hh.trans_eq (by
    unfold moderateCentralConstant
    simp only [div_eq_mul_inv,mul_add,add_mul]
    ac_rfl)

end
end PaperC.V282.PoissonQuantitativeTailCells
