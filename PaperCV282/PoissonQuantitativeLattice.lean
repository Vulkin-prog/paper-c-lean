import PaperCV282.PoissonQuantitativeEntropy
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Summing Gaussian envelopes on the moving Poisson lattice

The rate need not be integral. Half-open cells are genuinely disjoint, and the
finite sum bound is uniform over the rate and every selected set of atoms.
-/
namespace PaperC.V282.PoissonQuantitativeLattice

open MeasureTheory Real Set

noncomputable section

def latticePoint (rate : ℝ) (n : ℕ) : ℝ := ((n : ℝ)-rate)/sqrt rate

def latticeCell (rate : ℝ) (n : ℕ) : Set ℝ :=
  Ico (latticePoint rate n) (latticePoint rate n+1/sqrt rate)

theorem latticeCell_pairwise {rate : ℝ} (_hr : 0<rate) : Pairwise (fun i j : ℕ => Disjoint (latticeCell rate i) (latticeCell rate j)) := by
  intro i j hij
  have hgap {a b : ℕ} (hab : a<b) : latticePoint rate a+1/sqrt rate≤latticePoint rate b := by
    have hh : (a : ℝ)+1≤b := by exact_mod_cast (Nat.succ_le_iff.mpr hab)
    unfold latticePoint
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) (sqrt_nonneg _)
  rcases lt_or_gt_of_ne hij with hij|hji
  · apply Set.disjoint_left.mpr
    intro x hi hj
    exact (not_lt_of_ge ((hgap hij).trans hj.1)) hi.2
  · exact (show Disjoint (latticeCell rate j) (latticeCell rate i) from Set.disjoint_left.mpr
      (fun x hj hi => (not_lt_of_ge ((hgap hji).trans hi.1)) hj.2)).symm

theorem latticeCell_volume {rate : ℝ} (hr : 0<rate) (n : ℕ) :
    volume.real (latticeCell rate n)=1/sqrt rate := by
  rw [measureReal_def,latticeCell,Real.volume_Ico]
  simp only [add_sub_cancel_left]
  exact ENNReal.toReal_ofReal (by positivity)

/-- Gaussian decay at a lattice point is controlled throughout its unit-mesh cell. -/
theorem lattice_gaussian_pointwise {rate : ℝ} (hr : 1≤rate) (n : ℕ) {x : ℝ}
    (hx : x∈latticeCell rate n) :
    exp (-(latticePoint rate n)^2/6)≤exp (1/6)*exp (-(1/12)*x^2) := by
  have hs : 1≤sqrt rate := (Real.one_le_sqrt).mpr hr
  have hh : 1/sqrt rate≤1 := (div_le_one (by positivity)).mpr hs
  have hd0 : 0≤x-latticePoint rate n := sub_nonneg.mpr hx.1
  have hd1 : x-latticePoint rate n≤1 := by have h := hx.2;linarith
  have hd2 : (x-latticePoint rate n)^2≤1 := by nlinarith
  have hb : x^2≤2*(latticePoint rate n)^2+2 := by
    nlinarith [sq_nonneg (2*latticePoint rate n-x)]
  rw [← exp_add]
  exact exp_le_exp.mpr (by nlinarith)

/-- A single cell comparison, including its exact volume. -/
theorem lattice_gaussian_cell_bound {rate : ℝ} (hr : 1≤rate) (n : ℕ) :
    (1/sqrt rate)*exp (-(latticePoint rate n)^2/6)≤
      exp (1/6)*(∫ x in latticeCell rate n,exp (-(1/12)*x^2)) := by
  have hi : Integrable (fun x : ℝ => exp (-(1/12)*x^2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ)<1/12)
  have hc : IntegrableOn (fun _ : ℝ => exp (-(latticePoint rate n)^2/6)) (latticeCell rate n) :=
    integrableOn_const (by rw [latticeCell,Real.volume_Ico];exact ENNReal.ofReal_ne_top)
  have h := setIntegral_mono_on hc (hi.const_mul (exp (1/6))).integrableOn
    measurableSet_Ico (fun x hx => lattice_gaussian_pointwise hr n hx)
  rw [setIntegral_const,latticeCell_volume (by linarith : 0<rate),smul_eq_mul,integral_const_mul] at h
  exact h

/-- Uniform finite Gaussian lattice sum, proved by summing disjoint genuine cells. -/
theorem gaussian_lattice_sum_le {rate : ℝ} (hr : 1≤rate) (s : Finset ℕ) :
    (1/sqrt rate)*(∑ n∈s,exp (-(latticePoint rate n)^2/6))≤exp (1/6)*sqrt (12*π) := by
  have hi : Integrable (fun x : ℝ => exp (-(1/12)*x^2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ)<1/12)
  have h := Finset.sum_le_sum (s := s) (fun n _ => lattice_gaussian_cell_bound hr n)
  rw [← Finset.mul_sum,← Finset.mul_sum] at h
  rw [← integral_biUnion_finset (s := latticeCell rate) s (fun _ _ => measurableSet_Ico)
    (fun i _ j _ hij => latticeCell_pairwise (by linarith : 0<rate) hij)
    (fun _ _ => hi.integrableOn)] at h
  have hu := setIntegral_le_integral (s := ⋃ i∈s,latticeCell rate i) hi (Filter.Eventually.of_forall fun x => (exp_pos _).le)
  have htot : (∫ x : ℝ,exp (-(1/12)*x^2))=sqrt (12*π) := by
    rw [integral_gaussian]
    congr 1
    ring
  exact h.trans (by rw [← htot];exact mul_le_mul_of_nonneg_left hu (exp_pos _).le)

end
end PaperC.V282.PoissonQuantitativeLattice
