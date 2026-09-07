import PaperCV282.ExactMarkedModel
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Field.GeomSum

/-! # Dimension-free sums of signed geometric mark weights -/
namespace PaperC.V282.SignedGeometricWeights

open ExactMarkedModel Affine
open scoped BigOperators

noncomputable section

/-- The rate of an excess-sign label divided by the base start rate. -/
def signedGeometricWeight (e : ℕ) : ℝ := 1/(2 : ℝ)^(e+2)

theorem signedGeometricWeight_pos (e : ℕ) : 0 < signedGeometricWeight e := by
  unfold signedGeometricWeight; positivity

theorem signedMarkRate_eq_base_mul_weight (L e : ℕ) :
    (signedMarkRate L e : ℝ) = (1/(2 : ℝ)^L)*signedGeometricWeight e := by
  simp only [signedMarkRate_coe, signedGeometricWeight, pow_add]
  ring

theorem sum_signedGeometricWeight_le_one (E : ℕ) :
    (∑ a : Fin (E+1) × F₂, signedGeometricWeight a.1.val) ≤ 1 := by
  simpa only [signedGeometricWeight, signedMarkRate_coe, zero_add,
    Fintype.sum_prod_type, pow_zero, div_one] using sum_all_signedMarkRate_le_base 0 E

theorem sqrt_signedGeometricWeight (e : ℕ) :
    Real.sqrt (signedGeometricWeight e) = (1/Real.sqrt 2)^e/2 := by
  apply (Real.sqrt_eq_iff_eq_sq (signedGeometricWeight_pos e).le (by positivity)).mpr
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold signedGeometricWeight
  rw [div_pow, ← pow_mul, mul_comm e 2, pow_mul, div_pow, hs]
  simp only [pow_add, one_pow]
  norm_num
  simp only [one_div, inv_pow]
  ring

/-- Summing over both signs costs a fixed geometric series, uniformly in E. -/
theorem sum_sqrt_signedGeometricWeight_le (E : ℕ) :
    (∑ a : Fin (E+1) × F₂, Real.sqrt (signedGeometricWeight a.1.val)) ≤ 2+Real.sqrt 2 := by
  have hs0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs1 : 1 < Real.sqrt (2 : ℝ) := by nlinarith
  have hr : (1 : ℝ)/Real.sqrt 2 < 1 := (div_lt_one hs0).mpr hs1
  have hsum := geom_sum_Ico_le_of_lt_one (m := 0) (n := E+1)
    (by positivity : (0 : ℝ) ≤ 1/Real.sqrt 2) hr
  have hfinite : (∑ a : Fin (E+1) × F₂, Real.sqrt (signedGeometricWeight a.1.val)) =
      ∑ i ∈ Finset.range (E+1), ((1 : ℝ)/Real.sqrt 2)^i := by
    simp only [Fintype.sum_prod_type, sqrt_signedGeometricWeight,
      Finset.sum_const, nsmul_eq_mul]
    norm_num
    convert Fin.sum_univ_eq_sum_range (fun i => ((1 : ℝ)/Real.sqrt 2)^i) (E+1) using 1
    all_goals
      apply Finset.sum_congr rfl
      intro i hi
      simp only [one_div, inv_pow] <;> ring
  rw [hfinite]
  have hden : 0 < 1-(1 : ℝ)/Real.sqrt 2 := sub_pos.mpr hr
  have heq : (1 : ℝ)/(1-1/Real.sqrt 2) = 2+Real.sqrt 2 := by
    apply (div_eq_iff (ne_of_gt hden)).mpr
    field_simp
    nlinarith
  simpa only [Nat.Ico_zero_eq_range, pow_zero, heq] using hsum

/-- A convenient integer ceiling for the squared signed geometric series. -/
theorem sum_sqrt_signedGeometricWeight_sq_le_twelve (E : ℕ) :
    (∑ a : Fin (E+1) × F₂, Real.sqrt (signedGeometricWeight a.1.val))^2 ≤ 12 := by
  have h := sum_sqrt_signedGeometricWeight_le E
  have h0 : 0 ≤ ∑ a : Fin (E+1) × F₂, Real.sqrt (signedGeometricWeight a.1.val) :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs : Real.sqrt (2 : ℝ) ≤ 3/2 := by nlinarith
  nlinarith

/-- A positive weighted geometric sum admits both the coarse and directional ceilings. -/
theorem weighted_geometric_pair_sum_le {E : ℕ} (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hw1 : ∀ a b, w a b ≤ 1)
    (hwd : ∀ a b, w a b ≤ K /
      (Real.sqrt (signedGeometricWeight a.1.val)*Real.sqrt (signedGeometricWeight b.1.val))) :
    (∑ a, ∑ b, w a b*signedGeometricWeight a.1.val*signedGeometricWeight b.1.val) ≤ min 1 (12*K) := by
  let q := fun a : Fin (E+1) × F₂ => signedGeometricWeight a.1.val
  have hq (a : Fin (E+1) × F₂) : 0 < q a := signedGeometricWeight_pos _
  have hcoarse : (∑ a, ∑ b, w a b*q a*q b) ≤ (∑ a, q a)^2 := by
    calc
      _ ≤ ∑ a, ∑ b, q a*q b := Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => by
        nlinarith [hw1 a b, mul_pos (hq a) (hq b)]))
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]; ring
  have hdir : (∑ a, ∑ b, w a b*q a*q b) ≤ K*(∑ a, Real.sqrt (q a))^2 := by
    calc
      _ ≤ ∑ a, ∑ b, K*Real.sqrt (q a)*Real.sqrt (q b) := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        have h := hwd a b
        change w a b ≤ K/(Real.sqrt (q a)*Real.sqrt (q b)) at h
        have ha := Real.sq_sqrt (hq a).le
        have hb := Real.sq_sqrt (hq b).le
        have hp := mul_pos (Real.sqrt_pos.2 (hq a)) (Real.sqrt_pos.2 (hq b))
        have hh := (le_div_iff₀ hp).mp h
        have hm := mul_le_mul_of_nonneg_right hh hp.le
        have heq : w a b * (Real.sqrt (q a)*Real.sqrt (q b)) *
            (Real.sqrt (q a)*Real.sqrt (q b)) = w a b*q a*q b := by
          calc
            _ = w a b*(Real.sqrt (q a))^2*(Real.sqrt (q b))^2 := by ring
            _ = _ := by rw [ha, hb]
        rw [heq] at hm
        simpa only [mul_assoc] using hm
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]; ring
  apply le_min
  · have hs := sum_signedGeometricWeight_le_one E
    have h0 : 0 ≤ ∑ a, q a := Finset.sum_nonneg (fun a _ => (hq a).le)
    change (∑ a, q a) ≤ 1 at hs
    exact hcoarse.trans (by nlinarith)
  · have hs := sum_sqrt_signedGeometricWeight_sq_le_twelve E
    exact hdir.trans (by nlinarith)

end
end PaperC.V282.SignedGeometricWeights
