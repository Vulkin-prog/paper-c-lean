import PaperCV282.SignedGeometricWeights
import PaperCV282.DirectionalHessian

/-! # Normalizing the signed directional Hessian at the full target intensity -/
namespace PaperC.V282.SignedDirectionalFactors

open ExactMarkedModel SignedGeometricWeights DirectionalHessian DirectionalSteinInput
open scoped BigOperators NNReal

noncomputable section

/-- Full target means of the signed excess coordinates. -/
def signedAggregateRates (lambda : ℝ≥0) (E : ℕ) : Fin (E+1) × F₂ → ℝ≥0 :=
  fun a => lambda * signedMarkRate 0 a.1.val

/-- The dimension-free factor used by the actual aggregated arithmetic ledger. -/
def signedDirectionalFactor (lambda : ℝ) : ℝ :=
  min 1 (12*((1+max 0 (Real.log (2*lambda)))/lambda))

theorem signedAggregateRates_coe (lambda : ℝ≥0) (E : ℕ) (a : Fin (E+1) × F₂) :
    (signedAggregateRates lambda E a : ℝ) = (lambda : ℝ)*signedGeometricWeight a.1.val := by
  simp [signedAggregateRates, signedMarkRate_coe, signedGeometricWeight]

theorem signedAggregateRates_pos {lambda : ℝ≥0} (hlambda : 0 < lambda) (E : ℕ)
    (a : Fin (E+1) × F₂) : 0 < signedAggregateRates lambda E a := by
  change (0 : ℝ) < (signedAggregateRates lambda E a : ℝ)
  rw [signedAggregateRates_coe]
  exact mul_pos hlambda (signedGeometricWeight_pos _)

theorem sum_signedAggregateRates_le (lambda : ℝ≥0) (E : ℕ) :
    (∑ a, (signedAggregateRates lambda E a : ℝ)) ≤ lambda := by
  simp only [signedAggregateRates_coe, ← Finset.mul_sum]
  have h := sum_signedGeometricWeight_le_one E
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h lambda.coe_nonneg

/-- The coefficient depends on total retained mark mass only through an upper bound by lambda. -/
theorem directionalCoefficient_signed_le {lambda : ℝ≥0} (hlambda : 0 < lambda) (E : ℕ) :
    directionalCoefficient (signedAggregateRates lambda E) ≤ 1+max 0 (Real.log (2*(lambda : ℝ))) := by
  have hpos : 0 < ∑ a, (signedAggregateRates lambda E a : ℝ) :=
    Finset.sum_pos (fun a _ => signedAggregateRates_pos hlambda E a) Finset.univ_nonempty
  have hle := sum_signedAggregateRates_le lambda E
  have hlog := Real.log_le_log (by positivity : 0 < 2*∑ a, (signedAggregateRates lambda E a : ℝ))
    (by linarith : 2*∑ a, (signedAggregateRates lambda E a : ℝ) ≤ 2*(lambda : ℝ))
  have hm := max_le_max_left 0 hlog
  unfold directionalCoefficient
  linarith

/-- The product of square roots preserves lambda exactly, including both signs. -/
theorem sqrt_signedAggregateRates_mul (lambda : ℝ≥0) (E : ℕ) (a b : Fin (E+1) × F₂) :
    Real.sqrt (signedAggregateRates lambda E a : ℝ)*Real.sqrt (signedAggregateRates lambda E b : ℝ) =
      (lambda : ℝ)*(Real.sqrt (signedGeometricWeight a.1.val)*Real.sqrt (signedGeometricWeight b.1.val)) := by
  simp only [signedAggregateRates_coe, Real.sqrt_mul lambda.coe_nonneg]
  calc
    _ = (Real.sqrt (lambda : ℝ))^2*
        (Real.sqrt (signedGeometricWeight a.1.val)*Real.sqrt (signedGeometricWeight b.1.val)) := by ring
    _ = _ := by rw [Real.sq_sqrt lambda.coe_nonneg]

/-- Actual entrywise factor, normalized with the full target lambda rather than good-site mass. -/
theorem entryFactor_signed_le {lambda : ℝ≥0} (hlambda : 0 < lambda) (E : ℕ)
    (a b : Fin (E+1) × F₂) :
    entryFactor (signedAggregateRates lambda E) a b ≤
      ((1+max 0 (Real.log (2*(lambda : ℝ))))/(lambda : ℝ)) /
        (Real.sqrt (signedGeometricWeight a.1.val)*Real.sqrt (signedGeometricWeight b.1.val)) := by
  apply (min_le_right _ _).trans
  rw [sqrt_signedAggregateRates_mul]
  have hd : 0 ≤ (lambda : ℝ)*(Real.sqrt (signedGeometricWeight a.1.val)*Real.sqrt (signedGeometricWeight b.1.val)) := by
    positivity
  exact (div_le_div_of_nonneg_right (directionalCoefficient_signed_le hlambda E) hd).trans_eq (by ring)

theorem signedDirectionalFactor_nonneg {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    0 ≤ signedDirectionalFactor lambda := by
  unfold signedDirectionalFactor
  exact le_min (by norm_num) (by positivity)

theorem signedDirectionalFactor_le_one (lambda : ℝ) : signedDirectionalFactor lambda ≤ 1 := min_le_left _ _

/-- Summing the normalized genuine Hessian over all signed marks is uniformly bounded. -/
theorem weighted_signedAggregateRates_le {lambda : ℝ≥0} (hlambda : 0 < lambda) (E : ℕ) :
    (∑ a, ∑ b, entryFactor (signedAggregateRates lambda E) a b *
      signedGeometricWeight a.1.val*signedGeometricWeight b.1.val) ≤ signedDirectionalFactor lambda := by
  exact weighted_geometric_pair_sum_le _ (by positivity)
    (entryFactor_le_one _) (entryFactor_signed_le hlambda E)

end
end PaperC.V282.SignedDirectionalFactors
