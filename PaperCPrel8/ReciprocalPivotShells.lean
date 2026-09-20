import PaperCPrel8.DirectedFootprint
import PaperCPrel8.SaddleEnvelope

/-! # Actual reciprocal-pivot tails and logarithmic shells

All sums use the actual largest odd-valuation prime. Rounded cutoffs are
identified exactly. Shell counting and the discarded tail are finite bounds,
with no asymptotic or independence premise.
-/
namespace PaperC.Prel8.ReciprocalPivotShells
open PaperC.Prel8.OddPrimePivot PaperC.Prel8.DirectedFootprint
open PaperC.Prel8.SaddleEnvelope PaperC.V282.SaddleParameters
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Reciprocal pivots above a real exponential cutoff, counted on positive integers. -/
def reciprocalTail (X : ℕ) (w : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 X, if Real.exp w < (largestOddPrime m : ℝ) then (largestOddPrime m : ℝ)⁻¹ else 0

/-- Passing to the natural floor of the cutoff changes no term of the tail. -/
theorem reciprocalTail_eq (X : ℕ) (w : ℝ) :
    reciprocalTail X w = reciprocalPivots X ⌊Real.exp w⌋₊ := by
  simp only [reciprocalTail, reciprocalPivots, Finset.sum_filter,
    Nat.floor_lt (Real.exp_pos w).le]

/-- Every term beyond a cutoff is bounded by its reciprocal exponential. -/
theorem reciprocalTail_le (X : ℕ) (w : ℝ) :
    reciprocalTail X w ≤ (X : ℝ)*Real.exp (-w) := by
  have h : reciprocalTail X w ≤ ∑ _m ∈ Finset.Icc 1 X, Real.exp (-w) := by
    apply Finset.sum_le_sum
    intro m _
    split_ifs with hm
    · rw [Real.exp_neg]
      exact inv_anti₀ (Real.exp_pos _) hm.le
    · exact (Real.exp_pos _).le
  simpa using h

/-- One logarithmic shell costs its full sublevel count times the reciprocal lower edge. -/
theorem reciprocalTail_step (X : ℕ) (w : ℝ) :
    reciprocalTail X w ≤ Real.exp (-w)*(pivotValues X ⌊Real.exp (w+1)⌋₊).card +
      reciprocalTail X (w+1) := by
  have hp (m : ℕ) :
      (if Real.exp w < (largestOddPrime m : ℝ) then (largestOddPrime m : ℝ)⁻¹ else 0) ≤
      Real.exp (-w)*(if largestOddPrime m ≤ ⌊Real.exp (w+1)⌋₊ then (1 : ℝ) else 0) +
      (if Real.exp (w+1) < (largestOddPrime m : ℝ) then (largestOddPrime m : ℝ)⁻¹ else 0) := by
    simp only [Nat.le_floor_iff (Real.exp_pos (w+1)).le]
    by_cases hu : (largestOddPrime m : ℝ) ≤ Real.exp (w+1)
    · simp only [hu, not_lt.mpr hu, ite_true, ite_false, mul_one, add_zero]
      split_ifs with hl
      · rw [Real.exp_neg]
        exact inv_anti₀ (Real.exp_pos _) hl.le
      · exact (Real.exp_pos _).le
    · have hhi : Real.exp (w+1) < (largestOddPrime m : ℝ) := lt_of_not_ge hu
      have hlo : Real.exp w < (largestOddPrime m : ℝ) :=
        (Real.exp_le_exp.mpr (by linarith : w≤w+1)).trans_lt hhi
      simp [hu,hhi,hlo]
  have h := Finset.sum_le_sum (s := Finset.Icc 1 X) (fun m _ => hp m)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  simpa only [reciprocalTail, pivotValues, Finset.sum_boole] using h

/-- Iteration keeps one residual tail and exactly one count per shell. -/
theorem reciprocalTail_shells (X K : ℕ) (w : ℝ) :
    reciprocalTail X w ≤
      (∑ i ∈ Finset.range K, Real.exp (-(w+i))*(pivotValues X ⌊Real.exp (w+i+1)⌋₊).card) +
      reciprocalTail X (w+K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hs := reciprocalTail_step X (w+K)
    rw [Finset.sum_range_succ]
    push_cast
    simpa only [add_assoc] using ih.trans (add_le_add le_rfl hs)

/-- Finite shell bound including the discarded large-pivot tail. -/
theorem reciprocalTail_shells_and_tail (X K : ℕ) (w : ℝ) :
    reciprocalPivots X ⌊Real.exp w⌋₊ ≤
      (∑ i ∈ Finset.range K, Real.exp (-(w+i))*(pivotValues X ⌊Real.exp (w+i+1)⌋₊).card) +
      (X : ℝ)*Real.exp (-(w+K)) := by
  rw [← reciprocalTail_eq]
  exact (reciprocalTail_shells X K w).trans (add_le_add le_rfl (reciprocalTail_le X (w+K)))

/-- Uniform count and saddle envelopes combine with the exact one-unit shell shift. -/
theorem reciprocalTail_of_uniform_bounds (X K : ℕ) (V H nu delta epsilon : ℝ)
    (hcount : ∀ i ∈ Finset.range K,
      ((pivotValues X ⌊Real.exp (V+i+1)⌋₊).card : ℝ) ≤
        X*Real.exp (-saddleCost (H/(V+i+1))+delta*nu))
    (henvelope : ∀ i ∈ Finset.range K,
      2*V-epsilon*nu ≤ (V+i+1)+saddleCost (H/(V+i+1))) :
    reciprocalPivots X ⌊Real.exp V⌋₊ ≤
      X*((K : ℝ)*Real.exp (1-2*V+(epsilon+delta)*nu)+Real.exp (-(V+K))) := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range K) :
      Real.exp (-(V+i))*((pivotValues X ⌊Real.exp (V+i+1)⌋₊).card : ℝ) ≤
      X*Real.exp (1-2*V+(epsilon+delta)*nu) := by
    calc
      _ ≤ Real.exp (-(V+i))*(X*Real.exp (-saddleCost (H/(V+i+1))+delta*nu)) :=
        mul_le_mul_of_nonneg_left (hcount i hi) (Real.exp_pos _).le
      _ = X*Real.exp (-(V+i)-saddleCost (H/(V+i+1))+delta*nu) := by
        rw [show -(V+i)-saddleCost (H/(V+i+1))+delta*nu =
          -(V+i)+(-saddleCost (H/(V+i+1))+delta*nu) by ring]
        simp only [Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [henvelope i hi])) (Nat.cast_nonneg _)
  calc
    _ ≤ _ := reciprocalTail_shells_and_tail X K V
    _ ≤ (∑ _i ∈ Finset.range K, (X : ℝ)*Real.exp (1-2*V+(epsilon+delta)*nu))+
        (X : ℝ)*Real.exp (-(V+K)) := add_le_add (Finset.sum_le_sum hterm) le_rfl
    _ = _ := by simp; ring

end
end PaperC.Prel8.ReciprocalPivotShells
