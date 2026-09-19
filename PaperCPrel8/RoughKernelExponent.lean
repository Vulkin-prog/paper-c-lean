import PaperCPrel8.RoughKernelAllocation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Converting the all-prime CRT weight to a threshold power

Every prime of the odd rough kernel lies above the unchanged small-prime
cutoff. This is a product estimate, not a largest-prime estimate.
-/
namespace PaperC.Prel8.RoughKernelExponent
open Finset LargeOddKernel RoughKernelAllocation ArratiaGoldsteinGordonInput
noncomputable section

/-- The number of prime factors is controlled by the logarithm of their product. -/
theorem card_log_le (Y m : ℕ) (hY : 1 < Y) :
    ((largeOddPrimeSupport Y m).card : ℝ)*Real.log Y ≤ Real.log (largeOddKernel Y m) := by
  have hp (p : ℕ) (h : p ∈ largeOddPrimeSupport Y m) : 0 < (p:ℝ) := by
    exact_mod_cast (prime_and_large_of_mem_largeOddPrimeSupport h).1.pos
  simp only [largeOddKernel,Nat.cast_prod,id_eq]
  rw [Real.log_prod (fun p h ↦ (hp p h).ne')]
  calc
    _ = ∑ p ∈ largeOddPrimeSupport Y m, Real.log Y := by simp
    _ ≤ _ := sum_le_sum (fun p h ↦ Real.log_le_log (by exact_mod_cast (show 0<Y by omega))
      (by exact_mod_cast (prime_and_large_of_mem_largeOddPrimeSupport h).2.le))

/-- Literal z^omega(r)/r <= T^(-1+log z/log Y), for r>=T and 1<=z<Y. -/
theorem kernel_weight_le (Y m : ℕ) (T z : ℝ) (hT : 0 < T)
    (hz : 1 ≤ z) (hzY : z < Y) (hrT : T ≤ (largeOddKernel Y m:ℝ)) :
    z^ArithmeticFunction.cardDistinctFactors (largeOddKernel Y m) / (largeOddKernel Y m:ℝ) ≤
      T^(-1+Real.log z/Real.log Y) := by
  have hY : 1 < Y := by exact_mod_cast (lt_of_le_of_lt hz hzY)
  have hlogY : 0 < Real.log (Y:ℝ) := Real.log_pos (by exact_mod_cast hY)
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz
  have hr : 0 < (largeOddKernel Y m:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (largeOddKernel_ne_zero Y m)
  have hc := card_log_le Y m hY
  have hc' : ((largeOddPrimeSupport Y m).card:ℝ) ≤ Real.log (largeOddKernel Y m)/Real.log Y :=
    (le_div_iff₀ hlogY).mpr hc
  have ha : -1+Real.log z/Real.log Y < 0 := by
    have h := Real.log_lt_log (by linarith : 0<z) hzY
    have := (div_lt_one hlogY).mpr h
    linarith
  have he : ((largeOddPrimeSupport Y m).card:ℝ)*Real.log z - Real.log (largeOddKernel Y m) ≤
      (-1+Real.log z/Real.log Y)*Real.log (largeOddKernel Y m) := by
    have := mul_le_mul_of_nonneg_right hc' hlogz
    convert sub_le_sub_right this (Real.log (largeOddKernel Y m)) using 1; ring
  have ht := mul_le_mul_of_nonpos_left (Real.log_le_log hT hrT) ha.le
  rw [cardDistinctFactors_largeOddKernel,← Real.rpow_natCast,Real.rpow_def_of_pos (by linarith : 0<z),
    Real.rpow_def_of_pos hT]
  rw [show (largeOddKernel Y m:ℝ) = Real.exp (Real.log (largeOddKernel Y m)) from (Real.exp_log hr).symm,
    ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  nlinarith only [he,ht]

/-- The actual CRT hosting event has the threshold-power bound at every good source vertex. -/
theorem allocation_threshold_bound (n h Q Y m : ℕ) (hn : 0<n) (hh : 0<h)
    (hr : largeOddKernel Y m ≤ 2*n) (T : ℝ) (hT : 0<T)
    (hTY : T ≤ (largeOddKernel Y m:ℝ)) (hzY : 3*(h:ℝ)*(Q+1) < Y) :
    eventProbability (gridLaw n h hn)
      (fun J ↦ ∀ p ∈ largeOddPrimeSupport Y m,
        ∃ b : Fin h, ∃ a : Fin (Q+1), p ∣ J.val b + a.val) ≤
      T^(-1+Real.log (3*(h:ℝ)*(Q+1))/Real.log Y) := by
  apply (rough_allocation_probability n h Q Y m hn hr).trans
  apply kernel_weight_le Y m T _ hT _ hzY hTY
  have : (1:ℝ) ≤ h := by exact_mod_cast hh
  have : (0:ℝ) ≤ Q := Nat.cast_nonneg Q
  nlinarith

end
end PaperC.Prel8.RoughKernelExponent
