import PaperCV282.PrimeEulerPNT
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The fixed lower split in the weighted PNT calculation

The singularity of Ei at zero is logarithmic. Its subtraction from the
finite lower prime sum therefore costs only O_A(1+|log zeta|), uniformly
in the moving upper cutoff. All constants below are explicit.
-/

namespace PaperC.V282.PrimeEulerLowerSplit

open PrimeEulerPNT PrimeEulerRankin DefectCounting ExponentialIntegral

noncomputable section

/-- A derivative bound gives a uniform linear majorant for exp(t)-1 on [0,1]. -/
theorem exp_sub_one_le_linear {t : ℝ} (ht : 0 ≤ t) (htone : t ≤ 1) :
    Real.exp t - 1 ≤ Real.exp 1 * t := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := 1) (f := Real.exp) (f' := Real.exp) (C := Real.exp 1)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)] using Real.exp_le_exp.mpr hx.2.le)
    t ⟨ht, htone⟩
  simp only [Real.exp_zero, sub_zero, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- Subtracting the logarithmic singularity leaves a bounded derivative near zero. -/
theorem hasDerivAt_Ei_sub_log {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => exponentialIntegral t - Real.log t) ((Real.exp t - 1) / t) t := by
  apply ((hasDerivAt_exponentialIntegral ht).sub (Real.hasDerivAt_log ht.ne')).congr_deriv
  ring

/-- The near-zero logarithmic remainder is bounded independently of its positive argument. -/
theorem abs_Ei_sub_log_le_near_zero {v : ℝ} (hv : 0 < v) (hvone : v ≤ 1) :
    |exponentialIntegral v - Real.log v| ≤ |exponentialIntegral 1| + Real.exp 1 := by
  have hderiv (t : ℝ) (ht : t ∈ Set.Ico v 1) : |(Real.exp t - 1) / t| ≤ Real.exp 1 := by
    have htpos := hv.trans_le ht.1
    have hnonneg : 0 ≤ (Real.exp t - 1) / t :=
      div_nonneg (by linarith [Real.one_le_exp_iff.mpr htpos.le]) htpos.le
    rw [abs_of_nonneg hnonneg]
    exact (div_le_iff₀ htpos).mpr (exp_sub_one_le_linear htpos.le ht.2.le)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := v) (b := 1) (f := fun t => exponentialIntegral t - Real.log t)
    (f' := fun t => (Real.exp t - 1) / t) (C := Real.exp 1)
    (fun t ht => (hasDerivAt_Ei_sub_log (hv.trans_le ht.1)).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hderiv t ht)
    1 ⟨hvone, le_rfl⟩
  simp only [Real.log_one, sub_zero, Real.norm_eq_abs] at h
  have hunit : Real.exp 1 * (1 - v) ≤ Real.exp 1 := by nlinarith [Real.exp_pos 1]
  have htriangle := abs_sub (exponentialIntegral v - Real.log v) (exponentialIntegral 1)
  have hnorm : |exponentialIntegral v - Real.log v| ≤
      |(exponentialIntegral v - Real.log v) - exponentialIntegral 1| + |exponentialIntegral 1| := by
    have hh := abs_add_le ((exponentialIntegral v - Real.log v) - exponentialIntegral 1) (exponentialIntegral 1)
    simpa only [sub_add_cancel] using hh
  rw [abs_sub_comm] at h
  linarith

/-- The fixed lower weighted prime sum costs at most the numerical cutoff. -/
theorem rankinPrimeSum_le_cutoff (Y : ℕ) {zeta : ℝ} (hzeta : zeta ≤ 1) :
    rankinPrimeSum Y zeta ≤ Y := by
  have hsub : smallPrimesUpTo Y ⊆ Finset.Icc 1 Y := by
    intro p hp
    obtain ⟨hprime, hpY⟩ := mem_smallPrimesUpTo.mp hp
    exact Finset.mem_Icc.mpr ⟨hprime.one_le, hpY⟩
  have hcard : (smallPrimesUpTo Y).card ≤ Y :=
    (Finset.card_le_card hsub).trans_eq (by simp)
  calc
    _ ≤ ∑ _p ∈ smallPrimesUpTo Y, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpone : (1 : ℝ) ≤ p := by exact_mod_cast (mem_smallPrimesUpTo.mp hp).1.one_le
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hpone (show -1 + zeta ≤ 0 by linarith)
    _ = ((smallPrimesUpTo Y).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast hcard

/-- Precise lower-split cost: only the logarithm of zeta can diverge as zeta decreases to zero. -/
theorem abs_lower_split_le {A zeta : ℝ} (hA : 1 < A) (hzeta : 0 < zeta)
    (hzetaOne : zeta ≤ 1) (hlow : zeta * Real.log A ≤ 1) :
    |rankinPrimeSum ⌊A⌋₊ zeta - exponentialIntegral (zeta * Real.log A)| ≤
      A + |Real.log zeta| + |Real.log (Real.log A)| + |exponentialIntegral 1| + Real.exp 1 := by
  have hlogA := Real.log_pos hA
  have hnear := abs_Ei_sub_log_le_near_zero (mul_pos hzeta hlogA) hlow
  have hsum : 0 ≤ rankinPrimeSum ⌊A⌋₊ zeta := Finset.sum_nonneg (fun _ _ => by positivity)
  have hsumupper := (rankinPrimeSum_le_cutoff ⌊A⌋₊ hzetaOne).trans (Nat.floor_le (by linarith : 0 ≤ A))
  have hlog : |Real.log (zeta * Real.log A)| ≤ |Real.log zeta| + |Real.log (Real.log A)| := by
    rw [Real.log_mul hzeta.ne' hlogA.ne']
    exact abs_add_le _ _
  have hEi : |exponentialIntegral (zeta * Real.log A)| ≤
      |exponentialIntegral (zeta * Real.log A) - Real.log (zeta * Real.log A)| +
        |Real.log (zeta * Real.log A)| := by
    simpa only [sub_add_cancel] using abs_add_le
      (exponentialIntegral (zeta * Real.log A) - Real.log (zeta * Real.log A)) (Real.log (zeta * Real.log A))
  have htriangle := abs_sub (rankinPrimeSum ⌊A⌋₊ zeta) (exponentialIntegral (zeta * Real.log A))
  rw [abs_of_nonneg hsum] at htriangle
  linarith

/-- The entire weighted prime sum is close to Ei(zeta log b), with a finite PNT remainder.
All moving-cutoff dependence is displayed; no weighted-prime asymptotic is assumed. -/
theorem weighted_prime_full_error_le {A b zeta eta : ℝ}
    (hA : 1 < A) (hAb : A ≤ b) (hzeta : 0 < zeta) (hzetaOne : zeta ≤ 1)
    (hlow : zeta * Real.log A ≤ 1)
    (hR : ∀ t ∈ Set.Icc A b, |primeCountingRemainder t| ≤ eta * t / Real.log t) :
    |rankinPrimeSum ⌊b⌋₊ zeta - exponentialIntegral (zeta * Real.log b)| ≤
      eta * (b ^ zeta / Real.log b + A ^ zeta / Real.log A +
        (1 - zeta) * (exponentialIntegral (zeta * Real.log b) - exponentialIntegral (zeta * Real.log A))) +
      (A + |Real.log zeta| + |Real.log (Real.log A)| + |exponentialIntegral 1| + Real.exp 1) := by
  have htail := weighted_prime_error_le hA hAb hzeta hzetaOne hR
  have hlower := abs_lower_split_le hA hzeta hzetaOne hlow
  have htriangle := abs_add_le
    (rankinPrimeSum ⌊b⌋₊ zeta - rankinPrimeSum ⌊A⌋₊ zeta -
      (exponentialIntegral (zeta * Real.log b) - exponentialIntegral (zeta * Real.log A)))
    (rankinPrimeSum ⌊A⌋₊ zeta - exponentialIntegral (zeta * Real.log A))
  have heq : rankinPrimeSum ⌊b⌋₊ zeta - rankinPrimeSum ⌊A⌋₊ zeta -
      (exponentialIntegral (zeta * Real.log b) - exponentialIntegral (zeta * Real.log A)) +
      (rankinPrimeSum ⌊A⌋₊ zeta - exponentialIntegral (zeta * Real.log A)) =
      rankinPrimeSum ⌊b⌋₊ zeta - exponentialIntegral (zeta * Real.log b) := by ring
  rw [heq] at htriangle
  exact htriangle.trans (add_le_add htail hlower)

end
end PaperC.V282.PrimeEulerLowerSplit
