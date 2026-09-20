import PaperCPrel8.RoughKernelRankin

/-! # Reciprocal rough-kernel sums

The empty rough support is removed before taking the finite Euler product.
The weight parameter is independent of the small-prime cutoff.
-/
namespace PaperC.Prel8.RoughKernelReciprocal

open scoped BigOperators
open DefectCounting LargeOddKernel LargeKernelWeightedCounting V11.RankinTilt
open V282.DefectiveRankinCount

noncomputable section

/-- Canonical support injection with an arbitrary nonnegative rough-support weight. -/
theorem weighted_fibres (Y X : ℕ) (w : Finset ℕ → ℝ) (hw : ∀ t, 0 ≤ w t) :
    (∑ n ∈ Finset.Icc 1 X, w (largeOddPrimeSupport Y n)) ≤
      ∑ small ∈ (smallPrimesUpTo Y).powerset,
        ∑ large ∈ (largePrimesBetween Y X).powerset,
          (Nat.sqrt (X / (small.prod id * large.prod id)) : ℝ) * w large := by
  classical
  have heq : (∑ n ∈ Finset.Icc 1 X, w (largeOddPrimeSupport Y n)) =
      ∑ t ∈ canonicalKernelTriplesUpTo Y X, w t.2.1 := by
    rw [canonicalKernelTriplesUpTo, Finset.sum_image]
    · rfl
    · intro m hm n hn hmn
      exact canonicalKernelTriple_injective_of_ne_zero
        (by have := (Finset.mem_Icc.mp hm).1; omega)
        (by have := (Finset.mem_Icc.mp hn).1; omega) hmn
  rw [heq]
  calc
    _ ≤ ∑ t ∈ kernelTriplesUpTo Y X, w t.2.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (canonicalKernelTriplesUpTo_subset_kernelTriplesUpTo Y X) (fun t _ _ ↦ hw t.2.1)
    _ = _ := by
      rw [kernelTriplesUpTo, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro small _
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro large _
      simp [Nat.card_Icc]

/-- The same injection at a variable Rankin exponent. -/
theorem weighted_rankin (Y X : ℕ) (w : Finset ℕ → ℝ) (hw : ∀ t, 0 ≤ w t)
    {σ : ℝ} (hσ : σ ≤ 1 / 2) :
    (∑ n ∈ Finset.Icc 1 X, w (largeOddPrimeSupport Y n)) ≤
      (X : ℝ) ^ (1 - σ) * rankinEulerProduct Y σ *
        ∑ large ∈ (largePrimesBetween Y X).powerset,
          (↑(large.prod id) : ℝ) ^ (-1 + σ) * w large := by
  calc
    _ ≤ ∑ small ∈ (smallPrimesUpTo Y).powerset,
        ∑ large ∈ (largePrimesBetween Y X).powerset,
          (X : ℝ) ^ (1 - σ) * (∏ p ∈ small, (p : ℝ) ^ (-1 + σ)) *
            (↑(large.prod id) : ℝ) ^ (-1 + σ) * w large := by
      apply (weighted_fibres Y X w hw).trans
      apply Finset.sum_le_sum
      intro small hsmall
      apply Finset.sum_le_sum
      intro large hlarge
      apply mul_le_mul_of_nonneg_right _ (hw large)
      apply RoughKernelRankin.square_fibre_split Y X (large.prod id) small
        (Finset.mem_powerset.mp hsmall) _ hσ
      apply one_le_prod_of_subset_smallPrimesUpTo
      intro p hp
      have hp' := mem_largePrimesBetween.mp (Finset.mem_powerset.mp hlarge hp)
      exact mem_smallPrimesUpTo.mpr ⟨hp'.1, hp'.2.2⟩
    _ = _ := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.prod_one_add]
      rfl

/-- A support weight is the product of its prime weights at exponent -2+σ. -/
theorem support_weight (large : Finset ℕ) {z σ : ℝ}
    (hpos : ∀ p ∈ large, 0 < p) :
    (↑(large.prod id) : ℝ) ^ (-1 + σ) * (z ^ large.card / (↑(large.prod id) : ℝ)) =
      ∏ p ∈ large, z * (p : ℝ) ^ (-2 + σ) := by
  rw [cast_prod_rpow_eq_prod]
  have hid : (↑(large.prod id) : ℝ) = ∏ p ∈ large, (p : ℝ) := by simp
  rw [hid, ← Finset.prod_const, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpos p hp
  calc
    _ = z * ((p : ℝ) ^ (-1 + σ) / p) := by ring
    _ = _ := by
      rw [← Real.rpow_sub_one hp0.ne']
      congr 2
      ring

/-- Remove the empty support before summing the Euler product. -/
theorem nonempty_support_sum (P : Finset ℕ) (f : ℕ → ℝ) :
    (∑ t ∈ P.powerset, if t = ∅ then 0 else ∏ p ∈ t, f p) =
      (∏ p ∈ P, (1 + f p)) - 1 := by
  classical
  have h := Finset.prod_one_add (s := P) (f := f)
  have hsum : (∑ t ∈ P.powerset, ∏ p ∈ t, f p) =
      1 + ∑ t ∈ P.powerset, if t = ∅ then 0 else ∏ p ∈ t, f p := by
    rw [← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset P)]
    simp only [Finset.prod_empty]
    have heq : (∑ t ∈ P.powerset, if t = ∅ then 0 else ∏ p ∈ t, f p) =
        ∑ t ∈ P.powerset.erase ∅, ∏ p ∈ t, f p := by
      rw [← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset P)]
      simp only [ite_true, add_zero]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [(Finset.mem_erase.mp ht).1, ite_false]
    rw [heq, add_comm]
  rw [← h] at hsum
  linarith

/-- Actual weighted reciprocal sum; no zeta factor and no asymptotic premise. -/
theorem reciprocal_le_euler (Y X : ℕ) {z σ : ℝ} (hz : 0 ≤ z) (hσ : σ ≤ 1 / 2) :
    (∑ n ∈ Finset.Icc 1 X,
      if largeOddPrimeSupport Y n = ∅ then 0 else
        z ^ (largeOddPrimeSupport Y n).card / (largeOddKernel Y n : ℝ)) ≤
      (X : ℝ) ^ (1 - σ) * rankinEulerProduct Y σ *
        ((∏ p ∈ largePrimesBetween Y X, (1 + z * (p : ℝ) ^ (-2 + σ))) - 1) := by
  classical
  have h := weighted_rankin Y X
    (fun t ↦ if t = ∅ then 0 else z ^ t.card / (↑(t.prod id) : ℝ))
    (fun t ↦ by split_ifs <;> positivity) hσ
  change (∑ n ∈ Finset.Icc 1 X,
    if largeOddPrimeSupport Y n = ∅ then 0 else
      z ^ (largeOddPrimeSupport Y n).card / (largeOddKernel Y n : ℝ)) ≤ _ at h
  have heq : (∑ t ∈ (largePrimesBetween Y X).powerset,
      (↑(t.prod id) : ℝ) ^ (-1 + σ) * (if t = ∅ then 0 else z ^ t.card / (↑(t.prod id) : ℝ))) =
      (∏ p ∈ largePrimesBetween Y X, (1 + z * (p : ℝ) ^ (-2 + σ))) - 1 := by
    rw [← nonempty_support_sum]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hte : t = ∅
    · simp [hte]
    · simp only [hte, ite_false]
      exact support_weight t (fun p hp ↦
        (mem_largePrimesBetween.mp (Finset.mem_powerset.mp ht hp)).1.pos)
  rwa [heq] at h

/-- The finite rough-prime Euler product is controlled by an integer power tail. -/
theorem euler_le_exp (Y X : ℕ) (hY : 1 ≤ Y) {z σ : ℝ}
    (hz : 0 ≤ z) (hσ : σ < 1) :
    (∏ p ∈ largePrimesBetween Y X, (1 + z * (p : ℝ) ^ (-2 + σ))) ≤
      Real.exp (z * (Y : ℝ) ^ (-(1 - σ)) / (1 - σ)) := by
  apply (Real.prod_one_add_le_exp_sum _ (fun p ↦
    mul_nonneg hz (Real.rpow_nonneg (Nat.cast_nonneg p) _))).trans
  apply Real.exp_le_exp.mpr
  have hs : (∑ p ∈ largePrimesBetween Y X, (p : ℝ) ^ (-2 + σ)) ≤
      (Y : ℝ) ^ (-(1 - σ)) / (1 - σ) := by
    calc
      _ ≤ ∑ p ∈ Finset.Ioc Y X, (p : ℝ) ^ (-2 + σ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (largePrimesBetween_subset_Ioc Y X)
          (fun p _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
      _ ≤ _ := by
        have he : -2 + σ = -1 - (1 - σ) := by ring
        rw [he]
        exact RoughKernelPowerSums.sum_Ioc_tail_le Y X hY (by linarith)
  rw [← Finset.mul_sum]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hs hz

/-- Finite reciprocal estimate for the actual rough support with its empty term removed. -/
theorem reciprocal_le_exp (Y X : ℕ) (hY : 1 ≤ Y)
    {z σ : ℝ} (hz : 0 ≤ z) (hσ : σ ≤ 1 / 2) :
    (∑ n ∈ Finset.Icc 1 X,
      if largeOddPrimeSupport Y n = ∅ then 0 else
        z ^ (largeOddPrimeSupport Y n).card / (largeOddKernel Y n : ℝ)) ≤
      (X : ℝ) ^ (1 - σ) * rankinEulerProduct Y σ *
        (Real.exp (z * (Y : ℝ) ^ (-(1 - σ)) / (1 - σ)) - 1) := by
  apply (reciprocal_le_euler Y X hz hσ).trans
  apply mul_le_mul_of_nonneg_left (sub_le_sub_right (euler_le_exp Y X hY hz (by linarith)) 1)
  apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  unfold rankinEulerProduct
  exact Finset.prod_nonneg (fun p _ ↦ by positivity)

/-- Population-normalized reciprocal estimate, with independent cutoff and weight. -/
theorem normalized_reciprocal_le_exp (Y X : ℕ) (hY : 1 ≤ Y) (hX : 0 < X)
    {z σ : ℝ} (hz : 0 ≤ z) (hσ : σ ≤ 1 / 2) :
    (∑ n ∈ Finset.Icc 1 X,
      if largeOddPrimeSupport Y n = ∅ then 0 else
        z ^ (largeOddPrimeSupport Y n).card / (largeOddKernel Y n : ℝ)) / X ≤
      (X : ℝ) ^ (-σ) * rankinEulerProduct Y σ *
        (Real.exp (z * (Y : ℝ) ^ (-(1 - σ)) / (1 - σ)) - 1) := by
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have h := div_le_div_of_nonneg_right (reciprocal_le_exp Y X hY hz hσ) hx.le
  have hp : (X : ℝ) ^ (1 - σ) = (X : ℝ) ^ (-σ) * X := by
    rw [show 1 - σ = -σ + 1 by ring, Real.rpow_add hx, Real.rpow_one]
  rw [hp] at h
  convert h using 1; field_simp

/-- Support notation agrees exactly with the paper's nontrivial-kernel omega sum. -/
theorem literal_sum_eq (Y X : ℕ) (z : ℝ) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n ↦ 1 < largeOddKernel Y n),
      z ^ ArithmeticFunction.cardDistinctFactors (largeOddKernel Y n) /
        (largeOddKernel Y n : ℝ)) =
    ∑ n ∈ Finset.Icc 1 X, if largeOddPrimeSupport Y n = ∅ then 0 else
      z ^ (largeOddPrimeSupport Y n).card / (largeOddKernel Y n : ℝ) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  rw [cardDistinctFactors_largeOddKernel]
  have h1 := one_le_largeOddKernel Y n
  have he := largeOddKernel_eq_one_iff_support_eq_empty Y n
  by_cases h : largeOddPrimeSupport Y n = ∅
  · have hk := he.mpr h
    simp [h, hk]
  · have hk : 1 < largeOddKernel Y n := by
      have : largeOddKernel Y n ≠ 1 := fun hx ↦ h (he.mp hx)
      omega
    simp [h, hk]

/-- The literal population-normalized reciprocal bound of G.1, strengthened. -/
theorem literal_normalized_reciprocal_le (Y X : ℕ) (hY : 1 ≤ Y) (hX : 0 < X)
    {z σ : ℝ} (hz : 0 ≤ z) (hσ : σ ≤ 1 / 2) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n ↦ 1 < largeOddKernel Y n),
      z ^ ArithmeticFunction.cardDistinctFactors (largeOddKernel Y n) /
        (largeOddKernel Y n : ℝ)) / X ≤
      (X : ℝ) ^ (-σ) * rankinEulerProduct Y σ *
        (Real.exp (z * (Y : ℝ) ^ (-(1 - σ)) / (1 - σ)) - 1) := by
  rw [literal_sum_eq]
  exact normalized_reciprocal_le_exp Y X hY hX hz hσ

end

end PaperC.Prel8.RoughKernelReciprocal
