import PaperCV282.DefectiveRankinCount
import PaperCV11.RankinEnvelope
import PaperCV11.PrimeHarmonic
import PaperC.Analysis.ReciprocalThreeHalvesTail

/-!
# Exact logarithms and a uniform remainder for the Rankin Euler product

The difference between the weighted prime sum and the logarithm of the
product is at most two, uniformly in the cutoff and in zeta≤1/4. This is
the elementary logarithmic remainder required in companion (B.2).
The PNT main term Ei(u), with its uniform error, is not asserted here.
-/

namespace PaperC.V282.PrimeEulerRankin

open DefectCounting DefectiveRankinCount

noncomputable section

/-- The weighted prime sum before taking logarithms of Euler factors. -/
def rankinPrimeSum (Y : ℕ) (zeta : ℝ) : ℝ :=
  ∑ p ∈ smallPrimesUpTo Y, (p : ℝ) ^ (-1 + zeta)

/-- The exact logarithmic sum, with no asymptotic replacement. -/
def rankinLogSum (Y : ℕ) (zeta : ℝ) : ℝ :=
  ∑ p ∈ smallPrimesUpTo Y, Real.log (1 + (p : ℝ) ^ (-1 + zeta))

theorem rankinEulerProduct_pos (Y : ℕ) (zeta : ℝ) : 0 < rankinEulerProduct Y zeta := by
  apply Finset.prod_pos
  intro p _
  positivity

/-- Taking logarithms is an exact finite operation. -/
theorem log_rankinEulerProduct (Y : ℕ) (zeta : ℝ) :
    Real.log (rankinEulerProduct Y zeta) = rankinLogSum Y zeta := by
  apply Real.log_prod
  intro p _
  positivity

theorem rankinEulerProduct_eq_exp (Y : ℕ) (zeta : ℝ) :
    rankinEulerProduct Y zeta = Real.exp (rankinLogSum Y zeta) := by
  rw [← log_rankinEulerProduct, Real.exp_log (rankinEulerProduct_pos Y zeta)]

/-- Elementary logarithmic loss, valid for every nonnegative summand. -/
theorem sub_log_one_add_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t - Real.log (1 + t) ∧ t - Real.log (1 + t) ≤ t ^ 2 := by
  have hu := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + t)
  have hl := Real.le_log_one_add_of_nonneg ht
  have hl' : t - t ^ 2 ≤ 2 * t / (t + 2) := by
    apply (le_div_iff₀ (by positivity : 0 < t + 2)).mpr
    nlinarith [mul_nonneg ht (sq_nonneg t)]
  constructor <;> linarith

/-- The log Euler product never exceeds its weighted prime sum. -/
theorem rankinLogSum_le_primeSum (Y : ℕ) (zeta : ℝ) :
    rankinLogSum Y zeta ≤ rankinPrimeSum Y zeta := by
  apply Finset.sum_le_sum
  intro p _
  exact sub_nonneg.mp (sub_log_one_add_bounds (by positivity : 0 ≤ (p : ℝ) ^ (-1 + zeta))).1

/-- A uniform O(1) remainder, proved by the convergent integer series n^(-3/2). -/
theorem primeSum_sub_logSum_le_two (Y : ℕ) {zeta : ℝ} (hzeta : zeta ≤ 1 / 4) :
    rankinPrimeSum Y zeta - rankinLogSum Y zeta ≤ 2 := by
  have hsub : smallPrimesUpTo Y ⊆ Finset.Ioc 1 Y := by
    intro p hp
    obtain ⟨hprime, hY⟩ := mem_smallPrimesUpTo.mp hp
    exact Finset.mem_Ioc.mpr ⟨hprime.one_lt, hY⟩
  calc
    _ = ∑ p ∈ smallPrimesUpTo Y,
        ((p : ℝ) ^ (-1 + zeta) - Real.log (1 + (p : ℝ) ^ (-1 + zeta))) := by
      rw [Finset.sum_sub_distrib]
      rfl
    _ ≤ ∑ p ∈ smallPrimesUpTo Y, (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpone : (1 : ℝ) ≤ p := by exact_mod_cast (mem_smallPrimesUpTo.mp hp).1.one_le
      have hsq : ((p : ℝ) ^ (-1 + zeta)) ^ 2 ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_mul_natCast (by positivity)]
        exact Real.rpow_le_rpow_of_exponent_le hpone (by norm_num; linarith)
      exact (sub_log_one_add_bounds (by positivity)).2.trans hsq
    _ ≤ ∑ n ∈ Finset.Ioc 1 Y, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => Real.rpow_nonneg (by positivity) _)
    _ ≤ 2 := by simpa using sum_Ioc_rpow_neg_three_halves_le 1 Y le_rfl

/-- Absolute-error form, uniform even when the prime cutoff varies. -/
theorem abs_logSum_sub_primeSum_le_two (Y : ℕ) {zeta : ℝ} (hzeta : zeta ≤ 1 / 4) :
    |rankinLogSum Y zeta - rankinPrimeSum Y zeta| ≤ 2 := by
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (rankinLogSum_le_primeSum Y zeta))]
  exact primeSum_sub_logSum_le_two Y hzeta

/-- A completely proved, though non-sharp, unconditional analytic envelope. -/
theorem rankinEulerProduct_le_exp_loglog {Y : ℕ} (hY : 3 ≤ Y)
    {zeta : ℝ} (hzeta : 0 ≤ zeta) :
    rankinEulerProduct Y zeta ≤
      Real.exp ((Y : ℝ) ^ zeta * (120 * Real.log (Real.log ((3 * Y : ℕ) : ℝ)))) := by
  exact V11.RankinEnvelope.prod_one_add_rankin_le_exp Y hzeta
    (V11.PrimeHarmonic.sum_inv_smallPrimesUpTo_real_le_loglog Y hY)

/-- Exact exponential form of the finite Rankin bound, before the PNT step. -/
theorem normalized_defectiveValues_le_exp_logSum {X : ℕ} (hX : 0 < X) (Y : ℕ)
    {zeta : ℝ} (hzeta : zeta ≤ 1 / 2) :
    ((defectiveValues X Y).card : ℝ) / X ≤
      Real.exp (-zeta * Real.log X + rankinLogSum Y zeta) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  calc
    _ ≤ (X : ℝ) ^ (-zeta) * rankinEulerProduct Y zeta := normalized_defectiveValues_le_rankin hX Y hzeta
    _ = _ := by
      rw [rankinEulerProduct_eq_exp, Real.rpow_def_of_pos hXpos, ← Real.exp_add]
      congr 1
      ring

/-- The weighted prime sum may replace the logarithmic sum as an upper bound. -/
theorem normalized_defectiveValues_le_exp_primeSum {X : ℕ} (hX : 0 < X) (Y : ℕ)
    {zeta : ℝ} (hzeta : zeta ≤ 1 / 2) :
    ((defectiveValues X Y).card : ℝ) / X ≤
      Real.exp (-zeta * Real.log X + rankinPrimeSum Y zeta) := by
  exact (normalized_defectiveValues_le_exp_logSum hX Y hzeta).trans
    (Real.exp_le_exp.mpr (by linarith [rankinLogSum_le_primeSum Y zeta]))

/-- The floor cutoff selects exactly the primes below the real exponential cutoff. -/
theorem mem_primes_floor_exp_iff (w : ℝ) (p : ℕ) :
    p ∈ smallPrimesUpTo ⌊Real.exp w⌋₊ ↔ p.Prime ∧ (p : ℝ) ≤ Real.exp w := by
  rw [mem_smallPrimesUpTo, Nat.le_floor_iff (Real.exp_nonneg w)]

end
end PaperC.V282.PrimeEulerRankin
