import PaperC.Arithmetic.DyadicPrimeReciprocalSums
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Paper C v1.1: an elementary prime-harmonic bound

The prime-harmonic input in Proposition 3.3 is derived here from the existing
certified Chebyshev estimate.  The proof covers the primes above `4` by
adjacent dyadic shells, applies `sum_inv_dyadicPrimes_le` to each shell, and
then bounds the resulting harmonic sum.  No Mertens theorem, PNT invocation,
or additional literature interface is used.
-/

namespace PaperC
namespace V11
namespace PrimeHarmonic

open scoped BigOperators

open DefectCounting
open DyadicPrimeReciprocalSums

/-- Split the dyadic interval above `4` into its previous part and last shell. -/
theorem dyadicPrimes_four_succ_eq_union (K : ℕ) :
    dyadicPrimes 4 (K + 1) =
      dyadicPrimes 4 K ∪ dyadicPrimes (4 * 2 ^ K) 1 := by
  ext p
  simp only [mem_dyadicPrimes, Finset.mem_union]
  have hcut : 4 * 2 ^ (K + 1) = (4 * 2 ^ K) * 2 := by
    rw [pow_succ]
    ring
  constructor
  · rintro ⟨hp, h4p, hpUpper⟩
    by_cases hmid : p ≤ 4 * 2 ^ K
    · exact Or.inl ⟨hp, h4p, hmid⟩
    · exact Or.inr ⟨hp, lt_of_not_ge hmid,
        by simpa [hcut] using hpUpper⟩
  · rintro (hp | hp)
    · exact ⟨hp.1, hp.2.1,
        hp.2.2.trans (by
          rw [pow_succ]
          omega)⟩
    · exact ⟨hp.1,
        (Nat.le_mul_of_pos_right 4 (by positivity)).trans_lt hp.2.1,
        by simpa [hcut] using hp.2.2⟩

/-- The accumulated dyadic interval and its next shell are disjoint. -/
theorem disjoint_dyadicPrimes_four_shell (K : ℕ) :
    Disjoint (dyadicPrimes 4 K) (dyadicPrimes (4 * 2 ^ K) 1) := by
  rw [Finset.disjoint_left]
  intro p hpLeft hpRight
  exact (Nat.not_lt_of_ge (mem_dyadicPrimes.mp hpLeft).2.2)
    (mem_dyadicPrimes.mp hpRight).2.1

/-- The reciprocal mass of the `K`-th shell is at most `14/(K+2)`. -/
theorem sum_inv_shell_four_le (K : ℕ) :
    (∑ p ∈ dyadicPrimes (4 * 2 ^ K) 1, 1 / (p : ℚ)) ≤
      14 / ((K + 2 : ℕ) : ℚ) := by
  have hbase : 4 ≤ 4 * 2 ^ K :=
    Nat.le_mul_of_pos_right 4 (by positivity)
  have h := sum_inv_dyadicPrimes_le (4 * 2 ^ K) 1 hbase
  have hpow : 4 * 2 ^ K = 2 ^ (K + 2) := by
    calc
      4 * 2 ^ K = 2 ^ 2 * 2 ^ K := by norm_num
      _ = 2 ^ (2 + K) := (pow_add 2 2 K).symm
      _ = 2 ^ (K + 2) := by congr 1; omega
  simpa [hpow, Nat.log_pow (by norm_num : 1 < 2)] using h

/-- Dyadic shell summation in harmonic-number form. -/
theorem sum_inv_dyadicPrimes_four_le_harmonic (K : ℕ) :
    (∑ p ∈ dyadicPrimes 4 K, 1 / (p : ℚ)) ≤
      14 * harmonic K := by
  induction K with
  | zero => simp [dyadicPrimes]
  | succ K ih =>
      rw [dyadicPrimes_four_succ_eq_union,
        Finset.sum_union (disjoint_dyadicPrimes_four_shell K),
        harmonic_succ]
      have hshell := sum_inv_shell_four_le K
      have hdenom :
          (1 / (((K + 2 : ℕ) : ℚ))) ≤
            1 / (((K + 1 : ℕ) : ℚ)) := by
        apply one_div_le_one_div_of_le
        · positivity
        · norm_num
      calc
        (∑ p ∈ dyadicPrimes 4 K, 1 / (p : ℚ)) +
              ∑ p ∈ dyadicPrimes (4 * 2 ^ K) 1, 1 / (p : ℚ)
            ≤ 14 * harmonic K + 14 / (((K + 2 : ℕ) : ℚ)) :=
          add_le_add ih hshell
        _ ≤ 14 * harmonic K + 14 / (((K + 1 : ℕ) : ℚ)) := by
          simp only [div_eq_mul_inv, one_mul] at hdenom ⊢
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hdenom
              (by norm_num : (0 : ℚ) ≤ 14))
        _ = 14 * (harmonic K + (((K + 1 : ℕ) : ℚ))⁻¹) := by
          rw [div_eq_mul_inv]
          ring

/-- Every prime up to `T` is either at most `4` or in the dyadic cover. -/
theorem smallPrimesUpTo_subset_low_union_dyadic (T : ℕ) :
    smallPrimesUpTo T ⊆
      smallPrimesUpTo 4 ∪ dyadicPrimes 4 (Nat.log 2 T + 1) := by
  intro p hp
  have hpData := mem_smallPrimesUpTo.mp hp
  by_cases hp4 : p ≤ 4
  · exact Finset.mem_union_left _
      (mem_smallPrimesUpTo.mpr ⟨hpData.1, hp4⟩)
  · apply Finset.mem_union_right
    rw [mem_dyadicPrimes]
    refine ⟨hpData.1, lt_of_not_ge hp4, ?_⟩
    have hT : T < 2 ^ (Nat.log 2 T + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) T
    calc
      p ≤ T := hpData.2
      _ ≤ 4 * 2 ^ (Nat.log 2 T + 1) := by omega

/-- The low-prime part and the dyadic part of the cover are disjoint. -/
theorem disjoint_low_dyadic (T : ℕ) :
    Disjoint (smallPrimesUpTo 4)
      (dyadicPrimes 4 (Nat.log 2 T + 1)) := by
  rw [Finset.disjoint_left]
  intro p hpLow hpHigh
  exact (Nat.not_lt_of_ge (mem_smallPrimesUpTo.mp hpLow).2)
    (mem_dyadicPrimes.mp hpHigh).2.1

/-- A deliberately coarse constant bound for the primes at most `4`. -/
theorem sum_inv_smallPrimesUpTo_low_le :
    (∑ p ∈ smallPrimesUpTo 4, 1 / (p : ℚ)) ≤ 4 := by
  calc
    (∑ p ∈ smallPrimesUpTo 4, 1 / (p : ℚ)) ≤
        ∑ _p ∈ smallPrimesUpTo 4, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpQ : (0 : ℚ) < (p : ℚ) := by
        exact_mod_cast (mem_smallPrimesUpTo.mp hp).1.pos
      rw [div_le_iff₀ hpQ]
      simpa using (mem_smallPrimesUpTo.mp hp).1.one_le
    _ = ((smallPrimesUpTo 4).card : ℚ) := by simp
    _ ≤ 4 := by norm_cast

/-- A finite rational prime-harmonic bound obtained from the shell cover. -/
theorem sum_inv_smallPrimesUpTo_le_harmonic_log (T : ℕ) :
    (∑ p ∈ smallPrimesUpTo T, 1 / (p : ℚ)) ≤
      4 + 14 * harmonic (Nat.log 2 T + 1) := by
  calc
    (∑ p ∈ smallPrimesUpTo T, 1 / (p : ℚ)) ≤
        ∑ p ∈ (smallPrimesUpTo 4 ∪
          dyadicPrimes 4 (Nat.log 2 T + 1)), 1 / (p : ℚ) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (smallPrimesUpTo_subset_low_union_dyadic T)
        (fun p _ _ ↦ by positivity)
    _ = (∑ p ∈ smallPrimesUpTo 4, 1 / (p : ℚ)) +
        ∑ p ∈ dyadicPrimes 4 (Nat.log 2 T + 1), 1 / (p : ℚ) := by
      rw [Finset.sum_union (disjoint_low_dyadic T)]
    _ ≤ 4 + 14 * harmonic (Nat.log 2 T + 1) :=
      add_le_add sum_inv_smallPrimesUpTo_low_le
        (sum_inv_dyadicPrimes_four_le_harmonic _)

/-- Real version of the finite harmonic-number bound. -/
theorem sum_inv_smallPrimesUpTo_real_le_harmonic_log (T : ℕ) :
    (∑ p ∈ smallPrimesUpTo T, (p : ℝ)⁻¹) ≤
      4 + 14 * (harmonic (Nat.log 2 T + 1) : ℝ) := by
  have h := sum_inv_smallPrimesUpTo_le_harmonic_log T
  simp only [one_div] at h
  have hR :
      ((∑ p ∈ smallPrimesUpTo T, (p : ℚ)⁻¹ : ℚ) : ℝ) ≤
        ((4 + 14 * harmonic (Nat.log 2 T + 1) : ℚ) : ℝ) :=
    Rat.cast_le.mpr h
  simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] using hR

/-- First logarithmic form of the finite reciprocal-prime estimate. -/
theorem sum_inv_smallPrimesUpTo_real_le_log_logTwo (T : ℕ) :
    (∑ p ∈ smallPrimesUpTo T, (p : ℝ)⁻¹) ≤
      18 + 14 * Real.log (Nat.log 2 T + 1) := by
  have hh := harmonic_le_one_add_log (Nat.log 2 T + 1)
  have hh' :
      (harmonic (Nat.log 2 T + 1) : ℝ) ≤
        1 + Real.log (Nat.log 2 T + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  calc
    (∑ p ∈ smallPrimesUpTo T, (p : ℝ)⁻¹) ≤
        4 + 14 * (harmonic (Nat.log 2 T + 1) : ℝ) :=
      sum_inv_smallPrimesUpTo_real_le_harmonic_log T
    _ ≤ 4 + 14 * (1 + Real.log (Nat.log 2 T + 1)) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hh'
          (by norm_num : (0 : ℝ) ≤ 14))
    _ = 18 + 14 * Real.log (Nat.log 2 T + 1) := by ring

/-- Relate the dyadic logarithm to the manuscript's `log log (3T)` scale. -/
theorem one_add_log_natLog_add_two_le (T : ℕ) (hT : 3 ≤ T) :
    1 + Real.log ((Nat.log 2 T + 2 : ℕ) : ℝ) ≤
      6 * Real.log (Real.log ((3 * T : ℕ) : ℝ)) := by
  let L : ℝ := Real.log ((3 * T : ℕ) : ℝ)
  have hT0 : T ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hT)
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hT0)
  have hlogT_nonneg : 0 ≤ Real.log (T : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ T by omega))
  have hlog2_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 :=
    lt_of_lt_of_le (by norm_num) hlog2_half
  have hk_logb := Real.natLog_le_logb T 2
  have hk_mul : (Nat.log 2 T : ℝ) * Real.log 2 ≤ Real.log (T : ℝ) := by
    apply (le_div_iff₀ hlog2pos).mp
    simpa [Real.logb] using hk_logb
  have hk_nonneg : 0 ≤ (Nat.log 2 T : ℝ) := by positivity
  have hk_half : (Nat.log 2 T : ℝ) / 2 ≤
      (Nat.log 2 T : ℝ) * Real.log 2 := by
    nlinarith
  have hk_le : (Nat.log 2 T : ℝ) ≤ 2 * Real.log (T : ℝ) := by
    nlinarith
  have hT_le : (T : ℝ) ≤ ((3 * T : ℕ) : ℝ) := by
    exact_mod_cast (show T ≤ 3 * T by omega)
  have hlogT_le_L : Real.log (T : ℝ) ≤ L := by
    dsimp [L]
    exact Real.log_le_log hTpos hT_le
  have hnine_le : (9 : ℝ) ≤ ((3 * T : ℕ) : ℝ) := by
    exact_mod_cast (show 9 ≤ 3 * T by omega)
  have hlog9_le_L : Real.log 9 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) hnine_le
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hL_two : 2 ≤ L := by
    rw [hlog9] at hlog9_le_L
    linarith [Real.log_three_gt_d9]
  have hk_add_two : ((Nat.log 2 T + 2 : ℕ) : ℝ) ≤ 3 * L := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  have hlog_k : Real.log ((Nat.log 2 T + 2 : ℕ) : ℝ) ≤
      Real.log (3 * L) := by
    apply Real.log_le_log (by positivity)
    exact hk_add_two
  have hlog_prod : Real.log (3 * L) = Real.log 3 + Real.log L := by
    rw [Real.log_mul (by norm_num) (by linarith)]
  have hlog2_le_logL : Real.log 2 ≤ Real.log L :=
    Real.log_le_log (by norm_num) hL_two
  have hconst : 1 + Real.log 3 ≤ 5 * Real.log 2 := by
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  calc
    1 + Real.log ((Nat.log 2 T + 2 : ℕ) : ℝ) ≤
        1 + Real.log (3 * L) := by linarith
    _ = 1 + Real.log 3 + Real.log L := by rw [hlog_prod]; ring
    _ ≤ 5 * Real.log 2 + Real.log L := by linarith
    _ ≤ 5 * Real.log L + Real.log L := by linarith
    _ = 6 * Real.log L := by ring
    _ = 6 * Real.log (Real.log ((3 * T : ℕ) : ℝ)) := by rfl

/-- The matching estimate with `Nat.log 2 T + 1`. -/
theorem one_add_log_natLog_add_one_le (T : ℕ) (hT : 3 ≤ T) :
    1 + Real.log ((Nat.log 2 T + 1 : ℕ) : ℝ) ≤
      6 * Real.log (Real.log ((3 * T : ℕ) : ℝ)) := by
  calc
    1 + Real.log ((Nat.log 2 T + 1 : ℕ) : ℝ) ≤
        1 + Real.log ((Nat.log 2 T + 2 : ℕ) : ℝ) := by
      rw [add_le_add_iff_left]
      apply Real.log_le_log (by positivity)
      norm_num
    _ ≤ 6 * Real.log (Real.log ((3 * T : ℕ) : ℝ)) :=
      one_add_log_natLog_add_two_le T hT

/--
Explicit unconditional prime-harmonic bound used below.  The constant `120`
is absolute and deliberately generous.
-/
theorem sum_inv_smallPrimesUpTo_real_le_loglog
    (T : ℕ) (hT : 3 ≤ T) :
    (∑ p ∈ smallPrimesUpTo T, (p : ℝ)⁻¹) ≤
      120 * Real.log (Real.log ((3 * T : ℕ) : ℝ)) := by
  have hbase := sum_inv_smallPrimesUpTo_real_le_log_logTwo T
  have hscale := one_add_log_natLog_add_one_le T hT
  have hscale' :
      1 + Real.log ((Nat.log 2 T : ℝ) + 1) ≤
        6 * Real.log (Real.log ((3 * T : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hscale
  have hnine_le : (9 : ℝ) ≤ ((3 * T : ℕ) : ℝ) := by
    exact_mod_cast (show 9 ≤ 3 * T by omega)
  have hinner : 2 ≤ Real.log ((3 * T : ℕ) : ℝ) := by
    have hlog9 : Real.log 9 ≤ Real.log ((3 * T : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) hnine_le
    rw [show (9 : ℝ) = 3 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)] at hlog9
    linarith [Real.log_three_gt_d9]
  have houter : (1 / 2 : ℝ) ≤
      Real.log (Real.log ((3 * T : ℕ) : ℝ)) := by
    calc
      (1 / 2 : ℝ) ≤ Real.log 2 := by
        linarith [Real.log_two_gt_d9]
      _ ≤ Real.log (Real.log ((3 * T : ℕ) : ℝ)) :=
        Real.log_le_log (by norm_num) hinner
  calc
    (∑ p ∈ smallPrimesUpTo T, (p : ℝ)⁻¹) ≤
        18 + 14 * Real.log (Nat.log 2 T + 1) := hbase
    _ ≤ 18 + 14 *
          (6 * Real.log (Real.log ((3 * T : ℕ) : ℝ)) - 1) := by
      nlinarith [hscale']
    _ ≤ 120 * Real.log (Real.log ((3 * T : ℕ) : ℝ)) := by
      nlinarith

end PrimeHarmonic
end V11
end PaperC
