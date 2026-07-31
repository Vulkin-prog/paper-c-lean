import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# An elementary reciprocal-three-halves tail

The relational-host estimate in §4 of Paper C only needs a tail estimate for
the convergent series `∑ n⁻³ᐟ²`.  We deliberately sum over every integer,
rather than using any information about the distribution of primes.
-/

namespace PaperC

open scoped BigOperators

/--
The finite tail of the reciprocal-three-halves series is at most
`2 / √B`.

This is the integral comparison for the decreasing function
`x ↦ x⁻³ᐟ²`.  Its formulation with `Finset.Ioc B X` is the one used by the
large-odd-kernel Euler product.
-/
theorem sum_Ioc_rpow_neg_three_halves_le
    (B X : ℕ) (hB : 1 ≤ B) :
    (∑ n ∈ Finset.Ioc B X, (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
      2 * (Real.sqrt B)⁻¹ := by
  by_cases hBX : B ≤ X
  · have hanti :
        AntitoneOn (fun x : ℝ ↦ x ^ (-(3 / 2 : ℝ)))
          (Set.Icc (B : ℝ) X) := by
      refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono ?_
      intro x hx
      exact Set.mem_Ioi.mpr <|
        (show (0 : ℝ) < B by exact_mod_cast Nat.zero_lt_of_lt hB).trans_le hx.1
    have hsum := hanti.sum_le_integral_Ico hBX
    have hindex :
        (∑ i ∈ Finset.Ico B X,
            ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) =
          ∑ n ∈ Finset.Ioc B X, (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      exact Finset.sum_bij (fun i _ ↦ i + 1)
        (fun i hi ↦ by
          simp only [Finset.mem_Ico, Finset.mem_Ioc] at hi ⊢
          omega)
        (fun i hi j hj hij ↦ by
          change i + 1 = j + 1 at hij
          omega)
        (fun n hn ↦ by
          simp only [Finset.mem_Ioc] at hn
          have hmem : n - 1 ∈ Finset.Ico B X := by
            simp only [Finset.mem_Ico]
            exact ⟨Nat.le_sub_one_of_lt hn.1,
              Nat.sub_one_lt_of_le (Nat.zero_lt_of_lt hn.1) hn.2⟩
          have heq : (fun i (_ : i ∈ Finset.Ico B X) ↦ i + 1)
              (n - 1) hmem = n := by
            change n - 1 + 1 = n
            exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
              (Nat.ne_zero_of_lt (Nat.zero_lt_of_lt hn.1)))
          exact ⟨n - 1, hmem, heq⟩)
        (fun _ _ ↦ rfl)
    rw [← hindex]
    calc
      (∑ i ∈ Finset.Ico B X,
          ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
          ≤ ∫ x in (B : ℝ)..X, x ^ (-(3 / 2 : ℝ)) := hsum
      _ = 2 * ((B : ℝ) ^ (-(1 / 2 : ℝ)) -
          (X : ℝ) ^ (-(1 / 2 : ℝ))) := by
        rw [integral_rpow]
        · ring
        · right
          constructor
          · norm_num
          · intro hzero
            rw [Set.mem_uIcc] at hzero
            have hBpos : (0 : ℝ) < B := by
              exact_mod_cast Nat.zero_lt_of_lt hB
            have hXpos : (0 : ℝ) < X := by
              exact_mod_cast (Nat.zero_lt_of_lt hB).trans_le hBX
            rcases hzero with hzero | hzero <;> linarith
      _ ≤ 2 * (B : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [mul_sub]
        have hnonneg :
            0 ≤ 2 * (X : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_nonneg (by norm_num)
            (Real.rpow_nonneg (Nat.cast_nonneg X) _)
        exact sub_le_self _ hnonneg
      _ = 2 * (Real.sqrt B)⁻¹ := by
        rw [Real.rpow_neg (Nat.cast_nonneg B), ← Real.sqrt_eq_rpow]
  · have : Finset.Ioc B X = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro n hn
      simp only [Finset.mem_Ioc] at hn
      exact hBX (hn.1.trans_le hn.2).le
    simp [this]

end PaperC
