import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic

/-! # The exact incidence surplus and its optimal cutoff

Companion E.4 optimizes a family of lower bounds indexed by the reciprocal
medium-prime cutoff K. This is an optimization within that family only.
-/

namespace PaperC.V282.HarmonicIncidenceSurplus

/-- The surplus obtained from a medium interval (B/K,B]. -/
def surplus (K : ℕ) : ℚ := (harmonic K - 2) / (K + 1)

/-- Harmonic numbers are strictly increasing. -/
theorem harmonic_strictMono : StrictMono harmonic := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [harmonic_succ]
  have hp : (0 : ℚ) < (n + 1 : ℕ) := by positivity
  exact lt_add_of_pos_right _ (inv_pos.mpr hp)

/-- The discrete derivative has the exact sign of 3-H_K. -/
theorem surplus_step (K : ℕ) :
    surplus (K + 1) - surplus K =
      (3 - harmonic K) / (((K : ℚ) + 1) * (K + 2)) := by
  unfold surplus
  rw [harmonic_succ]
  push_cast
  have h1 : (K : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (K : ℚ) + 1 + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem harmonic_ten_lt_three : harmonic 10 < 3 := by
  norm_num [harmonic, Finset.sum_range_succ]

theorem harmonic_eleven_eq : harmonic 11 = 83711 / 27720 := by
  norm_num [harmonic, Finset.sum_range_succ]

theorem three_lt_harmonic_eleven : 3 < harmonic 11 := by
  rw [harmonic_eleven_eq]
  norm_num

/-- This is the rational constant printed in Theorem 7.1. -/
theorem surplus_eleven_eq : surplus 11 = 28271 / 332640 := by
  rw [surplus, harmonic_eleven_eq]
  norm_num

theorem one_twelfth_lt_surplus_eleven : (1 : ℚ) / 12 < surplus 11 := by
  rw [surplus_eleven_eq]
  norm_num

/-- Beyond eleven each successive cutoff strictly decreases the surplus. -/
theorem surplus_succ_lt {K : ℕ} (hK : 11 ≤ K) : surplus (K + 1) < surplus K := by
  have hH : 3 < harmonic K :=
    three_lt_harmonic_eleven.trans_le (harmonic_strictMono.monotone hK)
  have hd : surplus (K + 1) - surplus K < 0 := by
    rw [surplus_step]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  linarith

/-- Eleven uniquely maximizes the whole natural-number cutoff family. -/
theorem surplus_lt_eleven_of_ne {K : ℕ} (hK : K ≠ 11) : surplus K < surplus 11 := by
  by_cases hsmall : K < 11
  · interval_cases K <;> norm_num [surplus, harmonic, Finset.sum_range_succ]
  · have hdec : StrictAnti (fun n : ℕ => surplus (n + 11)) := by
      apply strictAnti_nat_of_succ_lt
      intro n
      simpa only [Nat.add_right_comm n 1 11] using
        surplus_succ_lt (K := n + 11) (by omega)
    have hlt := hdec (show 0 < K - 11 by omega)
    simpa only [Nat.zero_add, Nat.sub_add_cancel (by omega : 11 ≤ K)] using hlt

/-- Equality in the optimal bound characterizes the selected cutoff. -/
theorem surplus_le_eleven (K : ℕ) : surplus K ≤ surplus 11 := by
  by_cases hK : K = 11
  · simp [hK]
  · exact (surplus_lt_eleven_of_ne hK).le

theorem surplus_eq_eleven_iff (K : ℕ) : surplus K = surplus 11 ↔ K = 11 := by
  constructor
  · intro h
    by_contra hn
    exact (ne_of_lt (surplus_lt_eleven_of_ne hn)) h
  · rintro rfl
    rfl

end PaperC.V282.HarmonicIncidenceSurplus
