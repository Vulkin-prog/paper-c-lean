import PaperC.Probability.CriticalRunWindow

/-!
# Elementary powers in the critical run-length window

The upper half of `|L - log₂ N| ≤ C` gives the uniform estimate

`2^L ≤ exp(C log 2) N`.

This module also packages the three integer-division consequences used in
the channel decomposition.  They are stated for natural powers cast to
`ℝ`, so downstream counting bounds can apply them without further coercion
work.
-/

namespace PaperC
namespace CriticalChannelPowers

/--
The direct upper-power consequence of the manuscript run-length window.
Only positivity of `N` is needed; there is no additional asymptotic
threshold.
-/
theorem two_pow_runLength_le_balance_mul
    {C : ℝ} {N L : ℕ}
    (hN : 0 < N)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    (2 : ℝ) ^ L ≤
      CriticalRunWindow.balanceConstant C * (N : ℝ) := by
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hupper :
      (L : ℝ) - Real.log N / Real.log 2 ≤ C :=
    (abs_le.mp hrun).2
  have hscaled :=
    mul_le_mul_of_nonneg_right hupper hlogTwo.le
  have hquotient :
      (Real.log N / Real.log 2) * Real.log 2 =
        Real.log N := by
    field_simp
  have hexponent :
      (L : ℝ) * Real.log 2 ≤
        C * Real.log 2 + Real.log N := by
    rw [sub_mul, hquotient] at hscaled
    linarith
  have hpow :
      (2 : ℝ) ^ L =
        Real.exp ((L : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ L = (Real.exp (Real.log 2)) ^ L := by
        rw [Real.exp_log]
        norm_num
      _ = Real.exp ((L : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul (Real.log 2) L).symm
  rw [hpow]
  unfold CriticalRunWindow.balanceConstant
  calc
    Real.exp ((L : ℝ) * Real.log 2) ≤
        Real.exp (C * Real.log 2 + Real.log N) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (C * Real.log 2) *
        Real.exp (Real.log N) := by
      rw [Real.exp_add]
    _ = Real.exp (C * Real.log 2) * (N : ℝ) := by
      rw [Real.exp_log hNreal]

/-- The elementary exponent comparison `4^(L/2) ≤ 2^L`. -/
private theorem four_pow_half_le_two_pow (L : ℕ) :
    4 ^ (L / 2) ≤ 2 ^ L := by
  calc
    4 ^ (L / 2) = 2 ^ (2 * (L / 2)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    _ ≤ 2 ^ L :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The cube comparison `(2^(L/3))³ ≤ 2^L`. -/
private theorem two_pow_third_cube_le_two_pow (L : ℕ) :
    (2 ^ (L / 3)) ^ 3 ≤ 2 ^ L := by
  calc
    (2 ^ (L / 3)) ^ 3 = 2 ^ ((L / 3) * 3) := by
      rw [pow_mul]
    _ ≤ 2 ^ L :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The comparison `(4^(L/3))³ ≤ (2^L)²`. -/
private theorem four_pow_third_cube_le_two_pow_sq (L : ℕ) :
    (4 ^ (L / 3)) ^ 3 ≤ (2 ^ L) ^ 2 := by
  have hthird := two_pow_third_cube_le_two_pow L
  calc
    (4 ^ (L / 3)) ^ 3 =
        ((2 ^ (L / 3)) ^ 3) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
      ring
    _ ≤ (2 ^ L) ^ 2 :=
      Nat.pow_le_pow_left hthird 2

/-- Cast form of `4^(L/2) ≤ exp(C log 2) N`. -/
theorem four_pow_half_cast_le_balance_mul
    {C : ℝ} {N L : ℕ}
    (hN : 0 < N)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    ((4 ^ (L / 2) : ℕ) : ℝ) ≤
      CriticalRunWindow.balanceConstant C * (N : ℝ) := by
  have hcast :
      ((4 ^ (L / 2) : ℕ) : ℝ) ≤ (2 : ℝ) ^ L := by
    exact_mod_cast four_pow_half_le_two_pow L
  exact hcast.trans
    (two_pow_runLength_le_balance_mul hN hrun)

/-- Cubed cast form of `2^(L/3) ≤ exp(C log 2) N`. -/
theorem two_pow_third_cast_cube_le_balance_mul
    {C : ℝ} {N L : ℕ}
    (hN : 0 < N)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    (((2 ^ (L / 3) : ℕ) : ℝ)) ^ 3 ≤
      CriticalRunWindow.balanceConstant C * (N : ℝ) := by
  have hcast :
      (((2 ^ (L / 3) : ℕ) : ℝ)) ^ 3 ≤
        (2 : ℝ) ^ L := by
    exact_mod_cast two_pow_third_cube_le_two_pow L
  exact hcast.trans
    (two_pow_runLength_le_balance_mul hN hrun)

/--
Cubed cast form of the fourth-power scale:
`(4^(L/3))³ ≤ exp(C log 2)² N²`.
-/
theorem four_pow_third_cast_cube_le_balance_sq_mul
    {C : ℝ} {N L : ℕ}
    (hN : 0 < N)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    (((4 ^ (L / 3) : ℕ) : ℝ)) ^ 3 ≤
      (CriticalRunWindow.balanceConstant C) ^ 2 *
        (N : ℝ) ^ 2 := by
  have hcast :
      (((4 ^ (L / 3) : ℕ) : ℝ)) ^ 3 ≤
        ((2 : ℝ) ^ L) ^ 2 := by
    exact_mod_cast four_pow_third_cube_le_two_pow_sq L
  have hmain :=
    two_pow_runLength_le_balance_mul hN hrun
  have hleft : 0 ≤ (2 : ℝ) ^ L := by
    positivity
  have hright :
      0 ≤ CriticalRunWindow.balanceConstant C * (N : ℝ) := by
    exact mul_nonneg
      (CriticalRunWindow.balanceConstant_nonneg C)
      (Nat.cast_nonneg N)
  have hsquare :
      ((2 : ℝ) ^ L) ^ 2 ≤
        (CriticalRunWindow.balanceConstant C * (N : ℝ)) ^ 2 := by
    nlinarith
  calc
    (((4 ^ (L / 3) : ℕ) : ℝ)) ^ 3 ≤
        ((2 : ℝ) ^ L) ^ 2 := hcast
    _ ≤ (CriticalRunWindow.balanceConstant C * (N : ℝ)) ^ 2 :=
      hsquare
    _ = (CriticalRunWindow.balanceConstant C) ^ 2 *
        (N : ℝ) ^ 2 := by ring

end CriticalChannelPowers
end PaperC
