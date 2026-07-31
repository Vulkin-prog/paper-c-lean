import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Numerical simplifications for the Runge bound

The coefficient estimate available in the formalization is deliberately
coarser than the contour estimate in the manuscript, but it is uniform for
all coefficients.  These elementary inequalities show that the resulting
constants still fit comfortably into the claimed `(C d R)^(2d)` scale.
-/

namespace PaperC
namespace RungeNumerics

/--
For `k ≥ 1` and `R ≥ 1`, the geometric-tail numerator produced by the
coefficient bound

`|c_m| ≤ 2^(2k) (2R)^m`

is bounded by `(8R)^(2k)`.
-/
theorem tailNumerator_le
    {k R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R) :
    2 ^ (2 * k + 1) * (2 * R) ^ (k + 1) ≤
      (8 * R) ^ (2 * k) := by
  have hexp₁ : 2 * k + 1 ≤ 2 * (2 * k) := by omega
  have htwo :
      2 ^ (2 * k + 1) ≤ 4 ^ (2 * k) := by
    calc
      2 ^ (2 * k + 1) ≤ 2 ^ (2 * (2 * k)) :=
        Nat.pow_le_pow_right (by norm_num) hexp₁
      _ = 4 ^ (2 * k) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hexp₂ : k + 1 ≤ 2 * k := by omega
  have hbase : 1 ≤ 2 * R := by omega
  have hratio :
      (2 * R) ^ (k + 1) ≤ (2 * R) ^ (2 * k) :=
    Nat.pow_le_pow_right hbase hexp₂
  calc
    2 ^ (2 * k + 1) * (2 * R) ^ (k + 1) ≤
        4 ^ (2 * k) * (2 * R) ^ (2 * k) :=
      Nat.mul_le_mul htwo hratio
    _ = (8 * R) ^ (2 * k) := by
      rw [← mul_pow]
      congr 1
      omega

/--
After the dyadic gap contributes the additional factor `2^(2k)`, the whole
non-equality branch is bounded by `(16R)^(2k)`.
-/
theorem dyadicTailNumerator_le
    {k R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R) :
    2 ^ (2 * k) *
        (2 ^ (2 * k + 1) * (2 * R) ^ (k + 1)) ≤
      (16 * R) ^ (2 * k) := by
  calc
    2 ^ (2 * k) *
        (2 ^ (2 * k + 1) * (2 * R) ^ (k + 1)) ≤
        2 ^ (2 * k) * (8 * R) ^ (2 * k) :=
      Nat.mul_le_mul_left _ (tailNumerator_le hk hR)
    _ = (16 * R) ^ (2 * k) := by
      rw [← mul_pow]
      congr 1
      omega

/-- The preceding constant is certainly of the manuscript's `C d R` form. -/
theorem dyadicTailNumerator_le_paperScale
    {k R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R) :
    2 ^ (2 * k) *
        (2 ^ (2 * k + 1) * (2 * R) ^ (k + 1)) ≤
      (16 * (2 * k) * R) ^ (2 * k) := by
  refine (dyadicTailNumerator_le hk hR).trans ?_
  apply Nat.pow_le_pow_left
  have hk2 : 1 ≤ 2 * k := by omega
  have hbase :=
    Nat.mul_le_mul_right R (Nat.mul_le_mul_left 16 hk2)
  simpa [Nat.mul_assoc] using hbase

/--
The explicit height expression obtained for the auxiliary polynomial `Q`
fits the paper's `(C d R)^(2d)` scale.  Here `d = 2k`; the concrete absolute
constant is `128`.
-/
theorem one_add_auxiliaryHeightExpression_le_paperScale
    {k R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R) :
    1 +
        (2 ^ (4 * k) * (2 ^ (2 * k) * R ^ (2 * k)) +
          (2 * k + 1) *
            ((k + 1) * (16 * R) ^ (2 * k)) ^ 2) ≤
      (128 * (2 * k) * R) ^ (4 * k) := by
  let A : ℕ := (128 * k * R) ^ (4 * k)
  have hbase : 1 ≤ 8 * R := by omega
  have hexp : 2 * k ≤ 4 * k := by omega
  have hfirst :
      2 ^ (4 * k) * (2 ^ (2 * k) * R ^ (2 * k)) ≤ A := by
    calc
      2 ^ (4 * k) * (2 ^ (2 * k) * R ^ (2 * k)) =
          2 ^ (4 * k + 2 * k) * R ^ (2 * k) := by
        rw [← mul_assoc, ← pow_add]
      _ = 8 ^ (2 * k) * R ^ (2 * k) := by
        congr 1
        rw [show 4 * k + 2 * k = 3 * (2 * k) by omega]
        symm
        calc
          8 ^ (2 * k) = (2 ^ 3) ^ (2 * k) := by norm_num
          _ = 2 ^ (3 * (2 * k)) := by rw [← pow_mul]
      _ = (8 * R) ^ (2 * k) := by
        rw [mul_pow]
      _ ≤ (8 * R) ^ (4 * k) :=
        Nat.pow_le_pow_right hbase hexp
      _ ≤ A := by
        apply Nat.pow_le_pow_left
        have hk8 : 8 ≤ 128 * k := by omega
        exact Nat.mul_le_mul_right R hk8
  have hcoeff :
      (2 * k + 1) * (k + 1) ^ 2 ≤
        (8 * k) ^ (4 * k) := by
    have h₁ : 2 * k + 1 ≤ 8 * k := by omega
    have h₂ : k + 1 ≤ 8 * k := by omega
    have hcubic :
        (2 * k + 1) * (k + 1) ^ 2 ≤
          (8 * k) ^ 3 := by
      calc
        (2 * k + 1) * (k + 1) ^ 2 ≤
            (8 * k) * (8 * k) ^ 2 :=
          Nat.mul_le_mul h₁ (Nat.pow_le_pow_left h₂ 2)
        _ = (8 * k) ^ 3 := by ring
    exact hcubic.trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ 8 * k) (by omega))
  have hsecond :
      (2 * k + 1) *
          ((k + 1) * (16 * R) ^ (2 * k)) ^ 2 ≤ A := by
    calc
      (2 * k + 1) *
          ((k + 1) * (16 * R) ^ (2 * k)) ^ 2 =
          ((2 * k + 1) * (k + 1) ^ 2) *
            (16 * R) ^ (4 * k) := by
        rw [mul_pow, ← pow_mul]
        ring_nf
      _ ≤ (8 * k) ^ (4 * k) *
            (16 * R) ^ (4 * k) :=
        Nat.mul_le_mul_right _ hcoeff
      _ = A := by
        rw [← mul_pow]
        dsimp [A]
        congr 1
        ring
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact Nat.one_le_pow (4 * k) (128 * k * R) (by positivity)
  have hsum :
      1 +
          (2 ^ (4 * k) * (2 ^ (2 * k) * R ^ (2 * k)) +
            (2 * k + 1) *
              ((k + 1) * (16 * R) ^ (2 * k)) ^ 2) ≤
        3 * A := by
    omega
  calc
    1 +
        (2 ^ (4 * k) * (2 ^ (2 * k) * R ^ (2 * k)) +
          (2 * k + 1) *
            ((k + 1) * (16 * R) ^ (2 * k)) ^ 2) ≤
        3 * A := hsum
    _ ≤ 2 ^ (4 * k) * A := by
      exact Nat.mul_le_mul_right A
        (by
          have : 2 ^ 2 ≤ 2 ^ (4 * k) := by
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
          omega)
    _ = (128 * (2 * k) * R) ^ (4 * k) := by
      dsimp [A]
      rw [← mul_pow]
      congr 1
      ring

end RungeNumerics
end PaperC
