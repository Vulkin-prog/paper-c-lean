import PaperC.Algebra.RungeTruncation
import PaperC.Analysis.GeometricTail
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The analytic tail in Runge's argument

This file formalizes the exact geometric-series core of equation (3.3).
For real coefficients satisfying

`|c m| ≤ M * (2 * R)^m`

and `4 * R < U`, the series `∑ c m / U^m` converges.  Its difference
from the truncation through degree `k` is the shifted tail, and after
multiplication by `U^k` that tail is at most

`2 * M * (2 * R)^(k+1) / U`.

The final section instantiates the estimate with the coefficients constructed
in `RungeCoefficients` and relates the finite sum to the polynomial
`RungeTruncation.rungeTruncation`.
-/

namespace PaperC
namespace RungeTailEstimate

open Finset
open scoped BigOperators Topology

/-- The series term occurring after writing the Runge expansion at `1 / U`. -/
noncomputable def coefficientSeriesTerm (c : ℕ → ℝ) (U : ℝ) (m : ℕ) : ℝ :=
  c m / U ^ m

private theorem ratio_nonneg
    {R U : ℝ} (hR : 0 ≤ R) (hU : 4 * R < U) :
    0 ≤ 2 * R / U := by
  have hU0 : 0 < U := lt_of_le_of_lt (by nlinarith : 0 ≤ 4 * R) hU
  positivity

private theorem ratio_le_half
    {R U : ℝ} (hR : 0 ≤ R) (hU : 4 * R < U) :
    2 * R / U ≤ 1 / 2 := by
  have hU0 : 0 < U := lt_of_le_of_lt (by nlinarith : 0 ≤ 4 * R) hU
  rw [div_le_iff₀ hU0]
  nlinarith

/-- Pointwise comparison with the geometric majorant. -/
theorem norm_coefficientSeriesTerm_le
    {c : ℕ → ℝ} {M R U : ℝ}
    (hR : 0 ≤ R) (hU : 4 * R < U)
    (hc : ∀ m, |c m| ≤ M * (2 * R) ^ m) (m : ℕ) :
    ‖coefficientSeriesTerm c U m‖ ≤
      M * (2 * R / U) ^ m := by
  have hU0 : 0 < U := lt_of_le_of_lt (by nlinarith : 0 ≤ 4 * R) hU
  rw [Real.norm_eq_abs, coefficientSeriesTerm, abs_div, abs_pow,
    abs_of_pos hU0]
  calc
    |c m| / U ^ m ≤ (M * (2 * R) ^ m) / U ^ m := by
      exact div_le_div_of_nonneg_right (hc m) (pow_nonneg hU0.le m)
    _ = M * (2 * R / U) ^ m := by
      rw [div_pow]
      ring

/-- Absolute convergence of the Runge series under the Cauchy-type
coefficient estimate. -/
theorem summable_coefficientSeriesTerm
    {c : ℕ → ℝ} {M R U : ℝ}
    (hR : 0 ≤ R) (hU : 4 * R < U)
    (hc : ∀ m, |c m| ≤ M * (2 * R) ^ m) :
    Summable (coefficientSeriesTerm c U) := by
  have hq0 : 0 ≤ 2 * R / U := ratio_nonneg hR hU
  have hq1 : ‖2 * R / U‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact (ratio_le_half hR hU).trans_lt (by norm_num)
  have hgeom : Summable (fun m : ℕ ↦ (2 * R / U) ^ m) :=
    summable_geometric_of_norm_lt_one hq1
  exact Summable.of_norm_bounded
    (hgeom.mul_left M)
    (norm_coefficientSeriesTerm_le hR hU hc)

/-- Splitting a convergent series after the term of index `k`. -/
theorem tsum_sub_sum_range_eq_tail
    {c : ℕ → ℝ} {U : ℝ}
    (hs : Summable (coefficientSeriesTerm c U)) (k : ℕ) :
    (∑' m : ℕ, coefficientSeriesTerm c U m) -
        ∑ m ∈ Finset.range (k + 1), coefficientSeriesTerm c U m =
      ∑' n : ℕ, coefficientSeriesTerm c U (n + (k + 1)) := by
  have hsplit := hs.sum_add_tsum_nat_add (k + 1)
  linarith

/-- The unscaled tail is bounded by twice its first geometric majorant. -/
theorem abs_tail_le_two_mul
    {c : ℕ → ℝ} {M R U : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hU : 4 * R < U)
    (hc : ∀ m, |c m| ≤ M * (2 * R) ^ m) (k : ℕ) :
    |(∑' m : ℕ, coefficientSeriesTerm c U m) -
        ∑ m ∈ Finset.range (k + 1), coefficientSeriesTerm c U m| ≤
      2 * M * (2 * R / U) ^ (k + 1) := by
  let q : ℝ := 2 * R / U
  have hq0 : 0 ≤ q := ratio_nonneg hR hU
  have hqhalf : q ≤ 1 / 2 := ratio_le_half hR hU
  have hq1 : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hqhalf.trans_lt (by norm_num)
  have hgeom : Summable (fun n : ℕ ↦ q ^ n) :=
    summable_geometric_of_norm_lt_one hq1
  have hshift : Summable (fun n : ℕ ↦ q ^ (n + (k + 1))) := by
    simpa using (summable_nat_add_iff (k + 1)).2 hgeom
  have hmajor :
      Summable (fun n : ℕ ↦ M * q ^ (n + (k + 1))) :=
    hshift.mul_left M
  have hterm :
      ∀ n : ℕ,
        ‖coefficientSeriesTerm c U (n + (k + 1))‖ ≤
          M * q ^ (n + (k + 1)) := by
    intro n
    simpa [q] using
      norm_coefficientSeriesTerm_le hR hU hc (n + (k + 1))
  rw [tsum_sub_sum_range_eq_tail
    (summable_coefficientSeriesTerm hR hU hc) k]
  calc
    |∑' n : ℕ, coefficientSeriesTerm c U (n + (k + 1))| =
        ‖∑' n : ℕ, coefficientSeriesTerm c U (n + (k + 1))‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, M * q ^ (n + (k + 1)) :=
      tsum_of_norm_bounded hmajor.hasSum hterm
    _ = M * ∑' n : ℕ, q ^ (n + (k + 1)) := by
      rw [hshift.tsum_mul_left]
    _ ≤ M * (2 * q ^ (k + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (GeometricTail.tsum_pow_natAdd_le_two_mul hq0 hqhalf (k + 1)) hM
    _ = 2 * M * (2 * R / U) ^ (k + 1) := by
      dsimp [q]
      ring

/--
Equation (3.3), in its exact abstract form: after multiplication by `U^k`,
the discarded part is bounded by

`2 M (2R)^(k+1) / U`.
-/
theorem pow_mul_abs_tail_le
    {c : ℕ → ℝ} {M R U : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hU : 4 * R < U)
    (hc : ∀ m, |c m| ≤ M * (2 * R) ^ m) (k : ℕ) :
    U ^ k *
        |(∑' m : ℕ, coefficientSeriesTerm c U m) -
          ∑ m ∈ Finset.range (k + 1), coefficientSeriesTerm c U m| ≤
      2 * M * (2 * R) ^ (k + 1) / U := by
  have hU0 : 0 < U := lt_of_le_of_lt (by nlinarith : 0 ≤ 4 * R) hU
  calc
    U ^ k *
        |(∑' m : ℕ, coefficientSeriesTerm c U m) -
          ∑ m ∈ Finset.range (k + 1), coefficientSeriesTerm c U m| ≤
        U ^ k * (2 * M * (2 * R / U) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left
        (abs_tail_le_two_mul hM hR hU hc k) (pow_nonneg hU0.le k)
    _ = 2 * M * (2 * R) ^ (k + 1) / U := by
      rw [div_pow]
      field_simp [hU0.ne']
      ring

section RungeCoefficients

/--
The finite sum in the analytic estimate is exactly the polynomial truncation
from `RungeTruncation`, after restoring the factor `u^k`.
-/
theorem eval_rungeTruncation_eq_pow_mul_partialSum
    {k : ℕ} (γ : Fin (2 * k) → ℤ) {u : ℚ} (hu : u ≠ 0) :
    (RungeTruncation.rungeTruncation γ).eval u =
      u ^ k *
        ∑ m ∈ Finset.range (k + 1),
          RungeCoefficients.rungeCoefficient γ m / u ^ m := by
  classical
  rw [RungeTruncation.rungeTruncation, Polynomial.eval_finsetSum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmk : m ≤ k := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
  rw [Polynomial.eval_monomial]
  field_simp [pow_ne_zero m hu]
  calc
    RungeCoefficients.rungeCoefficient γ m * u ^ (k - m) * u ^ m =
        RungeCoefficients.rungeCoefficient γ m *
          (u ^ (k - m) * u ^ m) := by ring
    _ = RungeCoefficients.rungeCoefficient γ m * u ^ k := by
      rw [pow_sub_mul_pow u hmk]

/-- The real-valued version of the rational Runge coefficient. -/
noncomputable def realRungeCoefficient
    {d : ℕ} (γ : Fin d → ℤ) (m : ℕ) : ℝ :=
  (RungeCoefficients.rungeCoefficient γ m : ℝ)

/--
Integer-evaluation version of
`eval_rungeTruncation_eq_pow_mul_partialSum`, cast to the real series used
by the analytic tail estimate.
-/
theorem cast_eval_rungeTruncation_eq_pow_mul_realPartialSum
    {k : ℕ} (γ : Fin (2 * k) → ℤ) {u : ℤ} (hu : u ≠ 0) :
    (((RungeTruncation.rungeTruncation γ).eval (u : ℚ) : ℚ) : ℝ) =
      (u : ℝ) ^ k *
        ∑ m ∈ Finset.range (k + 1),
          coefficientSeriesTerm (realRungeCoefficient γ) (u : ℝ) m := by
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have h :=
    eval_rungeTruncation_eq_pow_mul_partialSum γ huq
  unfold coefficientSeriesTerm realRungeCoefficient
  exact_mod_cast h

/--
The coefficient estimate from (3.2), now in the uniform form required by
the tail theorem and valid for every `m`.
-/
theorem abs_realRungeCoefficient_le
    {d : ℕ} (γ : Fin d → ℤ) {R : ℚ}
    (hd : 0 < d) (hR : 0 ≤ R)
    (hγ : ∀ ν, |(γ ν : ℚ)| ≤ R) (m : ℕ) :
    |realRungeCoefficient γ m| ≤
      (2 : ℝ) ^ d * (2 * (R : ℝ)) ^ m := by
  have hq :=
    RungeCoefficients.abs_rungeCoefficient_le hd hR hγ (m := m)
  have hr :
      |realRungeCoefficient γ m| ≤
        ((2 : ℚ) ^ (m + d) * R ^ m : ℚ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hq
    simpa only [realRungeCoefficient, Rat.cast_abs, map_mul, map_pow,
      Rat.cast_ofNat] using hcast
  calc
    |realRungeCoefficient γ m| ≤
        ((2 : ℚ) ^ (m + d) * R ^ m : ℚ) := hr
    _ = (2 : ℝ) ^ d * (2 * (R : ℝ)) ^ m := by
      push_cast
      rw [pow_add, mul_pow]
      ring

/--
Direct specialization of (3.3) to the coefficients constructed in
`RungeCoefficients`; no separate analytic coefficient hypothesis remains.
-/
theorem rungeCoefficient_pow_mul_abs_tail_le
    {d : ℕ} (γ : Fin d → ℤ) {R : ℚ} {U : ℝ}
    (hd : 0 < d) (hR : 0 ≤ R)
    (hγ : ∀ ν, |(γ ν : ℚ)| ≤ R)
    (hU : 4 * (R : ℝ) < U) (k : ℕ) :
    U ^ k *
        |(∑' m : ℕ, coefficientSeriesTerm
            (realRungeCoefficient γ) U m) -
          ∑ m ∈ Finset.range (k + 1),
            coefficientSeriesTerm (realRungeCoefficient γ) U m| ≤
      2 * (2 : ℝ) ^ d * (2 * (R : ℝ)) ^ (k + 1) / U := by
  exact pow_mul_abs_tail_le
    (show 0 ≤ (2 : ℝ) ^ d by positivity)
    (by exact_mod_cast hR) hU
    (abs_realRungeCoefficient_le γ hd hR hγ) k

end RungeCoefficients

end RungeTailEstimate
end PaperC
