import PaperC.Analysis.RungePowerSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue

/-!
# Analytic realization of the Runge square-root series

This file connects the formal half-binomial series used in
`RungePowerSeries` with an actually convergent real series.  The convergence
statement holds on the full open unit disk.  On the closed half disk (the
range used in Lemma 3.1, where `|γ / U| ≤ 1 / 2`) we identify its sum with the
positive real square root.
-/

namespace PaperC
namespace RungeAnalyticProduct

open Finset
open scoped BigOperators

-- The coefficient-ring argument of `PowerSeries.coeff` became implicit in
-- Lean 4.32.  This local compatibility syntax keeps the public statements
-- below textually unchanged.
local macro:max "PowerSeries.coeff" R:term:arg n:term:arg : term =>
  `(@PowerSeries.coeff $R _ $n)

local macro:max "PowerSeries.C" R:term:arg : term =>
  `(@PowerSeries.C $R _)

/-- The `n`th term of the real half-binomial series at `x`. -/
noncomputable def halfBinomialTerm (x : ℝ) (n : ℕ) : ℝ :=
  (RungeCoefficients.halfChoose n : ℝ) * x ^ n

/-- The analytic sum represented formally by `(1 + X)^(1/2)`. -/
noncomputable def halfBinomialSum (x : ℝ) : ℝ :=
  ∑' n : ℕ, halfBinomialTerm x n

theorem norm_halfBinomialTerm_le (x : ℝ) (n : ℕ) :
    ‖halfBinomialTerm x n‖ ≤ |x| ^ n := by
  rw [halfBinomialTerm, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_pow]
  have hc :
      |(RungeCoefficients.halfChoose n : ℝ)| ≤ 1 := by
    exact_mod_cast RungeCoefficients.abs_halfChoose_le_one n
  simpa using
    (mul_le_mul_of_nonneg_right hc (pow_nonneg (abs_nonneg x) n))

/-- Absolute convergence of the half-binomial series on `|x| < 1`. -/
theorem summable_halfBinomialTerm {x : ℝ} (hx : |x| < 1) :
    Summable (halfBinomialTerm x) := by
  exact Summable.of_norm_bounded
    (summable_geometric_of_lt_one (abs_nonneg x) hx)
    (norm_halfBinomialTerm_le x)

/-- Absolute summability, kept explicitly for Cauchy products. -/
theorem summable_norm_halfBinomialTerm {x : ℝ} (hx : |x| < 1) :
    Summable fun n : ℕ ↦ ‖halfBinomialTerm x n‖ := by
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_halfBinomialTerm_le x)
    (summable_geometric_of_lt_one (abs_nonneg x) hx)

/-- The series has its canonical `tsum` as sum on the open unit disk. -/
theorem hasSum_halfBinomialTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (halfBinomialTerm x) (halfBinomialSum x) :=
  (summable_halfBinomialTerm hx).hasSum

private theorem antidiagonal_halfBinomialTerm
    (x : ℝ) (n : ℕ) :
    (∑ kl ∈ Finset.antidiagonal n,
        halfBinomialTerm x kl.1 * halfBinomialTerm x kl.2) =
      ((PowerSeries.coeff ℚ n
          ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2) : ℚ) : ℝ) *
        x ^ n := by
  rw [pow_two, PowerSeries.coeff_mul]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hsum : kl.1 + kl.2 = n := by
    simpa using (Finset.mem_antidiagonal.mp hkl)
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
    halfBinomialTerm, RungeCoefficients.halfChoose]
  calc
    ↑(Ring.choose (1 / 2 : ℚ) kl.1) * x ^ kl.1 *
          (↑(Ring.choose (1 / 2 : ℚ) kl.2) * x ^ kl.2) =
        ↑(Ring.choose (1 / 2 : ℚ) kl.1) *
          ↑(Ring.choose (1 / 2 : ℚ) kl.2) *
          (x ^ kl.1 * x ^ kl.2) := by ring
    _ = ↑(Ring.choose (1 / 2 : ℚ) kl.1) *
          ↑(Ring.choose (1 / 2 : ℚ) kl.2) * x ^ n := by
      rw [← pow_add, hsum]

private theorem antidiagonal_halfBinomialTerm_eq
    (x : ℝ) (n : ℕ) :
    (∑ kl ∈ Finset.antidiagonal n,
        halfBinomialTerm x kl.1 * halfBinomialTerm x kl.2) =
      PowerSeries.coeff ℝ n
        (1 + PowerSeries.C ℝ x * PowerSeries.X) := by
  rw [antidiagonal_halfBinomialTerm,
    RungePowerSeries.binomialSeries_half_sq]
  cases n with
  | zero =>
      simp
  | succ n =>
      cases n with
      | zero =>
          simp
      | succ n =>
          simp [PowerSeries.coeff_X]

/--
The square of the convergent half-binomial sum is `1 + x`.  This statement
does not yet choose between the two square roots.
-/
theorem halfBinomialSum_sq {x : ℝ} (hx : |x| < 1) :
    halfBinomialSum x ^ 2 = 1 + x := by
  have hs := summable_norm_halfBinomialTerm hx
  have hmul :=
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hs
  rw [← pow_two, ← halfBinomialSum] at hmul
  rw [hmul]
  have hcoeff :
      (fun n : ℕ ↦
          ∑ kl ∈ Finset.antidiagonal n,
            halfBinomialTerm x kl.1 * halfBinomialTerm x kl.2) =
        fun n : ℕ ↦ PowerSeries.coeff ℝ n
          (1 + PowerSeries.C ℝ x * PowerSeries.X) := by
    funext n
    exact antidiagonal_halfBinomialTerm_eq x n
  rw [hcoeff]
  have hexplicit :
      (fun n : ℕ ↦ PowerSeries.coeff ℝ n
          (1 + PowerSeries.C ℝ x * PowerSeries.X)) =
        fun n : ℕ ↦ if n = 0 then 1 else if n = 1 then x else 0 := by
    funext n
    cases n with
    | zero =>
        simp
    | succ n =>
        cases n with
        | zero =>
            simp
        | succ n =>
            simp
  rw [hexplicit]
  have hfinite :
      HasSum
        (fun n : ℕ ↦ if n = 0 then 1 else if n = 1 then x else 0)
        (1 + x) := by
    have hzero := hasSum_ite_eq 0 (1 : ℝ)
    have hone := hasSum_ite_eq 1 x
    convert hzero.add hone using 1
    · funext n
      by_cases hn0 : n = 0
      · simp [hn0]
      · by_cases hn1 : n = 1
        · simp [hn1]
        · simp [hn0, hn1]
  exact hfinite.tsum_eq

/--
Distance from the constant term, bounded by the corresponding geometric
tail.  This elementary estimate is what selects the positive square-root
branch in the numerical range used by the paper.
-/
theorem abs_halfBinomialSum_sub_one_le {x : ℝ} (hx : |x| < 1) :
    |halfBinomialSum x - 1| ≤ |x| / (1 - |x|) := by
  have hs := summable_halfBinomialTerm hx
  have hsplit :
      halfBinomialSum x =
        1 + ∑' n : ℕ, halfBinomialTerm x (n + 1) := by
    rw [halfBinomialSum, hs.tsum_eq_zero_add]
    simp [halfBinomialTerm, RungeCoefficients.halfChoose]
  rw [hsplit, add_sub_cancel_left]
  have hgeom :
      Summable fun n : ℕ ↦ |x| ^ (n + 1) := by
    have hbase := summable_geometric_of_lt_one (abs_nonneg x) hx
    simpa only [pow_succ'] using Summable.mul_left |x| hbase
  have htailNorm :
      ‖∑' n : ℕ, halfBinomialTerm x (n + 1)‖ ≤
        ∑' n : ℕ, |x| ^ (n + 1) := by
    exact tsum_of_norm_bounded hgeom.hasSum
      (fun n ↦ norm_halfBinomialTerm_le x (n + 1))
  rw [Real.norm_eq_abs] at htailNorm
  have hxnorm : ‖|x|‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg x)] using hx
  rw [geom_series_succ |x| hxnorm,
    tsum_geometric_of_lt_one (abs_nonneg x) hx] at htailNorm
  have hden : 0 < 1 - |x| := sub_pos.mpr hx
  calc
    |∑' n : ℕ, halfBinomialTerm x (n + 1)| ≤
        (1 - |x|)⁻¹ - 1 := htailNorm
    _ = |x| / (1 - |x|) := by
      field_simp
      ring

/-- On the closed half disk the analytic branch has nonnegative sign. -/
theorem halfBinomialSum_nonneg_of_abs_le_half
    {x : ℝ} (hxhalf : |x| ≤ 1 / 2) :
    0 ≤ halfBinomialSum x := by
  have hx : |x| < 1 := by linarith
  have htail := abs_halfBinomialSum_sub_one_le hx
  have hden : 0 < 1 - |x| := sub_pos.mpr hx
  have hratio : |x| / (1 - |x|) ≤ 1 := by
    rw [div_le_iff₀ hden]
    linarith
  have habs : |halfBinomialSum x - 1| ≤ 1 :=
    htail.trans hratio
  linarith [(abs_le.mp habs).1]

/-- In fact the branch is strictly positive on the closed half disk. -/
theorem halfBinomialSum_pos_of_abs_le_half
    {x : ℝ} (hxhalf : |x| ≤ 1 / 2) :
    0 < halfBinomialSum x := by
  have hx : |x| < 1 := by linarith
  have hsnonneg := halfBinomialSum_nonneg_of_abs_le_half hxhalf
  have hsquare := halfBinomialSum_sq hx
  have hxlower : -(1 / 2 : ℝ) ≤ x :=
    le_trans (by linarith : -(1 / 2 : ℝ) ≤ -|x|) (neg_abs_le x)
  nlinarith

/--
Analytic identification with the positive real square root in precisely the
uniform range needed for Runge's argument.
-/
theorem halfBinomialSum_eq_sqrt_of_abs_le_half
    {x : ℝ} (hxhalf : |x| ≤ 1 / 2) :
    halfBinomialSum x = Real.sqrt (1 + x) := by
  have hx : |x| < 1 := by linarith
  have hnonneg : 0 ≤ 1 + x := by
    have := neg_abs_le x
    linarith
  have hsnonneg :=
    (halfBinomialSum_nonneg_of_abs_le_half hxhalf)
  symm
  apply (Real.sqrt_eq_iff_eq_sq hnonneg hsnonneg).2
  exact (halfBinomialSum_sq hx).symm

private theorem continuousOn_halfBinomialSum_mul
    {x : ℝ} (hx : |x| < 1) :
    ContinuousOn (fun t : ℝ ↦ halfBinomialSum (t * x))
      (Set.Icc 0 1) := by
  unfold halfBinomialSum
  apply continuousOn_tsum
  · intro n
    exact
      (continuous_const.mul
        ((continuous_id.mul continuous_const).pow n)).continuousOn
  · exact summable_geometric_of_lt_one (abs_nonneg x) hx
  · intro n t ht
    calc
      ‖halfBinomialTerm (t * x) n‖ ≤ |t * x| ^ n :=
        norm_halfBinomialTerm_le (t * x) n
      _ ≤ |x| ^ n := by
        apply pow_le_pow_left₀ (abs_nonneg (t * x))
        rw [abs_mul, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (abs_nonneg x) ht.2

@[simp]
theorem halfBinomialSum_zero :
    halfBinomialSum 0 = 1 := by
  rw [halfBinomialSum]
  have hterm :
      halfBinomialTerm 0 =
        fun n : ℕ ↦ if n = 0 then 1 else 0 := by
    funext n
    cases n with
    | zero =>
        simp [halfBinomialTerm, RungeCoefficients.halfChoose]
    | succ n =>
        simp [halfBinomialTerm]
  rw [hterm]
  exact (hasSum_ite_eq 0 (1 : ℝ)).tsum_eq

/--
The convergent series chooses the positive square-root branch on the whole
open unit interval.  The sign is propagated from `x = 0` by continuity; a
zero is impossible because the square is `1 + x > 0`.
-/
theorem halfBinomialSum_pos {x : ℝ} (hx : |x| < 1) :
    0 < halfBinomialSum x := by
  by_contra hnot
  have hsle : halfBinomialSum x ≤ 0 := le_of_not_gt hnot
  let f : ℝ → ℝ := fun t ↦ halfBinomialSum (t * x)
  have hfcont : ContinuousOn f (Set.Icc 0 1) := by
    exact continuousOn_halfBinomialSum_mul hx
  have hzeroMem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := by
    constructor
    · simpa [f] using hsle
    · simp [f]
  rcases
      (intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hfcont)
        hzeroMem with
    ⟨t, ht, htzero⟩
  have htAbs : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have htx : |t * x| < 1 := by
    calc
      |t * x| = |t| * |x| := abs_mul t x
      _ ≤ 1 * |x| :=
        mul_le_mul_of_nonneg_right htAbs (abs_nonneg x)
      _ < 1 := by simpa using hx
  have hsquare := halfBinomialSum_sq htx
  have hpositive : 0 < 1 + t * x := by
    have := (abs_lt.mp htx).1
    linarith
  have htz : halfBinomialSum (t * x) = 0 := by
    simpa [f] using htzero
  rw [htz] at hsquare
  norm_num at hsquare
  linarith

/-- Full open-unit-disk identification with the positive real square root. -/
theorem halfBinomialSum_eq_sqrt {x : ℝ} (hx : |x| < 1) :
    halfBinomialSum x = Real.sqrt (1 + x) := by
  have hbase : 0 ≤ 1 + x := by
    have := (abs_lt.mp hx).1
    linarith
  symm
  apply
    (Real.sqrt_eq_iff_eq_sq hbase
      (halfBinomialSum_pos hx).le).2
  exact (halfBinomialSum_sq hx).symm

/--
The Runge factor with integer shift `γ`: convergence holds whenever
`|γ z| < 1`.
-/
theorem hasSum_sqrtFactorSeries
    (γ : ℤ) {z : ℝ} (hz : |(γ : ℝ) * z| < 1) :
    HasSum
      (fun n : ℕ ↦
        ((RungeCoefficients.halfChoose n : ℚ) : ℝ) *
          ((γ : ℝ) * z) ^ n)
      (halfBinomialSum ((γ : ℝ) * z)) := by
  change HasSum (halfBinomialTerm ((γ : ℝ) * z))
    (halfBinomialSum ((γ : ℝ) * z))
  exact hasSum_halfBinomialTerm hz

/--
On the full convergence disk, the Runge factor sums to the positive real
square root.
-/
theorem hasSum_sqrtFactorSeries_eq_sqrt_of_abs_lt_one
    (γ : ℤ) {z : ℝ} (hz : |(γ : ℝ) * z| < 1) :
    HasSum
      (fun n : ℕ ↦
        ((RungeCoefficients.halfChoose n : ℚ) : ℝ) *
          ((γ : ℝ) * z) ^ n)
      (Real.sqrt (1 + (γ : ℝ) * z)) := by
  rw [← halfBinomialSum_eq_sqrt hz]
  exact hasSum_sqrtFactorSeries γ hz

/--
On `|γ z| ≤ 1/2`, the convergent Runge factor is the positive square root
of `1 + γ z`.
-/
theorem hasSum_sqrtFactorSeries_eq_sqrt
    (γ : ℤ) {z : ℝ} (hz : |(γ : ℝ) * z| ≤ 1 / 2) :
    HasSum
      (fun n : ℕ ↦
        ((RungeCoefficients.halfChoose n : ℚ) : ℝ) *
          ((γ : ℝ) * z) ^ n)
      (Real.sqrt (1 + (γ : ℝ) * z)) := by
  have hunit : |(γ : ℝ) * z| < 1 := by linarith
  rw [← halfBinomialSum_eq_sqrt_of_abs_le_half hz]
  exact hasSum_sqrtFactorSeries γ hunit

/-! ## Finite products -/

/-- Real evaluation term attached to a rational formal power series. -/
noncomputable def realPowerSeriesTerm
    (f : PowerSeries ℚ) (z : ℝ) (n : ℕ) : ℝ :=
  ((PowerSeries.coeff ℚ n f : ℚ) : ℝ) * z ^ n

private theorem antidiagonal_realPowerSeriesTerm_mul
    (f g : PowerSeries ℚ) (z : ℝ) (n : ℕ) :
    (∑ kl ∈ Finset.antidiagonal n,
        realPowerSeriesTerm f z kl.1 *
          realPowerSeriesTerm g z kl.2) =
      realPowerSeriesTerm (f * g) z n := by
  rw [realPowerSeriesTerm, PowerSeries.coeff_mul]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hsum : kl.1 + kl.2 = n := by
    simpa using Finset.mem_antidiagonal.mp hkl
  rw [realPowerSeriesTerm, realPowerSeriesTerm]
  calc
    (↑((PowerSeries.coeff ℚ kl.1) f) * z ^ kl.1) *
          (↑((PowerSeries.coeff ℚ kl.2) g) * z ^ kl.2) =
        ↑((PowerSeries.coeff ℚ kl.1) f) *
          ↑((PowerSeries.coeff ℚ kl.2) g) *
          (z ^ kl.1 * z ^ kl.2) := by ring
    _ = ↑((PowerSeries.coeff ℚ kl.1) f) *
          ↑((PowerSeries.coeff ℚ kl.2) g) * z ^ n := by
      rw [← pow_add, hsum]

private theorem summable_norm_realPowerSeriesTerm_mul
    {f g : PowerSeries ℚ} {z : ℝ}
    (hf : Summable fun n : ℕ ↦ ‖realPowerSeriesTerm f z n‖)
    (hg : Summable fun n : ℕ ↦ ‖realPowerSeriesTerm g z n‖) :
    Summable fun n : ℕ ↦ ‖realPowerSeriesTerm (f * g) z n‖ := by
  have hconv :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  apply hconv.congr
  intro n
  rw [antidiagonal_realPowerSeriesTerm_mul]

private theorem hasSum_realPowerSeriesTerm_mul
    {f g : PowerSeries ℚ} {z sf sg : ℝ}
    (hf : HasSum (realPowerSeriesTerm f z) sf)
    (hg : HasSum (realPowerSeriesTerm g z) sg)
    (hfnorm : Summable fun n : ℕ ↦ ‖realPowerSeriesTerm f z n‖)
    (hgnorm : Summable fun n : ℕ ↦ ‖realPowerSeriesTerm g z n‖) :
    HasSum (realPowerSeriesTerm (f * g) z) (sf * sg) := by
  let conv : ℕ → ℝ := fun n ↦
    ∑ kl ∈ Finset.antidiagonal n,
      realPowerSeriesTerm f z kl.1 *
        realPowerSeriesTerm g z kl.2
  have hconvNorm :
      Summable fun n : ℕ ↦ ‖conv n‖ :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm hfnorm hgnorm
  have hconv : Summable conv := hconvNorm.of_norm
  have hproduct :=
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      hfnorm hgnorm
  rw [hf.tsum_eq, hg.tsum_eq] at hproduct
  have hconvSum : HasSum conv (sf * sg) := by
    rw [hproduct]
    exact hconv.hasSum
  convert hconvSum using 1
  funext n
  exact (antidiagonal_realPowerSeriesTerm_mul f g z n).symm

@[simp]
theorem realPowerSeriesTerm_sqrtFactorSeries
    (γ : ℤ) (z : ℝ) (n : ℕ) :
    realPowerSeriesTerm (RungePowerSeries.sqrtFactorSeries γ) z n =
      halfBinomialTerm ((γ : ℝ) * z) n := by
  rw [realPowerSeriesTerm,
    RungePowerSeries.coeff_sqrtFactorSeries, halfBinomialTerm]
  push_cast
  rw [mul_pow]
  ring

private theorem sqrtFactorSeriesProduct_unit_spec
    {d : ℕ} (γ : Fin d → ℤ) (z : ℝ)
    (s : Finset (Fin d))
    (hz : ∀ i ∈ s, |(γ i : ℝ) * z| < 1) :
    (Summable fun n : ℕ ↦
      ‖realPowerSeriesTerm
        (∏ i ∈ s, RungePowerSeries.sqrtFactorSeries (γ i)) z n‖) ∧
    HasSum
      (realPowerSeriesTerm
        (∏ i ∈ s, RungePowerSeries.sqrtFactorSeries (γ i)) z)
      (∏ i ∈ s, halfBinomialSum ((γ i : ℝ) * z)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      constructor
      · have heq :
          (fun n : ℕ ↦
            ‖realPowerSeriesTerm (1 : PowerSeries ℚ) z n‖) =
            fun n : ℕ ↦ if n = 0 then 1 else 0 := by
          funext n
          cases n with
          | zero =>
              simp [realPowerSeriesTerm]
          | succ n =>
              simp [realPowerSeriesTerm]
        rw [heq]
        exact (hasSum_ite_eq 0 (1 : ℝ)).summable
      · convert hasSum_ite_eq 0 (1 : ℝ) using 1
        · funext n
          cases n with
          | zero =>
              simp [realPowerSeriesTerm]
          | succ n =>
              simp [realPowerSeriesTerm]
  | @insert a s ha ih =>
      have hza : |(γ a : ℝ) * z| < 1 :=
        hz a (by simp)
      have hzrest : ∀ i ∈ s, |(γ i : ℝ) * z| < 1 := by
        intro i hi
        exact hz i (by simp [hi])
      have hrec := ih hzrest
      have hfactorNorm :
          Summable fun n : ℕ ↦
            ‖realPowerSeriesTerm
              (RungePowerSeries.sqrtFactorSeries (γ a)) z n‖ := by
        simpa only [realPowerSeriesTerm_sqrtFactorSeries] using
          summable_norm_halfBinomialTerm hza
      have hfactorSum :
          HasSum
            (realPowerSeriesTerm
              (RungePowerSeries.sqrtFactorSeries (γ a)) z)
            (halfBinomialSum ((γ a : ℝ) * z)) := by
        convert hasSum_sqrtFactorSeries (γ a) hza using 1
        funext n
        rw [realPowerSeriesTerm_sqrtFactorSeries, halfBinomialTerm]
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      constructor
      · exact summable_norm_realPowerSeriesTerm_mul
          hfactorNorm hrec.1
      · exact hasSum_realPowerSeriesTerm_mul
          hfactorSum hrec.2 hfactorNorm hrec.1

private theorem sqrtFactorSeriesProduct_spec
    {d : ℕ} (γ : Fin d → ℤ) (z : ℝ)
    (s : Finset (Fin d))
    (hz : ∀ i ∈ s, |(γ i : ℝ) * z| ≤ 1 / 2) :
    (Summable fun n : ℕ ↦
      ‖realPowerSeriesTerm
        (∏ i ∈ s, RungePowerSeries.sqrtFactorSeries (γ i)) z n‖) ∧
    HasSum
      (realPowerSeriesTerm
        (∏ i ∈ s, RungePowerSeries.sqrtFactorSeries (γ i)) z)
      (∏ i ∈ s, Real.sqrt (1 + (γ i : ℝ) * z)) := by
  classical
  have hunit :
      ∀ i ∈ s, |(γ i : ℝ) * z| < 1 := by
    intro i hi
    exact (hz i hi).trans_lt (by norm_num)
  have hspec :=
    sqrtFactorSeriesProduct_unit_spec γ z s hunit
  refine ⟨hspec.1, ?_⟩
  have hproducts :
      (∏ i ∈ s, halfBinomialSum ((γ i : ℝ) * z)) =
        ∏ i ∈ s, Real.sqrt (1 + (γ i : ℝ) * z) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact halfBinomialSum_eq_sqrt_of_abs_le_half (hz i hi)
  rw [← hproducts]
  exact hspec.2

/--
On the full polydisk `|γᵢ z| < 1`, the coefficient series converges to the
finite product of the analytic half-binomial sums.
-/
theorem hasSum_rungeCoefficient_mul_pow_eq_prod_halfBinomialSum
    {d : ℕ} (γ : Fin d → ℤ) {z : ℝ}
    (hz : ∀ i, |(γ i : ℝ) * z| < 1) :
    HasSum
      (fun m : ℕ ↦
        (RungeCoefficients.rungeCoefficient γ m : ℝ) * z ^ m)
      (∏ i, halfBinomialSum ((γ i : ℝ) * z)) := by
  classical
  have hspec :=
    sqrtFactorSeriesProduct_unit_spec γ z Finset.univ
      (fun i _ ↦ hz i)
  convert hspec.2 using 1
  funext m
  change
    (RungeCoefficients.rungeCoefficient γ m : ℝ) * z ^ m =
      realPowerSeriesTerm (RungePowerSeries.rungeProductSeries γ) z m
  rw [realPowerSeriesTerm,
    RungePowerSeries.coeff_rungeProductSeries]

/--
On the full polydisk, the Runge coefficient series sums to the finite product
of the positive real square roots.
-/
theorem hasSum_rungeCoefficient_mul_pow_eq_prod_sqrt_of_abs_lt_one
    {d : ℕ} (γ : Fin d → ℤ) {z : ℝ}
    (hz : ∀ i, |(γ i : ℝ) * z| < 1) :
    HasSum
      (fun m : ℕ ↦
        (RungeCoefficients.rungeCoefficient γ m : ℝ) * z ^ m)
      (∏ i, Real.sqrt (1 + (γ i : ℝ) * z)) := by
  have hsum :=
    hasSum_rungeCoefficient_mul_pow_eq_prod_halfBinomialSum γ hz
  have hproducts :
      (∏ i, halfBinomialSum ((γ i : ℝ) * z)) =
        ∏ i, Real.sqrt (1 + (γ i : ℝ) * z) := by
    apply Finset.prod_congr rfl
    intro i _
    exact halfBinomialSum_eq_sqrt (hz i)
  rw [← hproducts]
  exact hsum

/--
The finite Cauchy product of the convergent Runge factors has coefficient
`rungeCoefficient γ m`, and its sum is the product of the positive square
roots.  This is the analytic counterpart of
`RungePowerSeries.coeff_rungeProductSeries`.
-/
theorem hasSum_rungeCoefficient_mul_pow_eq_prod_sqrt
    {d : ℕ} (γ : Fin d → ℤ) {z : ℝ}
    (hz : ∀ i, |(γ i : ℝ) * z| ≤ 1 / 2) :
    HasSum
      (fun m : ℕ ↦
        (RungeCoefficients.rungeCoefficient γ m : ℝ) * z ^ m)
      (∏ i, Real.sqrt (1 + (γ i : ℝ) * z)) := by
  classical
  have hspec :=
    sqrtFactorSeriesProduct_spec γ z Finset.univ
      (fun i _ ↦ hz i)
  convert hspec.2 using 1
  funext m
  change
    (RungeCoefficients.rungeCoefficient γ m : ℝ) * z ^ m =
      realPowerSeriesTerm (RungePowerSeries.rungeProductSeries γ) z m
  rw [realPowerSeriesTerm,
    RungePowerSeries.coeff_rungeProductSeries]

end RungeAnalyticProduct
end PaperC
