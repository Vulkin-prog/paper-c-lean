import PaperC.Analysis.RungeAnalyticProduct
import PaperC.Analysis.RungeScaling
import PaperC.Analysis.RungeTailEstimate

/-!
# The quantitative analytic estimate in Runge's lemma

This file assembles the three independently certified ingredients:

* the Runge coefficient series is the product of the positive square roots;
* scaling that product by `U^k` gives the nonnegative integer square root of
  `∏ (U + γᵢ)`;
* the discarded coefficient tail is bounded geometrically.

The result is equation (3.3), with the explicit (slightly coarser) numerator

`2^(2k+1) * (2R)^(k+1)`.

This remains well inside the scale asserted in the paper.
-/

namespace PaperC
namespace RungeEstimate

open Finset
open scoped BigOperators

private theorem abs_cast_shift_div_le_half
    {U R : ℕ} (hU : 4 * R < U) {γ : ℤ}
    (hγ : |γ| ≤ (R : ℤ)) :
    |(γ : ℝ) * (1 / (U : ℝ))| ≤ 1 / 2 := by
  have hU0 : (0 : ℝ) < U := by
    exact_mod_cast (show 0 < U by omega)
  have hγr : |(γ : ℝ)| ≤ (R : ℝ) := by
    exact_mod_cast hγ
  have hRU : (R : ℝ) / (U : ℝ) < 1 / 4 := by
    rw [div_lt_iff₀ hU0]
    have hcast : (4 : ℝ) * (R : ℝ) < (U : ℝ) := by
      exact_mod_cast hU
    nlinarith
  calc
    |(γ : ℝ) * (1 / (U : ℝ))| =
        |(γ : ℝ)| / (U : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / (U : ℝ)))]
      field_simp
    _ ≤ (R : ℝ) / (U : ℝ) :=
      div_le_div_of_nonneg_right hγr hU0.le
    _ ≤ 1 / 2 := by linarith

private theorem one_add_shift_div_nonneg
    {U R : ℕ} (hU : 4 * R < U) {γ : ℤ}
    (hγ : |γ| ≤ (R : ℤ)) :
    0 ≤ 1 + (γ : ℝ) / (U : ℝ) := by
  have hhalf :=
    abs_cast_shift_div_le_half hU hγ
  have hrewrite :
      (γ : ℝ) * (1 / (U : ℝ)) =
        (γ : ℝ) / (U : ℝ) := by ring
  rw [hrewrite] at hhalf
  have := neg_abs_le ((γ : ℝ) / (U : ℝ))
  linarith

private theorem coefficientSeriesTerm_eq_mul_one_div_pow
    {d : ℕ} (γ : Fin d → ℤ) (U : ℕ) (m : ℕ) :
    RungeTailEstimate.coefficientSeriesTerm
        (RungeTailEstimate.realRungeCoefficient γ) (U : ℝ) m =
      (RungeCoefficients.rungeCoefficient γ m : ℝ) *
        (1 / (U : ℝ)) ^ m := by
  simp [RungeTailEstimate.coefficientSeriesTerm,
    RungeTailEstimate.realRungeCoefficient, div_eq_mul_inv,
    inv_pow]

/--
Equation (3.3), stated over the reals.  The integer `a` is any square root
of the evaluated split product; the analytic branch selects `|a|`.
-/
theorem abs_natAbs_sub_rungeTruncation_le_real
    {k U R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (hU : 4 * R < U)
    (γ : Fin (2 * k) → ℤ)
    (hγ : ∀ i, |γ i| ≤ (R : ℤ))
    (a : ℤ)
    (hproduct :
      (∏ i, ((U : ℤ) + γ i)) = a ^ 2) :
    |((a.natAbs : ℕ) : ℝ) -
        (((RungeTruncation.rungeTruncation γ).eval (U : ℚ) : ℚ) : ℝ)| ≤
      ((2 ^ (2 * k + 1) * (2 * R) ^ (k + 1) : ℕ) : ℝ) /
        (U : ℝ) := by
  have hUone : 1 ≤ U := by omega
  have hU0z : (U : ℤ) ≠ 0 := by omega
  let s : Fin (2 * k) → ℝ :=
    fun i ↦ Real.sqrt (1 + (γ i : ℝ) / (U : ℝ))
  have hsnonneg : ∀ i, 0 ≤ s i := by
    intro i
    exact Real.sqrt_nonneg _
  have hsq :
      ∀ i, (s i) ^ 2 =
        1 + (γ i : ℝ) / (U : ℝ) := by
    intro i
    exact Real.sq_sqrt
      (one_add_shift_div_nonneg hU (hγ i))
  have hproductReal :
      (∏ i, ((U : ℝ) + (γ i : ℝ))) = (a : ℝ) ^ 2 := by
    exact_mod_cast hproduct
  have hscaled :
      RungeScaling.scaledRungeValue U s = |(a : ℝ)| :=
    RungeScaling.scaledRungeValue_eq_abs_integer
      hUone γ s hsnonneg hsq a hproductReal
  have hscaledNatAbs :
      RungeScaling.scaledRungeValue U s =
        ((a.natAbs : ℕ) : ℝ) := by
    rw [hscaled, ← Int.cast_abs, ← Int.cast_natAbs]
  have hz :
      ∀ i, |(γ i : ℝ) * (1 / (U : ℝ))| ≤ 1 / 2 :=
    fun i ↦ abs_cast_shift_div_le_half hU (hγ i)
  have hseries :=
    RungeAnalyticProduct.hasSum_rungeCoefficient_mul_pow_eq_prod_sqrt
      γ hz
  have htsum :
      (∑' m : ℕ,
          RungeTailEstimate.coefficientSeriesTerm
            (RungeTailEstimate.realRungeCoefficient γ)
            (U : ℝ) m) =
        ∏ i, s i := by
    calc
      (∑' m : ℕ,
          RungeTailEstimate.coefficientSeriesTerm
            (RungeTailEstimate.realRungeCoefficient γ)
            (U : ℝ) m) =
          ∑' m : ℕ,
            (RungeCoefficients.rungeCoefficient γ m : ℝ) *
              (1 / (U : ℝ)) ^ m := by
        apply tsum_congr
        intro m
        exact coefficientSeriesTerm_eq_mul_one_div_pow γ U m
      _ = ∏ i, Real.sqrt
          (1 + (γ i : ℝ) * (1 / (U : ℝ))) :=
        hseries.tsum_eq
      _ = ∏ i, s i := by
        apply Finset.prod_congr rfl
        intro i _
        simp only [s]
        congr 2
        ring
  have hpartial :=
    RungeTailEstimate.cast_eval_rungeTruncation_eq_pow_mul_realPartialSum
      γ hU0z
  have hpartialNat :
      (((RungeTruncation.rungeTruncation γ).eval
        (U : ℚ) : ℚ) : ℝ) =
        (U : ℝ) ^ k *
          ∑ m ∈ Finset.range (k + 1),
            RungeTailEstimate.coefficientSeriesTerm
              (RungeTailEstimate.realRungeCoefficient γ)
              (U : ℝ) m := by
    simpa only [Int.cast_natCast] using hpartial
  have htail :=
    RungeTailEstimate.rungeCoefficient_pow_mul_abs_tail_le
      γ (d := 2 * k) (R := (R : ℚ))
      (U := (U : ℝ))
      (by omega) (by positivity)
      (fun i ↦ by exact_mod_cast hγ i)
      (show 4 * (R : ℝ) < (U : ℝ) by exact_mod_cast hU) k
  have hidentity :
      |((a.natAbs : ℕ) : ℝ) -
          (((RungeTruncation.rungeTruncation γ).eval
            (U : ℚ) : ℚ) : ℝ)| =
        (U : ℝ) ^ k *
          |(∑' m : ℕ,
              RungeTailEstimate.coefficientSeriesTerm
                (RungeTailEstimate.realRungeCoefficient γ)
                (U : ℝ) m) -
            ∑ m ∈ Finset.range (k + 1),
              RungeTailEstimate.coefficientSeriesTerm
                (RungeTailEstimate.realRungeCoefficient γ)
                (U : ℝ) m| := by
    rw [← hscaledNatAbs, RungeScaling.scaledRungeValue,
      hpartialNat, htsum]
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity :
      0 ≤ (U : ℝ) ^ k)]
  rw [hidentity]
  calc
    (U : ℝ) ^ k *
          |(∑' m : ℕ,
              RungeTailEstimate.coefficientSeriesTerm
                (RungeTailEstimate.realRungeCoefficient γ)
                (U : ℝ) m) -
            ∑ m ∈ Finset.range (k + 1),
              RungeTailEstimate.coefficientSeriesTerm
                (RungeTailEstimate.realRungeCoefficient γ)
                (U : ℝ) m| ≤
        2 * (2 : ℝ) ^ (2 * k) *
          (2 * (R : ℝ)) ^ (k + 1) / (U : ℝ) :=
      htail
    _ =
        ((2 ^ (2 * k + 1) * (2 * R) ^ (k + 1) : ℕ) : ℝ) /
          (U : ℝ) := by
      push_cast
      rw [pow_succ']
      ring

/-- Rational form of equation (3.3), ready for the dyadic separation lemma. -/
theorem abs_natAbs_sub_rungeTruncation_le
    {k U R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (hU : 4 * R < U)
    (γ : Fin (2 * k) → ℤ)
    (hγ : ∀ i, |γ i| ≤ (R : ℤ))
    (a : ℤ)
    (hproduct :
      (∏ i, ((U : ℤ) + γ i)) = a ^ 2) :
    |((a.natAbs : ℕ) : ℚ) -
        (RungeTruncation.rungeTruncation γ).eval (U : ℚ)| ≤
      (2 ^ (2 * k + 1) * (2 * R) ^ (k + 1) : ℕ) /
        (U : ℚ) := by
  have hreal :=
    abs_natAbs_sub_rungeTruncation_le_real
      hk hR hU γ hγ a hproduct
  exact (Rat.cast_le (K := ℝ)).mp (by
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_natCast,
      Rat.cast_div, map_mul, map_pow, Rat.cast_ofNat] using hreal)

end RungeEstimate
end PaperC
