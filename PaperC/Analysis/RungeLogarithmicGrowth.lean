import PaperC.Coding.RungeDefectApplication
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic sufficient conditions for the Runge scale

The defect-code argument is naturally parameterised by a radius of order
`log U / log R`, whereas the quantitative Runge theorem returns the integral
condition

`(128 * (2 * t) * R) ^ (4 * t) < U`.

This file records the exact logarithmic bridge.  Keeping it as a named lemma
prevents the asymptotic application from hiding a real-to-natural conversion.
-/

namespace PaperC
namespace RungeLogarithmicGrowth

/--
Exponentiating the strict logarithmic comparison gives the endpoint growth
condition required by `RungeDefectApplication`.
-/
theorem endpoint_growth_of_log
    {U R t : ℕ}
    (ht : 1 ≤ t)
    (hR : 1 ≤ R)
    (hU : 2 ≤ U)
    (hlog :
      (4 * t : ℝ) * Real.log (128 * (2 * t) * R) <
        Real.log U) :
    (128 * (2 * t) * R) ^ (4 * t) < U := by
  have htpos : 0 < t := Nat.zero_lt_of_lt ht
  have hRpos : 0 < R := Nat.zero_lt_of_lt hR
  have hbase : 0 < 128 * (2 * t) * R := by positivity
  have hpow : 0 < (128 * (2 * t) * R) ^ (4 * t) :=
    pow_pos hbase _
  have hUpos : 0 < U := by omega
  have hlogPower :
      Real.log (((128 * (2 * t) * R) ^ (4 * t) : ℕ) : ℝ) <
        Real.log (U : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlog
  have hexp := Real.exp_lt_exp.mpr hlogPower
  rw [Real.exp_log (Nat.cast_pos.mpr hpow),
    Real.exp_log (Nat.cast_pos.mpr hUpos)] at hexp
  exact_mod_cast hexp

/-- Conversely, a strict endpoint growth comparison yields its logarithmic form. -/
theorem log_endpoint_of_growth
    {U R t : ℕ}
    (ht : 1 ≤ t)
    (hR : 1 ≤ R)
    (hgrowth :
      (128 * (2 * t) * R) ^ (4 * t) < U) :
    (4 * t : ℝ) * Real.log (128 * (2 * t) * R) <
      Real.log U := by
  have htpos : 0 < t := Nat.zero_lt_of_lt ht
  have hRpos : 0 < R := Nat.zero_lt_of_lt hR
  have hbase : 0 < 128 * (2 * t) * R := by positivity
  have hpow : 0 < (128 * (2 * t) * R) ^ (4 * t) :=
    pow_pos hbase _
  have hcast :
      (((128 * (2 * t) * R) ^ (4 * t) : ℕ) : ℝ) <
        (U : ℝ) := by
    exact_mod_cast hgrowth
  have hlogs :=
    Real.log_lt_log (Nat.cast_pos.mpr hpow) hcast
  rw [Nat.cast_pow, Real.log_pow] at hlogs
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlogs

/--
A convenient capped form of the comparison.  In applications `T` is a
simple upper bound for the chosen coding radius `t`; the factor `8` leaves a
strict factor-of-two margin after taking logarithms.
-/
theorem endpoint_growth_of_log_cap
    {U R t T : ℕ}
    (ht : 1 ≤ t)
    (hR : 1 ≤ R)
    (hU : 2 ≤ U)
    (htT : t ≤ T)
    (hlog :
      (8 * t : ℝ) * Real.log (256 * T * R) ≤
        Real.log U) :
    (128 * (2 * t) * R) ^ (4 * t) < U := by
  apply endpoint_growth_of_log ht hR hU
  have hbaseNat :
      128 * (2 * t) * R ≤ 256 * T * R := by
    calc
      128 * (2 * t) * R = 256 * t * R := by ring
      _ ≤ 256 * T * R :=
        Nat.mul_le_mul_right R (Nat.mul_le_mul_left 256 htT)
  have hbasePos : 0 < (128 * (2 * t) * R : ℕ) := by
    have htpos : 0 < t := Nat.zero_lt_of_lt ht
    have hRpos : 0 < R := Nat.zero_lt_of_lt hR
    positivity
  have hlogMono :
      Real.log (128 * (2 * t) * R) ≤
        Real.log (256 * T * R) := by
    apply Real.log_le_log
    · exact_mod_cast hbasePos
    · exact_mod_cast hbaseNat
  have hlogUpos : 0 < Real.log (U : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < U by omega)
  have hscaled :
      (4 * t : ℝ) * Real.log (128 * (2 * t) * R) ≤
        (4 * t : ℝ) * Real.log (256 * T * R) :=
    mul_le_mul_of_nonneg_left hlogMono (by positivity)
  have hhalf :
      (4 * t : ℝ) * Real.log (256 * T * R) ≤
        Real.log U / 2 := by
    nlinarith
  exact hscaled.trans_lt (by nlinarith)

/--
An explicit integer radius obtained by flooring the safe logarithmic
quotient.  The auxiliary cap `T` is kept separate so that monotonicity in the
base of the Runge scale is transparent.
-/
noncomputable def cappedRadius (U R T : ℕ) : ℕ :=
  ⌊Real.log U / (8 * Real.log (256 * T * R))⌋₊

/-- The floored radius satisfies its defining weak logarithmic inequality. -/
theorem cappedRadius_log_condition
    {U R T : ℕ}
    (hU : 1 ≤ U)
    (hR : 1 ≤ R)
    (hT : 1 ≤ T) :
    (8 * cappedRadius U R T : ℝ) *
        Real.log (256 * T * R) ≤
      Real.log U := by
  have hcapNat : 1 < 256 * T * R := by
    have hRpos : 0 < R := Nat.zero_lt_of_lt hR
    have hTpos : 0 < T := Nat.zero_lt_of_lt hT
    nlinarith [show 256 ≤ 256 * T * R by
      calc
        256 = 256 * 1 * 1 := by norm_num
        _ ≤ 256 * T * R :=
          Nat.mul_le_mul
            (Nat.mul_le_mul_left 256 hT) hR]
  have hlogCapPos :
      0 < Real.log (256 * T * R : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hcapNat
  have hdenPos :
      0 < (8 : ℝ) * Real.log (256 * T * R) := by
    positivity
  have hlogUNonneg : 0 ≤ Real.log (U : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hU)
  have hquotNonneg :
      0 ≤ Real.log (U : ℝ) /
        (8 * Real.log (256 * T * R)) :=
    div_nonneg hlogUNonneg hdenPos.le
  have hfloor :
      (cappedRadius U R T : ℝ) ≤
        Real.log U / (8 * Real.log (256 * T * R)) := by
    exact Nat.floor_le hquotNonneg
  calc
    (8 * cappedRadius U R T : ℝ) *
          Real.log (256 * T * R)
        = (cappedRadius U R T : ℝ) *
            (8 * Real.log (256 * T * R)) := by ring
    _ ≤ (Real.log U / (8 * Real.log (256 * T * R))) *
          (8 * Real.log (256 * T * R)) :=
      mul_le_mul_of_nonneg_right hfloor hdenPos.le
    _ = Real.log U := by
      exact div_mul_cancel₀ _ hdenPos.ne'

/--
Whenever the floored radius is nonzero and remains below its advertised cap,
it automatically satisfies the integral endpoint growth condition.
-/
theorem endpoint_growth_cappedRadius
    {U R T : ℕ}
    (hU : 2 ≤ U)
    (hR : 1 ≤ R)
    (hT : 1 ≤ T)
    (hpositive : 1 ≤ cappedRadius U R T)
    (hbelow : cappedRadius U R T ≤ T) :
    (128 * (2 * cappedRadius U R T) * R) ^
        (4 * cappedRadius U R T) < U := by
  apply endpoint_growth_of_log_cap hpositive hR hU hbelow
  exact cappedRadius_log_condition (by omega) hR hT

/-- Logarithmic comparison satisfied by the explicit floored radius. -/
theorem cappedRadius_log_endpoint
    {U R T : ℕ}
    (hU : 2 ≤ U)
    (hR : 1 ≤ R)
    (hT : 1 ≤ T)
    (hpositive : 1 ≤ cappedRadius U R T)
    (hbelow : cappedRadius U R T ≤ T) :
    (4 * cappedRadius U R T : ℝ) *
        Real.log (128 * (2 * cappedRadius U R T) * R) <
      Real.log U := by
  apply log_endpoint_of_growth hpositive hR
  exact endpoint_growth_cappedRadius hU hR hT hpositive hbelow

/-- A logarithmic endpoint condition remains true after increasing `U`. -/
theorem log_endpoint_mono
    {U V R t : ℕ}
    (hU : 1 ≤ U)
    (hUV : U ≤ V)
    (hlog :
      (4 * t : ℝ) * Real.log (128 * (2 * t) * R) <
        Real.log U) :
    (4 * t : ℝ) * Real.log (128 * (2 * t) * R) <
      Real.log V := by
  apply hlog.trans_le
  apply Real.log_le_log
  · exact_mod_cast (show 0 < U by omega)
  · exact_mod_cast hUV

/--
Logarithmic form of the absence of short square-product words.  The remaining
size hypothesis `2 * R ≤ U` is the translation-range assumption already
present in the quantitative Runge theorem.
-/
theorem noShortRungeSquare_of_log
    {U R t : ℕ}
    (ht : 1 ≤ t)
    (hR : 1 ≤ R)
    (hU : 2 * R ≤ U)
    (hlog :
      (4 * t : ℝ) * Real.log (128 * (2 * t) * R) <
        Real.log U) :
    DefectCodeDistance.NoShortRungeSquare U R t := by
  apply RungeDefectApplication.noShortRungeSquare_of_endpoint_growth hR hU
  apply endpoint_growth_of_log ht hR
  · omega
  · exact hlog

end RungeLogarithmicGrowth
end PaperC
