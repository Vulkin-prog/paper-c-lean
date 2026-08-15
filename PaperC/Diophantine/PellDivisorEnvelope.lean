import PaperC.Diophantine.HalterKochConductorDescent
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# From the Nicolas--Robin divisor estimate to the Pell envelope

The generalized-Pell argument uses the classical divisor estimate only
through a rather specialized bound which also contains the (already
formalized) logarithmic count of units in one principal-ideal fibre.

This module separates those two layers.  `NicolasRobinDivisorLogBoundStatement`
is the direct logarithmic consequence of the explicit Nicolas--Robin maximum,
while `nicolasRobinPellEnvelope_of_divisorLogBound` proves in Lean all of the
polynomial-height substitution and absorption of the unit-orbit factor.

No assertion about quadratic fields, ideals, or Pell equations is assumed in
this module.
-/

namespace PaperC
namespace PellInput

noncomputable section

/--
A safe rational majorant for the Nicolas--Robin maximum.

The paper prints the decimal `1.5379`; its table is rounded (the value at
the maximizing integer is approximately `1.53793986`).  We therefore use
the source-implied exact majorant `2`, not the rounded decimal as an exact
rational inequality.
-/
def nicolasRobinConstant : ℝ :=
  2 * Real.log 2

/--
Source-shaped divisor-function input.

Nicolas and Robin define

`f(n) = log(d(n)) log(log n) / (log 2 log n)`

and locate its maximum at the value printed as `1.5379`.  We record the
cross-multiplied consequence with the safe exact majorant `2`, above the
harmless threshold `64`, where both logarithms are positive.
-/
/- AUDIT_BRIDGE
{
  "id": "NR83-T1-divisor-log-bound",
  "kind": "external",
  "status": "open",
  "lean_name": "PaperC.PellInput.NicolasRobinDivisorLogBoundStatement",
  "citation": {
    "authors": ["J.-L. Nicolas", "G. Robin"],
    "title": "Majorations explicites pour le nombre de diviseurs de N",
    "journal": "Canadian Mathematical Bulletin 26 (1983), no. 4, 485–492",
    "doi": "10.4153/CMB-1983-078-5",
    "locator": "definition of f and Théorème 1, p. 485"
  },
  "source_statement": {
    "verbatim": "Le maximum de f(n) est atteint en n = 6983776800, et l'on a : max f(n) = 1,5379.",
    "verbatim_is_excerpt": true,
    "displayed_formulas": {
      "divisor_function": "d(n) = ∑_{d|n} 1",
      "normalized_function": "f(n) = log(d(n)) log(log n) / (log 2 log n)",
      "lean_statement": "log(d(n)) log(log n) ≤ 2 log(2) log(n), for n ≥ 64"
    },
    "source_url": "https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D424A2915C0A748C93CF4962D0120B94/S0008439500065188a.pdf/majorations_explicites_pour_le_nombre_de_diviseurs_de_n.pdf",
    "verification": "manual_primary_source_check_required",
    "verification_note": "The printed 1.5379 is rounded (the maximizing value is approximately 1.53793986), so Lean deliberately uses the safe exact majorant 2 rather than interpreting the four-decimal display as an exact rational bound. The proposition is restricted to n ≥ 64 so log(log n) is positive. PellDivisorEnvelope proves every later polynomial-height and unit-orbit consequence."
  },
  "manuscript_locator": {
    "result": "Lemma 9.2",
    "equation": "(9.3)",
    "pages": "28–29"
  },
  "formalization_relation": "source-shaped Nicolas–Robin input only: the direct logarithmic divisor inequality above n=64. Lean derives the former specialized Pell envelope, including polynomial substitution, all finite small-m cases, the squared divisor factor, and logarithmic height absorption"
}
AUDIT_BRIDGE -/
def NicolasRobinDivisorLogBoundStatement : Prop :=
  ∀ n : ℕ, 64 ≤ n →
    Real.log (n.divisors.card : ℝ) *
        Real.log (Real.log (n : ℝ)) ≤
      nicolasRobinConstant * Real.log (n : ℝ)

theorem nicolasRobinConstant_nonneg :
    0 ≤ nicolasRobinConstant := by
  unfold nicolasRobinConstant
  positivity

/--
The function `x / log x` is monotone once `x ≥ e`.

Mathlib provides the equivalent antitonicity of `log x / x`; this is the
positive-denominator conversion needed below.
-/
theorem div_log_mono_on_exp_one
    {x y : ℝ} (hx : Real.exp 1 ≤ x) (hxy : x ≤ y) :
    x / Real.log x ≤ y / Real.log y := by
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hypos : 0 < y := hxpos.trans_le hxy
  have hlogx : 0 < Real.log x := by
    have : (1 : ℝ) ≤ Real.log x := by
      rwa [Real.le_log_iff_exp_le hxpos]
    linarith
  have hlogy : 0 < Real.log y := by
    exact hlogx.trans_le (Real.log_le_log hxpos hxy)
  have hantitone :
      Real.log y / y ≤ Real.log x / x :=
    Real.log_div_self_antitoneOn hx (hx.trans hxy) hxy
  apply (div_le_div_iff₀ hlogx hlogy).2
  have hcross :=
    (div_le_div_iff₀ hypos hxpos).1 hantitone
  simpa only [mul_comm] using hcross

/-- At the fixed threshold `64`, `log n` already lies in `[e, ∞)`. -/
theorem exp_one_le_log_nat_of_sixtyFour_le
    {n : ℕ} (hn : 64 ≤ n) :
    Real.exp 1 ≤ Real.log (n : ℝ) := by
  have hlog64 :
      Real.exp 1 ≤ Real.log (64 : ℝ) := by
    have hexp : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    have hlogTwo : (2 / 3 : ℝ) < Real.log 2 :=
      (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9
    have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      calc
        Real.log (64 : ℝ) = Real.log ((2 : ℝ) ^ 6) := by norm_num
        _ = (6 : ℕ) * Real.log 2 := Real.log_pow 2 6
        _ = 6 * Real.log 2 := by norm_num
    rw [h64]
    nlinarith
  exact hlog64.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hn))

/--
Uniform polynomial substitution for the Nicolas--Robin exponent:
if `64 ≤ m ≤ N^K`, then

`log m / log log m ≤ K log N / log log N`.
-/
theorem divisor_log_ratio_le_polynomial_ratio
    {K N m : ℕ} (hK : 0 < K) (hN : 64 ≤ N)
    (hm : 64 ≤ m) (hmN : m ≤ N ^ K) :
    Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) ≤
      (K : ℝ) * Real.log (N : ℝ) /
        Real.log (Real.log (N : ℝ)) := by
  have hNm : 0 < (m : ℝ) := by positivity
  have hNN : 0 < (N : ℝ) := by positivity
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hloglogN : 0 < Real.log (Real.log (N : ℝ)) := by
    have hlogNgt : 1 < Real.log (N : ℝ) := by
      have hlog64 :
          (1 : ℝ) < Real.log (64 : ℝ) := by
        have hlogTwo : (2 / 3 : ℝ) < Real.log 2 :=
          (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
            Real.log_two_gt_d9
        have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
          calc
            Real.log (64 : ℝ) = Real.log ((2 : ℝ) ^ 6) := by norm_num
            _ = (6 : ℕ) * Real.log 2 := Real.log_pow 2 6
            _ = 6 * Real.log 2 := by norm_num
        rw [h64]
        nlinarith
      exact hlog64.trans_le
        (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
    exact Real.log_pos hlogNgt
  have hlogm_le :
      Real.log (m : ℝ) ≤ (K : ℝ) * Real.log (N : ℝ) := by
    calc
      Real.log (m : ℝ) ≤ Real.log ((N ^ K : ℕ) : ℝ) :=
        Real.log_le_log hNm (by exact_mod_cast hmN)
      _ = (K : ℝ) * Real.log (N : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
  have hmono :=
    div_log_mono_on_exp_one
      (exp_one_le_log_nat_of_sixtyFour_le hm) hlogm_le
  have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hdenom :
      Real.log (Real.log (N : ℝ)) ≤
        Real.log ((K : ℝ) * Real.log (N : ℝ)) := by
    apply Real.log_le_log hlogN
    nlinarith
  calc
    Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))
        ≤ ((K : ℝ) * Real.log (N : ℝ)) /
            Real.log ((K : ℝ) * Real.log (N : ℝ)) :=
      hmono
    _ ≤ ((K : ℝ) * Real.log (N : ℝ)) /
          Real.log (Real.log (N : ℝ)) := by
      exact div_le_div_of_nonneg_left
        (by positivity) hloglogN hdenom

/--
The explicit unit-orbit envelope is at most a fixed multiple of `log N`
under the polynomial height bound used by generalized Pell.
-/
theorem pellUnitOrbitEnvelope_le_log
    {K N H : ℕ} (hK : 0 < K) (hN : 64 ≤ N)
    (hH : H ≤ N ^ (2 * K)) :
    (pellUnitOrbitEnvelope H : ℝ) ≤
      (48 : ℝ) * (K + 1) * Real.log (N : ℝ) := by
  have hlogN :
      1 ≤ Real.log (N : ℝ) := by
    have hlogTwo : (2 / 3 : ℝ) < Real.log 2 :=
      (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9
    have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      calc
        Real.log (64 : ℝ) = Real.log ((2 : ℝ) ^ 6) := by norm_num
        _ = (6 : ℕ) * Real.log 2 := Real.log_pow 2 6
        _ = 6 * Real.log 2 := by norm_num
    have hone64 : (1 : ℝ) ≤ Real.log (64 : ℝ) := by
      rw [h64]
      nlinarith
    exact hone64.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  by_cases hHzero : H = 0
  · subst H
    have hzero : pellUnitOrbitEnvelope 0 = 6 := by
      norm_num [pellUnitOrbitEnvelope]
    rw [hzero]
    have hKnonneg : (0 : ℝ) ≤ K := by positivity
    norm_num
    nlinarith
  have hHpos : 0 < H := Nat.pos_of_ne_zero hHzero
  have hargpos : 0 < 2 * H ^ 2 := by positivity
  have hnatLog :
      (Nat.log 2 (2 * H ^ 2) : ℝ) ≤
        Real.logb 2 (2 * H ^ 2 : ℕ) := by
    exact_mod_cast Real.natLog_le_logb (2 * H ^ 2) 2
  have hlogH :
      Real.log (H : ℝ) ≤
        (2 * K : ℕ) * Real.log (N : ℝ) := by
    calc
      Real.log (H : ℝ) ≤
          Real.log ((N ^ (2 * K) : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hH)
      _ = (2 * K : ℕ) * Real.log (N : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
  have hlogArg :
      Real.log (2 * H ^ 2 : ℕ) ≤
        Real.log 2 + (4 * K : ℕ) * Real.log (N : ℝ) := by
    calc
      Real.log (2 * H ^ 2 : ℕ) =
          Real.log 2 + Real.log ((H : ℝ) ^ 2) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
          Real.log_mul (by norm_num) (by positivity)]
      _ = Real.log 2 + 2 * Real.log (H : ℝ) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log 2 +
          2 * ((2 * K : ℕ) * Real.log (N : ℝ)) := by
        gcongr
      _ = Real.log 2 +
          (4 * K : ℕ) * Real.log (N : ℝ) := by
        push_cast
        ring
  have hlogArgNonneg : 0 ≤ Real.log (2 * H ^ 2 : ℕ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * H ^ 2 by omega))
  have hlogTwoPos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogb :
      Real.logb 2 (2 * H ^ 2 : ℕ) ≤
        2 * (Real.log 2 +
          (4 * K : ℕ) * Real.log (N : ℝ)) := by
    rw [Real.logb]
    calc
      Real.log (2 * H ^ 2 : ℕ) / Real.log 2
          ≤ 2 * Real.log (2 * H ^ 2 : ℕ) := by
        apply (div_le_iff₀ hlogTwoPos).2
        have htwoLog : (1 : ℝ) ≤ 2 * Real.log 2 := by
          nlinarith [Real.log_two_gt_d9]
        nlinarith
      _ ≤ 2 * (Real.log 2 +
          (4 * K : ℕ) * Real.log (N : ℝ)) := by
        gcongr
  have hlogTwoLe : Real.log (2 : ℝ) ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  unfold pellUnitOrbitEnvelope
  push_cast
  calc
    (2 : ℝ) * (2 * ((Nat.log 2 (2 * H ^ 2) : ℝ) + 1) + 1)
        ≤ 2 * (2 *
            (2 * (Real.log 2 +
              (4 * K : ℕ) * Real.log (N : ℝ)) + 1) + 1) := by
      gcongr
      exact hnatLog.trans hlogb
    _ ≤ (14 + 32 * (K : ℝ)) * Real.log (N : ℝ) := by
      push_cast
      nlinarith
    _ ≤ (48 : ℝ) * (K + 1) * Real.log (N : ℝ) := by
      have hKnonneg : (0 : ℝ) ≤ K := by positivity
      nlinarith

/--
For large `N`, the logarithmic factor is itself bounded by an exponential
at the `log N / log log N` scale.  The explicit coefficient is convenient
for absorbing arbitrary fixed constants without asymptotic notation.
-/
theorem loglog_le_four_log_div_loglog
    {N : ℕ} (hNloglog : 4 ≤ Real.log (Real.log (N : ℝ))) :
    Real.log (Real.log (N : ℝ)) ≤
      4 * (Real.log (N : ℝ) /
        Real.log (Real.log (N : ℝ))) := by
  have hNtwo : 2 ≤ N := by
    by_contra h
    have hNsmall : N ≤ 1 := by omega
    interval_cases N <;> norm_num at hNloglog
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let t := Real.log (Real.log (N : ℝ))
  have ht : 0 < t := by dsimp [t]; linarith
  have hadd :
      1 + t / 2 ≤ Real.exp (t / 2) := by
    simpa [add_comm] using Real.add_one_le_exp (t / 2)
  have hsquare :
      (1 + t / 2) ^ 2 ≤ (Real.exp (t / 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hadd 2
  have hquad : t ^ 2 / 4 ≤ Real.log (N : ℝ) := by
    calc
      t ^ 2 / 4 ≤ (1 + t / 2) ^ 2 := by nlinarith
      _ ≤ (Real.exp (t / 2)) ^ 2 := hsquare
      _ = Real.exp t := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      _ = Real.log (N : ℝ) := by
        dsimp [t]
        exact Real.exp_log hlogNpos
  dsimp [t] at ht hquad ⊢
  calc
    Real.log (Real.log (N : ℝ)) ≤
        (4 * Real.log (N : ℝ)) /
          Real.log (Real.log (N : ℝ)) := by
      apply (le_div_iff₀ ht).2
      nlinarith
    _ = 4 * (Real.log (N : ℝ) /
        Real.log (Real.log (N : ℝ))) := by ring

theorem constant_mul_log_le_exp_log_div_loglog
    {N : ℕ} (hNloglog : 4 ≤ Real.log (Real.log (N : ℝ)))
    (C : ℝ) (hC : 0 ≤ C) :
    C * Real.log (N : ℝ) ≤
      Real.exp
        (4 * (C + 1) *
          (Real.log (N : ℝ) /
            Real.log (Real.log (N : ℝ)))) := by
  let t := Real.log (Real.log (N : ℝ))
  let r := Real.log (N : ℝ) / t
  have ht : 0 < t := by dsimp [t]; linarith
  have hNtwo : 2 ≤ N := by
    by_contra h
    have hNsmall : N ≤ 1 := by omega
    interval_cases N <;> norm_num at hNloglog
  have hlogNpos : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have ht_four_r : t ≤ 4 * r := by
    simpa only [t, r] using
      loglog_le_four_log_div_loglog hNloglog
  have hquarter : (1 / 4 : ℝ) ≤ r := by
    have htLower : (4 : ℝ) ≤ t := by
      simpa only [t] using hNloglog
    nlinarith
  have hlogN :
      Real.log (N : ℝ) ≤ Real.exp (4 * r) := by
    calc
      Real.log (N : ℝ) = Real.exp t := by
        dsimp [t]
        exact (Real.exp_log hlogNpos).symm
      _ ≤ Real.exp (4 * r) :=
        Real.exp_le_exp.mpr ht_four_r
  have hconstant :
      C ≤ Real.exp (4 * C * r) := by
    calc
      C ≤ 1 + C := by linarith
      _ ≤ Real.exp C := by
        simpa [add_comm] using Real.add_one_le_exp C
      _ ≤ Real.exp (4 * C * r) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  calc
    C * Real.log (N : ℝ)
        ≤ Real.exp (4 * C * r) * Real.exp (4 * r) :=
      mul_le_mul hconstant hlogN
        hlogNpos.le (Real.exp_nonneg _)
    _ = Real.exp (4 * (C + 1) * r) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp
        (4 * (C + 1) *
          (Real.log (N : ℝ) /
            Real.log (Real.log (N : ℝ)))) := by
      rfl

/--
All postprocessing in the Pell divisor envelope is internal.

Thus the specialized open proposition
`NicolasRobinPellEnvelopeStatement` follows from the direct
Nicolas--Robin logarithmic divisor estimate.
-/
theorem nicolasRobinPellEnvelope_of_divisorLogBound
    (hNR : NicolasRobinDivisorLogBoundStatement) :
    NicolasRobinPellEnvelopeStatement := by
  intro K hK
  let A : ℝ := nicolasRobinConstant
  let C : ℝ := 48 * ((K : ℝ) + 1)
  let B : ℝ := 4 * (C + 1)
  let c : ℝ := 2 * A * K + B + 65536
  have hA : 0 ≤ A := nicolasRobinConstant_nonneg
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (Real.exp (Real.exp 4))
  refine ⟨c, hc, max N₀ 64, ?_⟩
  intro N hN M H hM hMN hHN
  have hNN₀ : N₀ ≤ N := (le_max_left N₀ 64).trans hN
  have hN64 : 64 ≤ N := (le_max_right N₀ 64).trans hN
  have hthreshold :
      Real.exp (Real.exp 4) < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hNN₀)
  have hlogN :
      Real.exp 4 < Real.log (N : ℝ) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos (Real.exp 4)) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hloglogN :
      4 < Real.log (Real.log (N : ℝ)) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos 4) hlogN
    simpa only [Real.log_exp] using hlogs
  have hratioPos :
      0 ≤ Real.log (N : ℝ) /
        Real.log (Real.log (N : ℝ)) := by
    positivity
  let r : ℝ :=
    Real.log (N : ℝ) /
      Real.log (Real.log (N : ℝ))
  have hr : 0 ≤ r := by simpa only [r] using hratioPos
  have hrQuarter : (1 / 4 : ℝ) ≤ r := by
    have hfour :=
      loglog_le_four_log_div_loglog hloglogN.le
    dsimp [r] at hfour ⊢
    nlinarith
  have horbit :
      (pellUnitOrbitEnvelope H : ℝ) ≤ Real.exp (B * r) := by
    have hlinear :=
      pellUnitOrbitEnvelope_le_log hK hN64 hHN
    have hexp :=
      constant_mul_log_le_exp_log_div_loglog
        hloglogN.le C hC
    simpa only [C, B, r] using hlinear.trans hexp
  let m := M.natAbs
  have hm0 : m ≠ 0 := Int.natAbs_ne_zero.mpr hM
  have hmN : m ≤ N ^ K := hMN
  have hdiv :
      (m.divisors.card : ℝ) ≤
        64 * Real.exp (A * K * r) := by
    by_cases hm64 : 64 ≤ m
    · have hloglogm :
          0 < Real.log (Real.log (m : ℝ)) := by
        have he := exp_one_le_log_nat_of_sixtyFour_le hm64
        exact Real.log_pos
          ((show (1 : ℝ) < Real.exp 1 by
            rw [Real.one_lt_exp_iff]
            norm_num) |>.trans_le he)
      have hraw := hNR m hm64
      have hlogdiv :
          Real.log (m.divisors.card : ℝ) ≤
            A * (Real.log (m : ℝ) /
              Real.log (Real.log (m : ℝ))) := by
        change
          Real.log (m.divisors.card : ℝ) *
              Real.log (Real.log (m : ℝ)) ≤
            A * Real.log (m : ℝ) at hraw
        calc
          Real.log (m.divisors.card : ℝ) ≤
              (A * Real.log (m : ℝ)) /
                Real.log (Real.log (m : ℝ)) :=
            (le_div_iff₀ hloglogm).2 hraw
          _ = A * (Real.log (m : ℝ) /
              Real.log (Real.log (m : ℝ))) := by ring
      have hratio :=
        divisor_log_ratio_le_polynomial_ratio hK hN64 hm64 hmN
      have hexponent :
          A * (Real.log (m : ℝ) /
            Real.log (Real.log (m : ℝ))) ≤ A * K * r := by
        calc
          A * (Real.log (m : ℝ) /
              Real.log (Real.log (m : ℝ))) ≤
              A * ((K : ℝ) * Real.log (N : ℝ) /
                Real.log (Real.log (N : ℝ))) :=
            mul_le_mul_of_nonneg_left hratio hA
          _ = A * K * r := by
            dsimp [r]
            ring
      have hcardPos :
          0 < (m.divisors.card : ℝ) := by
        exact_mod_cast
          (Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hm0))
      have hsmall :
          (m.divisors.card : ℝ) ≤ Real.exp (A * K * r) := by
        calc
          (m.divisors.card : ℝ) =
              Real.exp (Real.log (m.divisors.card : ℝ)) :=
            (Real.exp_log hcardPos).symm
          _ ≤ Real.exp (A * K * r) :=
            Real.exp_le_exp.mpr (hlogdiv.trans hexponent)
      nlinarith [Real.exp_pos (A * K * r)]
    · have hmle : m < 64 := Nat.lt_of_not_ge hm64
      have hcard :
          (m.divisors.card : ℝ) ≤ 64 := by
        exact_mod_cast
          (Nat.card_divisors_le_self m |>.trans hmle.le)
      have hexpOne : (1 : ℝ) ≤ Real.exp (A * K * r) := by
        rw [Real.one_le_exp_iff]
        positivity
      nlinarith
  have hconstant :
      (16384 : ℝ) ≤ Real.exp (65536 * r) := by
    calc
      (16384 : ℝ) ≤ 1 + 16384 := by norm_num
      _ ≤ Real.exp 16384 := by
        simpa [add_comm] using Real.add_one_le_exp (16384 : ℝ)
      _ ≤ Real.exp (65536 * r) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  calc
    (((4 * m.divisors.card ^ 2) *
          pellUnitOrbitEnvelope H : ℕ) : ℝ) =
        4 * (m.divisors.card : ℝ) ^ 2 *
          (pellUnitOrbitEnvelope H : ℝ) := by norm_num
    _ ≤ 4 * (64 * Real.exp (A * K * r)) ^ 2 *
          Real.exp (B * r) := by
      gcongr
    _ = 16384 *
          Real.exp ((2 * A * K + B) * r) := by
      rw [mul_pow, show (64 : ℝ) ^ 2 = 4096 by norm_num,
        pow_two, ← Real.exp_add]
      calc
        4 * (4096 * Real.exp
              (A * K * r + A * K * r)) *
            Real.exp (B * r) =
            16384 * (Real.exp
              (A * K * r + A * K * r) *
                Real.exp (B * r)) := by ring
        _ = 16384 * Real.exp
              ((A * K * r + A * K * r) + B * r) := by
          rw [← Real.exp_add]
        _ = 16384 *
              Real.exp ((2 * A * K + B) * r) := by
          congr 2
          ring
    _ ≤ Real.exp (65536 * r) *
          Real.exp ((2 * A * K + B) * r) := by
      gcongr
    _ = Real.exp (c * r) := by
      rw [← Real.exp_add]
      dsimp [c]
      congr 1
      ring
    _ = expLogLogBound c N := by
      unfold expLogLogBound
      dsimp [r]
      congr 1
      ring

/--
Lemma 9.2 from the conductor comparison and the source-shaped
Nicolas--Robin inequality.

Compared with
`generalizedPellPolynomialBox_of_quadraticOrder_nicolasRobin`, the second
hypothesis no longer bundles any polynomial substitution, unit count, or
height absorption.
-/
theorem generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound
    (hConductor : QuadraticOrderConductorFiberBoundStatement)
    (hNR : NicolasRobinDivisorLogBoundStatement) :
    GeneralizedPellPolynomialBoxStatement :=
  generalizedPellPolynomialBox_of_quadraticOrder_nicolasRobin
    hConductor
    (nicolasRobinPellEnvelope_of_divisorLogBound hNR)

/--
Lemma 9.2 from the source-shaped Nicolas--Robin inequality, with the
quadratic-order comparison supplied by its internal modulo-two construction.
-/
theorem generalizedPellPolynomialBox_of_divisorLogBound
    (hNR : NicolasRobinDivisorLogBoundStatement) :
    GeneralizedPellPolynomialBoxStatement :=
  generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound
    quadraticOrderConductorFiberBound hNR

end

end PellInput
end PaperC
