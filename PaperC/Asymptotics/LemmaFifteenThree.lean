import PaperC.Asymptotics.HighZoneTwoDefects
import PaperC.Asymptotics.SquarefreeSmoothCritical
import PaperC.Combinatorics.DefectiveVertexIntervalBound
import PaperC.Probability.CriticalRunWindow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

set_option maxHeartbeats 1600000

/-!
# Lemma 15.3 in the critical run-length window

This module closes the analytic envelope left after the finite Pell assembly
in `HighZoneTwoDefects`.  It combines

* the PNT bound for squarefree smooth kernels;
* the internal generalized-Pell input already registered for Lemma 9.2;
* the literal window `|L-log₂ N| ≤ C`.

No new bridge is introduced.
-/

namespace PaperC
namespace LemmaFifteenThree

open Filter
open PrimeNumberTheoremInput
open SquarefreeSmoothCount
open HighZoneTwoDefects

noncomputable section

/-! ## Reusable logarithmic comparisons -/

/--
Every positive multiple of `log² N` is eventually at most the corresponding
multiple of `N`.  This is the natural-number specialization of Mathlib's
`log^2=o(id)`.
-/
theorem log_sq_le_linear_eventually
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Real.log (N : ℝ) ^ 2 ≤ ε * (N : ℝ) := by
  have hraw :
      ∀ᶠ N : ℕ in atTop,
        ‖Real.log (N : ℝ) ^ 2‖ ≤ ε * ‖(N : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      (Real.isLittleO_pow_log_id_atTop.bound hε)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hraw
  refine ⟨N₀, ?_⟩
  intro N hN
  have h := hN₀ N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at h
  exact h

/-- Eventually `log² B ≤ B`, in a convenient threshold form. -/
theorem log_sq_le_self_eventually :
    ∃ B₀ : ℕ, ∀ B ≥ B₀,
      Real.log (B : ℝ) ^ 2 ≤ (B : ℝ) := by
  obtain ⟨B₀, hB₀⟩ :=
    log_sq_le_linear_eventually (ε := 1) (by norm_num)
  exact ⟨B₀, fun B hB ↦ by simpa using hB₀ B hB⟩

/-- Eventual positivity of `loglog N`, with domination of a fixed log. -/
theorem log_const_le_loglog_eventually
    {A : ℝ} (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 < Real.log (Real.log (N : ℝ)) ∧
        Real.log A ≤ Real.log (Real.log (N : ℝ)) := by
  let T : ℝ := max (Real.exp 1) A
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp T)
  refine ⟨N₀, ?_⟩
  intro N hN
  have hthreshold : Real.exp T < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hTlog : T < Real.log (N : ℝ) := by
    have hlogs := Real.log_lt_log (Real.exp_pos T) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hexpOne :
      Real.exp 1 < Real.log (N : ℝ) :=
    (le_max_left _ _).trans_lt hTlog
  have hAlog :
      A < Real.log (N : ℝ) :=
    (le_max_right _ _).trans_lt hTlog
  have hpositive :
      0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos
      ((by
        have : (1 : ℝ) < Real.exp 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.mpr (by norm_num)
        exact this.trans hexpOne))
  exact ⟨hpositive, Real.log_le_log hA hAlog.le⟩

/--
Replacing `L` by the complete-window height `B=L+1` costs at most a factor
two at the `B/log B` scale.
-/
theorem succ_div_log_le_two_mul_div_log
    {L : ℕ} (hL : 2 ≤ L) :
    ((L + 1 : ℕ) : ℝ) /
        Real.log ((L + 1 : ℕ) : ℝ) ≤
      2 * ((L : ℝ) / Real.log (L : ℝ)) := by
  have hLpos : 0 < (L : ℝ) := by positivity
  have hlogLpos : 0 < Real.log (L : ℝ) :=
    Real.log_pos (by exact_mod_cast hL)
  have hlogSuccPos :
      0 < Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L + 1 by omega))
  have hnum :
      (((L + 1 : ℕ) : ℝ)) ≤ 2 * (L : ℝ) := by
    exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  have hlog :
      Real.log (L : ℝ) ≤
        Real.log ((L + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log hLpos
    exact_mod_cast Nat.le_succ L
  calc
    ((L + 1 : ℕ) : ℝ) /
          Real.log ((L + 1 : ℕ) : ℝ)
        ≤ (2 * (L : ℝ)) /
          Real.log ((L + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hnum hlogSuccPos.le
    _ ≤ (2 * (L : ℝ)) / Real.log (L : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hlogLpos hlog
    _ = 2 * ((L : ℝ) / Real.log (L : ℝ)) := by ring

/--
Multiplying the dyadic height by three changes
`log N/loglog N` by at most a factor two, eventually.
-/
theorem three_mul_log_div_loglog_le_two
    {N : ℕ}
    (hN : 3 ≤ N)
    (hloglogN : 0 < Real.log (Real.log (N : ℝ))) :
    Real.log ((3 * N : ℕ) : ℝ) /
        Real.log (Real.log ((3 * N : ℕ) : ℝ)) ≤
      2 * (Real.log (N : ℝ) /
        Real.log (Real.log (N : ℝ))) := by
  have hNpos : 0 < (N : ℝ) := by positivity
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogThreeLe :
      Real.log (3 : ℝ) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hN
  have hlogMul :
      Real.log ((3 * N : ℕ) : ℝ) =
        Real.log 3 + Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) hNpos.ne']
  have hlogHeight :
      Real.log (N : ℝ) ≤
        Real.log ((3 * N : ℕ) : ℝ) := by
    rw [hlogMul]
    have : 0 ≤ Real.log (3 : ℝ) :=
      Real.log_nonneg (by norm_num)
    linarith
  have hloglogHeight :
      Real.log (Real.log (N : ℝ)) ≤
        Real.log (Real.log ((3 * N : ℕ) : ℝ)) :=
    Real.log_le_log hlogNpos hlogHeight
  have hdenomHeight :
      0 < Real.log (Real.log ((3 * N : ℕ) : ℝ)) :=
    hloglogN.trans_le hloglogHeight
  calc
    Real.log ((3 * N : ℕ) : ℝ) /
          Real.log (Real.log ((3 * N : ℕ) : ℝ))
        ≤ (2 * Real.log (N : ℝ)) /
          Real.log (Real.log ((3 * N : ℕ) : ℝ)) := by
      apply div_le_div_of_nonneg_right _ hdenomHeight.le
      rw [hlogMul]
      linarith
    _ ≤ (2 * Real.log (N : ℝ)) /
          Real.log (Real.log (N : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity)
        hloglogN hloglogHeight
    _ = 2 * (Real.log (N : ℝ) /
          Real.log (Real.log (N : ℝ))) := by ring

/--
The function `log X / loglog X` is increasing on sufficiently large natural
arguments.  This is the reciprocal form of
`Real.log_div_self_antitoneOn`, applied at `log X`.
-/
theorem log_div_loglog_monotone_eventually :
    ∃ X₀ : ℕ, ∀ X Y : ℕ,
      X₀ ≤ X →
      X ≤ Y →
      Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) ≤
        Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ)) := by
  obtain ⟨X₀, hX₀⟩ :=
    exists_nat_gt (Real.exp (Real.exp 1))
  refine ⟨X₀, ?_⟩
  intro X Y hX hXY
  have hthresholdX :
      Real.exp (Real.exp 1) < (X : ℝ) :=
    hX₀.trans_le (by exact_mod_cast hX)
  have hthresholdY :
      Real.exp (Real.exp 1) < (Y : ℝ) :=
    hthresholdX.trans_le (by exact_mod_cast hXY)
  have hXpos : 0 < (X : ℝ) :=
    (Real.exp_pos _).trans hthresholdX
  have hYpos : 0 < (Y : ℝ) :=
    (Real.exp_pos _).trans hthresholdY
  have hlogX :
      Real.exp 1 < Real.log (X : ℝ) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos (Real.exp 1)) hthresholdX
    simpa only [Real.log_exp] using hlogs
  have hlogY :
      Real.exp 1 < Real.log (Y : ℝ) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos (Real.exp 1)) hthresholdY
    simpa only [Real.log_exp] using hlogs
  have hlogXY :
      Real.log (X : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hXpos (by exact_mod_cast hXY)
  have hanti :=
    Real.log_div_self_antitoneOn
      hlogX.le hlogY.le hlogXY
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    (Real.exp_pos 1).trans hlogX
  have hlogYpos : 0 < Real.log (Y : ℝ) :=
    (Real.exp_pos 1).trans hlogY
  have hloglogXpos :
      0 < Real.log (Real.log (X : ℝ)) :=
    Real.log_pos
      ((by
        have : (1 : ℝ) < Real.exp 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.mpr (by norm_num)
        exact this.trans hlogX))
  have hloglogYpos :
      0 < Real.log (Real.log (Y : ℝ)) :=
    Real.log_pos
      ((by
        have : (1 : ℝ) < Real.exp 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.mpr (by norm_num)
        exact this.trans hlogY))
  rw [div_le_div_iff₀ hlogYpos hlogXpos] at hanti
  rw [div_le_div_iff₀ hloglogXpos hloglogYpos]
  nlinarith

/-! ## The combined exponent -/

/-- A concrete coefficient for the final `L/log L` envelope. -/
noncomputable def criticalExponentConstant (c : ℝ) : ℝ :=
  2 *
    (4 * Real.log 2 + 2 +
      4 * c / CriticalRunWindow.lowerConstant)

theorem criticalExponentConstant_nonneg
    {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ criticalExponentConstant c := by
  unfold criticalExponentConstant
  have hlower :=
    CriticalRunWindow.lowerConstant_pos
  have hlogTwo : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  positivity

/--
All three logarithmic losses in the finite count fit under one explicit
multiple of `L/log L`.
-/
theorem combined_exponent_le_critical
    {c : ℝ} (hc : 0 ≤ c)
    {N L : ℕ}
    (hN : 3 ≤ N)
    (hL : 2 ≤ L)
    (hwindow :
      CriticalWindowParameters.InCriticalWindow
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1))
    (hloglogN : 0 < Real.log (Real.log (N : ℝ)))
    (hlogc₂ :
      Real.log CriticalRunWindow.upperConstant ≤
        Real.log (Real.log (N : ℝ)))
    (hlogSq :
      Real.log ((L + 1 : ℕ) : ℝ) ^ 2 ≤
        ((L + 1 : ℕ) : ℝ)) :
    (4 * Real.log 2) *
          (((L + 1 : ℕ) : ℝ) /
            Real.log ((L + 1 : ℕ) : ℝ)) +
        2 * Real.log ((L + 1 : ℕ) : ℝ) +
        c *
          (Real.log ((3 * N : ℕ) : ℝ) /
            Real.log (Real.log ((3 * N : ℕ) : ℝ))) ≤
      criticalExponentConstant c *
        ((L : ℝ) / Real.log (L : ℝ)) := by
  let B : ℕ := L + 1
  let c₁ : ℝ := CriticalRunWindow.lowerConstant
  let c₂ : ℝ := CriticalRunWindow.upperConstant
  have hc₁ : 0 < c₁ := by
    simpa only [c₁] using CriticalRunWindow.lowerConstant_pos
  have hc₁c₂ : c₁ < c₂ := by
    simpa only [c₁, c₂] using
      CriticalRunWindow.lowerConstant_lt_upperConstant
  have hBtwo : 2 ≤ B := by
    dsimp [B]
    omega
  have hlogBpos : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast hBtwo)
  have hBdivNonneg :
      0 ≤ (B : ℝ) / Real.log (B : ℝ) :=
    div_nonneg (Nat.cast_nonneg B) hlogBpos.le
  have hcompare :
      Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) ≤
        (2 / c₁) *
          ((B : ℝ) / Real.log (B : ℝ)) := by
    apply
      DefectiveVertexIntervalBound.log_div_loglog_le_two_div_lower_mul_height_div_log
        hc₁ hc₁c₂
    · simpa only [c₁, c₂, B] using hwindow
    · exact Real.log_pos
        (by
          have : (1 : ℝ) < (N : ℝ) := by
            exact_mod_cast (show 1 < N by omega)
          exact this)
    · exact hloglogN
    · exact_mod_cast hBtwo
    · simpa only [c₂] using hlogc₂
  have hthree :=
    three_mul_log_div_loglog_le_two hN hloglogN
  have hPell :
      c *
          (Real.log ((3 * N : ℕ) : ℝ) /
            Real.log (Real.log ((3 * N : ℕ) : ℝ))) ≤
        (4 * c / c₁) *
          ((B : ℝ) / Real.log (B : ℝ)) := by
    calc
      c *
            (Real.log ((3 * N : ℕ) : ℝ) /
              Real.log (Real.log ((3 * N : ℕ) : ℝ)))
          ≤ c *
            (2 *
              (Real.log (N : ℝ) /
                Real.log (Real.log (N : ℝ)))) :=
        mul_le_mul_of_nonneg_left hthree hc
      _ ≤ c *
            (2 *
              ((2 / c₁) *
                ((B : ℝ) / Real.log (B : ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcompare (by norm_num)) hc
      _ = (4 * c / c₁) *
            ((B : ℝ) / Real.log (B : ℝ)) := by ring
  have hsquare :
      2 * Real.log (B : ℝ) ≤
        2 * ((B : ℝ) / Real.log (B : ℝ)) := by
    have hrewrite :
        2 * ((B : ℝ) / Real.log (B : ℝ)) =
          (2 * (B : ℝ)) / Real.log (B : ℝ) := by ring
    rw [hrewrite, le_div_iff₀ hlogBpos]
    have hlogSqB :
        Real.log (B : ℝ) ^ 2 ≤ (B : ℝ) := by
      simpa only [B] using hlogSq
    nlinarith [hlogSqB, show
      Real.log (B : ℝ) * Real.log (B : ℝ) =
        Real.log (B : ℝ) ^ 2 by ring]
  have hBtoL :
      (B : ℝ) / Real.log (B : ℝ) ≤
        2 * ((L : ℝ) / Real.log (L : ℝ)) := by
    simpa only [B] using succ_div_log_le_two_mul_div_log hL
  have hcoefficient :
      0 ≤ 4 * Real.log 2 + 2 + 4 * c / c₁ := by
    have hlogTwo : 0 ≤ Real.log (2 : ℝ) :=
      Real.log_nonneg (by norm_num)
    positivity
  calc
    (4 * Real.log 2) *
            (((L + 1 : ℕ) : ℝ) /
              Real.log ((L + 1 : ℕ) : ℝ)) +
          2 * Real.log ((L + 1 : ℕ) : ℝ) +
          c *
            (Real.log ((3 * N : ℕ) : ℝ) /
              Real.log (Real.log ((3 * N : ℕ) : ℝ)))
        ≤ (4 * Real.log 2) *
              ((B : ℝ) / Real.log (B : ℝ)) +
            2 * ((B : ℝ) / Real.log (B : ℝ)) +
            (4 * c / c₁) *
              ((B : ℝ) / Real.log (B : ℝ)) := by
          dsimp only [B] at hsquare hPell ⊢
          linarith
    _ = (4 * Real.log 2 + 2 + 4 * c / c₁) *
          ((B : ℝ) / Real.log (B : ℝ)) := by ring
    _ ≤ (4 * Real.log 2 + 2 + 4 * c / c₁) *
          (2 * ((L : ℝ) / Real.log (L : ℝ))) :=
      mul_le_mul_of_nonneg_left hBtoL hcoefficient
    _ = criticalExponentConstant c *
          ((L : ℝ) / Real.log (L : ℝ)) := by
      dsimp [criticalExponentConstant, c₁]
      ring

/--
Range version of the combined exponent: only the top height `M` is in the
critical window, while the Pell parameter may be any `N ≤ M`.
-/
theorem combined_exponent_le_critical_range
    {c : ℝ} (hc : 0 ≤ c)
    {M N L : ℕ}
    (hM : 3 ≤ M)
    (hL : 2 ≤ L)
    (hwindow :
      CriticalWindowParameters.InCriticalWindow
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant M (L + 1))
    (hloglogM : 0 < Real.log (Real.log (M : ℝ)))
    (hlogc₂ :
      Real.log CriticalRunWindow.upperConstant ≤
        Real.log (Real.log (M : ℝ)))
    (hlogSq :
      Real.log ((L + 1 : ℕ) : ℝ) ^ 2 ≤
        ((L + 1 : ℕ) : ℝ))
    (hratio :
      Real.log ((3 * N : ℕ) : ℝ) /
          Real.log (Real.log ((3 * N : ℕ) : ℝ)) ≤
        Real.log ((3 * M : ℕ) : ℝ) /
          Real.log (Real.log ((3 * M : ℕ) : ℝ))) :
    (4 * Real.log 2) *
          (((L + 1 : ℕ) : ℝ) /
            Real.log ((L + 1 : ℕ) : ℝ)) +
        2 * Real.log ((L + 1 : ℕ) : ℝ) +
        c *
          (Real.log ((3 * N : ℕ) : ℝ) /
            Real.log (Real.log ((3 * N : ℕ) : ℝ))) ≤
      criticalExponentConstant c *
        ((L : ℝ) / Real.log (L : ℝ)) := by
  have htop :=
    combined_exponent_le_critical hc hM hL hwindow
      hloglogM hlogc₂ hlogSq
  have hscaled := mul_le_mul_of_nonneg_left hratio hc
  linarith

/--
Algebraic assembly of the finite kernel/Pell estimate once its total exponent
has been bounded.
-/
theorem assemble_twoDefectWindow_bound
    {c K : ℝ} {N L : ℕ}
    (hfinite :
      ((twoDefectWindowStarts (L + 1) N).card : ℝ) ≤
        ((squarefreeSmoothUpTo (L + 1) (3 * N)).card : ℝ) ^ 2 *
          (((L + 1 : ℕ) : ℝ)) ^ 2 *
          PellInput.expLogLogBound c (3 * N))
    (hkernel :
      ((squarefreeSmoothUpTo (L + 1) (3 * N)).card : ℝ) ≤
        Real.exp
          ((2 * Real.log 2) *
            (((L + 1 : ℕ) : ℝ) /
              Real.log ((L + 1 : ℕ) : ℝ))))
    (hexponent :
      (4 * Real.log 2) *
            (((L + 1 : ℕ) : ℝ) /
              Real.log ((L + 1 : ℕ) : ℝ)) +
          2 * Real.log ((L + 1 : ℕ) : ℝ) +
          c *
            (Real.log ((3 * N : ℕ) : ℝ) /
              Real.log (Real.log ((3 * N : ℕ) : ℝ))) ≤
        K * ((L : ℝ) / Real.log (L : ℝ))) :
    ((twoDefectWindowStarts (L + 1) N).card : ℝ) ≤
      Real.exp (K * ((L : ℝ) / Real.log (L : ℝ))) := by
  let D : ℝ :=
    ((squarefreeSmoothUpTo (L + 1) (3 * N)).card : ℝ)
  let E : ℝ :=
    (2 * Real.log 2) *
      (((L + 1 : ℕ) : ℝ) /
        Real.log ((L + 1 : ℕ) : ℝ))
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hExpNonneg : 0 ≤ Real.exp E := (Real.exp_pos E).le
  have hD : D ≤ Real.exp E := by
    simpa only [D, E] using hkernel
  have hDsq : D ^ 2 ≤ Real.exp E ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD)
      (add_nonneg hDnonneg hExpNonneg)]
  have hremainingNonneg :
      0 ≤ (((L + 1 : ℕ) : ℝ)) ^ 2 *
        PellInput.expLogLogBound c (3 * N) := by
    unfold PellInput.expLogLogBound
    positivity
  have hproduct :
      D ^ 2 * (((L + 1 : ℕ) : ℝ)) ^ 2 *
          PellInput.expLogLogBound c (3 * N) ≤
        Real.exp
          ((4 * Real.log 2) *
              (((L + 1 : ℕ) : ℝ) /
                Real.log ((L + 1 : ℕ) : ℝ)) +
            2 * Real.log ((L + 1 : ℕ) : ℝ) +
            c *
              (Real.log ((3 * N : ℕ) : ℝ) /
                Real.log (Real.log ((3 * N : ℕ) : ℝ)))) := by
    calc
      D ^ 2 * (((L + 1 : ℕ) : ℝ)) ^ 2 *
            PellInput.expLogLogBound c (3 * N)
          ≤ Real.exp E ^ 2 *
            (((L + 1 : ℕ) : ℝ)) ^ 2 *
              PellInput.expLogLogBound c (3 * N) := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_right hDsq hremainingNonneg)
      _ = Real.exp
          ((4 * Real.log 2) *
              (((L + 1 : ℕ) : ℝ) /
                Real.log ((L + 1 : ℕ) : ℝ)) +
            2 * Real.log ((L + 1 : ℕ) : ℝ) +
            c *
              (Real.log ((3 * N : ℕ) : ℝ) /
                Real.log (Real.log ((3 * N : ℕ) : ℝ)))) := by
        have hBpos :
            0 < (((L + 1 : ℕ) : ℝ)) := by positivity
        have hExpE :
            Real.exp E ^ 2 = Real.exp (2 * E) := by
          rw [← Real.exp_nat_mul]
          norm_num
        have hBexp :
            (((L + 1 : ℕ) : ℝ)) ^ 2 =
              Real.exp
                (2 * Real.log ((L + 1 : ℕ) : ℝ)) := by
          calc
            (((L + 1 : ℕ) : ℝ)) ^ 2 =
                (Real.exp
                  (Real.log ((L + 1 : ℕ) : ℝ))) ^ 2 := by
              rw [Real.exp_log hBpos]
            _ = Real.exp
                (2 * Real.log ((L + 1 : ℕ) : ℝ)) := by
              simpa using
                (Real.exp_nat_mul
                  (Real.log ((L + 1 : ℕ) : ℝ)) 2).symm
        rw [hExpE, hBexp]
        unfold PellInput.expLogLogBound
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [E]
        ring
  calc
    ((twoDefectWindowStarts (L + 1) N).card : ℝ)
        ≤ D ^ 2 * (((L + 1 : ℕ) : ℝ)) ^ 2 *
            PellInput.expLogLogBound c (3 * N) := by
      simpa only [D] using hfinite
    _ ≤ Real.exp
          ((4 * Real.log 2) *
              (((L + 1 : ℕ) : ℝ) /
                Real.log ((L + 1 : ℕ) : ℝ)) +
            2 * Real.log ((L + 1 : ℕ) : ℝ) +
            c *
              (Real.log ((3 * N : ℕ) : ℝ) /
                Real.log (Real.log ((3 * N : ℕ) : ℝ)))) :=
      hproduct
    _ ≤ Real.exp
          (K * ((L : ℝ) / Real.log (L : ℝ))) :=
      Real.exp_le_exp.mpr hexponent

/-! ## Lemma 15.3 -/

/--
Literal critical-window formulation of Lemma 15.3:

`#{x ∈ [N,2N) : mₓ ≥ 2} ≤ exp(K L / log L)`

eventually and uniformly for `|L-log₂ N| ≤ C`.

The only hypotheses are the already registered external PNT statement and
the already registered internal generalized-Pell statement.
-/
theorem lemma_fifteen_three
    {C : ℝ} (hC : 0 ≤ C)
    (hpnt : PrimeNumberTheoremStatement)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
        CriticalRunWindow.InRunLengthWindow C N L →
        ((twoDefectWindowStarts (L + 1) N).card : ℝ) ≤
          Real.exp
            (K * ((L : ℝ) / Real.log (L : ℝ))) := by
  obtain ⟨c, hc, Npell, hpellFinite⟩ :=
    generalizedPell_implies_twoDefectWindow_bound hPell
  obtain ⟨Bpnt, hpntKernel⟩ :=
    SquarefreeSmoothCritical.primeNumberTheorem_implies_squarefreeSmooth_bound
      hpnt
  obtain ⟨Blog, hlogSelf⟩ :=
    log_sq_le_self_eventually
  let c₁ : ℝ := CriticalRunWindow.lowerConstant
  let c₂ : ℝ := CriticalRunWindow.upperConstant
  have hc₁ : 0 < c₁ := by
    simpa only [c₁] using CriticalRunWindow.lowerConstant_pos
  have hc₁c₂ : c₁ < c₂ := by
    simpa only [c₁, c₂] using
      CriticalRunWindow.lowerConstant_lt_upperConstant
  have hc₂ : 0 < c₂ := hc₁.trans hc₁c₂
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hNadm⟩ :=
    CriticalWeightedDefect.admissible_eventually hc₁ hc₁c₂
  obtain ⟨Nheight, hNheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := c₂) hc₁ (max 3 (max Bpnt Blog))
  obtain ⟨Nlogs, hNlogs⟩ :=
    log_const_le_loglog_eventually hc₂
  have hε : 0 < 1 / (4 * c₂ ^ 2) := by positivity
  obtain ⟨Nsquare, hNsquare⟩ :=
    log_sq_le_linear_eventually hε
  let N₀ : ℕ :=
    max Nwindow
      (max Nadm
        (max Nheight
          (max Nlogs
            (max Nsquare (max Npell 4)))))
  refine ⟨criticalExponentConstant c,
    criticalExponentConstant_nonneg hc, N₀, ?_⟩
  intro N hN L hrun
  have hNwindowN : Nwindow ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNadmN : Nadm ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNheightN : Nheight ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNlogsN : Nlogs ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNsquareN : Nsquare ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNpellN : Npell ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNfour : 4 ≤ N := by
    dsimp [N₀] at hN
    omega
  have hcritical :
      CriticalWindowParameters.InCriticalWindow
        c₁ c₂ N (L + 1) :=
    (hNwindow N hNwindowN L hrun).1
  have hadm :
      CriticalWeightedDefect.Admissible c₁ c₂ N (L + 1) :=
    hNadm N hNadmN (L + 1) hcritical
  have hheight :
      max 3 (max Bpnt Blog) ≤ L + 1 :=
    hNheight N hNheightN (L + 1) hadm
  have hBthree : 3 ≤ L + 1 :=
    (le_max_left 3 (max Bpnt Blog)).trans hheight
  have hBpnt : Bpnt ≤ L + 1 :=
    (le_max_left Bpnt Blog).trans
      ((le_max_right 3 (max Bpnt Blog)).trans hheight)
  have hBlog : Blog ≤ L + 1 :=
    (le_max_right Bpnt Blog).trans
      ((le_max_right 3 (max Bpnt Blog)).trans hheight)
  have hLtwo : 2 ≤ L := by omega
  have hNthree : 3 ≤ N := hNfour.trans' (by norm_num)
  obtain ⟨hloglogN, hlogc₂⟩ :=
    hNlogs N hNlogsN
  have hlogSqB :
      Real.log ((L + 1 : ℕ) : ℝ) ^ 2 ≤
        ((L + 1 : ℕ) : ℝ) :=
    hlogSelf (L + 1) hBlog
  have hBN : L + 1 ≤ N := by
    have hupper :
        (((L + 1 : ℕ) : ℝ)) ≤
          c₂ * Real.log (N : ℝ) := hcritical.2.2.2
    have hscale :
        2 * c₂ * Real.log (N : ℝ) ≤ (N : ℝ) :=
      hadm.2.2.2.1
    have : (((L + 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by
      nlinarith
    exact_mod_cast this
  have hhigh : (L + 1) ^ 2 + 2 < N := by
    have hlogSqN :=
      hNsquare N hNsquareN
    have hlogNpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hBcastNonneg :
        0 ≤ (((L + 1 : ℕ) : ℝ)) := by positivity
    have hc₂logNonneg :
        0 ≤ c₂ * Real.log (N : ℝ) :=
      mul_nonneg hc₂.le hlogNpos.le
    have hBupper :
        (((L + 1 : ℕ) : ℝ)) ≤
          c₂ * Real.log (N : ℝ) :=
      hcritical.2.2.2
    have hBsquare :
        (((L + 1 : ℕ) : ℝ)) ^ 2 ≤
          (c₂ * Real.log (N : ℝ)) ^ 2 := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hBupper)
        (add_nonneg hBcastNonneg hc₂logNonneg)]
    have hquarter :
        (((L + 1 : ℕ) : ℝ)) ^ 2 ≤
          (N : ℝ) / 4 := by
      calc
        (((L + 1 : ℕ) : ℝ)) ^ 2
            ≤ (c₂ * Real.log (N : ℝ)) ^ 2 := hBsquare
        _ = c₂ ^ 2 * Real.log (N : ℝ) ^ 2 := by ring
        _ ≤ c₂ ^ 2 * ((1 / (4 * c₂ ^ 2)) * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogSqN (sq_nonneg c₂)
        _ = (N : ℝ) / 4 := by
          field_simp [hc₂.ne']
          ring
    have hreal :
        ((((L + 1) ^ 2 + 2 : ℕ) : ℝ)) < (N : ℝ) := by
      have hquarter' :
          ((L : ℝ) + 1) ^ 2 ≤ (N : ℝ) / 4 := by
        simpa only [Nat.cast_add, Nat.cast_one] using hquarter
      norm_num only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
      nlinarith [hquarter',
        show (4 : ℝ) ≤ (N : ℝ) by exact_mod_cast hNfour]
    exact_mod_cast hreal
  have hfinite :=
    hpellFinite (L + 1) N
      (hNpellN.trans (Nat.le_mul_of_pos_left N (by norm_num)))
      (by omega) hBN hhigh
  have hkernel :=
    hpntKernel (L + 1) hBpnt (3 * N)
  let D : ℝ :=
    ((squarefreeSmoothUpTo (L + 1) (3 * N)).card : ℝ)
  let E : ℝ :=
    (2 * Real.log 2) *
      (((L + 1 : ℕ) : ℝ) /
        Real.log ((L + 1 : ℕ) : ℝ))
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hExpNonneg : 0 ≤ Real.exp E := (Real.exp_pos E).le
  have hD : D ≤ Real.exp E := by
    simpa only [D, E] using hkernel
  have hDsq : D ^ 2 ≤ Real.exp E ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD)
      (add_nonneg hDnonneg hExpNonneg)]
  have hremainingNonneg :
      0 ≤ (((L + 1 : ℕ) : ℝ)) ^ 2 *
        PellInput.expLogLogBound c (3 * N) := by
    unfold PellInput.expLogLogBound
    positivity
  have hproduct :
      D ^ 2 * (((L + 1 : ℕ) : ℝ)) ^ 2 *
          PellInput.expLogLogBound c (3 * N) ≤
        Real.exp
          ((4 * Real.log 2) *
              (((L + 1 : ℕ) : ℝ) /
                Real.log ((L + 1 : ℕ) : ℝ)) +
            2 * Real.log ((L + 1 : ℕ) : ℝ) +
            c *
              (Real.log ((3 * N : ℕ) : ℝ) /
                Real.log (Real.log ((3 * N : ℕ) : ℝ)))) := by
    calc
      D ^ 2 * (((L + 1 : ℕ) : ℝ)) ^ 2 *
            PellInput.expLogLogBound c (3 * N)
          ≤ Real.exp E ^ 2 *
            (((L + 1 : ℕ) : ℝ)) ^ 2 *
              PellInput.expLogLogBound c (3 * N) :=
        by
          simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_right hDsq hremainingNonneg)
      _ = Real.exp
          ((4 * Real.log 2) *
              (((L + 1 : ℕ) : ℝ) /
                Real.log ((L + 1 : ℕ) : ℝ)) +
            2 * Real.log ((L + 1 : ℕ) : ℝ) +
            c *
              (Real.log ((3 * N : ℕ) : ℝ) /
                Real.log (Real.log ((3 * N : ℕ) : ℝ)))) := by
        have hBpos :
            0 < (((L + 1 : ℕ) : ℝ)) := by positivity
        have hExpE :
            Real.exp E ^ 2 = Real.exp (2 * E) := by
          rw [← Real.exp_nat_mul]
          norm_num
        have hBexp :
            (((L + 1 : ℕ) : ℝ)) ^ 2 =
              Real.exp
                (2 * Real.log ((L + 1 : ℕ) : ℝ)) := by
          calc
            (((L + 1 : ℕ) : ℝ)) ^ 2 =
                (Real.exp
                  (Real.log ((L + 1 : ℕ) : ℝ))) ^ 2 := by
              rw [Real.exp_log hBpos]
            _ = Real.exp
                (2 * Real.log ((L + 1 : ℕ) : ℝ)) := by
              simpa using
                (Real.exp_nat_mul
                  (Real.log ((L + 1 : ℕ) : ℝ)) 2).symm
        rw [hExpE, hBexp]
        unfold PellInput.expLogLogBound
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [E]
        ring
  have hexponent :=
    combined_exponent_le_critical hc hNthree hLtwo
      (by simpa only [c₁, c₂] using hcritical)
      hloglogN
      (by simpa only [c₂] using hlogc₂)
      hlogSqB
  calc
    ((twoDefectWindowStarts (L + 1) N).card : ℝ)
        ≤ D ^ 2 * (((L + 1 : ℕ) : ℝ)) ^ 2 *
            PellInput.expLogLogBound c (3 * N) := by
      simpa only [D] using hfinite
    _ ≤ Real.exp
          ((4 * Real.log 2) *
              (((L + 1 : ℕ) : ℝ) /
                Real.log ((L + 1 : ℕ) : ℝ)) +
            2 * Real.log ((L + 1 : ℕ) : ℝ) +
            c *
              (Real.log ((3 * N : ℕ) : ℝ) /
                Real.log (Real.log ((3 * N : ℕ) : ℝ)))) :=
      hproduct
    _ ≤ Real.exp
          (criticalExponentConstant c *
            ((L : ℝ) / Real.log (L : ℝ))) :=
      Real.exp_le_exp.mpr hexponent

/--
Exact height-range form of Lemma 15.3 from the manuscript.

Here `L` is critical for the top height `M`, and the same constant and
threshold work simultaneously for every dyadic height
`2 L² ≤ N ≤ M`.
-/
theorem lemma_fifteen_three_uniform_height_range
    {C : ℝ} (hC : 0 ≤ C)
    (hpnt : PrimeNumberTheoremStatement)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L,
        CriticalRunWindow.InRunLengthWindow C M L →
        ∀ N : ℕ, 2 * L ^ 2 ≤ N → N ≤ M →
          ((twoDefectWindowStarts (L + 1) N).card : ℝ) ≤
            Real.exp
              (K * ((L : ℝ) / Real.log (L : ℝ))) := by
  obtain ⟨c, hc, Npell, hpellFinite⟩ :=
    generalizedPell_implies_twoDefectWindow_bound hPell
  obtain ⟨Bpnt, hpntKernel⟩ :=
    SquarefreeSmoothCritical.primeNumberTheorem_implies_squarefreeSmooth_bound
      hpnt
  obtain ⟨Blog, hlogSelf⟩ :=
    log_sq_le_self_eventually
  obtain ⟨Xratio, hratioMono⟩ :=
    log_div_loglog_monotone_eventually
  let c₁ : ℝ := CriticalRunWindow.lowerConstant
  let c₂ : ℝ := CriticalRunWindow.upperConstant
  have hc₁ : 0 < c₁ := by
    simpa only [c₁] using CriticalRunWindow.lowerConstant_pos
  have hc₁c₂ : c₁ < c₂ := by
    simpa only [c₁, c₂] using
      CriticalRunWindow.lowerConstant_lt_upperConstant
  have hc₂ : 0 < c₂ := hc₁.trans hc₁c₂
  obtain ⟨Mwindow, hMwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Madm, hMadm⟩ :=
    CriticalWeightedDefect.admissible_eventually hc₁ hc₁c₂
  let Hmin : ℕ :=
    max 5 (max Bpnt (max Blog (max Npell Xratio)))
  obtain ⟨Mheight, hMheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := c₂) hc₁ Hmin
  obtain ⟨Mlogs, hMlogs⟩ :=
    log_const_le_loglog_eventually hc₂
  let M₀ : ℕ :=
    max Mwindow
      (max Madm (max Mheight (max Mlogs 4)))
  refine ⟨criticalExponentConstant c,
    criticalExponentConstant_nonneg hc, M₀, ?_⟩
  intro M hM L hrun N hNlower hNupper
  have hMwindowM : Mwindow ≤ M := by
    dsimp [M₀] at hM
    omega
  have hMadmM : Madm ≤ M := by
    dsimp [M₀] at hM
    omega
  have hMheightM : Mheight ≤ M := by
    dsimp [M₀] at hM
    omega
  have hMlogsM : Mlogs ≤ M := by
    dsimp [M₀] at hM
    omega
  have hMfour : 4 ≤ M := by
    dsimp [M₀] at hM
    omega
  have hcritical :
      CriticalWindowParameters.InCriticalWindow
        c₁ c₂ M (L + 1) :=
    (hMwindow M hMwindowM L hrun).1
  have hadm :
      CriticalWeightedDefect.Admissible c₁ c₂ M (L + 1) :=
    hMadm M hMadmM (L + 1) hcritical
  have hheight :
      Hmin ≤ L + 1 :=
    hMheight M hMheightM (L + 1) hadm
  have hLfive : 5 ≤ L + 1 :=
    (le_max_left 5
      (max Bpnt (max Blog (max Npell Xratio)))).trans
      (by simpa only [Hmin] using hheight)
  have hBpnt : Bpnt ≤ L + 1 := by
    have :
        Bpnt ≤ max Bpnt (max Blog (max Npell Xratio)) :=
      le_max_left _ _
    exact this.trans
      ((le_max_right 5
        (max Bpnt (max Blog (max Npell Xratio)))).trans
        (by simpa only [Hmin] using hheight))
  have hBlog : Blog ≤ L + 1 := by
    have :
        Blog ≤ max Blog (max Npell Xratio) :=
      le_max_left _ _
    exact this.trans
      ((le_max_right Bpnt (max Blog (max Npell Xratio))).trans
        ((le_max_right 5
          (max Bpnt (max Blog (max Npell Xratio)))).trans
          (by simpa only [Hmin] using hheight)))
  have hNpellHeight : Npell ≤ L + 1 := by
    have :
        Npell ≤ max Npell Xratio :=
      le_max_left _ _
    exact this.trans
      ((le_max_right Blog (max Npell Xratio)).trans
        ((le_max_right Bpnt (max Blog (max Npell Xratio))).trans
          ((le_max_right 5
            (max Bpnt (max Blog (max Npell Xratio)))).trans
            (by simpa only [Hmin] using hheight))))
  have hXratioHeight : Xratio ≤ L + 1 := by
    have :
        Xratio ≤ max Npell Xratio :=
      le_max_right _ _
    exact this.trans
      ((le_max_right Blog (max Npell Xratio)).trans
        ((le_max_right Bpnt (max Blog (max Npell Xratio))).trans
          ((le_max_right 5
            (max Bpnt (max Blog (max Npell Xratio)))).trans
            (by simpa only [Hmin] using hheight))))
  have hLfour : 4 ≤ L := by omega
  have hLtwo : 2 ≤ L := by omega
  have hNtwo : 2 ≤ N := by
    have : 2 * 4 ^ 2 ≤ N := by
      exact (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hLfour 2)).trans
        hNlower
    omega
  have hBN : L + 1 ≤ N := by
    have hlocal : L + 1 ≤ 2 * L ^ 2 := by
      nlinarith
    exact hlocal.trans hNlower
  have hhigh : (L + 1) ^ 2 + 2 < N := by
    have hlocal : (L + 1) ^ 2 + 2 < 2 * L ^ 2 := by
      nlinarith
    exact hlocal.trans_le hNlower
  have hNpell : Npell ≤ 3 * N := by
    omega
  have hXratio : Xratio ≤ 3 * N := by
    omega
  have hthreeNM : 3 * N ≤ 3 * M :=
    Nat.mul_le_mul_left 3 hNupper
  have hratio :
      Real.log ((3 * N : ℕ) : ℝ) /
          Real.log (Real.log ((3 * N : ℕ) : ℝ)) ≤
        Real.log ((3 * M : ℕ) : ℝ) /
          Real.log (Real.log ((3 * M : ℕ) : ℝ)) :=
    hratioMono (3 * N) (3 * M) hXratio hthreeNM
  obtain ⟨hloglogM, hlogc₂⟩ :=
    hMlogs M hMlogsM
  have hlogSqB :
      Real.log ((L + 1 : ℕ) : ℝ) ^ 2 ≤
        ((L + 1 : ℕ) : ℝ) :=
    hlogSelf (L + 1) hBlog
  have hfinite :=
    hpellFinite (L + 1) N hNpell hNtwo hBN hhigh
  have hkernel :=
    hpntKernel (L + 1) hBpnt (3 * N)
  have hexponent :=
    combined_exponent_le_critical_range hc
      (by omega : 3 ≤ M) hLtwo
      (by simpa only [c₁, c₂] using hcritical)
      hloglogM
      (by simpa only [c₂] using hlogc₂)
      hlogSqB hratio
  exact
    assemble_twoDefectWindow_bound
      hfinite hkernel hexponent

end
end LemmaFifteenThree
end PaperC
