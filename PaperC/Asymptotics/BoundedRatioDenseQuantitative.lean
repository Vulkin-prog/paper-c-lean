import PaperC.Asymptotics.BoundedRatioNonterminalCardinality
import PaperC.Asymptotics.PropositionElevenThree

set_option maxHeartbeats 1800000

/-!
# Quantitative decay for the bounded-ratio dense nonterminal envelope

The high-density branch of the bounded-ratio nonterminal argument already
has the exact factor

`exp (-(K log 2 - Cterm) sqrt (L+1) / log (L+1))`.

This module compares that factor with the quantitative scale of Corollary
11.3 in the critical run-length window.  The comparison is deliberately
separated from the finite mass bound: it applies directly to the canonical
envelope constructed in `BoundedRatioNonterminalCardinality`.
-/

namespace PaperC
namespace BoundedRatioDenseQuantitative

open BoundedRatioNonterminalCardinality

noncomputable section

/--
A positive fraction of the lower edge of the critical window.  Using
`min 1 lowerConstant` avoids an unnecessary square root in the explicit
constant.
-/
noncomputable def criticalSqrtCoefficient : ℝ :=
  min 1 CriticalRunWindow.lowerConstant

theorem criticalSqrtCoefficient_pos :
    0 < criticalSqrtCoefficient := by
  unfold criticalSqrtCoefficient
  exact lt_min zero_lt_one CriticalRunWindow.lowerConstant_pos

/--
The saving constant transported from the `B=L+1` scale to the `N` scale.
-/
noncomputable def denseQuantitativeConstant
    (Cterm K : ℝ) : ℝ :=
  (K * Real.log 2 - Cterm) * criticalSqrtCoefficient / 2

theorem denseQuantitativeConstant_pos
    {Cterm K : ℝ} (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2) :
    0 < denseQuantitativeConstant Cterm K := by
  have hgap : 0 < K * Real.log 2 - Cterm := by
    nlinarith
  unfold denseQuantitativeConstant
  exact div_pos
    (mul_pos hgap criticalSqrtCoefficient_pos) (by norm_num)

/--
Uniform comparison of the two square-root logarithmic scales:

`sqrt(log N) / loglog N
  ≤ (2 / min(1,c₁)) sqrt(L+1) / log(L+1)`.

Only the literal critical run-length window is assumed.
-/
theorem sqrtLog_div_loglog_le_heightScale_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
        Real.sqrt (Real.log N) /
            Real.log (Real.log N) ≤
          (2 / criticalSqrtCoefficient) *
            (Real.sqrt ((L + 1 : ℕ) : ℝ) /
              Real.log ((L + 1 : ℕ) : ℝ)) := by
  let c₁ : ℝ := CriticalRunWindow.lowerConstant
  let c₂ : ℝ := CriticalRunWindow.upperConstant
  let η : ℝ := criticalSqrtCoefficient
  have hc₁ : 0 < c₁ := by
    simpa only [c₁] using CriticalRunWindow.lowerConstant_pos
  have hc₂ : 0 < c₂ := by
    exact hc₁.trans (by
      simpa only [c₁, c₂] using
        CriticalRunWindow.lowerConstant_lt_upperConstant)
  have hη : 0 < η := by
    simpa only [η] using criticalSqrtCoefficient_pos
  have hηOne : η ≤ 1 := by
    dsimp only [η, criticalSqrtCoefficient]
    exact min_le_left _ _
  have hηc₁ : η ≤ c₁ := by
    dsimp only [η, criticalSqrtCoefficient, c₁]
    exact min_le_right _ _
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let T : ℝ := max (Real.exp 1) c₂
  obtain ⟨Nexp, hNexp⟩ :=
    exists_nat_gt (Real.exp T)
  refine ⟨max Nwindow Nexp, ?_⟩
  intro N hN L hrun
  have hNwindow : Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have hNexpN : Nexp ≤ N :=
    (le_max_right _ _).trans hN
  obtain ⟨hcritical, hLpos, _hbalance⟩ :=
    hwindow N hNwindow L hrun
  have hthreshold :
      Real.exp T < (N : ℝ) :=
    hNexp.trans_le (by exact_mod_cast hNexpN)
  have hTlog : T < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos T) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hlogN :
      Real.exp 1 < Real.log N := by
    exact (le_max_left _ _).trans_lt hTlog
  have hc₂log :
      c₂ < Real.log N :=
    (le_max_right _ _).trans_lt hTlog
  have hlogNpos : 0 < Real.log N :=
    (Real.exp_pos 1).trans hlogN
  have hlogNnonneg : 0 ≤ Real.log N := hlogNpos.le
  have hloglogNpos :
      0 < Real.log (Real.log N) :=
    Real.log_pos
      ((show (1 : ℝ) < Real.exp 1 by
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.mpr (by norm_num)).trans hlogN)
  have hlogc₂ :
      Real.log c₂ ≤ Real.log (Real.log N) :=
    Real.log_le_log hc₂ hc₂log.le
  have hBtwo : 2 ≤ L + 1 := by
    omega
  have hBpos : 0 < (((L + 1 : ℕ) : ℝ)) := by
    positivity
  have hlogBpos :
      0 < Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast hBtwo)
  have hlogB :
      Real.log ((L + 1 : ℕ) : ℝ) ≤
        2 * Real.log (Real.log N) := by
    have hlogProduct :
        Real.log ((L + 1 : ℕ) : ℝ) ≤
          Real.log (c₂ * Real.log N) := by
      apply Real.log_le_log hBpos
      simpa only [c₂] using hcritical.2.2.2
    calc
      Real.log ((L + 1 : ℕ) : ℝ) ≤
          Real.log (c₂ * Real.log N) := hlogProduct
      _ =
          Real.log c₂ + Real.log (Real.log N) := by
        rw [Real.log_mul hc₂.ne' hlogNpos.ne']
      _ ≤ 2 * Real.log (Real.log N) := by
        linarith
  have hηsq : η ^ 2 ≤ η := by
    nlinarith [sq_nonneg (η - 1)]
  have hηlog :
      η * Real.log N ≤ ((L + 1 : ℕ) : ℝ) := by
    calc
      η * Real.log N ≤ c₁ * Real.log N :=
        mul_le_mul_of_nonneg_right hηc₁ hlogNnonneg
      _ ≤ ((L + 1 : ℕ) : ℝ) := by
        simpa only [c₁] using hcritical.2.2.1
  have hsqrtLogSq :
      (Real.sqrt (Real.log N)) ^ 2 = Real.log N :=
    Real.sq_sqrt hlogNnonneg
  have hsquare :
      (η * Real.sqrt (Real.log N)) ^ 2 ≤
        ((L + 1 : ℕ) : ℝ) := by
    calc
      (η * Real.sqrt (Real.log N)) ^ 2 =
          η ^ 2 * Real.log N := by
        rw [mul_pow, hsqrtLogSq]
      _ ≤ η * Real.log N :=
        mul_le_mul_of_nonneg_right hηsq hlogNnonneg
      _ ≤ ((L + 1 : ℕ) : ℝ) := hηlog
  have hsqrtBsq :
      (Real.sqrt ((L + 1 : ℕ) : ℝ)) ^ 2 =
        ((L + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtLower :
      η * Real.sqrt (Real.log N) ≤
        Real.sqrt ((L + 1 : ℕ) : ℝ) := by
    apply
      (sq_le_sq₀
        (mul_nonneg hη.le (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)).mp
    simpa only [hsqrtBsq] using hsquare
  have hhalfLog :
      Real.log ((L + 1 : ℕ) : ℝ) / 2 ≤
        Real.log (Real.log N) := by
    linarith
  have hcross :
      ((η / 2) * Real.sqrt (Real.log N)) *
          Real.log ((L + 1 : ℕ) : ℝ) ≤
        Real.sqrt ((L + 1 : ℕ) : ℝ) *
          Real.log (Real.log N) := by
    calc
      ((η / 2) * Real.sqrt (Real.log N)) *
            Real.log ((L + 1 : ℕ) : ℝ) =
          (η * Real.sqrt (Real.log N)) *
            (Real.log ((L + 1 : ℕ) : ℝ) / 2) := by
        ring
      _ ≤
          Real.sqrt ((L + 1 : ℕ) : ℝ) *
            (Real.log ((L + 1 : ℕ) : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hsqrtLower
          (div_nonneg hlogBpos.le (by norm_num))
      _ ≤
          Real.sqrt ((L + 1 : ℕ) : ℝ) *
            Real.log (Real.log N) :=
        mul_le_mul_of_nonneg_left hhalfLog
          (Real.sqrt_nonneg _)
  have hratio :
      (η / 2) *
          (Real.sqrt (Real.log N) /
            Real.log (Real.log N)) ≤
        Real.sqrt ((L + 1 : ℕ) : ℝ) /
          Real.log ((L + 1 : ℕ) : ℝ) := by
    rw [← mul_div_assoc]
    apply
      (div_le_div_iff₀ hloglogNpos hlogBpos).2
    exact hcross
  calc
    Real.sqrt (Real.log N) /
          Real.log (Real.log N) =
        (2 / η) *
          ((η / 2) *
            (Real.sqrt (Real.log N) /
              Real.log (Real.log N))) := by
      field_simp [hη.ne']
    _ ≤
        (2 / η) *
          (Real.sqrt ((L + 1 : ℕ) : ℝ) /
            Real.log ((L + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ =
        (2 / criticalSqrtCoefficient) *
          (Real.sqrt ((L + 1 : ℕ) : ℝ) /
            Real.log ((L + 1 : ℕ) : ℝ)) := by
      simp only [η]

/--
The canonical high-density envelope is bounded by the quantitative
homogeneous scale with an explicit positive saving constant.
-/
theorem highDensityIntrinsicNonterminalMassEnvelope_uniformBigO_quantitative
    {C Cterm K : ℝ} (hC : 0 ≤ C) (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (highDensityIntrinsicNonterminalMassEnvelope C Cterm K)
      (PropositionElevenThree.quantitativeHomogeneousScale
        (denseQuantitativeConstant Cterm K)) := by
  let δ : ℝ := K * Real.log 2 - Cterm
  let c : ℝ := denseQuantitativeConstant Cterm K
  let a : ℝ := 8 * CriticalRunWindow.balanceConstant C
  have hc : 0 < c := by
    simpa only [c] using
      denseQuantitativeConstant_pos hCterm hthreshold
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact mul_nonneg (by norm_num)
      (CriticalRunWindow.balanceConstant_nonneg C)
  obtain ⟨Nratio, hratio⟩ :=
    sqrtLog_div_loglog_le_heightScale_eventually hC
  obtain ⟨Nheight, hheight⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity hC 2
  refine ⟨a, ha, max Nratio Nheight, ?_⟩
  intro N hN L hrun
  have hNratio : Nratio ≤ N :=
    (le_max_left _ _).trans hN
  have hNheight : Nheight ≤ N :=
    (le_max_right _ _).trans hN
  have hBtwo : 2 ≤ L + 1 :=
    hheight N hNheight L hrun
  have hscaleCompare :=
    hratio N hNratio L hrun
  have hcoefficient :
      c * (2 / criticalSqrtCoefficient) = δ := by
    dsimp only [c, denseQuantitativeConstant, δ]
    field_simp [criticalSqrtCoefficient_pos.ne']
  have hexponentCompare :
      c *
          (Real.sqrt (Real.log N) /
            Real.log (Real.log N)) ≤
        δ *
          (Real.sqrt ((L + 1 : ℕ) : ℝ) /
            Real.log ((L + 1 : ℕ) : ℝ)) := by
    calc
      c *
            (Real.sqrt (Real.log N) /
              Real.log (Real.log N)) ≤
          c *
            ((2 / criticalSqrtCoefficient) *
              (Real.sqrt ((L + 1 : ℕ) : ℝ) /
                Real.log ((L + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hscaleCompare hc.le
      _ =
        δ *
            (Real.sqrt ((L + 1 : ℕ) : ℝ) /
              Real.log ((L + 1 : ℕ) : ℝ)) := by
        rw [← mul_assoc, hcoefficient]
  have hgap :=
    terminalRankGapFactor_le_exp_gap
      (Cterm := Cterm) (K := K) (N := N) hBtwo
  have hgapQuantitative :
      terminalRankGapFactor Cterm K N L ≤
        Real.exp
          (-c * Real.sqrt (Real.log N) /
            Real.log (Real.log N)) := by
    refine hgap.trans (Real.exp_le_exp.mpr ?_)
    change
      -δ *
          (Real.sqrt ((L + 1 : ℕ) : ℝ) /
            Real.log ((L + 1 : ℕ) : ℝ)) ≤
        -c * Real.sqrt (Real.log N) /
          Real.log (Real.log N)
    calc
      -δ *
            (Real.sqrt ((L + 1 : ℕ) : ℝ) /
              Real.log ((L + 1 : ℕ) : ℝ)) =
          -(δ *
            (Real.sqrt ((L + 1 : ℕ) : ℝ) /
              Real.log ((L + 1 : ℕ) : ℝ))) := by ring
      _ ≤
          -(c *
            (Real.sqrt (Real.log N) /
              Real.log (Real.log N))) :=
        neg_le_neg hexponentCompare
      _ =
          -c * Real.sqrt (Real.log N) /
            Real.log (Real.log N) := by ring
  have henvelopeNonneg :=
    highDensityIntrinsicNonterminalMassEnvelope_nonneg
      C Cterm K N L
  have hscaleNonneg :
      0 ≤
        PropositionElevenThree.quantitativeHomogeneousScale
          (denseQuantitativeConstant Cterm K) N L := by
    unfold PropositionElevenThree.quantitativeHomogeneousScale
    positivity
  rw [abs_of_nonneg henvelopeNonneg, abs_of_nonneg hscaleNonneg]
  unfold highDensityIntrinsicNonterminalMassEnvelope
    PropositionElevenThree.quantitativeHomogeneousScale
  dsimp only [a, c]
  calc
    (8 * CriticalRunWindow.balanceConstant C) *
          (N : ℝ) ^ 2 *
          terminalRankGapFactor Cterm K N L ≤
        (8 * CriticalRunWindow.balanceConstant C) *
          (N : ℝ) ^ 2 *
          Real.exp
            (-denseQuantitativeConstant Cterm K *
              Real.sqrt (Real.log N) /
              Real.log (Real.log N)) :=
      mul_le_mul_of_nonneg_left hgapQuantitative
        (mul_nonneg
          (by positivity)
          (sq_nonneg (N : ℝ)))
    _ =
        (8 * CriticalRunWindow.balanceConstant C) *
          ((N : ℝ) ^ 2 *
            Real.exp
              (-denseQuantitativeConstant Cterm K *
                Real.sqrt (Real.log N) /
                Real.log (Real.log N))) := by
      ring

/--
Existential form convenient for the final Corollary 11.3 assembly.
-/
theorem exists_highDensityIntrinsicNonterminalMassEnvelope_quantitative
    {C Cterm K : ℝ} (hC : 0 ≤ C) (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2) :
    ∃ c : ℝ, 0 < c ∧
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (highDensityIntrinsicNonterminalMassEnvelope C Cterm K)
        (PropositionElevenThree.quantitativeHomogeneousScale c) :=
  ⟨denseQuantitativeConstant Cterm K,
    denseQuantitativeConstant_pos hCterm hthreshold,
    highDensityIntrinsicNonterminalMassEnvelope_uniformBigO_quantitative
      hC hCterm hthreshold⟩

end

end BoundedRatioDenseQuantitative
end PaperC
