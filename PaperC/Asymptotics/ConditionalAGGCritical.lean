import PaperC.Asymptotics.SteinChenCritical
import PaperC.Probability.ConditionalAGGAverage

set_option maxHeartbeats 1200000

/-!
# The averaged conditional AGG error in the critical window

This module closes the asymptotic averaging step of Corollary 13.9 at the
literal terminal prime cutoff.  It combines:

* the concrete averaged conditional AGG theorem;
* the two `o_C(1)` conclusions of `SteinChenCritical`;
* the literal critical-window inequalities needed by the finite theorem.

The final theorem receives the published AGG statement and, separately, the
three existing internal interfaces used by Proposition 11.2.  No aggregate
asymptotic hypothesis and no additional bridge are introduced here.
-/

namespace PaperC
namespace ConditionalAGGCritical

open ArratiaGoldsteinGordonInput
open ConditionalAGGAverage
open SectionThirteenFiniteBound
open TerminalPrimeCutoff

noncomputable section

/--
Total variation of the uniformly averaged conditional good-start law at the
literal terminal cutoff.
-/
noncomputable def averagedConditionalGoodTotalVariation
    (N L : ℕ) : ℝ :=
  natTotalVariation
    (averagedConditionalGoodLaw N L
      (terminalPrimeCutoff (L + 1)))
    (commonConditionalGoodPoissonLaw N L
      (terminalPrimeCutoff (L + 1)))

/-- The averaged conditional total variation is pointwise nonnegative. -/
theorem averagedConditionalGoodTotalVariation_nonneg
    (N L : ℕ) :
    0 ≤ averagedConditionalGoodTotalVariation N L :=
  natTotalVariation_nonneg _ _

/--
Asymptotic closure of the averaged conditional AGG estimate at the literal
terminal cutoff.

The hypotheses `hhosts`, `hnonterminal`, and `hterminal` are exactly the
three registered internal interfaces occurring in Proposition 11.2.
-/
theorem averagedConditionalGoodTotalVariation_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG : ArratiaGoldsteinGordonStatement)
    (A : ℕ) (hA : 1 ≤ A)
    (smallRowRank : PropositionElevenTwo.SmallRowRankFamily)
    (rankBudget : PropositionElevenTwo.RankBudgetFamily)
    (hhosts : PropositionNineNine.HostCountStatement C A)
    (hnonterminal :
      PropositionElevenTwo.NonterminalSectorMassStatement
        C A smallRowRank rankBudget)
    (hterminal :
      PropositionElevenTwo.TerminalSectorMassStatement
        C A smallRowRank rankBudget) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      averagedConditionalGoodTotalVariation
      (fun _ _ ↦ 1) := by
  have hbOne :=
    SteinChenCritical.steinBOne_uniformLittleOOne hC
  have hbTwo :=
    SteinChenCritical.steinBTwoAverage_uniformLittleOOne
      hC A hA smallRowRank rankBudget
      hhosts hnonterminal hterminal
  have hsum :=
    PropositionElevenTwo.uniformLittleOOn_add hbOne hbTwo
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Nsum, hNsum⟩ := hsum (ε / 2) hhalf
  refine ⟨max 2 (max Nwindow Nsum), ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nwindow Nsum)).trans hN
  have hw :=
    hwindow N
      ((le_max_left Nwindow Nsum).trans
        ((le_max_right 2 (max Nwindow Nsum)).trans hN))
      L hrun
  have hL : 0 < L := hw.2.1
  have hLY :
      L + 1 ≤ terminalPrimeCutoff (L + 1) :=
    window_succ_le_terminalPrimeCutoff hL le_rfl
  have hfinite :=
    averagedConditionalGood_natTotalVariation_le_steinTerms
      hAGG hNtwo hL hLY
  have hsmall :=
    hNsum N
      ((le_max_right Nwindow Nsum).trans
        ((le_max_right 2 (max Nwindow Nsum)).trans hN))
      L hrun
  change
    |averagedConditionalGoodTotalVariation N L| ≤
      ε * |(1 : ℝ)|
  rw [abs_of_nonneg
    (averagedConditionalGoodTotalVariation_nonneg N L),
    abs_one, mul_one]
  change
    natTotalVariation
        (averagedConditionalGoodLaw N L
          (terminalPrimeCutoff (L + 1)))
        (commonConditionalGoodPoissonLaw N L
          (terminalPrimeCutoff (L + 1))) ≤ ε
  change
    |SteinChenCritical.steinBOneReal N L +
      SteinChenCritical.steinBTwoAverageReal N L| ≤
        (ε / 2) * |(1 : ℝ)| at hsmall
  calc
    natTotalVariation
        (averagedConditionalGoodLaw N L
          (terminalPrimeCutoff (L + 1)))
        (commonConditionalGoodPoissonLaw N L
          (terminalPrimeCutoff (L + 1))) ≤
      2 *
        (SteinChenCritical.steinBOneReal N L +
          SteinChenCritical.steinBTwoAverageReal N L) := by
      simpa only [SteinChenCritical.steinBOneReal,
        SteinChenCritical.steinBTwoAverageReal] using hfinite
    _ ≤
        2 *
          |SteinChenCritical.steinBOneReal N L +
            SteinChenCritical.steinBTwoAverageReal N L| :=
      mul_le_mul_of_nonneg_left
        (le_abs_self _) (by norm_num)
    _ ≤ 2 * ((ε / 2) * |(1 : ℝ)|) :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ = ε := by
      rw [abs_one]
      ring

end

end ConditionalAGGCritical
end PaperC
