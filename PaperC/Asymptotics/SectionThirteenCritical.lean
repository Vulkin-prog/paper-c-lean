import PaperC.Asymptotics.BadStartMassCritical
import PaperC.Asymptotics.ConditionalAGGCritical
import PaperC.Probability.SectionThirteenCouplings

set_option maxHeartbeats 1200000

/-!
# Corollary 13.9 in the critical window

This module assembles the three finite comparisons of Section 13:

1. remove terminal bad starts by the exact full-cylinder coupling;
2. apply the averaged conditional Arratia--Goldstein--Gordon estimate;
3. couple the resulting Poisson law to the manuscript rate `N / 2^L`.

At the literal terminal prime cutoff, the first and third errors are the
already proved `o_C(1)` terms of Lemmas 13.3--13.4, while the middle error is
the conditional conclusion of `ConditionalAGGCritical`.
-/

namespace PaperC
namespace SectionThirteenCritical

open ArratiaGoldsteinGordonInput
open BadStartCount
open SectionThirteenFiniteBound
open SectionThirteenCouplings
open TerminalPrimeCutoff

noncomputable section

/-- The total variation distance appearing in Corollary 13.9. -/
noncomputable def fullDyadicTargetPoissonTotalVariation
    (N L : ℕ) : ℝ :=
  natTotalVariation
    (fullDyadicStartLaw N L)
    (targetPoissonLaw N L)

/-- The Corollary 13.9 total variation distance is nonnegative. -/
theorem fullDyadicTargetPoissonTotalVariation_nonneg
    (N L : ℕ) :
    0 ≤ fullDyadicTargetPoissonTotalVariation N L :=
  natTotalVariation_nonneg _ _

/--
Corollary 13.9: in the literal critical run-length window, the law of the
full dyadic start count is `o_C(1)` in total variation from the Poisson law
of rate `N / 2^L`.

The external AGG theorem and the three internal Proposition 11.2 interfaces
remain explicit hypotheses.
-/
theorem fullDyadicTargetPoissonTotalVariation_uniformLittleOOne
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
      fullDyadicTargetPoissonTotalVariation
      (fun _ _ ↦ 1) := by
  let terminalY : ℕ → ℕ :=
    fun L ↦ terminalPrimeCutoff (L + 1)
  have hbad :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          badStartProbabilityMassReal N L (terminalY L))
        (fun _ _ ↦ 1) := by
    simpa only [terminalY, badStartProbabilityMassReal,
      BadStartMassCritical.terminalBadStartProbabilityMass] using
      BadStartMassCritical.terminalBadStartProbabilityMass_uniformLittleOOne
        hC
  have hagg :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        ConditionalAGGCritical.averagedConditionalGoodTotalVariation
        (fun _ _ ↦ 1) :=
    ConditionalAGGCritical.averagedConditionalGoodTotalVariation_uniformLittleOOne
        hC hAGG A hA smallRowRank rankBudget
        hhosts hnonterminal hterminal
  have hcount :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          ((terminalBadStarts N L (terminalY L)).card : ℝ) /
            (2 : ℝ) ^ L)
        (fun _ _ ↦ 1) := by
    simpa only [terminalY] using
      TerminalBadStartsCritical.normalized_terminalBadStarts_uniformLittleOOne
        hC
  have hfirst :=
    PropositionElevenTwo.uniformLittleOOn_add hbad hagg
  have hsum :=
    PropositionElevenTwo.uniformLittleOOn_add hfirst hcount
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Nsum, hsumBound⟩ := hsum ε hε
  refine ⟨max 2 (max Nwindow Nsum), ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nwindow Nsum)).trans hN
  have htail :
      max Nwindow Nsum ≤ N :=
    (le_max_right 2 (max Nwindow Nsum)).trans hN
  have hw :=
    hwindow N ((le_max_left Nwindow Nsum).trans htail)
      L hrun
  have hL : 0 < L := hw.2.1
  have hLY :
      L + 1 ≤ terminalY L := by
    dsimp only [terminalY]
    exact window_succ_le_terminalPrimeCutoff hL le_rfl
  have hfinite :=
    natTotalVariation_fullDyadic_targetPoisson_le_components
      hNtwo hL hLY
  have hsmall :=
    hsumBound N
      ((le_max_right Nwindow Nsum).trans htail)
      L hrun
  change
    |fullDyadicTargetPoissonTotalVariation N L| ≤
      ε * |(1 : ℝ)|
  rw [abs_of_nonneg
    (fullDyadicTargetPoissonTotalVariation_nonneg N L),
    abs_one, mul_one]
  change
    natTotalVariation
        (fullDyadicStartLaw N L)
        (targetPoissonLaw N L) ≤ ε
  calc
    natTotalVariation
        (fullDyadicStartLaw N L)
        (targetPoissonLaw N L) ≤
      badStartProbabilityMassReal N L (terminalY L) +
        ConditionalAGGCritical.averagedConditionalGoodTotalVariation N L +
        ((terminalBadStarts N L (terminalY L)).card : ℝ) /
          (2 : ℝ) ^ L := by
      simpa only [terminalY,
        ConditionalAGGCritical.averagedConditionalGoodTotalVariation] using
          hfinite
    _ ≤
      |badStartProbabilityMassReal N L (terminalY L) +
        ConditionalAGGCritical.averagedConditionalGoodTotalVariation N L +
        ((terminalBadStarts N L (terminalY L)).card : ℝ) /
          (2 : ℝ) ^ L| :=
      le_abs_self _
    _ ≤ ε := by
      simpa only [abs_one, mul_one] using hsmall

end

end SectionThirteenCritical
end PaperC
