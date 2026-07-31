import PaperC.Asymptotics.CorollaryThirteenTen
import PaperC.Asymptotics.MaskedPoissonCritical

/-!
# Uniform quantitative rate under deterministic masks

The finite masked Chen--Stein construction is obtained by passing to the
induced subgraph on the mask.  Its first and second Stein terms are therefore
bounded term by term by the corresponding full-block terms.  The two
coupling corrections are the same full-block bad-start quantities.  This
file packages those pointwise dominations with the three quantitative groups
already assembled in Corollary 13.10.

The result is Remark 14.3, labelled `rem:masked-rate` in the manuscript:
the `(log log N)⁻²` rate is uniform simultaneously in the critical pair
`(N,L)` and in every deterministic mask `A ⊆ I_N`.
-/

namespace PaperC
namespace MaskedPoissonRate

open ArratiaGoldsteinGordonInput
open BadStartCount
open CorollaryThirteenTen
open MaskedPoissonCritical
open PropositionElevenThree
open SectionThirteenCouplings
open SectionThirteenRate
open SteinChenCritical
open TerminalPrimeCutoff

noncomputable section

/-- Big-oh with an additional uniform quantifier over deterministic masks. -/
def UniformMaskedBigOOn
    (admissible : ℕ → ℕ → Prop)
    (f : ℕ → ℕ → Finset ℕ → ℝ)
    (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
        |f N L mask| ≤ K * |g N L|

/-- The mask-independent finite upper envelope from the induced-subgraph
Chen--Stein comparison. -/
noncomputable def maskedRateEnvelope (N L : ℕ) : ℝ :=
  badStartProbabilityMassReal N L (terminalPrimeCutoff (L + 1)) +
    2 * (steinBOneReal N L + steinBTwoAverageReal N L) +
    ((terminalBadStarts N L (terminalPrimeCutoff (L + 1))).card : ℝ) /
      (2 : ℝ) ^ L

/-- The common full-block envelope has the rate of Corollary 13.10. -/
theorem maskedRateEnvelope_uniformBigO_canonical
    {C : ℝ} (hC : 0 ≤ C)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      maskedRateEnvelope inverseLogLogSquaredRate := by
  have hhom :=
    DyadicKappaQuantitative.homogeneousMass_uniformBigO
      hC hES hConductor hDivisor
  have hseparated :=
    separatedDefectMass_uniformBigO_of_homogeneousMass 3 hhom
  have hnumerator :=
    steinBTwoNumerator_uniformBigO_of_separatedDefectMass
      hC hseparated
  have hbOne := steinBOne_uniformBigO_explicitRate hC
  have hbTwo :=
    steinBTwoAverage_uniformBigO_explicitRate_of_numerator
      hC hnumerator
  have hstein :=
    uniformBigOOn_const_mul 2
      (uniformBigOOn_add hbOne hbTwo)
  have hbad :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          badStartProbabilityMassReal N L
            (terminalPrimeCutoff (L + 1)))
        inverseLogLogSquaredRate := by
    change UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      BadStartMassCritical.terminalBadStartProbabilityMass
      inverseLogLogSquaredRate
    exact
      terminalBadStartProbabilityMass_uniformBigO_explicitRate hC
  have hcount :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          ((terminalBadStarts N L
            (terminalPrimeCutoff (L + 1))).card : ℝ) /
              (2 : ℝ) ^ L)
        inverseLogLogSquaredRate :=
    normalized_terminalBadStarts_uniformBigO_explicitRate hC
  have hsum :=
    uniformBigOOn_add (uniformBigOOn_add hbad hstein) hcount
  change UniformBigOOn
    (CriticalRunWindow.InRunLengthWindow C)
    (fun N L ↦
      (badStartProbabilityMassReal N L
          (terminalPrimeCutoff (L + 1)) +
        2 * (steinBOneReal N L + steinBTwoAverageReal N L)) +
        ((terminalBadStarts N L
          (terminalPrimeCutoff (L + 1))).card : ℝ) /
            (2 : ℝ) ^ L)
    inverseLogLogSquaredRate
  simpa only [add_assoc] using hsum

/--
Remark 14.3 (`rem:masked-rate`): uniformly over every deterministic mask, the total
variation error is `O_C((log log N)⁻²)`.

The proof uses the literal finite masked estimate.  Its `b₁` and `b₂` terms
are dominated before averaging by the unmasked terms, while the removal and
parameter-shift costs are the two positive full-block corrections.
-/
theorem maskedPoissonTotalVariation_uniformBigO_canonical
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG : ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    UniformMaskedBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      maskedPoissonTotalVariation inverseLogLogSquaredRate := by
  obtain ⟨K, hK, Nrate, hrate⟩ :=
    maskedRateEnvelope_uniformBigO_canonical
      hC hES hConductor hDivisor
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  refine ⟨K, hK, max 2 (max Nrate Nwindow), ?_⟩
  intro N hN L hrun mask hmask
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nrate Nwindow)).trans hN
  have htail : max Nrate Nwindow ≤ N :=
    (le_max_right 2 (max Nrate Nwindow)).trans hN
  have hw :=
    hwindow N ((le_max_right Nrate Nwindow).trans htail) L hrun
  have hLY : L + 1 ≤ terminalPrimeCutoff (L + 1) :=
    window_succ_le_terminalPrimeCutoff hw.2.1 le_rfl
  have hfinite :=
    natTotalVariation_fullMasked_target_le
      hAGG hmask hNtwo hw.2.1 hLY
  have hpoint :
      maskedPoissonTotalVariation N L mask ≤
        maskedRateEnvelope N L := by
    simpa only [maskedPoissonTotalVariation, maskedRateEnvelope,
      steinBOneReal, steinBTwoAverageReal] using hfinite
  have hnonneg :
      0 ≤ maskedPoissonTotalVariation N L mask :=
    maskedPoissonTotalVariation_nonneg N L mask
  rw [abs_of_nonneg hnonneg]
  exact hpoint.trans
    (le_abs_self (maskedRateEnvelope N L) |>.trans
      (hrate N
        ((le_max_left Nrate Nwindow).trans htail)
        L hrun))

end

end MaskedPoissonRate
end PaperC
