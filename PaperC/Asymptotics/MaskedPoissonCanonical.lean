import PaperC.Asymptotics.DyadicKappaQuantitative
import PaperC.Asymptotics.MaskedPoissonCritical
import PaperC.Asymptotics.NonterminalSectorSaving

set_option maxHeartbeats 3600000

/-!
# Proposition 14.2 through the canonical `κ` mother mass

The proof of the uniform masked Poisson approximation only needs the
qualitative estimate `R₂(N,L)=o(N²)`.  The bounded-ratio `κ` development
proves the stronger rate

`R₂(N,L)=O(N²/(log log N)²)`

directly from the two source-shaped arithmetic inputs used by the
generalized-Pell argument.  Composing the two rates supplies Proposition
14.2 with the required qualitative mother-mass estimate.
-/

namespace PaperC
namespace MaskedPoissonCanonical

open ArratiaGoldsteinGordonInput

noncomputable section

/--
Canonical Proposition 14.2.

Uniformly over every deterministic mask of the dyadic block, the masked
start count is asymptotically Poisson in total variation throughout the
critical window.  Its only assumptions are the published AGG theorem and
the two remaining source-shaped external arithmetic inputs; the conductor
comparison is discharged internally.
-/
theorem maskedPoissonTotalVariation_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG : ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ L : ℕ, CriticalRunWindow.InRunLengthWindow C N L →
          ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
            MaskedPoissonCritical.maskedPoissonTotalVariation
                N L mask ≤ ε := by
  have hhomogeneousBigO :=
    DyadicKappaQuantitative.homogeneousMass_uniformBigO
      hC hES hDivisor
  have hhomogeneousLittleO :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass 3)
        (fun N _ ↦ (N : ℝ) ^ 2) :=
    NonterminalSectorSaving.uniformBigOOn_trans_uniformLittleOOn
      hhomogeneousBigO
      (NonterminalSectorSaving.quadraticDivLogLogSquaredScale_uniformLittleO_quadratic
          (CriticalRunWindow.InRunLengthWindow C))
  exact
    MaskedPoissonCritical.maskedPoissonTotalVariation_uniformLittleOOne_of_homogeneousMass
        hC hAGG hhomogeneousLittleO

/--
Theorem 1.2(i), source-facing canonical name.  The displayed supremum in the
paper is represented by the final uniform quantifier over all
`mask ⊆ I_N`.
-/
theorem theorem_one_two_i
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG : ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ L : ℕ, CriticalRunWindow.InRunLengthWindow C N L →
          ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
            MaskedPoissonCritical.maskedPoissonTotalVariation
                N L mask ≤ ε :=
  maskedPoissonTotalVariation_uniformLittleOOne
    hC hAGG hES hDivisor

end

end MaskedPoissonCanonical
end PaperC
