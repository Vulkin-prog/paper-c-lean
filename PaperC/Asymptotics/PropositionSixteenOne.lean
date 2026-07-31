import PaperC.Asymptotics.PropositionSixteenOneCore
import PaperC.Asymptotics.BoundedRatioSmallProductSector
import PaperC.Asymptotics.BoundedRatioSmallHeightSector
import PaperC.Asymptotics.BoundedRatioShallowCoreSector
import PaperC.Asymptotics.BoundedRatioManyDefectsAssembly
import PaperC.Asymptotics.BoundedRatioNonterminalAssembly
import PaperC.Asymptotics.BoundedRatioTerminalSummation
import PaperC.Combinatorics.BoundedRatioCanonicalTerminalPopulation
import PaperC.Diophantine.PellDivisorEnvelope

/-!
# Proposition 16.1: public assembly

The definitions, exact finite decomposition and narrow Section 17 interfaces
live in `PropositionSixteenOneCore`.  The public theorem is kept in this
separate module so that certified sector closures can import the core without
creating an import cycle.
-/

namespace PaperC
namespace PropositionSixteenOne

noncomputable section

open BoundedRatioCanonicalTerminalPopulation

/--
Proposition 16.1 with all three deep-sector transports visible.  This generic
interface is retained for callers that assemble the sectors independently.

The arithmetic cutoff is fixed at `A = 3`, as in the manuscript's Section 17
quantifier table.  Lemmas 17.14, 17.15 and 17.16 are discharged by the three
certified bounded-ratio modules imported above.  The principal canonical
wrapper below also constructs Lemmas 17.26, 17.28 and 17.30; this generic
interface is retained for independent sector assemblies.
-/
theorem proposition_sixteen_one
    {C : ℝ} (hC : 0 ≤ C)
    {κ₀ : ℕ} (_hκ₀ : 2 ≤ κ₀)
    (terminal : TerminalPredicateFamily)
    (hmany :
      ManyDefectsSectorStabilityStatement
        C κ₀ 3 terminal)
    (hnonterminal :
      NonterminalSectorStabilityStatement
        C κ₀ 3 terminal)
    (hterminal :
      TerminalSectorStabilityStatement
        C κ₀ 3 terminal)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    PropositionSixteenOneStatement C κ₀ := by
  apply proposition_sixteen_one_of_sector_estimates terminal
    (systematicMass_uniformLittleOInBoundedRatioWindow
      hC κ₀ 3 (by norm_num))
  intro sector
  cases sector with
  | smallPrimeProduct =>
      exact
        BoundedRatioSmallProductSector.smallPrimeProductSectorStability
          hC κ₀ 3 (by norm_num) terminal
  | smallCanonicalHeight =>
      exact
        BoundedRatioSmallHeightSector.smallCanonicalHeightSectorStability
          hC κ₀ 3 (by norm_num) terminal
  | shallowCore =>
      exact
        BoundedRatioShallowCoreSector.shallowCoreSectorStability
          hC κ₀ 3 terminal
  | alignedDeepCore =>
      exact
        alignedDeepCoreSector_uniformLittleOInBoundedRatioWindow
          hC κ₀ 3 terminal
  | manyDefects => exact hmany hES hPell
  | nonterminal => exact hnonterminal hES hPell
  | terminal => exact hterminal hPell

/--
Canonical Proposition 16.1 with the generalized-Pell package reconstructed
from the conductor comparison and the source-shaped Nicolas--Robin divisor
inequality.
-/
theorem proposition_sixteen_one_canonical
    {C : ℝ} (hC : 0 ≤ C)
    {κ₀ : ℕ} (hκ₀ : 2 ≤ κ₀)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    PropositionSixteenOneStatement C κ₀ := by
  have hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement :=
    PellInput.generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound
      hConductor hDivisor
  obtain ⟨K, hK, hnonterminal⟩ :=
    BoundedRatioNonterminalAssembly.exists_nonterminalSectorStability
      hC κ₀ 3
  have hterminal :
      TerminalSectorStabilityStatement C κ₀ 3
        (boundedIntrinsicTerminalPredicate 3 K) :=
    BoundedRatioTerminalSummation.intrinsicTerminalSectorStability
      hC κ₀ 3 K hκ₀ (by norm_num) hK
  exact
    proposition_sixteen_one hC hκ₀
      (boundedIntrinsicTerminalPredicate 3 K)
      (BoundedRatioManyDefectsAssembly.manyDefectsSectorStability
        hC κ₀ 3 (boundedIntrinsicTerminalPredicate 3 K))
      hnonterminal hterminal hES hPell

end

end PropositionSixteenOne
end PaperC
