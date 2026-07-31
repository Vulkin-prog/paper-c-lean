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
Proposition 16.1 with the canonical intrinsic terminal population.

The terminal test is no longer an arbitrary family supplied by a caller:
it is the exact inequality

`B + D# ≤ τ + floor(K * sqrt(B) / log(B))`.

By the now proved source-scoped Lemma 9.10 equivalence this is the manuscript
condition `s + k̃ ≤ floor(K * sqrt(B) / log(B))`.  This historical wrapper
still accepts estimates on the literal fifth, sixth and seventh fibres of
this fixed classifier.  The principal canonical theorem below constructs
the fifth estimate from Evertse--Silverman and Pell, and the seventh estimate
from Pell alone.
-/
theorem proposition_sixteen_one_canonical_of_sector_estimates
    {C : ℝ} (hC : 0 ≤ C)
    {κ₀ : ℕ} (hκ₀ : 2 ≤ κ₀)
    (K : ℝ)
    (hmany :
      ManyDefectsSectorStabilityStatement C κ₀ 3
        (boundedIntrinsicTerminalPredicate 3 K))
    (hnonterminal :
      NonterminalSectorStabilityStatement C κ₀ 3
        (boundedIntrinsicTerminalPredicate 3 K))
    (hterminal :
      TerminalSectorStabilityStatement C κ₀ 3
        (boundedIntrinsicTerminalPredicate 3 K))
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    PropositionSixteenOneStatement C κ₀ :=
  proposition_sixteen_one hC hκ₀
    (boundedIntrinsicTerminalPredicate 3 K)
    hmany hnonterminal hterminal hES hPell

/--
Historical canonical wrapper with an explicit Lemma 17.26 many-defects
estimate.

It constructs the terminal closure from generalized Pell; the source-exact
Lemma 9.10 arithmetic equivalence is now proved internally.  The wrapper is
retained for code that supplies the fifth-sector estimate directly.
-/
theorem proposition_sixteen_one_canonical_of_manyDefectsEstimate
    {C : ℝ} (hC : 0 ≤ C)
    {κ₀ : ℕ} (hκ₀ : 2 ≤ κ₀)
    (K : ℝ) (hK : 0 ≤ K)
    (hmany :
      ManyDefectsSectorStabilityStatement C κ₀ 3
        (boundedIntrinsicTerminalPredicate 3 K))
    (hnonterminal :
      NonterminalSectorStabilityStatement C κ₀ 3
        (boundedIntrinsicTerminalPredicate 3 K))
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    PropositionSixteenOneStatement C κ₀ := by
  have hterminal :
      TerminalSectorStabilityStatement C κ₀ 3
        (boundedIntrinsicTerminalPredicate 3 K) :=
    BoundedRatioTerminalSummation.intrinsicTerminalSectorStability
      hC κ₀ 3 K hκ₀ (by norm_num) hK
  exact
    proposition_sixteen_one hC hκ₀
      (boundedIntrinsicTerminalPredicate 3 K)
      hmany hnonterminal hterminal hES hPell

/--
Proposition 16.1 for the canonical intrinsic terminal population.

Historical canonical wrapper with an explicit Lemma 17.28 nonterminal
estimate.  Lemmas 17.26 and 17.30 are constructed internally.  It is
retained for callers that already provide the sixth-sector estimate.
-/
theorem proposition_sixteen_one_canonical_of_nonterminalEstimate
    {C : ℝ} (hC : 0 ≤ C)
    {κ₀ : ℕ} (hκ₀ : 2 ≤ κ₀)
    (K : ℝ) (hK : 0 ≤ K)
    (hnonterminal :
      NonterminalSectorStabilityStatement C κ₀ 3
        (boundedIntrinsicTerminalPredicate 3 K))
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    PropositionSixteenOneStatement C κ₀ := by
  exact
    proposition_sixteen_one_canonical_of_manyDefectsEstimate
      hC hκ₀ K hK
      (BoundedRatioManyDefectsAssembly.manyDefectsSectorStability
        hC κ₀ 3 (boundedIntrinsicTerminalPredicate 3 K))
      hnonterminal hES hPell

/--
Proposition 16.1 with the canonical intrinsic terminal population.

The complete Section 17 sector analysis is assembled internally.  Lemma
17.26 is obtained from Evertse--Silverman and generalized Pell; Lemma 17.28
constructs its own terminal threshold from the two-singleton host count;
and Lemma 17.30 follows from generalized Pell and the proved source-exact
Lemma 9.10 arithmetic equivalence.
-/
theorem proposition_sixteen_one_canonical_of_generalizedPell
    {C : ℝ} (hC : 0 ≤ C)
    {κ₀ : ℕ} (hκ₀ : 2 ≤ κ₀)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    PropositionSixteenOneStatement C κ₀ := by
  obtain ⟨K, hK, hnonterminal⟩ :=
    BoundedRatioNonterminalAssembly.exists_nonterminalSectorStability
      hC κ₀ 3
  exact
    proposition_sixteen_one_canonical_of_nonterminalEstimate
      hC hκ₀ K hK hnonterminal hES hPell

/--
Compatibility wrapper for the former specialized Nicolas--Robin Pell
envelope.
-/
theorem proposition_sixteen_one_canonical_of_pellEnvelope
    {C : ℝ} (hC : 0 ≤ C)
    {κ₀ : ℕ} (hκ₀ : 2 ≤ κ₀)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinPellEnvelopeStatement) :
    PropositionSixteenOneStatement C κ₀ :=
  proposition_sixteen_one_canonical_of_generalizedPell
    hC hκ₀ hES
      (PellInput.generalizedPellPolynomialBox_of_quadraticOrder_nicolasRobin
        hConductor hDivisor)

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
    PropositionSixteenOneStatement C κ₀ :=
  proposition_sixteen_one_canonical_of_generalizedPell
    hC hκ₀ hES
      (PellInput.generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound
        hConductor hDivisor)

end

end PropositionSixteenOne
end PaperC
