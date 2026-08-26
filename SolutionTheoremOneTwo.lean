import Solution
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Paper C external-audit solution: Theorem 1.2

This module reproduces the standalone statement surface from
`ChallengeTheoremOneTwo.lean` without importing that challenge.  It then
connects each of the three audited declarations to the frozen canonical
Paper C endpoint.  The only non-definitional translations are the finite-PMF
record used by the AGG premise and the compact marked-test record in clause
(iii).
-/

noncomputable section

open scoped BigOperators ENNReal NNReal NumberField Pointwise Topology
open Filter MeasureTheory Set

namespace PaperCAudit

/-! ## Infinite source model -/

-- Make the notation `(2 : ℝ)` independent of Lean's generated proof cache.
-- The imported solution surface and this standalone challenge otherwise can
-- elaborate the standard `OfNat` instance with different proof constants.
local instance instAtLeastTwoTwo : Nat.AtLeastTwo 2 :=
  ⟨Nat.le_refl 2⟩

local instance instOfNatRealTwo : OfNat ℝ 2 :=
  @instOfNatAtLeastTwo ℝ 2 Real.instNatCast instAtLeastTwoTwo

-- Pin the finite typeclass data used by every new Theorem 1.2 definition.
-- Instance synthesis can otherwise reuse implementation-detail proofs from
-- different earlier declarations in the challenge and solution modules.
local instance instNeZeroTwo : NeZero (2 : ℕ) := ⟨by decide⟩
local instance instFintypeF2 : Fintype F₂ := ZMod.fintype 2
local instance instNonemptyF2 : Nonempty F₂ := ⟨0⟩

namespace InfiniteRademacher

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Infinite assignments of independent prime bits. -/
abbrev InfiniteSample := ℕ → F₂

/-- Uniform law of one Rademacher bit. -/
noncomputable def coordinateMeasure : Measure F₂ :=
  (PMF.uniformOfFintype F₂).toMeasure

/-- Probability normalization of the coordinate law. -/
noncomputable instance instIsProbabilityMeasureCoordinateMeasure :
    IsProbabilityMeasure coordinateMeasure := by
  unfold coordinateMeasure
  infer_instance

/-- Infinite product law of the prime bits. -/
noncomputable def infiniteRademacherMeasure : Measure InfiniteSample :=
  Measure.infinitePi (fun _ : ℕ => coordinateMeasure)

/-- Infinite-model parity functional. -/
noncomputable def infiniteValueBit (ω : InfiniteSample) (n : ℕ) : F₂ :=
  (parityVec n).sum fun p e => ω (Nat.primeCounting' p) * e

end InfiniteRademacher

/-! ## Deterministically masked count -/

namespace MaskedPoissonCritical

open SectionThirteenCouplings
open SectionThirteenFiniteBound

local instance instDecidableProp (P : Prop) : Decidable P :=
  Classical.propDecidable P

local instance instFintypeSampleSpace (M : ℕ) : Fintype (SampleSpace M) :=
  @Pi.instFintype
    (PrimeUpTo M) (fun _ => F₂)
    (instDecidableEqPrimeUpTo M) (instFintypePrimeUpTo M)
    (fun _ => instFintypeF2)

/-- Target rate `|A_N|2⁻ᴸ` for a deterministic mask. -/
noncomputable def maskedTargetPoissonRate
    (L : ℕ) (mask : Finset ℕ) : ℝ≥0 :=
  ⟨(mask.card : ℝ) / (2 : ℝ) ^ L, by positivity⟩

/-- Poisson law at the masked target rate. -/
noncomputable def maskedTargetPoissonLaw
    (L : ℕ) (mask : Finset ℕ) : ℕ → ℝ :=
  ProbabilityTheory.poissonPMFReal (maskedTargetPoissonRate L mask)

/-- Literal masked start count on the complete cylinder. -/
noncomputable def fullMaskedDyadicCount
    (N L : ℕ) (mask : Finset ℕ)
    (ω : SampleSpace (dyadicCutoff N L)) : ℕ :=
  ∑ x ∈ mask, if startAt ω x L then 1 else 0

/-- Law of the complete masked start count. -/
noncomputable def fullMaskedDyadicStartLaw
    (N L : ℕ) (mask : Finset ℕ) : ℕ → ℝ :=
  @finiteNatLaw
    (SampleSpace (dyadicCutoff N L))
    (instFintypeSampleSpace (dyadicCutoff N L))
    (fullUniformPMF (dyadicCutoff N L))
    (fullMaskedDyadicCount N L mask)

/-- Total variation in Theorem 1.2(i). -/
noncomputable def maskedPoissonTotalVariation
    (N L : ℕ) (mask : Finset ℕ) : ℝ :=
  natTotalVariation
    (fullMaskedDyadicStartLaw N L mask)
    (maskedTargetPoissonLaw L mask)

end MaskedPoissonCritical

/-! ## Spatial source observable -/

namespace SpatialMarkedParameters

/-- Exact critical scale `N / 2^L`. -/
def criticalSpatialScale (N L : ℕ) : ℝ :=
  (N : ℝ) / (2 : ℝ) ^ L

end SpatialMarkedParameters

namespace InfiniteLaplaceTransfer

open InfiniteRademacher

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instDecidableProp (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Literal spatial Laplace functional under the infinite source model. -/
def infiniteSpatialLaplaceFunctional
    (N L : ℕ) (g : ℝ → ℝ)
    (ω : InfiniteSample) : ℝ :=
  Real.exp
    (-(∑ x ∈ dyadicBlock N,
      if StartEvent (infiniteValueBit ω) x L then
        g ((x : ℝ) / (N : ℝ))
      else 0))

/-- Spatial expectation under the literal infinite Rademacher law. -/
def infiniteSpatialLaplaceExpectation
    (N L : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∫ ω, infiniteSpatialLaplaceFunctional N L g ω
    ∂infiniteRademacherMeasure

end InfiniteLaplaceTransfer

/-! ## Complete marked source observable and mark tails -/

namespace MixedLengthAffine

/-- Bit-valued exact-run event with `q` affine rows. -/
def ExactLengthEvent (g : ℕ → F₂) (x q : ℕ) : Prop :=
  g (x - 1) + g x = 1 ∧
    (∀ j : ℕ, 0 < j → j + 1 < q → g x = g (x + j)) ∧
    g x + g (x + (q - 1)) = 1

/-- Number of affine rows attached to excess length `e`. -/
def excessRowCount (L e : ℕ) : ℕ :=
  L + e + 1

end MixedLengthAffine

namespace FullMarkedLaplaceTransfer

open InfiniteRademacher
open MixedLengthAffine

local instance instDecidableProp (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Literal Laplace functional of the complete marked source process. -/
def infiniteFullMarkedLaplaceFunctional
    (N L : ℕ) (g : ℝ → ℕ → ℝ)
    (ω : InfiniteSample) : ℝ :=
  Real.exp
    (-(∑ x ∈ dyadicBlock N,
      ∑' e : ℕ,
        if ExactLengthEvent (infiniteValueBit ω) x
            (excessRowCount L e) then
          g ((x : ℝ) / (N : ℝ)) e
        else 0))

/-- Expectation of the complete marked Laplace functional. -/
def infiniteFullMarkedLaplaceExpectation
    (N L : ℕ) (g : ℝ → ℕ → ℝ) : ℝ :=
  ∫ ω, infiniteFullMarkedLaplaceFunctional N L g ω
    ∂infiniteRademacherMeasure

end FullMarkedLaplaceTransfer

namespace MarkedDetruncation

open InfiniteRademacher
open MixedLengthAffine

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Event that the marked process contains a mark strictly larger than `E`. -/
def infiniteMarkTailEvent (N L E : ℕ) : Set InfiniteSample :=
  {ω | ∃ x ∈ dyadicBlock N, ∃ e : ℕ, E < e ∧
    ExactLengthEvent (infiniteValueBit ω) x
      (excessRowCount L e)}

/-- Source probability that some mark exceeds `E`. -/
def infiniteMarkTailProbability (N L E : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    (infiniteMarkTailEvent N L E)).toReal

end MarkedDetruncation

/-! ## Laplace-functional endpoint predicates -/

namespace SectionFourteenClosure

open FullMarkedLaplaceTransfer
open InfiniteLaplaceTransfer
open MarkedDetruncation
open SpatialMarkedParameters

/-- A nonnegative continuous test with finite support in the mark coordinate. -/
structure CompactMarkedTest where
  cutoff : ℕ
  toFun : ℝ → ℕ → ℝ
  continuousOn : ∀ e ≤ cutoff,
    ContinuousOn (fun t ↦ toFun t e) (Set.Icc (1 : ℝ) 2)
  nonnegative : ∀ t e, 0 ≤ toFun t e
  vanishesAbove : ∀ t e, cutoff < e → toFun t e = 0

/-- Full marked PPP target written using the finite support witness. -/
def compactMarkedPPPLaplaceTarget
    (rate : ℝ) (g : CompactMarkedTest) : ℝ :=
  Real.exp
    (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
      ∑ e ∈ Finset.range (g.cutoff + 1),
        (1 / (2 : ℝ) ^ (e + 1)) *
          (1 - Real.exp (-g.toFun t e))))

/-- Laplace-functional characterization of `PPP(rate · dt)` on `[1,2)`. -/
def SpatialPPPLaplaceCharacterization
    (Lseq : ℕ → ℕ) (rate : ℝ) : Prop :=
  ∀ g : ℝ → ℝ,
    ContinuousOn g (Set.Icc (1 : ℝ) 2) →
    (∀ t, 0 ≤ g t) →
    Tendsto
      (fun N : ℕ ↦
        infiniteSpatialLaplaceExpectation N (Lseq N) g)
      atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          (1 - Real.exp (-g t))))))

/-- Laplace-functional characterization of the marked limiting PPP. -/
def MarkedPPPLaplaceCharacterization
    (Lseq : ℕ → ℕ) (rate : ℝ) : Prop :=
  ∀ g : CompactMarkedTest,
    Tendsto
      (fun N : ℕ ↦
        infiniteFullMarkedLaplaceExpectation
          N (Lseq N) g.toFun)
      atTop
      (𝓝 (compactMarkedPPPLaplaceTarget rate g))

/-- Uniform tightness of the discrete mark coordinate. -/
def MarkedMarksUniformlyTight
    (Lseq : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ E N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      infiniteMarkTailProbability N (Lseq N) E ≤ ε

end SectionFourteenClosure

end PaperCAudit

/-! ## Explicit translations to the frozen Paper C endpoints -/

private theorem auditAGG_to_paperC
    (h : PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement) :
    PaperC.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement := by
  classical
  letI (p : Prop) : Decidable p := Classical.propDecidable p
  unfold PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement at h
  unfold PaperC.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement
  intro Ω ι instΩ instι instDec μ X G hdep
  let μAudit : PaperCAudit.FinitePMF Ω :=
    { prob := μ.prob
      nonneg := μ.nonneg
      sum_prob := μ.sum_prob }
  have hdepAudit :
      PaperCAudit.ArratiaGoldsteinGordonInput.HasExactDependencyGraph μAudit X G := by
    simpa [
      PaperCAudit.ArratiaGoldsteinGordonInput.HasExactDependencyGraph,
      PaperC.ArratiaGoldsteinGordonInput.HasExactDependencyGraph,
      PaperCAudit.ArratiaGoldsteinGordonInput.HasOutsidePattern,
      PaperC.ArratiaGoldsteinGordonInput.HasOutsidePattern,
      PaperCAudit.ArratiaGoldsteinGordonInput.OutsideIndex,
      PaperC.ArratiaGoldsteinGordonInput.OutsideIndex,
      PaperCAudit.ArratiaGoldsteinGordonInput.closedNeighborhood,
      PaperC.ArratiaGoldsteinGordonInput.closedNeighborhood,
      PaperCAudit.ArratiaGoldsteinGordonInput.eventProbability,
      PaperC.ArratiaGoldsteinGordonInput.eventProbability,
      μAudit] using hdep
  have hRate :
      PaperCAudit.ArratiaGoldsteinGordonInput.poissonRate μAudit X =
        PaperC.ArratiaGoldsteinGordonInput.poissonRate μ X := by
    apply Subtype.ext
    rfl
  have bound := h Ω ι μAudit X G hdepAudit
  simp only [
    PaperCAudit.ArratiaGoldsteinGordonInput.totalVariationToPoisson,
    PaperC.ArratiaGoldsteinGordonInput.totalVariationToPoisson,
    PaperCAudit.ArratiaGoldsteinGordonInput.indicatorSumLaw,
    PaperC.ArratiaGoldsteinGordonInput.indicatorSumLaw,
    PaperCAudit.ArratiaGoldsteinGordonInput.matchingPoissonLaw,
    PaperC.ArratiaGoldsteinGordonInput.matchingPoissonLaw,
    PaperCAudit.ArratiaGoldsteinGordonInput.bOne,
    PaperC.ArratiaGoldsteinGordonInput.bOne,
    PaperCAudit.ArratiaGoldsteinGordonInput.bTwo,
    PaperC.ArratiaGoldsteinGordonInput.bTwo,
    PaperCAudit.ArratiaGoldsteinGordonInput.marginal,
    PaperC.ArratiaGoldsteinGordonInput.marginal,
    PaperCAudit.ArratiaGoldsteinGordonInput.jointMarginal,
    PaperC.ArratiaGoldsteinGordonInput.jointMarginal,
    PaperCAudit.ArratiaGoldsteinGordonInput.eventProbability,
    PaperC.ArratiaGoldsteinGordonInput.eventProbability,
    PaperCAudit.ArratiaGoldsteinGordonInput.indicatorSum,
    PaperC.ArratiaGoldsteinGordonInput.indicatorSum,
    PaperCAudit.ArratiaGoldsteinGordonInput.closedNeighborhood,
    PaperC.ArratiaGoldsteinGordonInput.closedNeighborhood,
    μAudit, hRate] at bound ⊢
  exact bound

/-- Paper C, Theorem 1.2(i): uniform masked Poisson approximation. -/
theorem paper_c_theorem_one_two_i_deterministic_masks
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG :
      PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ L : ℕ, PaperCAudit.CriticalRunWindow.InRunLengthWindow C N L →
          ∀ mask : Finset ℕ, mask ⊆ PaperCAudit.dyadicBlock N →
            PaperCAudit.MaskedPoissonCritical.maskedPoissonTotalVariation
              N L mask ≤ ε := by
  exact
    PaperC.MaskedPoissonCanonical.theorem_one_two_i
      hC (auditAGG_to_paperC hAGG) hES hDivisor

/-- Paper C, Theorem 1.2(ii), in Laplace-functional form. -/
theorem paper_c_theorem_one_two_ii_spatial_laplace
    (hAGG :
      PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C rate : ℝ} (hC : 0 ≤ C)
    (hES :
      PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        PaperCAudit.CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hscale :
      Tendsto
        (fun N : ℕ ↦
          PaperCAudit.SpatialMarkedParameters.criticalSpatialScale N (Lseq N))
        atTop (𝓝 rate)) :
    PaperCAudit.SectionFourteenClosure.SpatialPPPLaplaceCharacterization
      Lseq rate := by
  exact
    PaperC.SectionFourteenClosure.theorem_one_two_ii_laplace
      (auditAGG_to_paperC hAGG) hC hES hDivisor
      Lseq hwindow hscale

/-- Paper C, Theorem 1.2(iii), marked Laplace form plus mark tightness. -/
theorem paper_c_theorem_one_two_iii_marked_laplace_and_tightness
    (hAGG :
      PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C rate : ℝ} (hC : 0 ≤ C)
    (hES :
      PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        PaperCAudit.CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hscale :
      Tendsto
        (fun N : ℕ ↦
          PaperCAudit.SpatialMarkedParameters.criticalSpatialScale N (Lseq N))
        atTop (𝓝 rate)) :
    PaperCAudit.SectionFourteenClosure.MarkedPPPLaplaceCharacterization
        Lseq rate ∧
      PaperCAudit.SectionFourteenClosure.MarkedMarksUniformlyTight Lseq := by
  have hcore :=
    PaperC.SectionFourteenClosure.theorem_one_two_iii_laplace_and_tightness
      (auditAGG_to_paperC hAGG) hC hES hDivisor
      Lseq hwindow hscale
  constructor
  · intro g
    let gCore : PaperC.SectionFourteenClosure.CompactMarkedTest :=
      { cutoff := g.cutoff
        toFun := g.toFun
        continuousOn := g.continuousOn
        nonnegative := g.nonnegative
        vanishesAbove := g.vanishesAbove }
    exact hcore.1 gCore
  · exact hcore.2

#print axioms paper_c_theorem_one_two_i_deterministic_masks
#print axioms paper_c_theorem_one_two_ii_spatial_laplace
#print axioms paper_c_theorem_one_two_iii_marked_laplace_and_tightness

end
