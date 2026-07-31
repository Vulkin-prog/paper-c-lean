import PaperC.Asymptotics.SpatialLaplaceCritical
import PaperC.Asymptotics.MarkedLaplaceCritical
import PaperC.Asymptotics.MarkedDetruncationCritical
import PaperC.Probability.FullMarkedLaplaceTransfer

/-!
# Public closure of Section 14

This module packages the two source-law Laplace-functional limits and the
final mark tightness estimate in theorem-level predicates.

The formalization does not depend on a standard topology of locally finite
point measures.  Its public endpoint is instead the complete Laplace
characterization of the limiting Poisson point processes.  For the marked
process, a compactly supported test includes a finite cutoff in the discrete
mark coordinate; the theorem quantifies over every such cutoff and is paired
with uniform tightness of the marks.
-/

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace PaperC
namespace SectionFourteenClosure

open InfiniteLaplaceTransfer
open FullMarkedLaplaceTransfer
open MarkedDetruncation
open SpatialMarkedParameters

noncomputable section

/-- A nonnegative continuous test with compact support in the discrete mark
coordinate. -/
structure CompactMarkedTest where
  cutoff : ℕ
  toFun : ℝ → ℕ → ℝ
  continuousOn : ∀ e ≤ cutoff,
    ContinuousOn (fun t ↦ toFun t e) (Set.Icc (1 : ℝ) 2)
  nonnegative : ∀ t e, 0 ≤ toFun t e
  vanishesAbove : ∀ t e, cutoff < e → toFun t e = 0

/-- The full marked PPP target, written using the finite support witness. -/
def compactMarkedPPPLaplaceTarget
    (rate : ℝ) (g : CompactMarkedTest) : ℝ :=
  Real.exp
    (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
      ∑ e ∈ Finset.range (g.cutoff + 1),
        (1 / (2 : ℝ) ^ (e + 1)) *
          (1 - Real.exp (-g.toFun t e))))

/-- Outside the support witness every summand in the full marked exponent
vanishes. -/
theorem compactMarkedTest_tsum_eq_finset
    (g : CompactMarkedTest) (t : ℝ) :
    (∑' e : ℕ,
        (1 / (2 : ℝ) ^ (e + 1)) *
          (1 - Real.exp (-g.toFun t e))) =
      ∑ e ∈ Finset.range (g.cutoff + 1),
        (1 / (2 : ℝ) ^ (e + 1)) *
          (1 - Real.exp (-g.toFun t e)) := by
  apply tsum_eq_sum
  intro e he
  have hcut : g.cutoff < e := by
    have : ¬e < g.cutoff + 1 := by
      simpa only [Finset.mem_range] using he
    omega
  rw [g.vanishesAbove t e hcut]
  simp

/-- Thus the finite-support target is literally the usual infinite marked
Laplace exponent. -/
theorem compactMarkedPPPLaplaceTarget_eq_tsum
    (rate : ℝ) (g : CompactMarkedTest) :
    compactMarkedPPPLaplaceTarget rate g =
      Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          ∑' e : ℕ,
            (1 / (2 : ℝ) ^ (e + 1)) *
              (1 - Real.exp (-g.toFun t e)))) := by
  unfold compactMarkedPPPLaplaceTarget
  have hfun :
      (fun t : ℝ ↦
        ∑ e ∈ Finset.range (g.cutoff + 1),
          (1 / (2 : ℝ) ^ (e + 1)) *
            (1 - Real.exp (-g.toFun t e))) =
      (fun t : ℝ ↦
        ∑' e : ℕ,
          (1 / (2 : ℝ) ^ (e + 1)) *
            (1 - Real.exp (-g.toFun t e))) := by
    funext t
    exact (compactMarkedTest_tsum_eq_finset g t).symm
  rw [hfun]

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

/-- Laplace-functional characterization of
`PPP(rate · dt ⊗ ν)`, `ν({e}) = 2^(-(e+1))`, on all compactly
mark-supported tests. -/
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

/-- Theorem 1.2(ii), in the exact Laplace-functional formulation available
for point processes in the current library. -/
theorem theorem_one_two_ii_laplace
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C rate : ℝ} (hC : 0 ≤ C)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hscale :
      Tendsto
        (fun N : ℕ ↦ criticalSpatialScale N (Lseq N))
        atTop (𝓝 rate)) :
    SpatialPPPLaplaceCharacterization Lseq rate := by
  intro g hg hg0
  exact
    SpatialLaplaceCritical.sectionFourteenTwo_spatialLaplaceFunctional
      hAGG hC hES hConductor hDivisor
      (N := fun N : ℕ ↦ N) (L := Lseq)
      tendsto_id hwindow hscale hg hg0

/-- Theorem 1.2(iii): the complete marked Laplace characterization together
with the manuscript's final uniform de-truncation estimate. -/
theorem theorem_one_two_iii_laplace_and_tightness
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C rate : ℝ} (hC : 0 ≤ C)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hscale :
      Tendsto
        (fun N : ℕ ↦ criticalSpatialScale N (Lseq N))
        atTop (𝓝 rate)) :
    MarkedPPPLaplaceCharacterization Lseq rate ∧
      MarkedMarksUniformlyTight Lseq := by
  constructor
  · intro g
    have htruncated :=
      MarkedLaplaceCritical.sectionFourteenFour_laplaceFunctional
        hAGG hC hES hConductor hDivisor
        (N := fun N : ℕ ↦ N) (L := Lseq)
        tendsto_id hwindow hscale g.continuousOn g.nonnegative
    apply htruncated.congr'
    exact Eventually.of_forall fun N ↦
      (infiniteFullMarkedLaplaceExpectation_eq_truncated
        N (Lseq N) g.cutoff g.toFun g.vanishesAbove).symm
  · exact
      MarkedDetruncationCritical.markTailProbabilities_uniformly_tight
        hC Lseq hwindow (by
          simpa only [criticalSpatialScale] using hscale)

end

end SectionFourteenClosure
end PaperC
