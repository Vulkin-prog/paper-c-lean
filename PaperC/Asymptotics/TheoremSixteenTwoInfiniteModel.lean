import PaperC.Asymptotics.TheoremSixteenTwo
import PaperC.Probability.InfiniteStartProbabilityTransfer

set_option maxHeartbeats 1600000

/-!
# Theorem 16.2 on the infinite Rademacher product law

`TheoremSixteenTwo` proves the global interior Poisson law on an explicit
finite prime cylinder.  The count is a finite observable, so the exact
source/cylinder image-law transfer identifies it with the corresponding
random variable on the infinite Rademacher product space.  This module
records that identification and exposes the canonical theorem directly in
the source model, without changing any arithmetic hypothesis.
-/

open scoped ENNReal
open MeasureTheory Set

namespace PaperC
namespace TheoremSixteenTwo

open ArratiaGoldsteinGordonInput
open ConditionalAGGAverage
open InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer
open InfiniteRademacher
open PellInput
open ProbabilityTheory
open SectionThirteenCouplings
open SectionThirteenFiniteBound

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Exact source/cylinder transfer for the global count -/

/--
The literal global interior start count as a random variable on the infinite
Rademacher product space.
-/
noncomputable def infiniteGlobalStartCount
    (M L : ℕ) (ω : InfiniteSample) : ℕ := by
  classical
  exact ∑ x ∈ globalStartIndices M,
    if StartEvent (infiniteValueBit ω) x L then 1 else 0

/-- Restriction to the common global cylinder preserves the literal count. -/
theorem globalStartCount_restrictToFinite_eq_infiniteGlobalStartCount
    (M L : ℕ) (ω : InfiniteSample) :
    globalStartCount M L
        (restrictToFinite (globalCylinderCutoff M L) ω) =
      infiniteGlobalStartCount M L ω := by
  classical
  unfold globalStartCount infiniteGlobalStartCount
  apply Finset.sum_congr rfl
  intro x hx
  have hxUpper : x < M :=
    (Finset.mem_Ico.mp
      (by simpa only [globalStartIndices] using hx)).2
  have hcut : x + L ≤ globalCylinderCutoff M L := by
    unfold globalCylinderCutoff dyadicCutoff
    omega
  have hiff :=
    startAt_restrictToFinite_iff
      (M := globalCylinderCutoff M L) (x := x) (L := L) ω hcut
  by_cases hstart : StartEvent (infiniteValueBit ω) x L
  · simp [hstart, hiff.mpr hstart]
  · have hfinite :
        ¬ startAt
          (restrictToFinite (globalCylinderCutoff M L) ω) x L :=
      fun h => hstart (hiff.mp h)
    simp [hstart, hfinite]

/-- One atom of the source global count. -/
def infiniteGlobalStartCountEvent
    (M L k : ℕ) : Set InfiniteSample :=
  {ω | infiniteGlobalStartCount M L ω = k}

/-- The matching atom on the common finite global cylinder. -/
def finiteGlobalStartCountEvent
    (M L k : ℕ) :
    Set (SampleSpace (globalCylinderCutoff M L)) :=
  {σ | globalStartCount M L σ = k}

/-- Each source atom is the preimage of its finite-cylinder counterpart. -/
theorem infiniteGlobalStartCountEvent_eq_preimage
    (M L k : ℕ) :
    infiniteGlobalStartCountEvent M L k =
      restrictToFinite (globalCylinderCutoff M L) ⁻¹'
        finiteGlobalStartCountEvent M L k := by
  ext ω
  change
    infiniteGlobalStartCount M L ω = k ↔
      globalStartCount M L
        (restrictToFinite (globalCylinderCutoff M L) ω) = k
  exact iff_of_eq
    (congrArg (fun count => count = k)
      (globalStartCount_restrictToFinite_eq_infiniteGlobalStartCount
        M L ω)).symm

/-- Finite global-count atoms are measurable. -/
theorem measurableSet_finiteGlobalStartCountEvent
    (M L k : ℕ) :
    MeasurableSet (finiteGlobalStartCountEvent M L k) :=
  Set.toFinite (finiteGlobalStartCountEvent M L k) |>.measurableSet

/-- Source global-count atoms are measurable cylinders. -/
theorem measurableSet_infiniteGlobalStartCountEvent
    (M L k : ℕ) :
    MeasurableSet (infiniteGlobalStartCountEvent M L k) := by
  rw [infiniteGlobalStartCountEvent_eq_preimage]
  exact
    (measurable_restrictToFinite (globalCylinderCutoff M L))
      (measurableSet_finiteGlobalStartCountEvent M L k)

/-- Mass function of the literal global count under the source law. -/
noncomputable def infiniteGlobalStartLaw
    (M L k : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    (infiniteGlobalStartCountEvent M L k)).toReal

/--
The source global-count law is exactly the finite law used in Theorem 16.2.
-/
theorem infiniteGlobalStartCount_law_eq_globalStartLaw
    (M L : ℕ) :
    infiniteGlobalStartLaw M L = globalStartLaw M L := by
  funext k
  classical
  unfold infiniteGlobalStartLaw
  rw [infiniteGlobalStartCountEvent_eq_preimage,
    ← Measure.map_apply
      (measurable_restrictToFinite (globalCylinderCutoff M L))
      (measurableSet_finiteGlobalStartCountEvent M L k),
    map_infiniteRademacherMeasure_restrictToFinite]
  simp only [finiteGlobalStartCountEvent]
  rw [finiteRademacherMeasure_event_eq_uniformEventProbability,
    ENNReal.toReal_ofReal]
  · rw [← finiteUniformProbability_eq_uniformEventProbability,
      ← eventProbability_fullUniformPMF_eq]
    unfold globalStartLaw globalUniformPMF finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro ω _hω
    by_cases hcount : globalStartCount M L ω = k <;> simp [hcount]
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

/-- Source probability that the literal global count is zero. -/
noncomputable def infiniteGlobalEmptyProbability
    (M L : ℕ) : ℝ :=
  infiniteGlobalStartLaw M L 0

/-- Exact transfer of the global void probability. -/
theorem infiniteGlobalEmptyProbability_eq_globalEmptyProbability
    (M L : ℕ) :
    infiniteGlobalEmptyProbability M L = globalEmptyProbability M L := by
  unfold infiniteGlobalEmptyProbability globalEmptyProbability
  exact congrFun
    (infiniteGlobalStartCount_law_eq_globalStartLaw M L) 0

/-! ## Canonical infinite-model endpoint -/

/-- The full statement of Theorem 16.2 on the source product law. -/
def TheoremSixteenTwoInfiniteModelStatement (C : ℝ) : Prop :=
  UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L =>
        natTotalVariation
          (infiniteGlobalStartLaw M L)
          (poissonPMFReal (globalStartRate M L)))
      (fun _ _ => 1) ∧
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L => globalStartMean M L - criticalScale M L)
      criticalScale ∧
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L =>
        infiniteGlobalEmptyProbability M L -
          Real.exp (-globalStartMean M L))
      (fun _ _ => 1)

/--
Canonical Theorem 16.2 stated directly on `infiniteGlobalStartCount`.  Its
six external inputs are exactly those of the finite-cylinder canonical
endpoint.
-/
theorem theorem_sixteen_two_infinite_model
    {C : ℝ} (hC : 0 < C)
    (hpnt :
      PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS :
      LaishramShoreyInput.LaishramShoreyStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement)
    (hBS :
      BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    TheoremSixteenTwoInfiniteModelStatement C := by
  rcases theorem_sixteen_two_canonical
      hC hpnt hLS hDivisor hBS hAGG hES with
    ⟨hTV, hmean, hempty⟩
  refine ⟨?_, hmean, ?_⟩
  · change
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun M L =>
          natTotalVariation
            (globalStartLaw M L)
            (poissonPMFReal (globalStartRate M L)))
        (fun _ _ => 1) at hTV
    simpa only [infiniteGlobalStartCount_law_eq_globalStartLaw] using hTV
  · change
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun M L =>
          infiniteGlobalEmptyProbability M L -
            Real.exp (-globalStartMean M L))
        (fun _ _ => 1)
    simpa only [infiniteGlobalEmptyProbability_eq_globalEmptyProbability]
      using hempty

end

end TheoremSixteenTwo
end PaperC
