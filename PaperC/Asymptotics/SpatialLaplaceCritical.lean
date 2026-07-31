import PaperC.Analysis.SpatialMarkedParameters
import PaperC.Asymptotics.BadStartMassCritical
import PaperC.Asymptotics.DyadicKappaQuantitative
import PaperC.Asymptotics.NonterminalSectorSaving
import PaperC.Asymptotics.SteinChenCritical
import PaperC.Probability.ConditionalExpectationAverage
import PaperC.Probability.InfiniteLaplaceTransfer
import PaperC.Probability.LaplaceVoidClosure
import PaperC.Probability.PoissonLaplaceFunctional
import PaperC.Probability.SectionThirteenCouplings

set_option maxHeartbeats 3600000

/-!
# Canonical spatial Laplace convergence in the critical window

This module completes the Laplace-functional argument of Section 14.2.
The finite exponential thinning is applied conditionally on the small-prime
cylinder, averaged exactly, and then compared with the full dyadic process.
The only losses are the two averaged Stein--Chen terms, the terminal bad-start
probability mass, and the normalized cardinal of the terminal bad set.

The final theorem is stated under the unrestricted Rademacher source law and
uses only the published AGG theorem and the three source-shaped arithmetic
inputs of the canonical `κ` route.
-/

namespace PaperC
namespace SpatialLaplaceCritical

open scoped BigOperators Topology

open Filter MeasureTheory Set
open ArratiaGoldsteinGordonInput
open ConditionalAGGAverage
open ConditionalAGGInstantiation
open ConditionalExpectationAverage
open ConditionalStartProbability
open IndependentThinning
open InfiniteCylinderTransfer
open InfiniteLaplaceTransfer
open LaplaceVoidClosure
open LargePrimeDependencyGraph
open PoissonLaplaceFunctional
open SectionThirteenCouplings
open SectionThirteenFiniteBound
open SpatialMarkedParameters
open SpatialThinningFinite
open BadStartCount
open TerminalPrimeCutoff

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Conditional spatial functionals and their parameter -/

/-- Test function on the subtype of good starts. -/
def spatialGoodTest
    (N L Y : ℕ) (g : ℝ → ℝ)
    (x : {x : ℕ // x ∈ goodStarts N L Y}) : ℝ :=
  g ((x.1 : ℝ) / (N : ℝ))

/-- Conditional good-start Laplace expectation at fixed small-prime signs. -/
def conditionalGoodSpatialLaplaceExpectation
    (N L Y : ℕ) (g : ℝ → ℝ)
    (σ : SmallSample (dyadicCutoff N L) Y) : ℝ :=
  finitePMFExpectation
    (largeUniformPMF (dyadicCutoff N L) Y)
    (exponentialFunctional
      (spatialGoodTest N L Y g)
      (conditionedGoodIndicator N L Y σ))

/-- Uniform average of the conditional good-start Laplace expectations. -/
def averagedGoodSpatialLaplaceExpectation
    (N L Y : ℕ) (g : ℝ → ℝ) : ℝ :=
  finiteUniformAverage
    (conditionalGoodSpatialLaplaceExpectation N L Y g)

/-- Spatial Laplace functional after deleting the terminal bad starts. -/
def finiteGoodSpatialLaplaceFunctional
    (N L Y : ℕ) (g : ℝ → ℝ)
    (ω : SampleSpace (dyadicCutoff N L)) : ℝ :=
  Real.exp
    (-(∑ x ∈ goodStarts N L Y,
      if startAt ω x L then
        g ((x : ℝ) / (N : ℝ))
      else 0))

/-- Thinned Poisson parameter restricted to the good starts. -/
def goodSpatialThinnedParameter
    (N L Y : ℕ) (g : ℝ → ℝ) : ℝ :=
  (∑ x ∈ goodStarts N L Y,
      spatialRetention g ((x : ℝ) / (N : ℝ))) /
    (2 : ℝ) ^ L

theorem exponentialFunctional_conditionedGood_eq
    (N L Y : ℕ) (g : ℝ → ℝ)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (η : LargeSample (dyadicCutoff N L) Y) :
    exponentialFunctional
        (spatialGoodTest N L Y g)
        (conditionedGoodIndicator N L Y σ) η =
      finiteGoodSpatialLaplaceFunctional N L Y g
        (assemble (dyadicCutoff N L) Y σ η) := by
  classical
  unfold exponentialFunctional spatialGoodTest
    finiteGoodSpatialLaplaceFunctional
  congr 2
  rw [Finset.sum_subtype
    (goodStarts N L Y) (fun _x ↦ Iff.rfl)
    (fun x : ℕ ↦
      if startAt
          (assemble (dyadicCutoff N L) Y σ η) x L then
        g ((x : ℝ) / (N : ℝ))
      else 0)]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hs :
      startAt (assemble (dyadicCutoff N L) Y σ η) x.1 L
  · rw [if_pos hs, if_pos]
    exact conditionedGoodIndicator_eq_true_iff.mpr hs
  · rw [if_neg hs, if_neg]
    exact fun h ↦ hs (conditionedGoodIndicator_eq_true_iff.mp h)

/-- Exact averaging identity for the deleted-bad-start functional. -/
theorem averagedGoodSpatialLaplaceExpectation_eq_fullPMF
    (N L Y : ℕ) (g : ℝ → ℝ) :
    averagedGoodSpatialLaplaceExpectation N L Y g =
      finitePMFExpectation
        (FinitePMF.uniform (SampleSpace (dyadicCutoff N L)))
        (finiteGoodSpatialLaplaceFunctional N L Y g) := by
  unfold averagedGoodSpatialLaplaceExpectation
    conditionalGoodSpatialLaplaceExpectation
  have hobs :
      ∀ σ : SmallSample (dyadicCutoff N L) Y,
        finitePMFExpectation
            (largeUniformPMF (dyadicCutoff N L) Y)
            (exponentialFunctional
              (spatialGoodTest N L Y g)
              (conditionedGoodIndicator N L Y σ)) =
          finitePMFExpectation
            (largeUniformPMF (dyadicCutoff N L) Y)
            (fun η ↦
              finiteGoodSpatialLaplaceFunctional N L Y g
                (assemble (dyadicCutoff N L) Y σ η)) := by
    intro σ
    unfold finitePMFExpectation
    apply Finset.sum_congr rfl
    intro η _hη
    rw [exponentialFunctional_conditionedGood_eq]
  simp_rw [hobs]
  have h :=
    finiteUniformAverage_largePMFExpectation_eq_full
      (dyadicCutoff N L) Y
      (finiteGoodSpatialLaplaceFunctional N L Y g)
  exact h

/-- The finite measure integral is the uniform-PMF spatial expectation. -/
theorem finiteSpatialLaplaceExpectation_eq_fullPMF
    (N L : ℕ) (g : ℝ → ℝ) :
    finiteSpatialLaplaceExpectation (dyadicCutoff N L) N L g =
      finitePMFExpectation
        (FinitePMF.uniform (SampleSpace (dyadicCutoff N L)))
        (finiteSpatialLaplaceFunctional
          (dyadicCutoff N L) N L g) := by
  unfold finiteSpatialLaplaceExpectation
  exact
    finiteRademacherIntegral_eq_uniformPMFExpectation
      (dyadicCutoff N L)
      (finiteSpatialLaplaceFunctional
        (dyadicCutoff N L) N L g)

/-- Exact identification of the conditional thinned Poisson parameter. -/
theorem conditionalSpatialParameter_eq_good
    {N L Y : ℕ} (g : ℝ → ℝ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    (∑ x : {x : ℕ // x ∈ goodStarts N L Y},
        marginal
          (largeUniformPMF (dyadicCutoff N L) Y)
          (conditionedGoodIndicator N L Y σ) x *
        exponentialRetention (spatialGoodTest N L Y g) x) =
      goodSpatialThinnedParameter N L Y g := by
  classical
  simp_rw [marginal_conditionedGoodIndicator_eq_baseline
    hN hL hLY σ]
  unfold goodSpatialThinnedParameter spatialGoodTest
    spatialRetention exponentialRetention
  rw [Finset.sum_div]
  rw [Finset.sum_subtype
    (goodStarts N L Y) (fun _x ↦ Iff.rfl)
    (fun x : ℕ ↦
      (1 - Real.exp (-g ((x : ℝ) / (N : ℝ)))) /
        (2 : ℝ) ^ L)]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-!
## Averaged conditional thinning bound
-/

/--
After averaging over the fixed small-prime signs, the good-start spatial
Laplace functional is within `4(b₁+b₂)` of its thinned Poisson exponential.
-/
theorem abs_averagedGoodSpatialLaplace_sub_exp_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L Y : ℕ} (g : ℝ → ℝ)
    (hg0 : ∀ t, 0 ≤ g t)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    |averagedGoodSpatialLaplaceExpectation N L Y g -
        Real.exp (-goodSpatialThinnedParameter N L Y g)| ≤
      4 * (conditionalBOneAverage N L Y +
        conditionalBTwoAverage N L Y) := by
  have hpoint :
      ∀ σ : SmallSample (dyadicCutoff N L) Y,
        |conditionalGoodSpatialLaplaceExpectation N L Y g σ -
            Real.exp (-goodSpatialThinnedParameter N L Y g)| ≤
          4 *
            (bOne
                (largeUniformPMF (dyadicCutoff N L) Y)
                (conditionedGoodIndicator N L Y σ)
                (largePrimeDependencyGraph N L Y) +
              bTwo
                (largeUniformPMF (dyadicCutoff N L) Y)
                (conditionedGoodIndicator N L Y σ)
                (largePrimeDependencyGraph N L Y)) := by
    intro σ
    have hfinite :=
      abs_exponentialFunctional_sub_exp_neg_parameter_le_of_dependency
        hAGG
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ)
        (largePrimeDependencyGraph N L Y)
        (spatialGoodTest N L Y g)
        (fun x ↦ hg0 ((x.1 : ℝ) / (N : ℝ)))
        (hasExactDependencyGraph_conditionedGoodIndicator hL σ)
    rw [conditionalSpatialParameter_eq_good
      g hN hL hLY σ] at hfinite
    exact hfinite
  calc
    |averagedGoodSpatialLaplaceExpectation N L Y g -
        Real.exp (-goodSpatialThinnedParameter N L Y g)| ≤
      finiteUniformAverage
        (fun σ : SmallSample (dyadicCutoff N L) Y ↦
          |conditionalGoodSpatialLaplaceExpectation N L Y g σ -
            Real.exp (-goodSpatialThinnedParameter N L Y g)|) := by
      exact abs_finiteUniformAverage_sub_le
        (conditionalGoodSpatialLaplaceExpectation N L Y g)
        (Real.exp (-goodSpatialThinnedParameter N L Y g))
    _ ≤
      finiteUniformAverage
        (fun σ : SmallSample (dyadicCutoff N L) Y ↦
          4 *
            (bOne
                (largeUniformPMF (dyadicCutoff N L) Y)
                (conditionedGoodIndicator N L Y σ)
                (largePrimeDependencyGraph N L Y) +
              bTwo
                (largeUniformPMF (dyadicCutoff N L) Y)
                (conditionedGoodIndicator N L Y σ)
                (largePrimeDependencyGraph N L Y))) :=
      finiteUniformAverage_mono hpoint
    _ =
      4 * (conditionalBOneAverage N L Y +
        conditionalBTwoAverage N L Y) := by
      unfold conditionalBOneAverage conditionalBTwoAverage
        finiteUniformAverage
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      ring

/-!
## Restoring the terminal bad starts
-/

theorem dyadicBlock_sdiff_goodStarts_eq_terminalBadStarts
    (N L Y : ℕ) :
    dyadicBlock N \ goodStarts N L Y =
      terminalBadStarts N L Y := by
  ext x
  constructor
  · intro hx
    have hxBlock : x ∈ dyadicBlock N := (Finset.mem_sdiff.mp hx).1
    have hxNotGood : x ∉ goodStarts N L Y :=
      (Finset.mem_sdiff.mp hx).2
    by_contra hxNotBad
    exact hxNotGood (mem_goodStarts.mpr ⟨hxBlock, hxNotBad⟩)
  · intro hxBad
    exact Finset.mem_sdiff.mpr
      ⟨terminalBadStarts_subset_dyadicBlock N L Y hxBad,
        fun hxGood ↦ (mem_goodStarts.mp hxGood).2 hxBad⟩

theorem goodStarts_subset_dyadicBlock
    (N L Y : ℕ) :
    goodStarts N L Y ⊆ dyadicBlock N :=
  fun _ hx ↦ (mem_goodStarts.mp hx).1

/-- Exact deleted part of the thinned spatial parameter. -/
theorem spatialThinnedParameter_sub_good_eq_badSum
    (N L Y : ℕ) (g : ℝ → ℝ) :
    spatialThinnedParameter N L g -
        goodSpatialThinnedParameter N L Y g =
      (∑ x ∈ terminalBadStarts N L Y,
          spatialRetention g ((x : ℝ) / (N : ℝ))) /
        (2 : ℝ) ^ L := by
  let r : ℕ → ℝ :=
    fun x ↦ spatialRetention g ((x : ℝ) / (N : ℝ))
  have hpartition :
      (∑ x ∈ terminalBadStarts N L Y, r x) +
          ∑ x ∈ goodStarts N L Y, r x =
        ∑ x ∈ dyadicBlock N, r x := by
    have h :=
      Finset.sum_sdiff
        (f := r) (goodStarts_subset_dyadicBlock N L Y)
    rw [dyadicBlock_sdiff_goodStarts_eq_terminalBadStarts] at h
    exact h
  unfold spatialThinnedParameter goodSpatialThinnedParameter
  dsimp only [r] at hpartition
  calc
    (∑ x ∈ dyadicBlock N,
          spatialRetention g ((x : ℝ) / (N : ℝ))) /
          (2 : ℝ) ^ L -
        (∑ x ∈ goodStarts N L Y,
          spatialRetention g ((x : ℝ) / (N : ℝ))) /
          (2 : ℝ) ^ L =
      ((∑ x ∈ dyadicBlock N,
          spatialRetention g ((x : ℝ) / (N : ℝ))) -
        ∑ x ∈ goodStarts N L Y,
          spatialRetention g ((x : ℝ) / (N : ℝ))) /
        (2 : ℝ) ^ L := by ring
    _ =
      (∑ x ∈ terminalBadStarts N L Y,
          spatialRetention g ((x : ℝ) / (N : ℝ))) /
        (2 : ℝ) ^ L := by
      congr 1
      linarith

theorem goodSpatialThinnedParameter_nonneg
    {N L Y : ℕ} {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t) :
    0 ≤ goodSpatialThinnedParameter N L Y g := by
  unfold goodSpatialThinnedParameter
  exact div_nonneg
    (Finset.sum_nonneg fun x _hx ↦
      spatialRetention_nonneg hg0 _)
    (by positivity)

theorem goodSpatialThinnedParameter_le_full
    {N L Y : ℕ} {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t) :
    goodSpatialThinnedParameter N L Y g ≤
      spatialThinnedParameter N L g := by
  rw [← sub_nonneg]
  rw [spatialThinnedParameter_sub_good_eq_badSum]
  exact div_nonneg
    (Finset.sum_nonneg fun x _hx ↦
      spatialRetention_nonneg hg0 _)
    (by positivity)

/-- The omitted thinned parameter is bounded by the normalized bad count. -/
theorem spatialThinnedParameter_sub_good_le_badCount
    {N L Y : ℕ} (g : ℝ → ℝ)
    (hg0 : ∀ t, 0 ≤ g t) :
    spatialThinnedParameter N L g -
        goodSpatialThinnedParameter N L Y g ≤
      ((terminalBadStarts N L Y).card : ℝ) /
        (2 : ℝ) ^ L := by
  rw [spatialThinnedParameter_sub_good_eq_badSum]
  apply div_le_div_of_nonneg_right
  · calc
      (∑ x ∈ terminalBadStarts N L Y,
          spatialRetention g ((x : ℝ) / (N : ℝ))) ≤
        ∑ _x ∈ terminalBadStarts N L Y, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x _hx
          exact spatialRetention_le_one g _
      _ = ((terminalBadStarts N L Y).card : ℝ) := by
        simp
  · positivity

/-- The map `a ↦ exp(-a)` is one-Lipschitz on the nonnegative half-line,
in the ordered form needed here. -/
theorem abs_exp_neg_sub_exp_neg_le
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ b - a := by
  have hgap : 0 ≤ b - a := sub_nonneg.mpr hab
  have hmono :
      Real.exp (-b) ≤ Real.exp (-a) :=
    Real.exp_le_exp.mpr (neg_le_neg hab)
  have hfactor :
      Real.exp (-b) =
        Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfirst : Real.exp (-a) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have hsecond0 : 0 ≤ 1 - Real.exp (-(b - a)) :=
    sub_nonneg.mpr
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hgap))
  have hsecond :
      1 - Real.exp (-(b - a)) ≤ b - a := by
    linarith [Real.add_one_le_exp (-(b - a))]
  rw [abs_of_nonneg (sub_nonneg.mpr hmono), hfactor]
  calc
    Real.exp (-a) -
          Real.exp (-a) * Real.exp (-(b - a)) =
        Real.exp (-a) *
          (1 - Real.exp (-(b - a))) := by ring
    _ ≤ 1 * (1 - Real.exp (-(b - a))) :=
      mul_le_mul_of_nonneg_right hfirst hsecond0
    _ ≤ b - a := by simpa using hsecond

theorem abs_exp_neg_good_sub_full_le_badCount
    {N L Y : ℕ} (g : ℝ → ℝ)
    (hg0 : ∀ t, 0 ≤ g t) :
    |Real.exp (-goodSpatialThinnedParameter N L Y g) -
        Real.exp (-spatialThinnedParameter N L g)| ≤
      ((terminalBadStarts N L Y).card : ℝ) /
        (2 : ℝ) ^ L := by
  exact
    (abs_exp_neg_sub_exp_neg_le
      (goodSpatialThinnedParameter_nonneg hg0)
      (goodSpatialThinnedParameter_le_full hg0)).trans
        (spatialThinnedParameter_sub_good_le_badCount g hg0)

/-! ## Expectation-level restoration of the bad starts -/

/-- Number of active terminal bad starts in one complete-cylinder sample. -/
def terminalBadActiveCount
    (N L Y : ℕ)
    (ω : SampleSpace (dyadicCutoff N L)) : ℕ :=
  ∑ x ∈ terminalBadStarts N L Y,
    if startAt ω x L then 1 else 0

/--
If no terminal bad start occurs, deleting the terminal bad set does not
change the spatial Laplace functional.
-/
theorem finiteSpatialLaplaceFunctional_eq_good_of_no_bad
    {N L Y : ℕ} (g : ℝ → ℝ)
    (ω : SampleSpace (dyadicCutoff N L))
    (hno :
      ¬∃ x ∈ terminalBadStarts N L Y, startAt ω x L) :
    finiteSpatialLaplaceFunctional
        (dyadicCutoff N L) N L g ω =
      finiteGoodSpatialLaplaceFunctional N L Y g ω := by
  classical
  unfold finiteSpatialLaplaceFunctional
    finiteGoodSpatialLaplaceFunctional
  congr 2
  let f : ℕ → ℝ :=
    fun x ↦
      if startAt ω x L then
        g ((x : ℝ) / (N : ℝ))
      else 0
  have hbad :
      (∑ x ∈ terminalBadStarts N L Y, f x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    dsimp only [f]
    rw [if_neg]
    exact fun hs ↦ hno ⟨x, hx, hs⟩
  change
    (∑ x ∈ dyadicBlock N, f x) =
      ∑ x ∈ goodStarts N L Y, f x
  have hsplit :
      (∑ x ∈ goodStarts N L Y, f x) +
          (∑ x ∈ terminalBadStarts N L Y, f x) =
        ∑ x ∈ dyadicBlock N, f x := by
    have h :=
      Finset.sum_sdiff
        (f := f) (goodStarts_subset_dyadicBlock N L Y)
    rw [dyadicBlock_sdiff_goodStarts_eq_terminalBadStarts] at h
    simpa only [add_comm] using h
  linarith

/-- Every complete spatial Laplace functional lies in `[0,1]`. -/
theorem finiteSpatialLaplaceFunctional_mem_unitInterval
    {N L : ℕ} {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t)
    (ω : SampleSpace (dyadicCutoff N L)) :
    0 ≤
        finiteSpatialLaplaceFunctional
          (dyadicCutoff N L) N L g ω ∧
      finiteSpatialLaplaceFunctional
          (dyadicCutoff N L) N L g ω ≤ 1 := by
  constructor
  · exact Real.exp_nonneg _
  · unfold finiteSpatialLaplaceFunctional
    apply Real.exp_le_one_iff.mpr
    simp only [neg_nonpos]
    exact Finset.sum_nonneg fun x _ ↦ by
      split_ifs
      · exact hg0 ((x : ℝ) / (N : ℝ))
      · exact le_rfl

/-- Every deleted-bad-start spatial functional lies in `[0,1]`. -/
theorem finiteGoodSpatialLaplaceFunctional_mem_unitInterval
    {N L Y : ℕ} {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t)
    (ω : SampleSpace (dyadicCutoff N L)) :
    0 ≤ finiteGoodSpatialLaplaceFunctional N L Y g ω ∧
      finiteGoodSpatialLaplaceFunctional N L Y g ω ≤ 1 := by
  constructor
  · exact Real.exp_nonneg _
  · unfold finiteGoodSpatialLaplaceFunctional
    apply Real.exp_le_one_iff.mpr
    simp only [neg_nonpos]
    exact Finset.sum_nonneg fun x _ ↦ by
      split_ifs
      · exact hg0 ((x : ℝ) / (N : ℝ))
      · exact le_rfl

/--
Pointwise, deleting the bad starts changes the functional by at most the
number of terminal bad starts that actually occur.
-/
theorem abs_finiteSpatialLaplaceFunctional_sub_good_le_count
    {N L Y : ℕ} {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t)
    (ω : SampleSpace (dyadicCutoff N L)) :
    |finiteSpatialLaplaceFunctional
        (dyadicCutoff N L) N L g ω -
      finiteGoodSpatialLaplaceFunctional N L Y g ω| ≤
      (terminalBadActiveCount N L Y ω : ℝ) := by
  classical
  by_cases hoccurs :
      ∃ x ∈ terminalBadStarts N L Y, startAt ω x L
  · obtain ⟨x, hx, hs⟩ := hoccurs
    have hcount : 1 ≤ terminalBadActiveCount N L Y ω := by
      unfold terminalBadActiveCount
      calc
        1 =
            (if startAt ω x L then 1 else 0) := by
          rw [if_pos hs]
        _ ≤
            ∑ y ∈ terminalBadStarts N L Y,
              if startAt ω y L then 1 else 0 := by
          apply Finset.single_le_sum
            (s := terminalBadStarts N L Y)
            (f := fun y ↦ if startAt ω y L then 1 else 0)
          · intro y _hy
            split_ifs <;> omega
          · exact hx
    have hfull :=
      finiteSpatialLaplaceFunctional_mem_unitInterval hg0 ω
    have hgood :=
      finiteGoodSpatialLaplaceFunctional_mem_unitInterval
        (Y := Y) hg0 ω
    have habs :
        |finiteSpatialLaplaceFunctional
            (dyadicCutoff N L) N L g ω -
          finiteGoodSpatialLaplaceFunctional N L Y g ω| ≤ 1 := by
      exact abs_sub_le_iff.mpr
        ⟨by linarith [hfull.1, hgood.2],
          by linarith [hgood.1, hfull.2]⟩
    exact habs.trans (by exact_mod_cast hcount)
  · rw [finiteSpatialLaplaceFunctional_eq_good_of_no_bad
      g ω hoccurs, sub_self, abs_zero]
    exact Nat.cast_nonneg _

/--
Restoring all terminal bad starts costs at most their exact first-moment
probability mass.
-/
theorem abs_finiteSpatialLaplaceExpectation_sub_averagedGood_le_badMass
    {N L Y : ℕ} {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t) :
    |finiteSpatialLaplaceExpectation
        (dyadicCutoff N L) N L g -
      averagedGoodSpatialLaplaceExpectation N L Y g| ≤
      badStartProbabilityMassReal N L Y := by
  classical
  rw [finiteSpatialLaplaceExpectation_eq_fullPMF,
    averagedGoodSpatialLaplaceExpectation_eq_fullPMF]
  let μ :=
    FinitePMF.uniform (SampleSpace (dyadicCutoff N L))
  let F :=
    finiteSpatialLaplaceFunctional
      (dyadicCutoff N L) N L g
  let G :=
    finiteGoodSpatialLaplaceFunctional N L Y g
  calc
    |finitePMFExpectation μ F - finitePMFExpectation μ G| =
        |∑ ω, μ.prob ω * (F ω - G ω)| := by
      unfold finitePMFExpectation
      rw [← Finset.sum_sub_distrib]
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro ω _hω
      ring
    _ ≤ ∑ ω, |μ.prob ω * (F ω - G ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ ω, μ.prob ω *
          (terminalBadActiveCount N L Y ω : ℝ) := by
      apply Finset.sum_le_sum
      intro ω _hω
      rw [abs_mul, abs_of_nonneg (μ.nonneg ω)]
      exact mul_le_mul_of_nonneg_left
        (abs_finiteSpatialLaplaceFunctional_sub_good_le_count
          hg0 ω)
        (μ.nonneg ω)
    _ =
        ∑ x ∈ terminalBadStarts N L Y,
          eventProbability μ (fun ω ↦ startAt ω x L) := by
      unfold terminalBadActiveCount eventProbability
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro ω _hω
      by_cases h : startAt ω x L <;> simp [h]
    _ = badStartProbabilityMassReal N L Y := by
      change
        (∑ x ∈ terminalBadStarts N L Y,
          eventProbability
            (fullUniformPMF (dyadicCutoff N L))
            (fun ω ↦ startAt ω x L)) =
          badStartProbabilityMassReal N L Y
      unfold badStartProbabilityMassReal
        BadStartMass.startProbabilityMass startProbability
      simp_rw [eventProbability_fullUniformPMF_eq,
        finiteUniformProbability_eq_uniformEventProbability]
      push_cast
      apply Finset.sum_congr rfl
      intro x _hx
      rfl

/-! ## The complete finite error envelope -/

/--
Finite spatial Laplace approximation before specializing the terminal
prime cutoff.
-/
theorem abs_finiteSpatialLaplace_sub_exp_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L Y : ℕ} (g : ℝ → ℝ)
    (hg0 : ∀ t, 0 ≤ g t)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    |finiteSpatialLaplaceExpectation
        (dyadicCutoff N L) N L g -
      Real.exp (-spatialThinnedParameter N L g)| ≤
      badStartProbabilityMassReal N L Y +
        4 *
          (((SteinChenTerms.steinBOne N L Y : ℚ) : ℝ) +
            ((SteinChenTerms.steinBTwoAverage N L Y : ℚ) : ℝ)) +
        ((terminalBadStarts N L Y).card : ℝ) /
          (2 : ℝ) ^ L := by
  have hremove :=
    abs_finiteSpatialLaplaceExpectation_sub_averagedGood_le_badMass
      (N := N) (L := L) (Y := Y) hg0
  have hagg :=
    abs_averagedGoodSpatialLaplace_sub_exp_le
      hAGG g hg0 hN hL hLY
  rw [conditionalBOneAverage_eq_steinBOne hN hL hLY,
    conditionalBTwoAverage_eq_steinBTwoAverage] at hagg
  have hparameter :=
    abs_exp_neg_good_sub_full_le_badCount
      (N := N) (L := L) (Y := Y) g hg0
  have hfirst :
      |finiteSpatialLaplaceExpectation
          (dyadicCutoff N L) N L g -
        Real.exp (-goodSpatialThinnedParameter N L Y g)| ≤
        badStartProbabilityMassReal N L Y +
          4 *
            (((SteinChenTerms.steinBOne N L Y : ℚ) : ℝ) +
              ((SteinChenTerms.steinBTwoAverage N L Y : ℚ) : ℝ)) :=
    (abs_sub_le _ _ _).trans (add_le_add hremove hagg)
  exact
    (abs_sub_le _ _ _).trans
      (add_le_add hfirst hparameter)

/-- Canonical terminal-cutoff error in the spatial Laplace approximation. -/
noncomputable def spatialLaplaceError
    (N L : ℕ) : ℝ :=
  badStartProbabilityMassReal N L
      (terminalPrimeCutoff (L + 1)) +
    4 *
      (SteinChenCritical.steinBOneReal N L +
        SteinChenCritical.steinBTwoAverageReal N L) +
    ((terminalBadStarts N L
      (terminalPrimeCutoff (L + 1))).card : ℝ) /
      (2 : ℝ) ^ L

/-- Finite approximation at the literal terminal prime cutoff. -/
theorem abs_finiteSpatialLaplace_sub_exp_le_error
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L : ℕ} (g : ℝ → ℝ)
    (hg0 : ∀ t, 0 ≤ g t)
    (hN : 2 ≤ N) (hL : 0 < L) :
    |finiteSpatialLaplaceExpectation
        (dyadicCutoff N L) N L g -
      Real.exp (-spatialThinnedParameter N L g)| ≤
      spatialLaplaceError N L := by
  have hLY :
      L + 1 ≤ terminalPrimeCutoff (L + 1) :=
    window_succ_le_terminalPrimeCutoff hL le_rfl
  simpa only [spatialLaplaceError,
    SteinChenCritical.steinBOneReal,
    SteinChenCritical.steinBTwoAverageReal] using
      abs_finiteSpatialLaplace_sub_exp_le
        hAGG g hg0 hN hL hLY

/--
The complete spatial error is `o_C(1)` once the dyadic homogeneous
mother mass is `o_C(N²)`.
-/
theorem spatialLaplaceError_uniformLittleOOne_of_homogeneousMass
    {C : ℝ} (hC : 0 ≤ C) {A : ℕ}
    (hhomogeneous :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass A)
        (fun N _ ↦ (N : ℝ) ^ 2)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      spatialLaplaceError
      (fun _ _ ↦ 1) := by
  have hbad :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          badStartProbabilityMassReal N L
            (terminalPrimeCutoff (L + 1)))
        (fun _ _ ↦ 1) := by
    simpa only [badStartProbabilityMassReal,
      BadStartMassCritical.terminalBadStartProbabilityMass] using
      BadStartMassCritical.terminalBadStartProbabilityMass_uniformLittleOOne
        hC
  have hbOne :=
    SteinChenCritical.steinBOne_uniformLittleOOne hC
  have hbTwo :=
    SteinChenCritical.steinBTwoAverage_uniformLittleOOne_of_propositionElevenTwo
      hC hhomogeneous
  have hterms :=
    PropositionElevenTwo.uniformLittleOOn_add hbOne hbTwo
  have htwice :=
    PropositionElevenTwo.uniformLittleOOn_add hterms hterms
  have hfour :=
    PropositionElevenTwo.uniformLittleOOn_add htwice htwice
  have hcount :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          ((terminalBadStarts N L
            (terminalPrimeCutoff (L + 1))).card : ℝ) /
              (2 : ℝ) ^ L)
        (fun _ _ ↦ 1) :=
    TerminalBadStartsCritical.normalized_terminalBadStarts_uniformLittleOOne
      hC
  have hfirst :=
    PropositionElevenTwo.uniformLittleOOn_add hbad hfour
  have hsum :=
    PropositionElevenTwo.uniformLittleOOn_add hfirst hcount
  have heq :
      spatialLaplaceError =
        fun N L ↦
          (badStartProbabilityMassReal N L
              (terminalPrimeCutoff (L + 1)) +
            ((SteinChenCritical.steinBOneReal N L +
                SteinChenCritical.steinBTwoAverageReal N L) +
              (SteinChenCritical.steinBOneReal N L +
                SteinChenCritical.steinBTwoAverageReal N L) +
              ((SteinChenCritical.steinBOneReal N L +
                  SteinChenCritical.steinBTwoAverageReal N L) +
                (SteinChenCritical.steinBOneReal N L +
                  SteinChenCritical.steinBTwoAverageReal N L)))) +
            ((terminalBadStarts N L
              (terminalPrimeCutoff (L + 1))).card : ℝ) /
                (2 : ℝ) ^ L := by
    funext N L
    unfold spatialLaplaceError
    ring
  rw [heq]
  exact hsum

/--
Canonical `κ`-route discharge of the spatial error.  Its only external
arithmetic assumptions are Evertse--Silverman, the conductor comparison,
and the Nicolas--Robin divisor inequality.
-/
theorem spatialLaplaceError_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      spatialLaplaceError
      (fun _ _ ↦ 1) := by
  apply
    spatialLaplaceError_uniformLittleOOne_of_homogeneousMass
      hC
  exact
    NonterminalSectorSaving.uniformBigOOn_trans_uniformLittleOOn
      (DyadicKappaQuantitative.homogeneousMass_uniformBigO
        hC hES hConductor hDivisor)
      (NonterminalSectorSaving.quadraticDivLogLogSquaredScale_uniformLittleO_quadratic
        (CriticalRunWindow.InRunLengthWindow C))

/-! ## Source-law Laplace convergence -/

/-- Restriction of a uniform `o(1)` bound to a critical sequence. -/
private theorem uniformLittleOOn_tendsto_zero
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hf :
      UniformLittleOOn admissible f (fun _ _ ↦ 1))
    {N L : ℕ → ℕ}
    (hN : Tendsto N atTop atTop)
    (hadmissible : ∀ᶠ n in atTop, admissible (N n) (L n)) :
    Tendsto (fun n ↦ f (N n) (L n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Nf, hNf⟩ := hf (ε / 2) (by positivity)
  obtain ⟨nN, hnN⟩ :=
    eventually_atTop.1
      (hN.eventually (eventually_ge_atTop Nf))
  obtain ⟨na, hna⟩ := eventually_atTop.1 hadmissible
  refine ⟨max nN na, ?_⟩
  intro n hn
  have hbound :=
    hNf (N n)
      (hnN n ((le_max_left _ _).trans hn))
      (L n)
      (hna n ((le_max_right _ _).trans hn))
  rw [Real.dist_eq]
  simp only [abs_one, mul_one, sub_zero] at hbound ⊢
  exact hbound.trans_lt (by linarith)

/--
Spatial Laplace-functional convergence from the qualitative dyadic
mother-mass conclusion.
-/
theorem sectionFourteenTwo_spatialLaplaceFunctional_of_homogeneousMass
    (hAGG : ArratiaGoldsteinGordonStatement)
    {C rate : ℝ} (hC : 0 ≤ C) {A : ℕ}
    (hhomogeneous :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass A)
        (fun N _ ↦ (N : ℝ) ^ 2))
    {N L : ℕ → ℕ} {g : ℝ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hwindow :
      ∀ᶠ n in atTop,
        CriticalRunWindow.InRunLengthWindow C (N n) (L n))
    (hscale :
      Tendsto
        (fun n ↦ criticalSpatialScale (N n) (L n))
        atTop (𝓝 rate))
    (hg : ContinuousOn g (Set.Icc (1 : ℝ) 2))
    (hg0 : ∀ t, 0 ≤ g t) :
    Tendsto
      (fun n ↦
        infiniteSpatialLaplaceExpectation (N n) (L n) g)
      atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          (1 - Real.exp (-g t)))))) := by
  have herror :=
    uniformLittleOOn_tendsto_zero
      (spatialLaplaceError_uniformLittleOOne_of_homogeneousMass
        hC hhomogeneous)
      hN hwindow
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  have hvalid :
      ∀ᶠ n in atTop, 2 ≤ N n ∧ 0 < L n := by
    have hNlarge :
        ∀ᶠ n in atTop, max 2 Nwindow ≤ N n :=
      hN.eventually (eventually_ge_atTop (max 2 Nwindow))
    filter_upwards [hNlarge, hwindow] with n hn hrun
    have hw :=
      hNwindow (N n) ((le_max_right 2 Nwindow).trans hn)
        (L n) hrun
    exact
      ⟨(le_max_left 2 Nwindow).trans hn, hw.2.1⟩
  have happrox :
      ∀ᶠ n in atTop,
        |infiniteSpatialLaplaceExpectation (N n) (L n) g -
          Real.exp
            (-spatialThinnedParameter (N n) (L n) g)| ≤
          spatialLaplaceError (N n) (L n) := by
    filter_upwards [hvalid] with n hn
    rw [infiniteSpatialLaplaceExpectation_eq_finite_dyadicCutoff]
    exact
      abs_finiteSpatialLaplace_sub_exp_le_error
        hAGG g hg0 hn.1 hn.2
  exact
    PoissonLaplaceFunctional.sectionFourteenTwo_laplaceFunctional
      hN hscale hg hg0 herror happrox

/--
Section 14.2 under the canonical `κ` arithmetic route.  The source
expectation converges to the Laplace functional of the homogeneous Poisson
point process on `[1,2)`.

The signature contains AGG and only the three literature inputs
Evertse--Silverman, HK13 conductor fibres, and Nicolas--Robin.
-/
theorem sectionFourteenTwo_spatialLaplaceFunctional
    (hAGG : ArratiaGoldsteinGordonStatement)
    {C rate : ℝ} (hC : 0 ≤ C)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement)
    {N L : ℕ → ℕ} {g : ℝ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hwindow :
      ∀ᶠ n in atTop,
        CriticalRunWindow.InRunLengthWindow C (N n) (L n))
    (hscale :
      Tendsto
        (fun n ↦ criticalSpatialScale (N n) (L n))
        atTop (𝓝 rate))
    (hg : ContinuousOn g (Set.Icc (1 : ℝ) 2))
    (hg0 : ∀ t, 0 ≤ g t) :
    Tendsto
      (fun n ↦
        infiniteSpatialLaplaceExpectation (N n) (L n) g)
      atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          (1 - Real.exp (-g t)))))) := by
  apply
    sectionFourteenTwo_spatialLaplaceFunctional_of_homogeneousMass
      hAGG hC
  · exact
      NonterminalSectorSaving.uniformBigOOn_trans_uniformLittleOOn
        (DyadicKappaQuantitative.homogeneousMass_uniformBigO
          hC hES hConductor hDivisor)
        (NonterminalSectorSaving.quadraticDivLogLogSquaredScale_uniformLittleO_quadratic
          (CriticalRunWindow.InRunLengthWindow C))
  · exact hN
  · exact hwindow
  · exact hscale
  · exact hg
  · exact hg0

end

end SpatialLaplaceCritical
end PaperC
