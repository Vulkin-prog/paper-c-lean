import PaperC.Asymptotics.ExactLengthBadStartMassCritical
import PaperC.Asymptotics.MarkedSteinChenCritical
import PaperC.Probability.MarkedLaplaceFiniteClosure
import PaperC.Probability.PoissonLaplaceFunctional

set_option maxHeartbeats 1800000

/-!
# Critical marked Laplace-functional convergence

This module closes the fixed-mark-cutoff Laplace argument of §14.4 under the
literal source law.

For a fixed `E`, the complete marked functional is compared with the family
obtained by deleting `D(L+E+1)`.  The three approximation terms are:

* the removed exact-length mass of Lemma 14.8;
* the marked first Stein--Chen term;
* the averaged marked second Stein--Chen term.

The retained Poisson parameter has the same limit as the complete parameter:
their difference is bounded by
`(E+1) 2^E · #D(L+E+1)/2^(L+E+1)`.

The endpoint is convergence of the exact source Laplace expectation to the
Laplace functional of the marked Poisson process, which is the
point-process characterization available without introducing a separate
topology-of-point-measures API.
-/

namespace PaperC
namespace MarkedLaplaceCritical

open scoped BigOperators Topology

open Filter MeasureTheory Set
open ExactLengthBadStartMassCritical
open InfiniteExactLengthProbabilityTransfer
open InfiniteLaplaceTransfer
open MarkedLaplaceFiniteClosure
open MarkedSteinChenCritical
open MarkedSteinChenTerms
open PoissonLaplaceFunctional
open SpatialMarkedParameters

noncomputable section

/-- Real form of the averaged marked second AGG term. -/
def markedBTwoAverageReal (E N L : ℕ) : ℝ :=
  ((markedBTwoAverage N L E : ℚ) : ℝ)

/-- Real form of the sharp local/separated marked second-term envelope. -/
def markedBTwoSplitReal (E N L : ℕ) : ℝ :=
  ((markedBTwoSplitEnvelope N L E : ℚ) : ℝ)

theorem markedBTwoAverageReal_nonneg (E N L : ℕ) :
    0 ≤ markedBTwoAverageReal E N L := by
  unfold markedBTwoAverageReal markedBTwoAverage
  apply Rat.cast_nonneg.mpr
  exact Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ by
      unfold MixedLengthAffine.mixedExactLengthProbability
        uniformEventProbability
      positivity

theorem markedBTwoSplitReal_nonneg (E N L : ℕ) :
    0 ≤ markedBTwoSplitReal E N L := by
  classical
  unfold markedBTwoSplitReal markedBTwoSplitEnvelope
  apply Rat.cast_nonneg.mpr
  exact Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ by
      split_ifs <;> positivity

/--
The sharp split-envelope estimate implies the concrete estimate on the
actual averaged `b₂`.
-/
theorem markedBTwoAverageReal_uniformLittleOOne_of_split
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ)
    (hSplit :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (markedBTwoSplitReal E)
        (fun _ _ ↦ 1)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (markedBTwoAverageReal E)
      (fun _ _ ↦ 1) := by
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Nsplit, hNsplit⟩ := hSplit ε hε
  refine ⟨max Nwindow Nsplit, ?_⟩
  intro N hN L hrun
  have hL : 1 ≤ L := by
    have hw :=
      hwindow N ((le_max_left _ _).trans hN) L hrun
    exact Nat.succ_le_iff.mpr hw.2.1
  have hfinite :=
    MarkedSteinChenTerms.markedBTwoAverage_le_splitEnvelope
      (N := N) (L := L) (E := E) hL
  have hfiniteReal :
      markedBTwoAverageReal E N L ≤
        markedBTwoSplitReal E N L :=
    Rat.cast_le.mpr hfinite
  have hsplit :=
    hNsplit N ((le_max_right _ _).trans hN) L hrun
  simp only [abs_one, mul_one,
    abs_of_nonneg (markedBTwoAverageReal_nonneg E N L)] at hsplit ⊢
  rw [abs_of_nonneg (markedBTwoSplitReal_nonneg E N L)] at hsplit
  exact hfiniteReal.trans hsplit

/--
Canonical arithmetic discharge of the sharp marked split envelope.

This is the literal identification between the real envelope used by the
Laplace closure and the one estimated in `MarkedSteinChenCritical`.
-/
theorem markedBTwoSplitReal_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (markedBTwoSplitReal E)
      (fun _ _ ↦ 1) := by
  change UniformLittleOOn
    (CriticalRunWindow.InRunLengthWindow C)
    (fun N L ↦ ((markedBTwoSplitEnvelope N L E : ℚ) : ℝ))
    (fun _ _ ↦ 1)
  exact
    MarkedSteinChenCritical.markedBTwoSplitEnvelopeReal_uniformLittleOOne
      hC E hES hPell

/--
A uniform `o(1)` estimate restricts to every critical sequence whose first
coordinate tends to infinity.
-/
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
Exact identification of the source expectation with the full uniform PMF
expectation on the common marked cylinder.
-/
theorem infiniteMarkedLaplaceExpectation_eq_uniformPMFExpectation
    (N L E : ℕ) (g : ℝ → ℕ → ℝ) :
    infiniteMarkedLaplaceExpectation N L E g =
      IndependentThinning.finitePMFExpectation
        (FinitePMF.uniform
          (SampleSpace
            (MarkedConditionalDependencyGraph.markedCylinderCutoff
              N L E)))
        (finiteMarkedLaplaceFunctional
          (MarkedConditionalDependencyGraph.markedCylinderCutoff N L E)
          N L E g) := by
  rw [infiniteMarkedLaplaceExpectation_eq_finite_dyadicCutoff]
  unfold finiteMarkedLaplaceExpectation
  rw [ConditionalExpectationAverage.finiteRademacherIntegral_eq_uniformPMFExpectation]
  rfl

/--
The removed parameter envelope tends to zero along every critical sequence.
-/
theorem removedMarkedParameterEnvelope_tendsto_zero
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ)
    {N L : ℕ → ℕ}
    (hN : Tendsto N atTop atTop)
    (hwindow :
      ∀ᶠ n in atTop,
        CriticalRunWindow.InRunLengthWindow C (N n) (L n)) :
    Tendsto
      (fun n ↦ removedMarkedParameterEnvelope E (N n) (L n))
      atTop (𝓝 0) := by
  have hcount :=
    uniformLittleOOn_tendsto_zero
      (commonNormalizedRemovedCountContribution_uniformLittleOOne hC E)
      hN hwindow
  have hmul :=
    hcount.const_mul ((E + 1 : ℝ) * (2 : ℝ) ^ E)
  simpa only [removedMarkedParameterEnvelope,
    commonNormalizedRemovedCountContribution, mul_zero] using hmul

/--
The retained marked parameter has the same Poisson/Riemann-sum limit as the
complete parameter.
-/
theorem tendsto_retainedMarkedThinnedParameter
    {C rate : ℝ} (hC : 0 ≤ C) {E : ℕ}
    {N L : ℕ → ℕ} {g : ℝ → ℕ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hwindow :
      ∀ᶠ n in atTop,
        CriticalRunWindow.InRunLengthWindow C (N n) (L n))
    (hscale :
      Tendsto
        (fun n ↦ criticalSpatialScale (N n) (L n))
        atTop (𝓝 rate))
    (hg :
      ∀ e ≤ E,
        ContinuousOn (fun t ↦ g t e) (Set.Icc (1 : ℝ) 2))
    (hg0 : ∀ t e, 0 ≤ g t e) :
    Tendsto
      (fun n ↦ retainedMarkedThinnedParameter (N n) (L n) E g)
      atTop
      (𝓝 (rate * ∫ t in Set.Ico (1 : ℝ) 2,
        markedRetentionIntegrand E g t)) := by
  have hfull :=
    tendsto_markedThinnedParameter hN hscale hg
  have henvelope :=
    removedMarkedParameterEnvelope_tendsto_zero hC E hN hwindow
  have habs :
      Tendsto
        (fun n ↦
          |markedThinnedParameter (N n) (L n) E g -
            retainedMarkedThinnedParameter (N n) (L n) E g|)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ ↦ abs_nonneg _
    · exact Eventually.of_forall fun n ↦
        abs_markedThinnedParameter_sub_retained_le_envelope
          (N := N n) (L := L n) (E := E) hg0
    · exact henvelope
  have hdiff :
      Tendsto
        (fun n ↦
          markedThinnedParameter (N n) (L n) E g -
            retainedMarkedThinnedParameter (N n) (L n) E g)
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hret := hfull.sub hdiff
  convert hret using 1
  · funext n
    ring
  · ring

/--
Source marked Laplace-functional convergence for fixed `E`, under the
literal concrete `o(1)` estimate for the averaged marked second AGG term.
-/
theorem sectionFourteenFour_laplaceFunctional_of_bTwo
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C rate : ℝ} (hC : 0 ≤ C) {E : ℕ}
    {N L : ℕ → ℕ} {g : ℝ → ℕ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hwindow :
      ∀ᶠ n in atTop,
        CriticalRunWindow.InRunLengthWindow C (N n) (L n))
    (hscale :
      Tendsto
        (fun n ↦ criticalSpatialScale (N n) (L n))
        atTop (𝓝 rate))
    (hg :
      ∀ e ≤ E,
        ContinuousOn (fun t ↦ g t e) (Set.Icc (1 : ℝ) 2))
    (hg0 : ∀ t e, 0 ≤ g t e)
    (hBTwo :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (markedBTwoAverageReal E)
        (fun _ _ ↦ 1)) :
    Tendsto
      (fun n ↦
        infiniteMarkedLaplaceExpectation (N n) (L n) E g)
      atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          ∑ e ∈ Finset.range (E + 1),
            (1 / (2 : ℝ) ^ (e + 1)) *
              (1 - Real.exp (-g t e)))))) := by
  have hparameter :=
    tendsto_retainedMarkedThinnedParameter
      hC hN hwindow hscale hg hg0
  have hremoved :=
    uniformLittleOOn_tendsto_zero
      (lemma_fourteen_seven hC E) hN hwindow
  have hbOne :=
    uniformLittleOOn_tendsto_zero
      (markedBOneReal_uniformLittleOOne hC E) hN hwindow
  have hbTwo :=
    uniformLittleOOn_tendsto_zero hBTwo hN hwindow
  let error : ℕ → ℝ :=
    fun n ↦
      totalRemovedInfiniteExactLengthProbability (N n) (L n) E +
        4 *
          (markedBOneReal E (N n) (L n) +
            markedBTwoAverageReal E (N n) (L n))
  have herror : Tendsto error atTop (𝓝 0) := by
    dsimp only [error]
    simpa only [totalRemovedInfiniteExactLengthProbability, mul_add,
      mul_comm, Nat.add_comm, zero_add, add_zero, zero_mul, mul_zero] using
      hremoved.add ((hbOne.add hbTwo).const_mul 4)
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  have hvalid :
      ∀ᶠ n in atTop, 2 ≤ N n ∧ 1 ≤ L n := by
    have hNlarge :
        ∀ᶠ n in atTop, max 2 Nwindow ≤ N n :=
      hN.eventually (eventually_ge_atTop (max 2 Nwindow))
    filter_upwards [hNlarge, hwindow] with n hn hrun
    have hw :=
      hNwindow (N n) ((le_max_right 2 Nwindow).trans hn)
        (L n) hrun
    exact
      ⟨(le_max_left 2 Nwindow).trans hn,
        Nat.succ_le_iff.mpr hw.2.1⟩
  have happrox :
      ∀ᶠ n in atTop,
        |infiniteMarkedLaplaceExpectation (N n) (L n) E g -
          Real.exp
            (-retainedMarkedThinnedParameter (N n) (L n) E g)| ≤
          error n := by
    filter_upwards [hvalid] with n hn
    rw [infiniteMarkedLaplaceExpectation_eq_uniformPMFExpectation]
    simpa only [error, markedBOneReal, markedBTwoAverageReal] using
      fullMarkedLaplace_le_retainedPoisson
        (N := N n) (L := L n) (E := E)
        hAGG hn.1 hn.2 g hg0
  have hlimit :=
    tendsto_laplace_of_parameter_and_error hparameter herror happrox
  simpa only [markedRetentionIntegrand, geometricMarkWeight,
    spatialRetention] using hlimit

/--
Variant of the fixed-`E` endpoint whose only second-term premise is the
sharp local/separated split envelope.
-/
theorem sectionFourteenFour_laplaceFunctional_of_split
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C rate : ℝ} (hC : 0 ≤ C) {E : ℕ}
    {N L : ℕ → ℕ} {g : ℝ → ℕ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hwindow :
      ∀ᶠ n in atTop,
        CriticalRunWindow.InRunLengthWindow C (N n) (L n))
    (hscale :
      Tendsto
        (fun n ↦ criticalSpatialScale (N n) (L n))
        atTop (𝓝 rate))
    (hg :
      ∀ e ≤ E,
        ContinuousOn (fun t ↦ g t e) (Set.Icc (1 : ℝ) 2))
    (hg0 : ∀ t e, 0 ≤ g t e)
    (hSplit :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (markedBTwoSplitReal E)
        (fun _ _ ↦ 1)) :
    Tendsto
      (fun n ↦
        infiniteMarkedLaplaceExpectation (N n) (L n) E g)
      atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          ∑ e ∈ Finset.range (E + 1),
            (1 / (2 : ℝ) ^ (e + 1)) *
              (1 - Real.exp (-g t e)))))) :=
  sectionFourteenFour_laplaceFunctional_of_bTwo
    hAGG hC hN hwindow hscale hg hg0
    (markedBTwoAverageReal_uniformLittleOOne_of_split hC E hSplit)

/--
Section 14.4 under the canonical `κ` arithmetic route.

The source marked Laplace expectation converges for every fixed mark cutoff.
The signature contains AGG and only the three literature inputs
Evertse--Silverman, the HK13 conductor comparison, and the Nicolas--Robin
divisor inequality.
-/
theorem sectionFourteenFour_laplaceFunctional
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C rate : ℝ} (hC : 0 ≤ C) {E : ℕ}
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement)
    {N L : ℕ → ℕ} {g : ℝ → ℕ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hwindow :
      ∀ᶠ n in atTop,
        CriticalRunWindow.InRunLengthWindow C (N n) (L n))
    (hscale :
      Tendsto
        (fun n ↦ criticalSpatialScale (N n) (L n))
        atTop (𝓝 rate))
    (hg :
      ∀ e ≤ E,
        ContinuousOn (fun t ↦ g t e) (Set.Icc (1 : ℝ) 2))
    (hg0 : ∀ t e, 0 ≤ g t e) :
    Tendsto
      (fun n ↦
        infiniteMarkedLaplaceExpectation (N n) (L n) E g)
      atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          ∑ e ∈ Finset.range (E + 1),
            (1 / (2 : ℝ) ^ (e + 1)) *
              (1 - Real.exp (-g t e)))))) := by
  apply
    sectionFourteenFour_laplaceFunctional_of_split
      hAGG hC hN hwindow hscale hg hg0
  exact
    markedBTwoSplitReal_uniformLittleOOne hC E hES
      (PellInput.generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound
        hConductor hDivisor)

end

end MarkedLaplaceCritical
end PaperC
