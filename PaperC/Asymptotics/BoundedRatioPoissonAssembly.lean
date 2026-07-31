import PaperC.Asymptotics.BoundedRatioSteinChenRates
import PaperC.Asymptotics.BoundedRatioSteinChenSecondTerm
import PaperC.Asymptotics.BoundedRatioWeightedDefect

set_option maxHeartbeats 1800000

/-!
# Finite and asymptotic bounded-ratio Poisson assembly

This module completes the probabilistic bookkeeping in Lemmas 17.35--17.37.
It identifies the uniform mixture of the conditional good-start laws with
the good-start law on the full local cylinder, applies the external
Arratia--Goldstein--Gordon theorem pointwise and averages it, couples good
and full counts, and changes the matching Poisson parameter to the exact
mean of the full count.

The final asymptotic theorem is deliberately modular in the averaged second
Stein--Chen term.  Its concrete `o(1)` estimate is proved separately from the
strong finite majorant in `BoundedRatioSteinChenSecondTerm`.
-/

namespace PaperC
namespace BoundedRatioPoissonAssembly

open scoped BigOperators NNReal

open ArratiaGoldsteinGordonInput
open BoundedRatioBadStarts
open BoundedRatioSteinChen
open BoundedRatioSteinChenRates
open BoundedRatioSteinChenSecondTerm
open ConditionalAGGAverage
open ConditionalStartProbability
open FiniteCylinderCountTransport
open ProbabilityTheory
open PropositionSixteenOne
open SectionThirteenCouplings
open SectionThirteenFiniteBound
open TerminalPrimeCutoff

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Exact identification of the conditional mixture -/

/-- Conditional and full good-start counts agree under `assemble`. -/
theorem boundedConditionedGoodIndicatorSum_eq_fullGoodStartCount
    (N M L Y : ℕ)
    (σ : SmallSample (boundedRatioCutoff M L) Y)
    (η : LargeSample (boundedRatioCutoff M L) Y) :
    indicatorSum
        (boundedConditionedGoodIndicator N M L Y σ) η =
      boundedFullGoodStartCount N M L Y
        (assemble (boundedRatioCutoff M L) Y σ η) := by
  classical
  unfold indicatorSum boundedFullGoodStartCount
  rw [Finset.card_filter]
  simp only [boundedConditionedGoodIndicator_eq_true_iff]
  rw [← Finset.sum_subtype
    (boundedGoodStarts N M L Y) (fun _x ↦ Iff.rfl)
    (fun x ↦
      if startAt
          (assemble (boundedRatioCutoff M L) Y σ η) x L then
        1
      else 0)]

/--
The uniform mixture of conditional good-count laws is exactly the good-count
law on the complete bounded-ratio cylinder.
-/
theorem boundedAveragedConditionalGoodLaw_eq_boundedFullGoodStartLaw
    (N M L Y : ℕ) :
    boundedAveragedConditionalGoodLaw N M L Y =
      boundedFullGoodStartLaw N M L Y := by
  funext k
  let P : SampleSpace (boundedRatioCutoff M L) → Prop :=
    fun ω ↦ boundedFullGoodStartCount N M L Y ω = k
  have htotal :=
    finiteUniformAverage_largeEventProbability_eq_full
      (boundedRatioCutoff M L) Y P
  have hfull :
      eventProbability
          (fullUniformPMF (boundedRatioCutoff M L)) P =
        ((uniformEventProbability P : ℚ) : ℝ) := by
    rw [eventProbability_fullUniformPMF_eq,
      finiteUniformProbability_eq_uniformEventProbability]
  rw [← hfull] at htotal
  convert htotal using 1 <;>
    simp [boundedAveragedConditionalGoodLaw,
      boundedConditionalGoodLaw, indicatorSumLaw,
      boundedFullGoodStartLaw, finiteNatLaw, eventProbability,
      boundedLargeUniformPMF, P,
      boundedConditionedGoodIndicatorSum_eq_fullGoodStartCount]
  · apply congrArg finiteUniformAverage
    funext σ
    apply Finset.sum_congr rfl
    intro η _hη
    by_cases hk :
        boundedFullGoodStartCount N M L Y
          (assemble (boundedRatioCutoff M L) Y σ η) = k <;>
      simp [hk]
  · apply Finset.sum_congr rfl
    intro ω _hω
    by_cases hk : boundedFullGoodStartCount N M L Y ω = k <;>
      simp [P, hk]

/-! ## Summability and the averaged AGG estimate -/

theorem boundedConditionalGoodLaw_eq_finiteNatLaw
    (N M L Y : ℕ)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    boundedConditionalGoodLaw N M L Y σ =
      finiteNatLaw
        (boundedLargeUniformPMF M L Y)
        (indicatorSum
          (boundedConditionedGoodIndicator N M L Y σ)) := by
  funext k
  unfold boundedConditionalGoodLaw indicatorSumLaw
    finiteNatLaw eventProbability
  apply Finset.sum_congr rfl
  intro η _hη
  split_ifs <;> rfl

theorem summable_boundedConditionalGoodLaw
    (N M L Y : ℕ)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    Summable (boundedConditionalGoodLaw N M L Y σ) := by
  rw [boundedConditionalGoodLaw_eq_finiteNatLaw]
  exact summable_finiteNatLaw _ _

theorem summable_boundedCommonConditionalGoodPoissonLaw
    (N M L Y : ℕ) :
    Summable (boundedCommonConditionalGoodPoissonLaw N M L Y) :=
  (poissonPMFRealSum _).summable

theorem boundedConditionalGoodLaw_nonneg
    (N M L Y : ℕ)
    (σ : SmallSample (boundedRatioCutoff M L) Y)
    (k : ℕ) :
    0 ≤ boundedConditionalGoodLaw N M L Y σ k :=
  indicatorSumLaw_nonneg _ _ _

theorem boundedCommonConditionalGoodPoissonLaw_nonneg
    (N M L Y k : ℕ) :
    0 ≤ boundedCommonConditionalGoodPoissonLaw N M L Y k :=
  poissonPMFReal_nonneg

theorem summable_abs_boundedConditionalGoodLaw_sub_commonPoisson
    (N M L Y : ℕ)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    Summable fun k ↦
      |boundedConditionalGoodLaw N M L Y σ k -
        boundedCommonConditionalGoodPoissonLaw N M L Y k| :=
  summable_abs_sub_of_nonneg
    (summable_boundedConditionalGoodLaw N M L Y σ)
    (summable_boundedCommonConditionalGoodPoissonLaw N M L Y)
    (boundedConditionalGoodLaw_nonneg N M L Y σ)
    (boundedCommonConditionalGoodPoissonLaw_nonneg N M L Y)

/-- Pointwise conditional AGG estimate on a bounded-ratio population. -/
theorem boundedConditionalGood_natTotalVariation_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    natTotalVariation
        (boundedConditionalGoodLaw N M L Y σ)
        (boundedCommonConditionalGoodPoissonLaw N M L Y) ≤
      2 *
        (bOne
            (boundedLargeUniformPMF M L Y)
            (boundedConditionedGoodIndicator N M L Y σ)
            (boundedLargePrimeDependencyGraph N M L Y) +
          bTwo
            (boundedLargeUniformPMF M L Y)
            (boundedConditionedGoodIndicator N M L Y σ)
            (boundedLargePrimeDependencyGraph N M L Y)) := by
  have hpoint :=
    totalVariationToPoisson_le
      hAGG
      (boundedLargeUniformPMF M L Y)
      (boundedConditionedGoodIndicator N M L Y σ)
      (boundedLargePrimeDependencyGraph N M L Y)
      (hasExactDependencyGraph_boundedConditionedGoodIndicator hL σ)
  change
    natTotalVariation
        (boundedConditionalGoodLaw N M L Y σ)
        (matchingPoissonLaw
          (boundedLargeUniformPMF M L Y)
          (boundedConditionedGoodIndicator N M L Y σ)) ≤
      _ at hpoint
  rw [boundedMatchingPoissonLaw_eq_common hN hL hLY σ] at hpoint
  exact hpoint

/--
The bounded conditional mixture satisfies the averaged AGG majorant.
-/
theorem boundedAveragedConditionalGood_natTotalVariation_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (boundedAveragedConditionalGoodLaw N M L Y)
        (boundedCommonConditionalGoodPoissonLaw N M L Y) ≤
      2 *
        (finiteUniformAverage
            (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
              bOne
                (boundedLargeUniformPMF M L Y)
                (boundedConditionedGoodIndicator N M L Y σ)
                (boundedLargePrimeDependencyGraph N M L Y)) +
          boundedConditionalBTwoAverage N M L Y) := by
  let firstTerm :
      SmallSample (boundedRatioCutoff M L) Y → ℝ :=
    fun σ ↦
      bOne
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y σ)
        (boundedLargePrimeDependencyGraph N M L Y)
  let secondTerm :
      SmallSample (boundedRatioCutoff M L) Y → ℝ :=
    fun σ ↦
      bTwo
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y σ)
        (boundedLargePrimeDependencyGraph N M L Y)
  have hmixture :=
    natTotalVariation_uniformMixture_le
      (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
        boundedConditionalGoodLaw N M L Y σ)
      (boundedCommonConditionalGoodPoissonLaw N M L Y)
      (summable_abs_boundedConditionalGoodLaw_sub_commonPoisson
        N M L Y)
  have haverage :
      finiteUniformAverage
          (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
            natTotalVariation
              (boundedConditionalGoodLaw N M L Y σ)
              (boundedCommonConditionalGoodPoissonLaw N M L Y)) ≤
        finiteUniformAverage
          (fun σ ↦ 2 * (firstTerm σ + secondTerm σ)) :=
    finiteUniformAverage_mono fun σ ↦
      boundedConditionalGood_natTotalVariation_le
        hAGG hN hL hLY σ
  calc
    natTotalVariation
        (boundedAveragedConditionalGoodLaw N M L Y)
        (boundedCommonConditionalGoodPoissonLaw N M L Y) ≤
      finiteUniformAverage
        (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
          natTotalVariation
            (boundedConditionalGoodLaw N M L Y σ)
            (boundedCommonConditionalGoodPoissonLaw N M L Y)) :=
      hmixture
    _ ≤ finiteUniformAverage
        (fun σ ↦ 2 * (firstTerm σ + secondTerm σ)) :=
      haverage
    _ =
        2 *
          (finiteUniformAverage firstTerm +
            finiteUniformAverage secondTerm) := by
      unfold finiteUniformAverage
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      ring
    _ =
        2 *
          (finiteUniformAverage
              (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
                bOne
                  (boundedLargeUniformPMF M L Y)
                  (boundedConditionedGoodIndicator N M L Y σ)
                  (boundedLargePrimeDependencyGraph N M L Y)) +
            boundedConditionalBTwoAverage N M L Y) := by
      rfl

/-! ## The common first term and the exact full-count rate -/

theorem terminalBOneAverage_eq
    {N M L : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) :
    finiteUniformAverage
        (fun σ :
            SmallSample (boundedRatioCutoff M L)
              (terminalPrimeCutoff (L + 1)) ↦
          bOne
            (boundedLargeUniformPMF M L
              (terminalPrimeCutoff (L + 1)))
            (boundedConditionedGoodIndicator N M L
              (terminalPrimeCutoff (L + 1)) σ)
            (boundedLargePrimeDependencyGraph N M L
              (terminalPrimeCutoff (L + 1)))) =
      terminalBOne N M L 0 := by
  have hLY :
      L + 1 ≤ terminalPrimeCutoff (L + 1) :=
    window_succ_le_terminalPrimeCutoff hL le_rfl
  simp_rw [bOne_boundedConditionedGoodIndicator_eq_card_div
    hN hL hLY]
  rw [terminalBOne_eq_terminalBOneNumerator_div hN hL 0]
  unfold finiteUniformAverage terminalBOneNumerator
  simp

/-- Exact full-count rate on the local bounded-ratio cylinder. -/
noncomputable def boundedFullStartRate
    (N M L : ℕ) : ℝ≥0 :=
  ⟨boundedFullStartMean N M L, by
    unfold boundedFullStartMean boundedStartProbability
    exact Finset.sum_nonneg fun x _hx ↦ eventProbability_nonneg _ _⟩

theorem boundedCommonConditionalGoodPoissonRate_eq
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    ((poissonRate
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y 0) : ℝ≥0) : ℝ) =
      ((boundedGoodStarts N M L Y).card : ℝ) /
        (2 : ℝ) ^ L := by
  change
    poissonParameter
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y 0) =
      _
  exact
    poissonParameter_boundedConditionedGoodIndicator_eq
      hN hL hLY 0

theorem abs_boundedCommonGoodRate_sub_fullRate_eq_badMass
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    |((poissonRate
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y 0) : ℝ≥0) : ℝ) -
      (boundedFullStartRate N M L : ℝ)| =
        boundedBadStartProbabilityMass N M L Y := by
  rw [boundedCommonConditionalGoodPoissonRate_eq hN hL hLY]
  have hrate :
      (boundedFullStartRate N M L : ℝ) =
        boundedFullStartMean N M L := rfl
  rw [hrate]
  rw [boundedFullStartMean_eq_goodParameter_add_badMass
    hN hL hLY]
  rw [sub_add_cancel_left, abs_neg]
  unfold boundedBadStartProbabilityMass boundedStartProbability
  rw [abs_of_nonneg]
  exact Finset.sum_nonneg fun x _hx ↦ eventProbability_nonneg _ _

theorem natTotalVariation_boundedCommonGoodPoisson_fullRate_le
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (boundedCommonConditionalGoodPoissonLaw N M L Y)
        (poissonPMFReal (boundedFullStartRate N M L)) ≤
      boundedBadStartProbabilityMass N M L Y := by
  change
    natTotalVariation
        (poissonPMFReal
          (poissonRate
            (boundedLargeUniformPMF M L Y)
            (boundedConditionedGoodIndicator N M L Y 0)))
        (poissonPMFReal (boundedFullStartRate N M L)) ≤ _
  exact
    (natTotalVariation_poisson_le_abs_rate_sub _ _).trans_eq
      (abs_boundedCommonGoodRate_sub_fullRate_eq_badMass
        hN hL hLY)

/-! ## Exact finite assembly -/

/--
Finite bounded-ratio Poisson estimate.  Its right-hand side consists only of
the bad-start coupling/rate corrections and the two averaged Stein--Chen
terms.
-/
theorem natTotalVariation_boundedFullStartLaw_fullRate_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (boundedFullStartLaw N M L)
        (poissonPMFReal (boundedFullStartRate N M L)) ≤
      2 * boundedBadStartProbabilityMass N M L Y +
        2 *
          (finiteUniformAverage
              (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
                bOne
                  (boundedLargeUniformPMF M L Y)
                  (boundedConditionedGoodIndicator N M L Y σ)
                  (boundedLargePrimeDependencyGraph N M L Y)) +
            boundedConditionalBTwoAverage N M L Y) := by
  have hfullSum :
      Summable (boundedFullStartLaw N M L) :=
    summable_finiteNatLaw _ _
  have hfullNonneg :
      ∀ k, 0 ≤ boundedFullStartLaw N M L k :=
    fun k ↦ finiteNatLaw_nonneg _ _ _
  have hgoodSum :
      Summable (boundedFullGoodStartLaw N M L Y) :=
    summable_finiteNatLaw _ _
  have hgoodNonneg :
      ∀ k, 0 ≤ boundedFullGoodStartLaw N M L Y k :=
    fun k ↦ finiteNatLaw_nonneg _ _ _
  have hcommonSum :=
    summable_boundedCommonConditionalGoodPoissonLaw N M L Y
  have hcommonNonneg :
      ∀ k, 0 ≤ boundedCommonConditionalGoodPoissonLaw N M L Y k :=
    boundedCommonConditionalGoodPoissonLaw_nonneg N M L Y
  have htargetSum :
      Summable (poissonPMFReal (boundedFullStartRate N M L)) :=
    (poissonPMFRealSum _).summable
  have htargetNonneg :
      ∀ k, 0 ≤ poissonPMFReal (boundedFullStartRate N M L) k :=
    fun _k ↦ poissonPMFReal_nonneg
  have houter :=
    natTotalVariation_triangle
      hfullSum hgoodSum htargetSum
      hfullNonneg hgoodNonneg htargetNonneg
  have hinner :=
    natTotalVariation_triangle
      hgoodSum hcommonSum htargetSum
      hgoodNonneg hcommonNonneg htargetNonneg
  have hcoupling :
      natTotalVariation
          (boundedFullStartLaw N M L)
          (boundedFullGoodStartLaw N M L Y) ≤
        boundedBadStartProbabilityMass N M L Y := by
    rw [natTotalVariation_comm]
    exact natTotalVariation_boundedGood_full_le_badMass N M L Y
  have hagg :
      natTotalVariation
          (boundedFullGoodStartLaw N M L Y)
          (boundedCommonConditionalGoodPoissonLaw N M L Y) ≤
        2 *
          (finiteUniformAverage
              (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
                bOne
                  (boundedLargeUniformPMF M L Y)
                  (boundedConditionedGoodIndicator N M L Y σ)
                  (boundedLargePrimeDependencyGraph N M L Y)) +
            boundedConditionalBTwoAverage N M L Y) := by
    rw [← boundedAveragedConditionalGoodLaw_eq_boundedFullGoodStartLaw]
    exact boundedAveragedConditionalGood_natTotalVariation_le
      hAGG hN hL hLY
  have hrate :=
    natTotalVariation_boundedCommonGoodPoisson_fullRate_le
      (M := M) hN hL hLY
  linarith

/-! ## Uniform bounded-ratio closure -/

/--
Once the concrete averaged second term is `o(1)`, the complete local
bounded-ratio count is Poisson with its exact mean, uniformly in the bounded
ratio window.
-/
theorem boundedFullStartLaw_poisson_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ)
    (hAGG : ArratiaGoldsteinGordonStatement)
    (hBTwo :
      UniformLittleOOneInBoundedRatioWindow C κ₀
        (fun N M L ↦
          boundedConditionalBTwoAverage N M L
            (terminalPrimeCutoff (L + 1)))) :
    UniformLittleOOneInBoundedRatioWindow C κ₀
      (fun N M L ↦
        natTotalVariation
          (boundedFullStartLaw N M L)
          (poissonPMFReal (boundedFullStartRate N M L))) := by
  have hbad :=
    BoundedRatioWeightedDefect.boundedBadStartProbabilityMass_uniformLittleOOne
      hC κ₀
  have hbOne :=
    terminalBOne_uniformLittleOOne hC κ₀
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Nbad, hbadBound⟩ :=
    hbad (ε / 8) (by positivity)
  obtain ⟨NbOne, hbOneBound⟩ :=
    hbOne (ε / 8) (by positivity)
  obtain ⟨NbTwo, hbTwoBound⟩ :=
    hBTwo (ε / 8) (by positivity)
  refine
    ⟨max 2 (max Nwindow (max Nbad (max NbOne NbTwo))), ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2
      (max Nwindow (max Nbad (max NbOne NbTwo)))).trans hN
  have htail :
      max Nwindow (max Nbad (max NbOne NbTwo)) ≤ N :=
    (le_max_right 2
      (max Nwindow (max Nbad (max NbOne NbTwo)))).trans hN
  have hw :=
    hwindow N ((le_max_left _ _).trans htail) L hrun
  have hL : 0 < L := hw.2.1
  have hLY :
      L + 1 ≤ terminalPrimeCutoff (L + 1) :=
    window_succ_le_terminalPrimeCutoff hL le_rfl
  have hbadN :
      |boundedBadStartProbabilityMass N M L
        (terminalPrimeCutoff (L + 1))| ≤ ε / 8 :=
    hbadBound N
      ((le_max_left Nbad (max NbOne NbTwo)).trans
        ((le_max_right Nwindow
          (max Nbad (max NbOne NbTwo))).trans htail))
      M L hNM hMκ hrun
  have hbOneN :
      |terminalBOne N M L
        (0 : TerminalSmallSample M L)| ≤ ε / 8 :=
    hbOneBound N
      ((le_max_left NbOne NbTwo).trans
        ((le_max_right Nbad (max NbOne NbTwo)).trans
          ((le_max_right Nwindow
            (max Nbad (max NbOne NbTwo))).trans htail)))
      M L hNM hMκ hrun 0
  have hbTwoN :
      |boundedConditionalBTwoAverage N M L
        (terminalPrimeCutoff (L + 1))| ≤ ε / 8 :=
    hbTwoBound N
      ((le_max_right NbOne NbTwo).trans
        ((le_max_right Nbad (max NbOne NbTwo)).trans
          ((le_max_right Nwindow
            (max Nbad (max NbOne NbTwo))).trans htail)))
      M L hNM hMκ hrun
  have hfinite :=
    natTotalVariation_boundedFullStartLaw_fullRate_le
      (M := M) hAGG hNtwo hL hLY
  rw [terminalBOneAverage_eq hNtwo hL] at hfinite
  have hbadNonneg :
      0 ≤ boundedBadStartProbabilityMass N M L
        (terminalPrimeCutoff (L + 1)) := by
    unfold boundedBadStartProbabilityMass boundedStartProbability
    exact Finset.sum_nonneg fun x _hx ↦ eventProbability_nonneg _ _
  have hbOneNonneg :
      0 ≤ terminalBOne N M L
        (0 : TerminalSmallSample M L) := by
    unfold terminalBOne
    exact bOne_nonneg _ _ _
  have hbTwoNonneg :
      0 ≤ boundedConditionalBTwoAverage N M L
        (terminalPrimeCutoff (L + 1)) := by
    unfold boundedConditionalBTwoAverage
    exact div_nonneg
      (Finset.sum_nonneg fun σ _hσ ↦ bTwo_nonneg _ _ _)
      (by positivity)
  rw [abs_of_nonneg hbadNonneg] at hbadN
  rw [abs_of_nonneg hbOneNonneg] at hbOneN
  rw [abs_of_nonneg hbTwoNonneg] at hbTwoN
  rw [abs_of_nonneg
    (natTotalVariation_nonneg _ _)]
  linarith

end

end BoundedRatioPoissonAssembly
end PaperC
