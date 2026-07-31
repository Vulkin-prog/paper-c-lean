import PaperC.Asymptotics.BadStartMassCritical
import PaperC.Asymptotics.ConditionalAGGCritical
import PaperC.Probability.MaskedSteinChen
import PaperC.Probability.SectionThirteenCouplings

set_option maxHeartbeats 1200000

/-!
# Proposition 14.2: Poisson approximation under every deterministic mask

This file proves the full scalar masked Poisson statement in the literal
critical window.  A mask is implemented by replacing every good-start
indicator outside it by the constant `false`.  We retain the original
dependency graph (a harmless supergraph of the induced graph), prove its
exact Boolean-pattern dependency property directly, and bound both
Stein--Chen terms by their unmasked counterparts.

The conditional laws are then averaged over the small-prime cylinder.
On the full cylinder, deleting masked bad starts is controlled by the same
bad-start union bound as in Section 13, while the Poisson parameter changes
by at most `#D_Y / 2^L`.  Thus the final majorant is independent of the mask.

The reusable asymptotic theorem below is conditional on the published AGG
statement and one explicit homogeneous-mass estimate.  No new bridge is
introduced.
-/

namespace PaperC
namespace MaskedPoissonCritical

open scoped BigOperators NNReal

open ProbabilityTheory
open ArratiaGoldsteinGordonInput
open BadStartCount
open ConditionalAGGAverage
open ConditionalAGGInstantiation
open ConditionalDependencyGraph
open ConditionalStartProbability
open LargePrimeDependencyGraph
open MaskedSteinChen
open SectionThirteenCouplings
open SectionThirteenFiniteBound
open SteinChenTerms
open TerminalPrimeCutoff

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## The masked conditional family -/

/--
The conditioned good-start indicator, set identically to false away from
the deterministic mask.
-/
noncomputable def maskedConditionedGoodIndicator
    (N L Y : ℕ) (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    {x : ℕ // x ∈ goodStarts N L Y} →
      LargeSample (dyadicCutoff N L) Y → Bool :=
  fun x η ↦
    if x.1 ∈ mask then
      conditionedGoodIndicator N L Y σ x η
    else false

@[simp]
theorem maskedConditionedGoodIndicator_eq_true_iff
    {N L Y : ℕ} {mask : Finset ℕ}
    {σ : SmallSample (dyadicCutoff N L) Y}
    {x : {x : ℕ // x ∈ goodStarts N L Y}}
    {η : LargeSample (dyadicCutoff N L) Y} :
    maskedConditionedGoodIndicator N L Y mask σ x η = true ↔
      x.1 ∈ mask ∧
        startAt
          (assemble (dyadicCutoff N L) Y σ η) x.1 L := by
  simp [maskedConditionedGoodIndicator,
    conditionedGoodIndicator_eq_true_iff]

theorem maskedConditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates
    {N L Y : ℕ} (mask : Finset ℕ)
    (hL : 0 < L)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (x : {x : ℕ // x ∈ goodStarts N L Y})
    (η θ : LargeSample (dyadicCutoff N L) Y)
    (heq :
      ∀ q : LargePrimeCoordinate (dyadicCutoff N L) Y,
        largeCoordinatePrime q ∈
            largePrimeCoordinates x.1 L Y →
          η q = θ q) :
    maskedConditionedGoodIndicator N L Y mask σ x η =
      maskedConditionedGoodIndicator N L Y mask σ x θ := by
  unfold maskedConditionedGoodIndicator
  split_ifs
  · exact
      conditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates
        hL σ x η θ heq
  · rfl

/--
The original graph remains an exact dependency graph after deterministic
masking.  Keeping this supergraph avoids any measurable-space bookkeeping
for induced subtypes; its `b₁,b₂` terms can only be larger.
-/
theorem hasExactDependencyGraph_maskedConditionedGoodIndicator
    {N L Y : ℕ} (mask : Finset ℕ)
    (hL : 0 < L)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    HasExactDependencyGraph
      (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y mask σ)
      (largePrimeDependencyGraph N L Y) := by
  classical
  intro α value pattern
  rw [eventProbability_largeUniformPMF_eq,
    eventProbability_largeUniformPMF_eq,
    eventProbability_largeUniformPMF_eq]
  norm_cast
  let e :=
    startCoordinateSplit (dyadicCutoff N L) Y α.1 L
  let P : LargeSample (dyadicCutoff N L) Y → Prop :=
    fun η ↦
      maskedConditionedGoodIndicator N L Y mask σ α η = value
  let Q : LargeSample (dyadicCutoff N L) Y → Prop :=
    fun η ↦
      HasOutsidePattern
        (maskedConditionedGoodIndicator N L Y mask σ)
        (largePrimeDependencyGraph N L Y)
        α pattern η
  let PA :
      StartSupportSample (dyadicCutoff N L) Y α.1 L → Prop :=
    fun a ↦ P (e.symm (a, 0))
  let QB :
      StartComplementSample (dyadicCutoff N L) Y α.1 L → Prop :=
    fun b ↦ Q (e.symm (0, b))
  apply finiteUniformProbability_and_eq_mul_of_product_support
    e P Q PA QB
  · intro η
    dsimp only [P, PA]
    have hindicator :
        maskedConditionedGoodIndicator N L Y mask σ α η =
          maskedConditionedGoodIndicator N L Y mask σ α
            (e.symm ((e η).1, 0)) := by
      apply
        maskedConditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates
          mask hL σ α
      intro q hq
      dsimp only [e]
      change
        η q =
          if largeCoordinatePrime q ∈
              largePrimeCoordinates α.1 L Y then
            η q
          else 0
      rw [if_pos hq]
    rw [hindicator]
  · intro η
    dsimp only [Q, QB]
    let θ := e.symm (0, (e η).2)
    have hindicator :
        ∀ β : OutsideIndex
            (largePrimeDependencyGraph N L Y) α,
          maskedConditionedGoodIndicator N L Y mask σ β.1 η =
            maskedConditionedGoodIndicator N L Y mask σ β.1 θ := by
      intro β
      have hnotMem :
          β.1 ∉
            closedNeighborhood
              (largePrimeDependencyGraph N L Y) α :=
        β.2
      have hne : α ≠ β.1 := by
        intro h
        apply hnotMem
        rw [← h]
        exact
          self_mem_closedNeighborhood
            (largePrimeDependencyGraph N L Y) α
      have hneNat : α.1 ≠ β.1.1 := by
        intro h
        apply hne
        apply Subtype.ext
        exact h
      have hnotAdj :
          ¬(largePrimeDependencyGraph N L Y).Adj α β.1 := by
        intro hadj
        exact hnotMem
          (mem_closedNeighborhood.mpr (Or.inr hadj))
      have hnotLarge :
          ¬LargePrimeAdjacent L Y α.1 β.1.1 := by
        simpa only [largePrimeDependencyGraph_adj] using hnotAdj
      have hdisjoint :
          Disjoint
            (largePrimeCoordinates α.1 L Y)
            (largePrimeCoordinates β.1.1 L Y) :=
        disjoint_largePrimeCoordinates_of_not_adjacent
          hneNat hnotLarge
      apply
        maskedConditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates
          mask hL σ β.1
      intro q hqβ
      have hnotα :
          largeCoordinatePrime q ∉
            largePrimeCoordinates α.1 L Y := by
        intro hqα
        exact
          (Finset.disjoint_left.mp hdisjoint)
            hqα hqβ
      dsimp only [θ, e]
      change
        η q =
          if largeCoordinatePrime q ∈
              largePrimeCoordinates α.1 L Y then
            0
          else η q
      rw [if_neg hnotα]
    constructor
    · intro h β
      rw [← hindicator β]
      exact h β
    · intro h β
      rw [hindicator β]
      exact h β

/-! ## Marginals and domination of the AGG terms -/

theorem marginal_maskedConditionedGoodIndicator
    {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (x : {x : ℕ // x ∈ goodStarts N L Y}) :
    marginal
        (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask σ) x =
      if x.1 ∈ mask then (1 : ℝ) / (2 : ℝ) ^ L else 0 := by
  by_cases hx : x.1 ∈ mask
  · unfold marginal
    simp only [maskedConditionedGoodIndicator, hx, if_pos]
    exact
      marginal_conditionedGoodIndicator_eq_baseline
        hN hL hLY σ x
  · unfold marginal eventProbability
    simp [maskedConditionedGoodIndicator, hx]

theorem marginal_masked_le_unmasked
    {N L Y : ℕ} (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (x : {x : ℕ // x ∈ goodStarts N L Y}) :
    marginal
        (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask σ) x ≤
      marginal
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ) x := by
  by_cases hx : x.1 ∈ mask
  · unfold marginal
    simp only [maskedConditionedGoodIndicator, hx, if_pos]
    exact le_rfl
  · have hzero :
        marginal
            (largeUniformPMF (dyadicCutoff N L) Y)
            (maskedConditionedGoodIndicator N L Y mask σ) x = 0 := by
      unfold marginal eventProbability
      simp [maskedConditionedGoodIndicator, hx]
    rw [hzero]
    exact marginal_nonneg _ _ _

theorem jointMarginal_masked_le_unmasked
    {N L Y : ℕ} (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (x y : {x : ℕ // x ∈ goodStarts N L Y}) :
    jointMarginal
        (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask σ) x y ≤
      jointMarginal
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ) x y := by
  by_cases hx : x.1 ∈ mask
  · by_cases hy : y.1 ∈ mask
    · unfold jointMarginal
      simp only [maskedConditionedGoodIndicator, hx, hy, if_pos]
      exact le_rfl
    · have hzero :
          jointMarginal
              (largeUniformPMF (dyadicCutoff N L) Y)
              (maskedConditionedGoodIndicator N L Y mask σ) x y = 0 := by
        unfold jointMarginal eventProbability
        simp [maskedConditionedGoodIndicator, hx, hy]
      rw [hzero]
      exact jointMarginal_nonneg _ _ _ _
  · have hzero :
        jointMarginal
            (largeUniformPMF (dyadicCutoff N L) Y)
            (maskedConditionedGoodIndicator N L Y mask σ) x y = 0 := by
      unfold jointMarginal eventProbability
      simp [maskedConditionedGoodIndicator, hx]
    rw [hzero]
    exact jointMarginal_nonneg _ _ _ _

theorem bOne_masked_le_unmasked
    {N L Y : ℕ} (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    bOne
        (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask σ)
        (largePrimeDependencyGraph N L Y) ≤
      bOne
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ)
        (largePrimeDependencyGraph N L Y) := by
  unfold bOne
  apply Finset.sum_le_sum
  intro x _hx
  apply Finset.sum_le_sum
  intro y _hy
  exact mul_le_mul
    (marginal_masked_le_unmasked mask σ x)
    (marginal_masked_le_unmasked mask σ y)
    (marginal_nonneg _ _ _)
    (marginal_nonneg _ _ _)

theorem bTwo_masked_le_unmasked
    {N L Y : ℕ} (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    bTwo
        (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask σ)
        (largePrimeDependencyGraph N L Y) ≤
      bTwo
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ)
        (largePrimeDependencyGraph N L Y) := by
  unfold bTwo
  apply Finset.sum_le_sum
  intro x _hx
  apply Finset.sum_le_sum
  intro y _hy
  exact jointMarginal_masked_le_unmasked mask σ x y

/-! ## Conditional laws and uniform averaging -/

/-- Law of the masked good-start count at a fixed small-prime assignment. -/
noncomputable def maskedConditionalGoodLaw
    (N L Y : ℕ) (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) : ℕ → ℝ :=
  indicatorSumLaw
    (largeUniformPMF (dyadicCutoff N L) Y)
    (maskedConditionedGoodIndicator N L Y mask σ)

/-- Matching Poisson law, represented using the zero small-prime assignment. -/
noncomputable def maskedCommonGoodPoissonLaw
    (N L Y : ℕ) (mask : Finset ℕ) : ℕ → ℝ :=
  matchingPoissonLaw
    (largeUniformPMF (dyadicCutoff N L) Y)
    (maskedConditionedGoodIndicator N L Y mask 0)

/-- Uniform mixture over all assignments of the small-prime signs. -/
noncomputable def averagedMaskedConditionalGoodLaw
    (N L Y : ℕ) (mask : Finset ℕ) : ℕ → ℝ :=
  fun k ↦
    finiteUniformAverage
      (fun σ : SmallSample (dyadicCutoff N L) Y ↦
        maskedConditionalGoodLaw N L Y mask σ k)

/-- The matching parameter does not depend on the small-prime assignment. -/
theorem poissonParameter_maskedConditioned_eq
    {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ τ : SmallSample (dyadicCutoff N L) Y) :
    poissonParameter
        (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask σ) =
      poissonParameter
        (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask τ) := by
  unfold poissonParameter
  apply Finset.sum_congr rfl
  intro x _hx
  rw [marginal_maskedConditionedGoodIndicator
      mask hN hL hLY σ x,
    marginal_maskedConditionedGoodIndicator
      mask hN hL hLY τ x]

/-- Every fixed-cylinder matching law is the common masked Poisson law. -/
theorem matchingPoissonLaw_maskedConditioned_eq_common
    {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    matchingPoissonLaw
        (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask σ) =
      maskedCommonGoodPoissonLaw N L Y mask := by
  have hrate :
      poissonRate
          (largeUniformPMF (dyadicCutoff N L) Y)
          (maskedConditionedGoodIndicator N L Y mask σ) =
        poissonRate
          (largeUniformPMF (dyadicCutoff N L) Y)
          (maskedConditionedGoodIndicator N L Y mask 0) := by
    apply NNReal.eq
    exact poissonParameter_maskedConditioned_eq
      mask hN hL hLY σ 0
  funext k
  simp only [maskedCommonGoodPoissonLaw,
    matchingPoissonLaw, hrate]

theorem maskedConditionalGoodLaw_eq_finiteNatLaw
    (N L Y : ℕ) (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    maskedConditionalGoodLaw N L Y mask σ =
      finiteNatLaw
        (largeUniformPMF (dyadicCutoff N L) Y)
        (indicatorSum
          (maskedConditionedGoodIndicator N L Y mask σ)) := by
  funext k
  unfold maskedConditionalGoodLaw indicatorSumLaw
    finiteNatLaw eventProbability
  apply Finset.sum_congr rfl
  intro η _hη
  split_ifs <;> rfl

theorem summable_maskedConditionalGoodLaw
    (N L Y : ℕ) (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    Summable (maskedConditionalGoodLaw N L Y mask σ) := by
  rw [maskedConditionalGoodLaw_eq_finiteNatLaw]
  exact summable_finiteNatLaw _ _

theorem maskedConditionalGoodLaw_nonneg
    (N L Y : ℕ) (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) (k : ℕ) :
    0 ≤ maskedConditionalGoodLaw N L Y mask σ k :=
  indicatorSumLaw_nonneg _ _ _

theorem summable_maskedCommonGoodPoissonLaw
    (N L Y : ℕ) (mask : Finset ℕ) :
    Summable (maskedCommonGoodPoissonLaw N L Y mask) :=
  (poissonPMFRealSum _).summable

theorem maskedCommonGoodPoissonLaw_nonneg
    (N L Y : ℕ) (mask : Finset ℕ) (k : ℕ) :
    0 ≤ maskedCommonGoodPoissonLaw N L Y mask k :=
  poissonPMFReal_nonneg

theorem summable_abs_maskedConditional_sub_common
    (N L Y : ℕ) (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    Summable fun k ↦
      |maskedConditionalGoodLaw N L Y mask σ k -
        maskedCommonGoodPoissonLaw N L Y mask k| :=
  summable_abs_sub_of_nonneg
    (summable_maskedConditionalGoodLaw N L Y mask σ)
    (summable_maskedCommonGoodPoissonLaw N L Y mask)
    (maskedConditionalGoodLaw_nonneg N L Y mask σ)
    (maskedCommonGoodPoissonLaw_nonneg N L Y mask)

/--
Pointwise conditional AGG estimate, already enlarged to the unmasked
conditional `b₁+b₂`.
-/
theorem maskedConditionalGood_natTotalVariation_le_unmaskedTerms
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    natTotalVariation
        (maskedConditionalGoodLaw N L Y mask σ)
        (maskedCommonGoodPoissonLaw N L Y mask) ≤
      2 *
        (bOne
            (largeUniformPMF (dyadicCutoff N L) Y)
            (conditionedGoodIndicator N L Y σ)
            (largePrimeDependencyGraph N L Y) +
          bTwo
            (largeUniformPMF (dyadicCutoff N L) Y)
            (conditionedGoodIndicator N L Y σ)
            (largePrimeDependencyGraph N L Y)) := by
  have hpoint :=
    totalVariationToPoisson_le
      hAGG
      (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y mask σ)
      (largePrimeDependencyGraph N L Y)
      (hasExactDependencyGraph_maskedConditionedGoodIndicator
        mask hL σ)
  change
    natTotalVariation
        (maskedConditionalGoodLaw N L Y mask σ)
        (matchingPoissonLaw
          (largeUniformPMF (dyadicCutoff N L) Y)
          (maskedConditionedGoodIndicator N L Y mask σ)) ≤
      _ at hpoint
  rw [matchingPoissonLaw_maskedConditioned_eq_common
    mask hN hL hLY σ] at hpoint
  calc
    natTotalVariation
        (maskedConditionalGoodLaw N L Y mask σ)
        (maskedCommonGoodPoissonLaw N L Y mask) ≤
      2 *
        (bOne
            (largeUniformPMF (dyadicCutoff N L) Y)
            (maskedConditionedGoodIndicator N L Y mask σ)
            (largePrimeDependencyGraph N L Y) +
          bTwo
            (largeUniformPMF (dyadicCutoff N L) Y)
            (maskedConditionedGoodIndicator N L Y mask σ)
            (largePrimeDependencyGraph N L Y)) := hpoint
    _ ≤
      2 *
        (bOne
            (largeUniformPMF (dyadicCutoff N L) Y)
            (conditionedGoodIndicator N L Y σ)
            (largePrimeDependencyGraph N L Y) +
          bTwo
            (largeUniformPMF (dyadicCutoff N L) Y)
            (conditionedGoodIndicator N L Y σ)
            (largePrimeDependencyGraph N L Y)) := by
      gcongr
      · exact bOne_masked_le_unmasked mask σ
      · exact bTwo_masked_le_unmasked mask σ

/--
Averaging the pointwise estimate gives exactly the unmasked average
Stein--Chen envelope, uniformly in the mask.
-/
theorem averagedMaskedConditionalGood_natTotalVariation_le_steinTerms
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (averagedMaskedConditionalGoodLaw N L Y mask)
        (maskedCommonGoodPoissonLaw N L Y mask) ≤
      2 *
        (((steinBOne N L Y : ℚ) : ℝ) +
          ((steinBTwoAverage N L Y : ℚ) : ℝ)) := by
  let firstTerm :
      SmallSample (dyadicCutoff N L) Y → ℝ :=
    fun σ ↦
      bOne
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ)
        (largePrimeDependencyGraph N L Y)
  let secondTerm :
      SmallSample (dyadicCutoff N L) Y → ℝ :=
    fun σ ↦
      bTwo
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ)
        (largePrimeDependencyGraph N L Y)
  have hmixture :=
    natTotalVariation_uniformMixture_le
      (fun σ : SmallSample (dyadicCutoff N L) Y ↦
        maskedConditionalGoodLaw N L Y mask σ)
      (maskedCommonGoodPoissonLaw N L Y mask)
      (summable_abs_maskedConditional_sub_common N L Y mask)
  have haverage :
      finiteUniformAverage
          (fun σ : SmallSample (dyadicCutoff N L) Y ↦
            natTotalVariation
              (maskedConditionalGoodLaw N L Y mask σ)
              (maskedCommonGoodPoissonLaw N L Y mask)) ≤
        finiteUniformAverage
          (fun σ ↦ 2 * (firstTerm σ + secondTerm σ)) :=
    finiteUniformAverage_mono fun σ ↦
      maskedConditionalGood_natTotalVariation_le_unmaskedTerms
        hAGG mask hN hL hLY σ
  calc
    natTotalVariation
        (averagedMaskedConditionalGoodLaw N L Y mask)
        (maskedCommonGoodPoissonLaw N L Y mask) ≤
      finiteUniformAverage
        (fun σ : SmallSample (dyadicCutoff N L) Y ↦
          natTotalVariation
            (maskedConditionalGoodLaw N L Y mask σ)
            (maskedCommonGoodPoissonLaw N L Y mask)) := hmixture
    _ ≤
      finiteUniformAverage
        (fun σ ↦ 2 * (firstTerm σ + secondTerm σ)) :=
      haverage
    _ =
        2 *
          (conditionalBOneAverage N L Y +
            conditionalBTwoAverage N L Y) := by
      unfold conditionalBOneAverage conditionalBTwoAverage
      dsimp only [firstTerm, secondTerm]
      unfold finiteUniformAverage
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      ring
    _ =
        2 *
          (((steinBOne N L Y : ℚ) : ℝ) +
            ((steinBTwoAverage N L Y : ℚ) : ℝ)) := by
      rw [conditionalBOneAverage_eq_steinBOne hN hL hLY,
        conditionalBTwoAverage_eq_steinBTwoAverage]

/-! ## Exact masked Poisson parameters -/

/-- Closed form of the common masked conditional rate. -/
theorem maskedCommonGoodPoissonRate_eq
    {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    ((poissonRate
        (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask 0) : ℝ≥0) : ℝ) =
      ((maskedGoodStarts N L Y mask).card : ℝ) /
        (2 : ℝ) ^ L := by
  change
    (∑ x,
      marginal
        (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask 0) x) =
      ((maskedGoodStarts N L Y mask).card : ℝ) / (2 : ℝ) ^ L
  simp_rw [marginal_maskedConditionedGoodIndicator
    mask hN hL hLY 0]
  rw [← Finset.sum_subtype
    (goodStarts N L Y)
    (fun _x ↦ Iff.rfl)
    (fun x ↦
      if x ∈ mask then (1 : ℝ) / (2 : ℝ) ^ L else 0)]
  rw [← Finset.sum_filter]
  have hfilter :
      (goodStarts N L Y).filter (fun x ↦ x ∈ mask) =
        maskedGoodStarts N L Y mask := by
    ext x
    simp [maskedGoodStarts, and_comm]
  rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Target rate `|A_N|2⁻ᴸ` for an arbitrary deterministic mask. -/
noncomputable def maskedTargetPoissonRate
    (L : ℕ) (mask : Finset ℕ) : ℝ≥0 :=
  ⟨(mask.card : ℝ) / (2 : ℝ) ^ L, by positivity⟩

/-- Poisson law at the masked target rate. -/
noncomputable def maskedTargetPoissonLaw
    (L : ℕ) (mask : Finset ℕ) : ℕ → ℝ :=
  poissonPMFReal (maskedTargetPoissonRate L mask)

/--
Exact rate loss caused by deleting the masked terminal bad starts.
-/
theorem abs_maskedCommonRate_sub_targetRate_eq
    {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    |((poissonRate
        (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask 0) : ℝ≥0) : ℝ) -
      (maskedTargetPoissonRate L mask : ℝ)| =
        ((maskedTerminalBadStarts N L Y mask).card : ℝ) /
          (2 : ℝ) ^ L := by
  rw [maskedCommonGoodPoissonRate_eq mask hN hL hLY]
  change
    |((maskedGoodStarts N L Y mask).card : ℝ) / (2 : ℝ) ^ L -
        (mask.card : ℝ) / (2 : ℝ) ^ L| =
      ((maskedTerminalBadStarts N L Y mask).card : ℝ) / (2 : ℝ) ^ L
  have hcard :
      ((maskedGoodStarts N L Y mask).card : ℝ) +
          ((maskedTerminalBadStarts N L Y mask).card : ℝ) =
        (mask.card : ℝ) := by
    exact_mod_cast
      card_maskedGood_add_card_bad
        (N := N) (L := L) (Y := Y) hmask
  have heq :
      ((maskedGoodStarts N L Y mask).card : ℝ) /
            (2 : ℝ) ^ L -
          (mask.card : ℝ) / (2 : ℝ) ^ L =
        -(((maskedTerminalBadStarts N L Y mask).card : ℝ) /
          (2 : ℝ) ^ L) := by
    field_simp
    linarith
  rw [heq, abs_neg, abs_of_nonneg]
  positivity

/-- Uniform full-block bound for the masked parameter coupling. -/
theorem natTotalVariation_maskedCommon_target_le_badCount
    {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (maskedCommonGoodPoissonLaw N L Y mask)
        (maskedTargetPoissonLaw L mask) ≤
      ((terminalBadStarts N L Y).card : ℝ) /
        (2 : ℝ) ^ L := by
  have hbase :
      natTotalVariation
          (maskedCommonGoodPoissonLaw N L Y mask)
          (maskedTargetPoissonLaw L mask) ≤
        ((maskedTerminalBadStarts N L Y mask).card : ℝ) /
          (2 : ℝ) ^ L := by
    change
      natTotalVariation
          (poissonPMFReal
            (poissonRate
              (largeUniformPMF (dyadicCutoff N L) Y)
              (maskedConditionedGoodIndicator N L Y mask 0)))
          (poissonPMFReal (maskedTargetPoissonRate L mask)) ≤ _
    exact
      (natTotalVariation_poisson_le_abs_rate_sub _ _).trans_eq
        (abs_maskedCommonRate_sub_targetRate_eq
          hmask hN hL hLY)
  exact hbase.trans (by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast
        card_maskedTerminalBadStarts_le N L Y mask
    · positivity)

/-! ## Identification with the complete cylinder -/

/-- Masked good indicators viewed on the complete prime cylinder. -/
noncomputable def fullMaskedGoodIndicator
    (N L Y : ℕ) (mask : Finset ℕ) :
    {x : ℕ // x ∈ goodStarts N L Y} →
      SampleSpace (dyadicCutoff N L) → Bool :=
  fun x ω ↦
    if x.1 ∈ mask then fullGoodIndicator N L Y x ω else false

@[simp]
theorem fullMaskedGoodIndicator_eq_true_iff
    {N L Y : ℕ} {mask : Finset ℕ}
    {x : {x : ℕ // x ∈ goodStarts N L Y}}
    {ω : SampleSpace (dyadicCutoff N L)} :
    fullMaskedGoodIndicator N L Y mask x ω = true ↔
      x.1 ∈ mask ∧ startAt ω x.1 L := by
  simp [fullMaskedGoodIndicator,
    fullGoodIndicator_eq_true_iff]

/-- Number of masked good starts on the full cylinder. -/
noncomputable def fullMaskedGoodStartCount
    (N L Y : ℕ) (mask : Finset ℕ)
    (ω : SampleSpace (dyadicCutoff N L)) : ℕ :=
  indicatorSum (fullMaskedGoodIndicator N L Y mask) ω

/-- Law of the masked good-start count on the full cylinder. -/
noncomputable def fullMaskedGoodStartLaw
    (N L Y : ℕ) (mask : Finset ℕ) : ℕ → ℝ :=
  indicatorSumLaw
    (fullUniformPMF (dyadicCutoff N L))
    (fullMaskedGoodIndicator N L Y mask)

theorem fullMaskedGoodStartLaw_eq_finiteNatLaw
    (N L Y : ℕ) (mask : Finset ℕ) :
    fullMaskedGoodStartLaw N L Y mask =
      finiteNatLaw
        (fullUniformPMF (dyadicCutoff N L))
        (fullMaskedGoodStartCount N L Y mask) := by
  funext k
  unfold fullMaskedGoodStartLaw indicatorSumLaw
    finiteNatLaw eventProbability fullMaskedGoodStartCount
  apply Finset.sum_congr rfl
  intro ω _hω
  split_ifs <;> rfl

/-- The conditional and full masked counts agree under `assemble`. -/
theorem conditionedMaskedIndicatorSum_eq_fullMaskedGoodStartCount
    (N L Y : ℕ) (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (η : LargeSample (dyadicCutoff N L) Y) :
    indicatorSum (maskedConditionedGoodIndicator N L Y mask σ) η =
      fullMaskedGoodStartCount N L Y mask
        (assemble (dyadicCutoff N L) Y σ η) := by
  classical
  unfold indicatorSum fullMaskedGoodStartCount
    fullMaskedGoodIndicator maskedConditionedGoodIndicator
    fullGoodIndicator conditionedGoodIndicator
  rfl

/--
The uniform mixture of conditional masked laws is the full-cylinder masked
good law.
-/
theorem averagedMaskedConditionalGoodLaw_eq_fullMaskedGoodStartLaw
    (N L Y : ℕ) (mask : Finset ℕ) :
    averagedMaskedConditionalGoodLaw N L Y mask =
      fullMaskedGoodStartLaw N L Y mask := by
  classical
  rw [fullMaskedGoodStartLaw_eq_finiteNatLaw]
  funext k
  let P : SampleSpace (dyadicCutoff N L) → Prop :=
    fun ω ↦ fullMaskedGoodStartCount N L Y mask ω = k
  have htotal :=
    finiteUniformAverage_largeEventProbability_eq_full
      (dyadicCutoff N L) Y P
  have hfull :
      eventProbability
          (fullUniformPMF (dyadicCutoff N L)) P =
        ((uniformEventProbability P : ℚ) : ℝ) := by
    rw [eventProbability_fullUniformPMF_eq,
      finiteUniformProbability_eq_uniformEventProbability]
  rw [← hfull] at htotal
  have hfinite :
      finiteNatLaw
          (fullUniformPMF (dyadicCutoff N L))
          (fullMaskedGoodStartCount N L Y mask) k =
        eventProbability
          (fullUniformPMF (dyadicCutoff N L)) P := by
    unfold finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro ω _hω
    by_cases hk : fullMaskedGoodStartCount N L Y mask ω = k <;>
      simp [P, hk]
  rw [hfinite]
  simpa only [averagedMaskedConditionalGoodLaw,
    maskedConditionalGoodLaw, indicatorSumLaw,
    P,
    conditionedMaskedIndicatorSum_eq_fullMaskedGoodStartCount] using htotal

/-! ## Coupling the good and complete masked counts -/

/-- Literal masked start count on the complete cylinder. -/
noncomputable def fullMaskedDyadicCount
    (N L : ℕ) (mask : Finset ℕ)
    (ω : SampleSpace (dyadicCutoff N L)) : ℕ :=
  ∑ x ∈ mask, if startAt ω x L then 1 else 0

/-- Law of the complete masked start count. -/
noncomputable def fullMaskedDyadicStartLaw
    (N L : ℕ) (mask : Finset ℕ) : ℕ → ℝ :=
  finiteNatLaw
    (fullUniformPMF (dyadicCutoff N L))
    (fullMaskedDyadicCount N L mask)

/-- The good masked count is a literal sum over `A_N \ D_Y`. -/
theorem fullMaskedGoodStartCount_eq_sum
    {N L Y : ℕ} {mask : Finset ℕ}
    (ω : SampleSpace (dyadicCutoff N L)) :
    fullMaskedGoodStartCount N L Y mask ω =
      ∑ x ∈ maskedGoodStarts N L Y mask,
        if startAt ω x L then 1 else 0 := by
  classical
  unfold fullMaskedGoodStartCount indicatorSum
  rw [Finset.card_filter]
  simp only [fullMaskedGoodIndicator_eq_true_iff]
  have hsubtype :
      (∑ x : {x : ℕ // x ∈ goodStarts N L Y},
          if x.1 ∈ mask ∧ startAt ω x.1 L then 1 else 0) =
        ∑ x ∈ goodStarts N L Y,
          if x ∈ mask ∧ startAt ω x L then 1 else 0 := by
    rw [← Finset.sum_subtype
      (goodStarts N L Y)
      (fun _x ↦ Iff.rfl)
      (fun x ↦
        if x ∈ mask ∧ startAt ω x L then 1 else 0)]
  rw [hsubtype]
  have hgoodMask :
      (goodStarts N L Y).filter (fun x ↦ x ∈ mask) =
        maskedGoodStarts N L Y mask := by
    ext x
    simp [maskedGoodStarts, and_comm]
  rw [← hgoodMask]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hm : x ∈ mask <;>
    simp [hm]

/--
If the good and complete masked counts disagree, some terminal bad start
occurs.  The conclusion is deliberately enlarged to the full bad set.
-/
theorem exists_bad_start_of_fullMaskedGood_ne_fullMaskedDyadic
    {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N)
    {ω : SampleSpace (dyadicCutoff N L)}
    (hne :
      fullMaskedGoodStartCount N L Y mask ω ≠
        fullMaskedDyadicCount N L mask ω) :
    ∃ x ∈ terminalBadStarts N L Y, startAt ω x L := by
  classical
  by_contra h
  push Not at h
  apply hne
  rw [fullMaskedGoodStartCount_eq_sum]
  unfold fullMaskedDyadicCount
  rw [maskedGoodStarts_eq_sdiff hmask]
  apply Finset.sum_subset Finset.sdiff_subset
  intro x hxMask hxNotGood
  have hxBad : x ∈ terminalBadStarts N L Y := by
    by_contra hxNotBad
    exact hxNotGood
      (Finset.mem_sdiff.mpr ⟨hxMask, hxNotBad⟩)
  rw [if_neg (h x hxBad)]

/-- Disagreement probability is bounded by the unmasked bad-start mass. -/
theorem disagreementProbability_fullMaskedGood_dyadic_le_badMass
    {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    disagreementProbability
        (fullUniformPMF (dyadicCutoff N L))
        (fullMaskedGoodStartCount N L Y mask)
        (fullMaskedDyadicCount N L mask) ≤
      badStartProbabilityMassReal N L Y := by
  classical
  have hpoint :
      ∀ ω : SampleSpace (dyadicCutoff N L),
        (if fullMaskedGoodStartCount N L Y mask ω ≠
              fullMaskedDyadicCount N L mask ω then
            (fullUniformPMF (dyadicCutoff N L)).prob ω
          else 0) ≤
          ∑ x ∈ terminalBadStarts N L Y,
            if startAt ω x L then
              (fullUniformPMF (dyadicCutoff N L)).prob ω
            else 0 := by
    intro ω
    by_cases hne :
        fullMaskedGoodStartCount N L Y mask ω ≠
          fullMaskedDyadicCount N L mask ω
    · rw [if_pos hne]
      obtain ⟨x, hxBad, hxStart⟩ :=
        exists_bad_start_of_fullMaskedGood_ne_fullMaskedDyadic
          hmask hne
      calc
        (fullUniformPMF (dyadicCutoff N L)).prob ω =
            (if startAt ω x L then
              (fullUniformPMF (dyadicCutoff N L)).prob ω
            else 0) := by rw [if_pos hxStart]
        _ ≤
            ∑ y ∈ terminalBadStarts N L Y,
              if startAt ω y L then
                (fullUniformPMF (dyadicCutoff N L)).prob ω
              else 0 := by
          apply Finset.single_le_sum
            (s := terminalBadStarts N L Y)
            (f := fun y ↦
              if startAt ω y L then
                (fullUniformPMF (dyadicCutoff N L)).prob ω
              else 0)
          · intro y _hy
            split_ifs
            · exact
                (fullUniformPMF
                  (dyadicCutoff N L)).nonneg ω
            · exact le_rfl
          · exact hxBad
    · rw [if_neg hne]
      exact Finset.sum_nonneg fun x _hx ↦ by
        split_ifs
        · exact
            (fullUniformPMF
              (dyadicCutoff N L)).nonneg ω
        · exact le_rfl
  have hsum :
      (∑ ω,
        if fullMaskedGoodStartCount N L Y mask ω ≠
              fullMaskedDyadicCount N L mask ω then
          (fullUniformPMF (dyadicCutoff N L)).prob ω
        else 0) ≤
        ∑ ω, ∑ x ∈ terminalBadStarts N L Y,
          if startAt ω x L then
            (fullUniformPMF (dyadicCutoff N L)).prob ω
          else 0 :=
    Finset.sum_le_sum fun ω _hω ↦ hpoint ω
  unfold disagreementProbability
  calc
    (∑ ω,
        if fullMaskedGoodStartCount N L Y mask ω ≠
              fullMaskedDyadicCount N L mask ω then
          (fullUniformPMF (dyadicCutoff N L)).prob ω
        else 0) ≤
      ∑ ω, ∑ x ∈ terminalBadStarts N L Y,
        if startAt ω x L then
          (fullUniformPMF (dyadicCutoff N L)).prob ω
        else 0 := hsum
    _ =
        ∑ x ∈ terminalBadStarts N L Y,
          eventProbability
            (fullUniformPMF (dyadicCutoff N L))
            (fun ω ↦ startAt ω x L) := by
      rw [Finset.sum_comm]
      rfl
    _ =
        badStartProbabilityMassReal N L Y := by
      unfold badStartProbabilityMassReal
        BadStartMass.startProbabilityMass startProbability
      simp_rw [eventProbability_fullUniformPMF_eq,
        finiteUniformProbability_eq_uniformEventProbability]
      push_cast
      apply Finset.sum_congr rfl
      intro x _hx
      rfl

/-- Removing bad starts from a masked count costs no more than in the block. -/
theorem natTotalVariation_averagedMaskedGood_fullMasked_le_badMass
    {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    natTotalVariation
        (averagedMaskedConditionalGoodLaw N L Y mask)
        (fullMaskedDyadicStartLaw N L mask) ≤
      badStartProbabilityMassReal N L Y := by
  rw [averagedMaskedConditionalGoodLaw_eq_fullMaskedGoodStartLaw]
  rw [fullMaskedGoodStartLaw_eq_finiteNatLaw]
  exact
    (natTotalVariation_finiteNatLaw_le_disagreement
      (fullUniformPMF (dyadicCutoff N L))
      (fullMaskedGoodStartCount N L Y mask)
      (fullMaskedDyadicCount N L mask)).trans
        (disagreementProbability_fullMaskedGood_dyadic_le_badMass
          hmask)

/-! ## Finite and critical-window assemblies -/

/--
The complete finite masked estimate.  Its right-hand side is identical to
the unmasked Section 13 envelope and hence independent of `mask`.
-/
theorem natTotalVariation_fullMasked_target_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (fullMaskedDyadicStartLaw N L mask)
        (maskedTargetPoissonLaw L mask) ≤
      badStartProbabilityMassReal N L Y +
        2 *
          (((steinBOne N L Y : ℚ) : ℝ) +
            ((steinBTwoAverage N L Y : ℚ) : ℝ)) +
        ((terminalBadStarts N L Y).card : ℝ) /
          (2 : ℝ) ^ L := by
  have hfullSum :
      Summable (fullMaskedDyadicStartLaw N L mask) := by
    unfold fullMaskedDyadicStartLaw
    exact summable_finiteNatLaw _ _
  have hfullNonneg :
      ∀ k, 0 ≤ fullMaskedDyadicStartLaw N L mask k := by
    intro k
    unfold fullMaskedDyadicStartLaw
    exact finiteNatLaw_nonneg _ _ _
  have havgSum :
      Summable (averagedMaskedConditionalGoodLaw N L Y mask) := by
    rw [averagedMaskedConditionalGoodLaw_eq_fullMaskedGoodStartLaw,
      fullMaskedGoodStartLaw_eq_finiteNatLaw]
    exact summable_finiteNatLaw _ _
  have havgNonneg :
      ∀ k, 0 ≤ averagedMaskedConditionalGoodLaw N L Y mask k := by
    intro k
    rw [averagedMaskedConditionalGoodLaw_eq_fullMaskedGoodStartLaw,
      fullMaskedGoodStartLaw_eq_finiteNatLaw]
    exact finiteNatLaw_nonneg _ _ _
  have hcommonSum :
      Summable (maskedCommonGoodPoissonLaw N L Y mask) :=
    summable_maskedCommonGoodPoissonLaw N L Y mask
  have hcommonNonneg :
      ∀ k, 0 ≤ maskedCommonGoodPoissonLaw N L Y mask k :=
    maskedCommonGoodPoissonLaw_nonneg N L Y mask
  have htargetSum :
      Summable (maskedTargetPoissonLaw L mask) := by
    unfold maskedTargetPoissonLaw
    exact (poissonPMFRealSum _).summable
  have htargetNonneg :
      ∀ k, 0 ≤ maskedTargetPoissonLaw L mask k := by
    intro k
    exact poissonPMFReal_nonneg
  have houter :=
    natTotalVariation_triangle
      hfullSum havgSum htargetSum
      hfullNonneg havgNonneg htargetNonneg
  have hinner :=
    natTotalVariation_triangle
      havgSum hcommonSum htargetSum
      havgNonneg hcommonNonneg htargetNonneg
  have hbad :
      natTotalVariation
          (fullMaskedDyadicStartLaw N L mask)
          (averagedMaskedConditionalGoodLaw N L Y mask) ≤
        badStartProbabilityMassReal N L Y := by
    rw [natTotalVariation_comm]
    exact
      natTotalVariation_averagedMaskedGood_fullMasked_le_badMass
        hmask
  have hagg :=
    averagedMaskedConditionalGood_natTotalVariation_le_steinTerms
      hAGG mask hN hL hLY
  have hparameter :=
    natTotalVariation_maskedCommon_target_le_badCount
      hmask hN hL hLY
  linarith

/-- Total variation appearing in Proposition 14.2 for one mask. -/
noncomputable def maskedPoissonTotalVariation
    (N L : ℕ) (mask : Finset ℕ) : ℝ :=
  natTotalVariation
    (fullMaskedDyadicStartLaw N L mask)
    (maskedTargetPoissonLaw L mask)

theorem maskedPoissonTotalVariation_nonneg
    (N L : ℕ) (mask : Finset ℕ) :
    0 ≤ maskedPoissonTotalVariation N L mask :=
  natTotalVariation_nonneg _ _

/--
Proposition 14.2, with the supremum over masks written as its exact uniform
quantifier:

for every `ε>0`, all sufficiently large critical `(N,L)` and every
deterministic `mask ⊆ I_N` have total-variation error at most `ε`.

The arithmetic hypothesis is only the qualitative mother-mass conclusion
`R₂=o(N²)`, allowing the canonical `κ` route to reuse this proof.
-/
theorem maskedPoissonTotalVariation_uniformLittleOOne_of_homogeneousMass
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG : ArratiaGoldsteinGordonStatement)
    {A : ℕ}
    (hhomogeneous :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass A)
        (fun N _ ↦ (N : ℝ) ^ 2)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ L : ℕ, CriticalRunWindow.InRunLengthWindow C N L →
          ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
            maskedPoissonTotalVariation N L mask ≤ ε := by
  let terminalY : ℕ → ℕ :=
    fun L ↦ terminalPrimeCutoff (L + 1)
  have hbad :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦ badStartProbabilityMassReal N L (terminalY L))
        (fun _ _ ↦ 1) := by
    change
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        BadStartMassCritical.terminalBadStartProbabilityMass
        (fun _ _ ↦ 1)
    exact
      BadStartMassCritical.terminalBadStartProbabilityMass_uniformLittleOOne hC
  have hbOne :=
    SteinChenCritical.steinBOne_uniformLittleOOne hC
  have hbTwo :=
    SteinChenCritical.steinBTwoAverage_uniformLittleOOne_of_propositionElevenTwo
      hC hhomogeneous
  have hterms :=
    PropositionElevenTwo.uniformLittleOOn_add hbOne hbTwo
  have hcount :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          ((terminalBadStarts N L (terminalY L)).card : ℝ) /
            (2 : ℝ) ^ L)
        (fun _ _ ↦ 1) := by
    simpa only [terminalY] using
      TerminalBadStartsCritical.normalized_terminalBadStarts_uniformLittleOOne
        hC
  have hsum₁ :=
    PropositionElevenTwo.uniformLittleOOn_add hbad hterms
  have hsum₂ :=
    PropositionElevenTwo.uniformLittleOOn_add hsum₁ hterms
  have hsum :=
    PropositionElevenTwo.uniformLittleOOn_add hsum₂ hcount
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Nsum, hsumBound⟩ := hsum ε hε
  refine ⟨max 2 (max Nwindow Nsum), ?_⟩
  intro N hN L hrun mask hmask
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nwindow Nsum)).trans hN
  have htail :
      max Nwindow Nsum ≤ N :=
    (le_max_right 2 (max Nwindow Nsum)).trans hN
  have hw :=
    hwindow N ((le_max_left Nwindow Nsum).trans htail)
      L hrun
  have hL : 0 < L := hw.2.1
  have hLY :
      L + 1 ≤ terminalY L := by
    dsimp only [terminalY]
    exact window_succ_le_terminalPrimeCutoff hL le_rfl
  have hfinite :=
    natTotalVariation_fullMasked_target_le
      hAGG hmask hNtwo hL hLY
  have hsmall :=
    hsumBound N
      ((le_max_right Nwindow Nsum).trans htail)
      L hrun
  change
    maskedPoissonTotalVariation N L mask ≤ ε
  change
    natTotalVariation
        (fullMaskedDyadicStartLaw N L mask)
        (maskedTargetPoissonLaw L mask) ≤ ε
  calc
    natTotalVariation
        (fullMaskedDyadicStartLaw N L mask)
        (maskedTargetPoissonLaw L mask) ≤
      badStartProbabilityMassReal N L (terminalY L) +
        2 *
          (SteinChenCritical.steinBOneReal N L +
            SteinChenCritical.steinBTwoAverageReal N L) +
        ((terminalBadStarts N L (terminalY L)).card : ℝ) /
          (2 : ℝ) ^ L := by
      simpa only [terminalY, SteinChenCritical.steinBOneReal,
        SteinChenCritical.steinBTwoAverageReal] using hfinite
    _ =
      (badStartProbabilityMassReal N L (terminalY L) +
          (SteinChenCritical.steinBOneReal N L +
            SteinChenCritical.steinBTwoAverageReal N L)) +
        (SteinChenCritical.steinBOneReal N L +
          SteinChenCritical.steinBTwoAverageReal N L) +
        ((terminalBadStarts N L (terminalY L)).card : ℝ) /
          (2 : ℝ) ^ L := by ring
    _ ≤
      |(badStartProbabilityMassReal N L (terminalY L) +
          (SteinChenCritical.steinBOneReal N L +
            SteinChenCritical.steinBTwoAverageReal N L)) +
        (SteinChenCritical.steinBOneReal N L +
          SteinChenCritical.steinBTwoAverageReal N L) +
        ((terminalBadStarts N L (terminalY L)).card : ℝ) /
          (2 : ℝ) ^ L| :=
      le_abs_self _
    _ ≤ ε := by
      simpa only [abs_one, mul_one] using hsmall

end

end MaskedPoissonCritical
end PaperC
