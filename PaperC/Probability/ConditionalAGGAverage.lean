import PaperC.Probability.ConditionalAGGInstantiation
import PaperC.Probability.SectionThirteenFiniteBound

set_option maxHeartbeats 1200000

/-!
# Averaging the conditional Arratia--Goldstein--Gordon bound

This module performs the finite averaging step following the pointwise
conditional AGG estimate.  The fixed small-prime assignment ranges over its
literal finite uniform cylinder.  Exact conditional marginals make the
matching Poisson law and the first Stein--Chen term independent of that
assignment.

The final subsection isolates the only remaining identification needed for
the second term: the finite law-of-total-probability equality between the
average conditional joint marginal and the unconditional joint start
probability.
-/

namespace PaperC
namespace ConditionalAGGAverage

open scoped BigOperators NNReal

open ProbabilityTheory
open ArratiaGoldsteinGordonInput
open ConditionalAGGInstantiation
open ConditionalDependencyGraph
open ConditionalStartProbability
open LargePrimeDependencyGraph
open SectionThirteenFiniteBound
open SectionTwelveMoments
open SteinChenTerms

noncomputable section

/-! ## Conditional laws and their finite averages -/

/-- Law of the good-start count after fixing the small-prime assignment. -/
noncomputable def conditionalGoodLaw
    (N L Y : ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    ℕ → ℝ :=
  indicatorSumLaw
    (largeUniformPMF (dyadicCutoff N L) Y)
    (conditionedGoodIndicator N L Y σ)

/--
The common matching Poisson law, represented using the zero small-prime
assignment.  Exact conditional marginals show below that every assignment
has this same matching law.
-/
noncomputable def commonConditionalGoodPoissonLaw
    (N L Y : ℕ) : ℕ → ℝ :=
  matchingPoissonLaw
    (largeUniformPMF (dyadicCutoff N L) Y)
    (conditionedGoodIndicator N L Y 0)

/-- Uniform mixture of the conditional good-start count laws. -/
noncomputable def averagedConditionalGoodLaw
    (N L Y : ℕ) : ℕ → ℝ :=
  fun k ↦
    finiteUniformAverage
      (fun σ : SmallSample (dyadicCutoff N L) Y ↦
        conditionalGoodLaw N L Y σ k)

/-- Uniform average of the first conditional Stein--Chen term. -/
noncomputable def conditionalBOneAverage
    (N L Y : ℕ) : ℝ :=
  finiteUniformAverage
    (fun σ : SmallSample (dyadicCutoff N L) Y ↦
      bOne
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ)
        (largePrimeDependencyGraph N L Y))

/-- Uniform average of the second conditional Stein--Chen term. -/
noncomputable def conditionalBTwoAverage
    (N L Y : ℕ) : ℝ :=
  finiteUniformAverage
    (fun σ : SmallSample (dyadicCutoff N L) Y ↦
      bTwo
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ)
        (largePrimeDependencyGraph N L Y))

/-- Uniform averaging is monotone for a nonempty finite index type. -/
theorem finiteUniformAverage_mono
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {f g : ι → ℝ}
    (hfg : ∀ i, f i ≤ g i) :
    finiteUniformAverage f ≤ finiteUniformAverage g := by
  unfold finiteUniformAverage
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun i _hi ↦ hfg i
  · positivity

/-! ## Common parameter and summability -/

/--
The Poisson parameter is independent of the fixed small-prime assignment.
-/
theorem poissonParameter_conditionedGoodIndicator_eq
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ τ : SmallSample (dyadicCutoff N L) Y) :
    poissonParameter
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ) =
      poissonParameter
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y τ) := by
  unfold poissonParameter
  apply Finset.sum_congr rfl
  intro x _hx
  rw [marginal_conditionedGoodIndicator_eq_baseline
      hN hL hLY σ x,
    marginal_conditionedGoodIndicator_eq_baseline
      hN hL hLY τ x]

/-- Every conditional matching Poisson law is the common one. -/
theorem matchingPoissonLaw_conditionedGoodIndicator_eq_common
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    matchingPoissonLaw
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ) =
      commonConditionalGoodPoissonLaw N L Y := by
  have hrate :
      poissonRate
          (largeUniformPMF (dyadicCutoff N L) Y)
          (conditionedGoodIndicator N L Y σ) =
        poissonRate
          (largeUniformPMF (dyadicCutoff N L) Y)
          (conditionedGoodIndicator N L Y 0) := by
    apply NNReal.eq
    exact poissonParameter_conditionedGoodIndicator_eq
      hN hL hLY σ 0
  funext k
  simp only [commonConditionalGoodPoissonLaw, matchingPoissonLaw, hrate]

/-- A conditional good-start count law is a finite pushforward law. -/
theorem conditionalGoodLaw_eq_finiteNatLaw
    (N L Y : ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    conditionalGoodLaw N L Y σ =
      finiteNatLaw
        (largeUniformPMF (dyadicCutoff N L) Y)
        (indicatorSum (conditionedGoodIndicator N L Y σ)) := by
  funext k
  unfold conditionalGoodLaw indicatorSumLaw finiteNatLaw eventProbability
  apply Finset.sum_congr rfl
  intro ω _hω
  split_ifs <;> rfl

/-- Every conditional good-start count law is summable. -/
theorem summable_conditionalGoodLaw
    (N L Y : ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    Summable (conditionalGoodLaw N L Y σ) := by
  rw [conditionalGoodLaw_eq_finiteNatLaw]
  exact summable_finiteNatLaw _ _

/-- The common Poisson law is summable. -/
theorem summable_commonConditionalGoodPoissonLaw
    (N L Y : ℕ) :
    Summable (commonConditionalGoodPoissonLaw N L Y) :=
  (poissonPMFRealSum _).summable

/-- The common Poisson law is pointwise nonnegative. -/
theorem commonConditionalGoodPoissonLaw_nonneg
    (N L Y k : ℕ) :
    0 ≤ commonConditionalGoodPoissonLaw N L Y k :=
  poissonPMFReal_nonneg

/-- Conditional good-start count laws are pointwise nonnegative. -/
theorem conditionalGoodLaw_nonneg
    (N L Y : ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (k : ℕ) :
    0 ≤ conditionalGoodLaw N L Y σ k :=
  indicatorSumLaw_nonneg _ _ _

/-- The half-`ℓ¹` distance used in the mixture step is summable. -/
theorem summable_abs_conditionalGoodLaw_sub_commonPoisson
    (N L Y : ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    Summable fun k ↦
      |conditionalGoodLaw N L Y σ k -
        commonConditionalGoodPoissonLaw N L Y k| :=
  summable_abs_sub_of_nonneg
    (summable_conditionalGoodLaw N L Y σ)
    (summable_commonConditionalGoodPoissonLaw N L Y)
    (conditionalGoodLaw_nonneg N L Y σ)
    (commonConditionalGoodPoissonLaw_nonneg N L Y)

/-! ## Pointwise and averaged AGG estimates -/

/-- Pointwise AGG estimate with the common Poisson law substituted. -/
theorem conditionalGood_natTotalVariation_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    natTotalVariation
        (conditionalGoodLaw N L Y σ)
        (commonConditionalGoodPoissonLaw N L Y) ≤
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
    conditionalGood_totalVariationToPoisson_le hAGG hL σ
  change
    natTotalVariation
        (conditionalGoodLaw N L Y σ)
        (matchingPoissonLaw
          (largeUniformPMF (dyadicCutoff N L) Y)
          (conditionedGoodIndicator N L Y σ)) ≤
      _ at hpoint
  rw [matchingPoissonLaw_conditionedGoodIndicator_eq_common
    hN hL hLY σ] at hpoint
  exact hpoint

/--
The uniform mixture satisfies the average conditional AGG majorant.
-/
theorem averagedConditionalGood_natTotalVariation_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (averagedConditionalGoodLaw N L Y)
        (commonConditionalGoodPoissonLaw N L Y) ≤
      2 *
        (conditionalBOneAverage N L Y +
          conditionalBTwoAverage N L Y) := by
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
        conditionalGoodLaw N L Y σ)
      (commonConditionalGoodPoissonLaw N L Y)
      (summable_abs_conditionalGoodLaw_sub_commonPoisson N L Y)
  have haverage :
      finiteUniformAverage
          (fun σ : SmallSample (dyadicCutoff N L) Y ↦
            natTotalVariation
              (conditionalGoodLaw N L Y σ)
              (commonConditionalGoodPoissonLaw N L Y)) ≤
        finiteUniformAverage
          (fun σ ↦ 2 * (firstTerm σ + secondTerm σ)) :=
    finiteUniformAverage_mono fun σ ↦
      conditionalGood_natTotalVariation_le
        hAGG hN hL hLY σ
  calc
    natTotalVariation
        (averagedConditionalGoodLaw N L Y)
        (commonConditionalGoodPoissonLaw N L Y) ≤
      finiteUniformAverage
        (fun σ : SmallSample (dyadicCutoff N L) Y ↦
          natTotalVariation
            (conditionalGoodLaw N L Y σ)
            (commonConditionalGoodPoissonLaw N L Y)) := hmixture
    _ ≤ finiteUniformAverage
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

/-! ## Identification of the first conditional term -/

/--
Membership in the closed graph neighborhood is the same as membership of
the underlying ordered natural-number pair in `closedDependencyPairs`.
-/
theorem pair_mem_closedDependencyPairs_iff
    {N L Y : ℕ}
    (α β : {x : ℕ // x ∈ goodStarts N L Y}) :
    (α.1, β.1) ∈ closedDependencyPairs N L Y ↔
      β ∈
        closedNeighborhood
          (largePrimeDependencyGraph N L Y) α := by
  rw [mem_closedDependencyPairs, mem_closedNeighborhood]
  constructor
  · rintro (hdiag | hedge)
    · exact Or.inl (Subtype.ext hdiag.2.symm)
    · exact Or.inr
        (mem_orderedDependencyEdges.mp hedge).2.2
  · rintro (rfl | hadj)
    · exact Or.inl ⟨β.2, rfl⟩
    · exact Or.inr
        (mem_orderedDependencyEdges.mpr
          ⟨α.2, β.2, hadj⟩)

/-- Dependent type of ordered closed-neighborhood pairs. -/
abbrev ClosedNeighborhoodPair (N L Y : ℕ) :=
  Σ α : {x : ℕ // x ∈ goodStarts N L Y},
    {β : {x : ℕ // x ∈ goodStarts N L Y} //
      β ∈
        closedNeighborhood
          (largePrimeDependencyGraph N L Y) α}

/--
Closed-neighborhood pairs in the subtype graph are canonically the natural
pairs counted by `SteinChenTerms.closedDependencyPairs`.
-/
noncomputable def closedNeighborhoodPairEquiv
    (N L Y : ℕ) :
    ClosedNeighborhoodPair N L Y ≃
      {pair : ℕ × ℕ //
        pair ∈ closedDependencyPairs N L Y} := by
  classical
  let toPair :
      ClosedNeighborhoodPair N L Y →
        {pair : ℕ × ℕ //
          pair ∈ closedDependencyPairs N L Y} :=
    fun pair ↦
      ⟨(pair.1.1, pair.2.1.1),
        (pair_mem_closedDependencyPairs_iff
          pair.1 pair.2.1).mpr pair.2.2⟩
  let fromPair :
      {pair : ℕ × ℕ //
        pair ∈ closedDependencyPairs N L Y} →
        ClosedNeighborhoodPair N L Y :=
    fun pair ↦ by
      have hmem :=
        mem_closedDependencyPairs.mp pair.2
      have hx : pair.1.1 ∈ goodStarts N L Y := by
        rcases hmem with hdiag | hedge
        · exact hdiag.1
        · exact (mem_orderedDependencyEdges.mp hedge).1
      have hy : pair.1.2 ∈ goodStarts N L Y := by
        rcases hmem with hdiag | hedge
        · rw [← hdiag.2]
          exact hdiag.1
        · exact (mem_orderedDependencyEdges.mp hedge).2.1
      let α : {x : ℕ // x ∈ goodStarts N L Y} :=
        ⟨pair.1.1, hx⟩
      let β : {x : ℕ // x ∈ goodStarts N L Y} :=
        ⟨pair.1.2, hy⟩
      exact
        ⟨α,
          ⟨β,
            (pair_mem_closedDependencyPairs_iff α β).mp
              pair.2⟩⟩
  exact
    { toFun := toPair
      invFun := fromPair
      left_inv := by
        intro pair
        have hfst :
            (fromPair (toPair pair)).1 = pair.1 := by
          apply Subtype.ext
          rfl
        apply Sigma.ext hfst
        cases hfst
        apply heq_of_eq
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro pair
        apply Subtype.ext
        rfl }

/-- Exact count of all closed graph neighborhoods. -/
theorem sum_card_closedNeighborhood_eq
    (N L Y : ℕ) :
    (∑ α : {x : ℕ // x ∈ goodStarts N L Y},
        (closedNeighborhood
          (largePrimeDependencyGraph N L Y) α).card) =
      (closedDependencyPairs N L Y).card := by
  calc
    (∑ α : {x : ℕ // x ∈ goodStarts N L Y},
        (closedNeighborhood
          (largePrimeDependencyGraph N L Y) α).card) =
        ∑ α : {x : ℕ // x ∈ goodStarts N L Y},
          Fintype.card
            {β : {x : ℕ // x ∈ goodStarts N L Y} //
              β ∈
                closedNeighborhood
                  (largePrimeDependencyGraph N L Y) α} := by
      simp only [Fintype.card_coe]
    _ = Fintype.card (ClosedNeighborhoodPair N L Y) :=
      Fintype.card_sigma.symm
    _ =
        Fintype.card
          {pair : ℕ × ℕ //
            pair ∈ closedDependencyPairs N L Y} :=
      Fintype.card_congr
        (closedNeighborhoodPairEquiv N L Y)
    _ = (closedDependencyPairs N L Y).card :=
      Fintype.card_coe _

/--
For every fixed small-prime assignment, the AGG first term is exactly the
real cast of the finite rational term `steinBOne`.
-/
theorem bOne_conditionedGoodIndicator_eq_steinBOne
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    bOne
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ)
        (largePrimeDependencyGraph N L Y) =
      ((steinBOne N L Y : ℚ) : ℝ) := by
  unfold bOne
  simp_rw [marginal_conditionedGoodIndicator_eq_baseline
    hN hL hLY σ]
  rw [steinBOne_eq_card_div]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  have hcountR :
      (∑ α : {x : ℕ // x ∈ goodStarts N L Y},
          ((closedNeighborhood
            (largePrimeDependencyGraph N L Y) α).card : ℝ)) =
        ((closedDependencyPairs N L Y).card : ℝ) := by
    exact_mod_cast sum_card_closedNeighborhood_eq N L Y
  rw [hcountR]
  push_cast
  rw [show 2 * L = L + L by omega, pow_add]
  ring

/-- The averaged first term is the same exact finite term. -/
theorem conditionalBOneAverage_eq_steinBOne
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    conditionalBOneAverage N L Y =
      ((steinBOne N L Y : ℚ) : ℝ) := by
  unfold conditionalBOneAverage
  simp_rw [bOne_conditionedGoodIndicator_eq_steinBOne
    hN hL hLY]
  unfold finiteUniformAverage
  simp

/-! ## The remaining joint-marginal averaging connector -/

/-- Uniform averaging commutes with a finite Fintype sum. -/
theorem finiteUniformAverage_fintypeSum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → ℝ) :
    finiteUniformAverage (fun i ↦ ∑ k, f i k) =
      ∑ k, finiteUniformAverage (fun i ↦ f i k) := by
  unfold finiteUniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

/-- Uniform averaging commutes with a sum over a fixed finite set. -/
theorem finiteUniformAverage_finsetSum
    {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (f : ι → κ → ℝ) :
    finiteUniformAverage (fun i ↦ ∑ k ∈ s, f i k) =
      ∑ k ∈ s, finiteUniformAverage (fun i ↦ f i k) := by
  unfold finiteUniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

/-! ### Finite law of total probability for the coordinate split -/

/-- The full prime-sign cylinder is the product of its small and large parts. -/
def sampleSplitEquiv (M Y : ℕ) :
    SampleSpace M ≃ SmallSample M Y × LargeSample M Y where
  toFun ω := (restrictSmall M Y ω, restrictLarge M Y ω)
  invFun pieces := assemble M Y pieces.1 pieces.2
  left_inv ω := assemble_restrictions M Y ω
  right_inv pieces := by
    apply Prod.ext
    · exact restrictSmall_assemble M Y pieces.1 pieces.2
    · exact restrictLarge_assemble M Y pieces.1 pieces.2

/--
Event points on the full cylinder are the disjoint union of the event fibers
over fixed small-prime assignments.
-/
def eventSplitEquiv
    (M Y : ℕ) (P : SampleSpace M → Prop) :
    {ω : SampleSpace M // P ω} ≃
      Σ σ : SmallSample M Y,
        {η : LargeSample M Y // P (assemble M Y σ η)} where
  toFun ω :=
    ⟨restrictSmall M Y ω.1,
      ⟨restrictLarge M Y ω.1, by
        rw [assemble_restrictions M Y ω.1]
        exact ω.2⟩⟩
  invFun pieces :=
    ⟨assemble M Y pieces.1 pieces.2.1, pieces.2.2⟩
  left_inv ω := by
    apply Subtype.ext
    exact assemble_restrictions M Y ω.1
  right_inv pieces := by
    rcases pieces with ⟨σ, ⟨η, hη⟩⟩
    have hfst :
        restrictSmall M Y (assemble M Y σ η) = σ :=
      restrictSmall_assemble M Y σ η
    apply Sigma.ext hfst
    apply
      (Subtype.heq_iff_coe_eq
        (fun θ ↦ by
          change
            P (assemble M Y
              (restrictSmall M Y (assemble M Y σ η)) θ) ↔
              P (assemble M Y σ θ)
          rw [restrictSmall_assemble M Y σ η])).2
    exact restrictLarge_assemble M Y σ η

/-- Cardinal form of the finite law of total probability. -/
theorem card_event_eq_sum_card_fibers
    (M Y : ℕ) (P : SampleSpace M → Prop)
    [DecidablePred P] :
    Fintype.card {ω : SampleSpace M // P ω} =
      ∑ σ : SmallSample M Y,
        Fintype.card
          {η : LargeSample M Y // P (assemble M Y σ η)} := by
  classical
  calc
    Fintype.card {ω : SampleSpace M // P ω} =
        Fintype.card
          (Σ σ : SmallSample M Y,
            {η : LargeSample M Y //
              P (assemble M Y σ η)}) :=
      Fintype.card_congr (eventSplitEquiv M Y P)
    _ = _ := Fintype.card_sigma

/-- Cardinal of the full cylinder as a product of the two coordinate pieces. -/
theorem card_sampleSpace_eq_mul
    (M Y : ℕ) :
    Fintype.card (SampleSpace M) =
      Fintype.card (SmallSample M Y) *
        Fintype.card (LargeSample M Y) := by
  calc
    Fintype.card (SampleSpace M) =
        Fintype.card
          (SmallSample M Y × LargeSample M Y) :=
      Fintype.card_congr (sampleSplitEquiv M Y)
    _ = _ := Fintype.card_prod _ _

/--
Exact rational law of total probability for finite uniform cylinders.
-/
theorem finiteUniformProbability_eq_average_fibers
    (M Y : ℕ) (P : SampleSpace M → Prop)
    [DecidablePred P] :
    finiteUniformProbability P =
      (∑ σ : SmallSample M Y,
        finiteUniformProbability
          (fun η : LargeSample M Y ↦
            P (assemble M Y σ η))) /
        (Fintype.card (SmallSample M Y) : ℚ) := by
  classical
  unfold finiteUniformProbability
  simp only [Nat.card_eq_fintype_card]
  rw [card_event_eq_sum_card_fibers M Y P,
    card_sampleSpace_eq_mul M Y]
  rw [← Finset.sum_div]
  rw [div_div]
  push_cast
  ring

/-- The two equivalent uniform-probability representations agree. -/
theorem finiteUniformProbability_eq_uniformEventProbability
    {M : ℕ} (P : SampleSpace M → Prop)
    [DecidablePred P] :
    finiteUniformProbability P =
      uniformEventProbability P := by
  classical
  unfold finiteUniformProbability uniformEventProbability
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/--
Real-valued averaging identity used by the conditional joint marginals.
-/
theorem finiteUniformAverage_largeEventProbability_eq_full
    (M Y : ℕ) (P : SampleSpace M → Prop)
    [DecidablePred P] :
    finiteUniformAverage
        (fun σ : SmallSample M Y ↦
          eventProbability
            (largeUniformPMF M Y)
            (fun η : LargeSample M Y ↦
              P (assemble M Y σ η))) =
      ((uniformEventProbability P : ℚ) : ℝ) := by
  classical
  simp_rw [eventProbability_largeUniformPMF_eq]
  unfold finiteUniformAverage
  rw [← Rat.cast_sum, ← Rat.cast_natCast, ← Rat.cast_div]
  rw [← finiteUniformProbability_eq_average_fibers M Y P]
  rw [finiteUniformProbability_eq_uniformEventProbability]

/--
The sole remaining finite connector for the second Stein--Chen term.

It is the law of total probability for the coordinate splitting:
averaging the large-cylinder joint marginal over all fixed small-prime
assignments gives the joint probability on the full cylinder.
-/
def ConditionalJointAverageStatement (N L Y : ℕ) : Prop :=
  ∀ (α β : {x : ℕ // x ∈ goodStarts N L Y}),
    finiteUniformAverage
        (fun σ : SmallSample (dyadicCutoff N L) Y ↦
          jointMarginal
            (largeUniformPMF (dyadicCutoff N L) Y)
            (conditionedGoodIndicator N L Y σ) α β) =
      ((jointStartProbability N L α.1 β.1 : ℚ) : ℝ)

/--
The joint-marginal averaging connector follows from the finite coordinate
product decomposition; it introduces no bridge hypothesis.
-/
theorem conditionalJointAverageStatement
    (N L Y : ℕ) :
    ConditionalJointAverageStatement N L Y := by
  classical
  intro α β
  let P : SampleSpace (dyadicCutoff N L) → Prop :=
    fun ω ↦ startAt ω α.1 L ∧ startAt ω β.1 L
  have htotal :=
    finiteUniformAverage_largeEventProbability_eq_full
      (dyadicCutoff N L) Y P
  simpa only [jointMarginal, P,
    conditionedGoodIndicator_eq_true_iff,
    jointStartProbability] using htotal

/--
The open graph neighborhood is exactly the natural ordered dependency-edge
relation.
-/
theorem pair_mem_orderedDependencyEdges_iff
    {N L Y : ℕ}
    (α β : {x : ℕ // x ∈ goodStarts N L Y}) :
    (α.1, β.1) ∈ orderedDependencyEdges N L Y ↔
      β ∈
        (closedNeighborhood
          (largePrimeDependencyGraph N L Y) α).erase α := by
  rw [mem_orderedDependencyEdges, Finset.mem_erase,
    mem_closedNeighborhood]
  constructor
  · rintro ⟨_hα, _hβ, hadj⟩
    have hne : β ≠ α := by
      intro h
      exact hadj.1 (congrArg Subtype.val h).symm
    exact ⟨hne, Or.inr hadj⟩
  · rintro ⟨hne, heq | hadj⟩
    · exact False.elim (hne heq)
    · exact ⟨α.2, β.2, hadj⟩

/-- Dependent type of ordered open-neighborhood pairs. -/
abbrev OpenNeighborhoodPair (N L Y : ℕ) :=
  Σ α : {x : ℕ // x ∈ goodStarts N L Y},
    {β : {x : ℕ // x ∈ goodStarts N L Y} //
      β ∈
        (closedNeighborhood
          (largePrimeDependencyGraph N L Y) α).erase α}

/-- Open-neighborhood pairs are canonically the ordered dependency edges. -/
noncomputable def openNeighborhoodPairEquiv
    (N L Y : ℕ) :
    OpenNeighborhoodPair N L Y ≃
      {pair : ℕ × ℕ //
        pair ∈ orderedDependencyEdges N L Y} := by
  classical
  let toPair :
      OpenNeighborhoodPair N L Y →
        {pair : ℕ × ℕ //
          pair ∈ orderedDependencyEdges N L Y} :=
    fun pair ↦
      ⟨(pair.1.1, pair.2.1.1),
        (pair_mem_orderedDependencyEdges_iff
          pair.1 pair.2.1).mpr pair.2.2⟩
  let fromPair :
      {pair : ℕ × ℕ //
        pair ∈ orderedDependencyEdges N L Y} →
        OpenNeighborhoodPair N L Y :=
    fun pair ↦ by
      have hmem :=
        mem_orderedDependencyEdges.mp pair.2
      let α : {x : ℕ // x ∈ goodStarts N L Y} :=
        ⟨pair.1.1, hmem.1⟩
      let β : {x : ℕ // x ∈ goodStarts N L Y} :=
        ⟨pair.1.2, hmem.2.1⟩
      exact
        ⟨α,
          ⟨β,
            (pair_mem_orderedDependencyEdges_iff α β).mp
              pair.2⟩⟩
  exact
    { toFun := toPair
      invFun := fromPair
      left_inv := by
        intro pair
        have hfst :
            (fromPair (toPair pair)).1 = pair.1 := by
          apply Subtype.ext
          rfl
        apply Sigma.ext hfst
        cases hfst
        apply heq_of_eq
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro pair
        apply Subtype.ext
        rfl }

/--
Assuming precisely the finite law-of-total-probability connector above, the
average conditional AGG second term is the real cast of
`steinBTwoAverage`.
-/
theorem conditionalBTwoAverage_eq_steinBTwoAverage_of_jointAverage
    {N L Y : ℕ}
    (hjoint : ConditionalJointAverageStatement N L Y) :
    conditionalBTwoAverage N L Y =
      ((steinBTwoAverage N L Y : ℚ) : ℝ) := by
  unfold ConditionalJointAverageStatement at hjoint
  have havg :
      conditionalBTwoAverage N L Y =
        ∑ α : {x : ℕ // x ∈ goodStarts N L Y},
          ∑ β ∈
              (closedNeighborhood
                (largePrimeDependencyGraph N L Y) α).erase α,
            finiteUniformAverage
              (fun σ : SmallSample (dyadicCutoff N L) Y ↦
                jointMarginal
                  (largeUniformPMF (dyadicCutoff N L) Y)
                  (conditionedGoodIndicator N L Y σ) α β) := by
    unfold conditionalBTwoAverage bTwo
    rw [finiteUniformAverage_fintypeSum]
    apply Finset.sum_congr rfl
    intro α _hα
    exact finiteUniformAverage_finsetSum _ _
  rw [havg]
  simp_rw [hjoint]
  have hsigma :
      (∑ α : {x : ℕ // x ∈ goodStarts N L Y},
          ∑ β ∈
              (closedNeighborhood
                (largePrimeDependencyGraph N L Y) α).erase α,
            ((jointStartProbability N L α.1 β.1 : ℚ) : ℝ)) =
        ∑ pair : OpenNeighborhoodPair N L Y,
          ((jointStartProbability N L
            pair.1.1 pair.2.1.1 : ℚ) : ℝ) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro α _hα
    exact
      Finset.sum_subtype
        ((closedNeighborhood
          (largePrimeDependencyGraph N L Y) α).erase α)
        (fun _β ↦ Iff.rfl)
        (fun β ↦
          ((jointStartProbability N L α.1 β.1 : ℚ) : ℝ))
  rw [hsigma]
  have hequiv :
      (∑ pair : OpenNeighborhoodPair N L Y,
          ((jointStartProbability N L
            pair.1.1 pair.2.1.1 : ℚ) : ℝ)) =
        ∑ pair :
            {pair : ℕ × ℕ //
              pair ∈ orderedDependencyEdges N L Y},
          ((jointStartProbability N L
            pair.1.1 pair.1.2 : ℚ) : ℝ) := by
    exact Fintype.sum_equiv
      (openNeighborhoodPairEquiv N L Y)
      (fun pair : OpenNeighborhoodPair N L Y ↦
        ((jointStartProbability N L
          pair.1.1 pair.2.1.1 : ℚ) : ℝ))
      (fun pair :
          {pair : ℕ × ℕ //
            pair ∈ orderedDependencyEdges N L Y} ↦
        ((jointStartProbability N L
          pair.1.1 pair.1.2 : ℚ) : ℝ))
      (fun _pair ↦ rfl)
  rw [hequiv]
  rw [← Finset.sum_subtype
    (orderedDependencyEdges N L Y)
    (fun _pair ↦ Iff.rfl)
    (fun pair ↦
      ((jointStartProbability N L
        pair.1 pair.2 : ℚ) : ℝ))]
  unfold steinBTwoAverage jointPairMass
  push_cast
  apply Finset.sum_congr rfl
  intro pair _hpair
  rfl

/--
The averaged second term is unconditionally identified: the required
law-of-total-probability connector was proved above from the coordinate split.
-/
theorem conditionalBTwoAverage_eq_steinBTwoAverage
    (N L Y : ℕ) :
    conditionalBTwoAverage N L Y =
      ((steinBTwoAverage N L Y : ℚ) : ℝ) :=
  conditionalBTwoAverage_eq_steinBTwoAverage_of_jointAverage
    (conditionalJointAverageStatement N L Y)

/-- Averaged AGG estimate expressed in the finite terms of Lemma 13.8. -/
theorem averagedConditionalGood_natTotalVariation_le_steinTerms
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (averagedConditionalGoodLaw N L Y)
        (commonConditionalGoodPoissonLaw N L Y) ≤
      2 *
        (((steinBOne N L Y : ℚ) : ℝ) +
          ((steinBTwoAverage N L Y : ℚ) : ℝ)) := by
  have haverage :=
    averagedConditionalGood_natTotalVariation_le
      hAGG hN hL hLY
  rw [conditionalBOneAverage_eq_steinBOne hN hL hLY,
    conditionalBTwoAverage_eq_steinBTwoAverage] at haverage
  exact haverage

/--
Fully concrete finite majorant for the averaged conditional AGG error.
-/
theorem averagedConditionalGood_natTotalVariation_le_finiteMajorant
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (averagedConditionalGoodLaw N L Y)
        (commonConditionalGoodPoissonLaw N L Y) ≤
      2 *
        (((N + (orderedDependencyEdges N L Y).card : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * L) +
          (((touchingOffDiagPairs N L).card +
              (orderedDependencyEdges N L Y).card +
              TouchingMass.touchingMass N L +
              jointDefectMass N L
                (separatedOffDiagPairs N L) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * L)) := by
  have hbase :=
    averagedConditionalGood_natTotalVariation_le_steinTerms
      hAGG hN hL hLY
  have hbOne :
      ((steinBOne N L Y : ℚ) : ℝ) ≤
        ((N + (orderedDependencyEdges N L Y).card : ℕ) : ℝ) /
          (2 : ℝ) ^ (2 * L) := by
    have hcast :
        ((steinBOne N L Y : ℚ) : ℝ) ≤
          (((((N + (orderedDependencyEdges N L Y).card : ℕ) : ℚ) /
            (2 : ℚ) ^ (2 * L)) : ℚ) : ℝ) :=
      Rat.cast_le.mpr (steinBOne_le N L Y)
    push_cast at hcast
    simpa only [Nat.cast_add] using hcast
  have hbTwo :
      ((steinBTwoAverage N L Y : ℚ) : ℝ) ≤
        (((touchingOffDiagPairs N L).card +
            (orderedDependencyEdges N L Y).card +
            TouchingMass.touchingMass N L +
            jointDefectMass N L
              (separatedOffDiagPairs N L) : ℕ) : ℝ) /
          (2 : ℝ) ^ (2 * L) := by
    have hcast :
        ((steinBTwoAverage N L Y : ℚ) : ℝ) ≤
          ((((((touchingOffDiagPairs N L).card +
              (orderedDependencyEdges N L Y).card +
              TouchingMass.touchingMass N L +
              jointDefectMass N L
                (separatedOffDiagPairs N L) : ℕ) : ℚ) /
            (2 : ℚ) ^ (2 * L)) : ℚ) : ℝ) :=
      Rat.cast_le.mpr
        (steinBTwoAverage_le (Y := Y) hN hL)
    push_cast at hcast
    simpa only [Nat.cast_add] using hcast
  calc
    natTotalVariation
        (averagedConditionalGoodLaw N L Y)
        (commonConditionalGoodPoissonLaw N L Y) ≤
      2 *
        (((steinBOne N L Y : ℚ) : ℝ) +
          ((steinBTwoAverage N L Y : ℚ) : ℝ)) := hbase
    _ ≤
        2 *
          (((N + (orderedDependencyEdges N L Y).card : ℕ) : ℝ) /
              (2 : ℝ) ^ (2 * L) +
            (((touchingOffDiagPairs N L).card +
                (orderedDependencyEdges N L Y).card +
                TouchingMass.touchingMass N L +
                jointDefectMass N L
                  (separatedOffDiagPairs N L) : ℕ) : ℝ) /
              (2 : ℝ) ^ (2 * L)) := by
      gcongr

end

end ConditionalAGGAverage
end PaperC
