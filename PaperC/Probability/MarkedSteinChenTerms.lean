import PaperC.Probability.MarkedConditionalDependencyGraph
import PaperC.Probability.ConditionalAGGAverage
import PaperC.Probability.TwoStartLocalRank

set_option maxHeartbeats 1800000

/-!
# Finite Stein--Chen terms for the truncated marked process

This module completes the finite averaging layer of §14.4.

* `markedBOneFinite` is the exact rational first AGG term after inserting
  the conditioned marginals `2^(-qₑ)`.
* `markedBTwoAverage` is the exact average (over the fixed small-prime
  coordinates) of the conditional second AGG term.
* `markedBTwoRelationEnvelope` is an explicit finite upper bound obtained
  from Lemma 14.5.  Same-start marks contribute zero; every other summand is
  bounded by the common length-`Q` relation defect divided by
  `2^(2(L+1))`.
* averaging the pointwise AGG theorem gives a total-variation bound for the
  retained marked count against its matching Poisson law.

No law-of-total-probability connector is assumed: the already proved finite
coordinate splitting is instantiated directly for exact-length events.
The only external input is the explicitly passed AGG theorem.
-/

namespace PaperC
namespace MarkedSteinChenTerms

open scoped BigOperators NNReal

open Affine
open ArratiaGoldsteinGordonInput
open ConditionalAGGAverage
open ConditionalAGGInstantiation
open ConditionalDependencyGraph
open ConditionalStartProbability
open ExactLengthBadStartMass
open ExactLengthConditionalRank
open LargePrimeDependencyGraph
open MarkedConditionalDependencyGraph
open MarkedLocalGeometry
open MixedLengthAffine
open ProbabilityTheory
open SectionThirteenFiniteBound
open SectionTwelveMoments
open SteinChenTerms
open TwoStartLocalRank

noncomputable section

/-! ## Exact finite first and second terms -/

/-- Rational first AGG term with the exact mark-dependent marginals. -/
def markedBOneFinite (N L E : ℕ) : ℚ :=
  ∑ α : MarkedIndex N L E,
    ∑ β ∈ closedNeighborhood (markedDependencyGraph N L E) α,
      ((1 : ℚ) / (2 : ℚ) ^ markedRowCount α) *
        ((1 : ℚ) / (2 : ℚ) ^ markedRowCount β)

/-- Number of ordered closed-neighborhood marked pairs. -/
def markedClosedPairCount (N L E : ℕ) : ℕ :=
  ∑ α : MarkedIndex N L E,
    (closedNeighborhood (markedDependencyGraph N L E) α).card

/-- Averaged conditional second term, written on the full prime cylinder. -/
def markedBTwoAverage (N L E : ℕ) : ℚ :=
  ∑ α : MarkedIndex N L E,
    ∑ β ∈
        (closedNeighborhood (markedDependencyGraph N L E) α).erase α,
      mixedExactLengthProbability
        (markedCylinderCutoff N L E)
        α.1.1 β.1.1 (markedRowCount α) (markedRowCount β)

/--
Oriented strict-overlap incompatibility of two exact marks.
-/
def MarkedStrictOverlap
    {N L E : ℕ} (α β : MarkedIndex N L E) : Prop :=
  (α.1.1 < β.1.1 ∧ β.1.1 - α.1.1 < L + α.2.1) ∨
  (β.1.1 < α.1.1 ∧ α.1.1 - β.1.1 < L + β.2.1)

/-- The two underlying starts, placed in increasing order. -/
def orderedMarkedStartPair
    {N L E : ℕ} (α β : MarkedIndex N L E) : ℕ × ℕ :=
  if α.1.1 ≤ β.1.1 then (α.1.1, β.1.1) else (β.1.1, α.1.1)

/--
Sharper split relation envelope.  In the local range the common relation is
read after ordering the starts, so that the concrete two-star estimate
applies directly.  In the separated range the original orientation is kept;
this makes projection to the ordered dependency-edge sum literal.
-/
noncomputable def markedBTwoSplitEnvelope (N L E : ℕ) : ℚ := by
  classical
  exact
    ∑ α : MarkedIndex N L E,
      ∑ β ∈
          (closedNeighborhood (markedDependencyGraph N L E) α).erase α,
        if α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β then 0
        else if Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E then
          (2 : ℚ) ^
              jointRho N (markedCommonRowCount L E)
                (orderedMarkedStartPair α β) /
            (2 : ℚ) ^ (2 * (L + 1))
        else
          (2 : ℚ) ^
              jointRho N (markedCommonRowCount L E) (α.1.1, β.1.1) /
            (2 : ℚ) ^ (2 * (L + 1))

/--
Common-`Q` relation envelope for the averaged second term.  Same-start
marks and strict overlaps are assigned their proved zero contribution.
-/
noncomputable def markedBTwoRelationEnvelope (N L E : ℕ) : ℚ := by
  classical
  exact
    ∑ α : MarkedIndex N L E,
      ∑ β ∈
          (closedNeighborhood (markedDependencyGraph N L E) α).erase α,
        if α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β then 0
        else
          (2 : ℚ) ^
              jointRho N (markedCommonRowCount L E) (α.1.1, β.1.1) /
            (2 : ℚ) ^ (2 * (L + 1))

/-! ### Projection of marked neighborhoods to the common graph -/

/-- Forget the mark while retaining the common-`Q` good-start certificate. -/
def commonStartOfMarked
    {N L E : ℕ} (α : MarkedIndex N L E) :
    {x : ℕ //
      x ∈ goodStarts N (markedCommonRowCount L E)
        (markedPrimeCutoff L E)} :=
  ⟨α.1.1, α.1.2⟩

/--
Every marked closed-neighborhood pair projects to a closed-neighborhood
pair in the common length-`Q` graph.
-/
theorem commonStart_mem_closedNeighborhood_of_marked
    {N L E : ℕ} {α β : MarkedIndex N L E}
    (hβ :
      β ∈ closedNeighborhood (markedDependencyGraph N L E) α) :
    commonStartOfMarked β ∈
      closedNeighborhood
        (largePrimeDependencyGraph N (markedCommonRowCount L E)
          (markedPrimeCutoff L E))
        (commonStartOfMarked α) := by
  rw [mem_closedNeighborhood] at hβ ⊢
  rcases hβ with hEq | hAdj
  · exact Or.inl (congrArg commonStartOfMarked hEq)
  · rcases hAdj with ⟨_hne, hsame | ⟨p, hp⟩⟩
    · apply Or.inl
      apply Subtype.ext
      exact hsame.symm
    · by_cases hxy : α.1.1 = β.1.1
      · apply Or.inl
        apply Subtype.ext
        exact hxy.symm
      · apply Or.inr
        refine ⟨?_, ?_⟩
        · exact hxy
        · obtain ⟨hpα, hpβ⟩ := Finset.mem_inter.mp hp
          exact ⟨p, Finset.mem_inter.mpr
            ⟨markedCoordinateSupport_subset_common α hpα,
              markedCoordinateSupport_subset_common β hpβ⟩⟩

/-- Dependent type of ordered marked closed-neighborhood pairs. -/
abbrev MarkedClosedNeighborhoodPair (N L E : ℕ) :=
  Σ α : MarkedIndex N L E,
    {β : MarkedIndex N L E //
      β ∈ closedNeighborhood (markedDependencyGraph N L E) α}

/--
Injective code of a marked closed pair by its common-graph pair and its two
marks.
-/
def markedClosedPairCode
    (N L E : ℕ) :
    MarkedClosedNeighborhoodPair N L E →
      ClosedNeighborhoodPair
          N (markedCommonRowCount L E) (markedPrimeCutoff L E) ×
        (Fin (E + 1) × Fin (E + 1)) :=
  fun pair ↦
    (⟨commonStartOfMarked pair.1,
      ⟨commonStartOfMarked pair.2.1,
        commonStart_mem_closedNeighborhood_of_marked pair.2.2⟩⟩,
      (pair.1.2, pair.2.1.2))

theorem markedClosedPairCode_injective
    (N L E : ℕ) :
    Function.Injective (markedClosedPairCode N L E) := by
  rintro ⟨α, ⟨β, hβ⟩⟩ ⟨γ, ⟨δ, hδ⟩⟩ h
  have hx :
      commonStartOfMarked α = commonStartOfMarked γ :=
    congrArg (fun z ↦ z.1.1) h
  have hy :
      commonStartOfMarked β = commonStartOfMarked δ :=
    congrArg (fun z ↦ z.1.2.1) h
  have he :
      α.2 = γ.2 :=
    congrArg (fun z ↦ z.2.1) h
  have hf :
      β.2 = δ.2 :=
    congrArg (fun z ↦ z.2.2) h
  have hα : α = γ := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Subtype.val hx
    · exact he
  have hβδ : β = δ := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Subtype.val hy
    · exact hf
  apply Sigma.ext hα
  subst γ
  apply heq_of_eq
  apply Subtype.ext
  exact hβδ

/--
The marked closed-pair population has multiplicity at most `(E+1)^2` over
the common graph.
-/
theorem markedClosedPairCount_le_common
    (N L E : ℕ) :
    markedClosedPairCount N L E ≤
      (E + 1) ^ 2 *
        (closedDependencyPairs
          N (markedCommonRowCount L E) (markedPrimeCutoff L E)).card := by
  have hsource :
      markedClosedPairCount N L E =
        Fintype.card (MarkedClosedNeighborhoodPair N L E) := by
    unfold markedClosedPairCount
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
  rw [hsource]
  calc
    Fintype.card (MarkedClosedNeighborhoodPair N L E) ≤
        Fintype.card
          (ClosedNeighborhoodPair
              N (markedCommonRowCount L E) (markedPrimeCutoff L E) ×
            (Fin (E + 1) × Fin (E + 1))) :=
      Fintype.card_le_of_injective
        (markedClosedPairCode N L E)
        (markedClosedPairCode_injective N L E)
    _ =
        (E + 1) ^ 2 *
          (closedDependencyPairs
            N (markedCommonRowCount L E) (markedPrimeCutoff L E)).card := by
      rw [Fintype.card_prod, Fintype.card_prod]
      have hcommon :
          Fintype.card
              (ClosedNeighborhoodPair
                N (markedCommonRowCount L E) (markedPrimeCutoff L E)) =
            (closedDependencyPairs
              N (markedCommonRowCount L E) (markedPrimeCutoff L E)).card :=
        Fintype.card_congr
          (closedNeighborhoodPairEquiv
            N (markedCommonRowCount L E) (markedPrimeCutoff L E))
          |>.trans (Fintype.card_coe _)
      rw [hcommon]
      simp [pow_two]
      ring

/-- The concrete conditional first AGG term is `markedBOneFinite`. -/
theorem bOne_conditionedMarkedIndicator_eq
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    bOne
        (largeUniformPMF
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
        (conditionedMarkedIndicator N L E σ)
        (markedDependencyGraph N L E) =
      ((markedBOneFinite N L E : ℚ) : ℝ) := by
  unfold bOne markedBOneFinite
  simp_rw [marginal_conditionedMarkedIndicator_eq_baseline
    hN hL σ]
  push_cast
  rfl

/--
Simple explicit cardinal majorant for the first marked term:

`b₁ ≤ #closed-pairs / 2^(2(L+1))`.
-/
theorem markedBOneFinite_le_closedPairCount
    {N L E : ℕ} :
    markedBOneFinite N L E ≤
      (markedClosedPairCount N L E : ℚ) /
        (2 : ℚ) ^ (2 * (L + 1)) := by
  have hpoint :
      ∀ α : MarkedIndex N L E,
        (1 : ℚ) / (2 : ℚ) ^ markedRowCount α ≤
          (1 : ℚ) / (2 : ℚ) ^ (L + 1) := by
    intro α
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    simp [markedRowCount, excessRowCount]
  calc
    markedBOneFinite N L E ≤
        ∑ α : MarkedIndex N L E,
          ∑ _β ∈ closedNeighborhood (markedDependencyGraph N L E) α,
            ((1 : ℚ) / (2 : ℚ) ^ (L + 1)) *
              ((1 : ℚ) / (2 : ℚ) ^ (L + 1)) := by
      unfold markedBOneFinite
      apply Finset.sum_le_sum
      intro α _hα
      apply Finset.sum_le_sum
      intro β _hβ
      exact mul_le_mul (hpoint α) (hpoint β)
        (by positivity) (by positivity)
    _ =
        (markedClosedPairCount N L E : ℚ) /
          (2 : ℚ) ^ (2 * (L + 1)) := by
      unfold markedClosedPairCount
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_sum,
        Nat.cast_ofNat]
      rw [← Finset.sum_mul]
      rw [show 2 * (L + 1) = (L + 1) + (L + 1) by omega,
        pow_add]
      ring

/--
The first marked term is bounded by a fixed `(E+1)^2 2^(2E)` multiple of
the already certified common-length first term from §13.
-/
theorem markedBOneFinite_le_commonSteinBOne
    (N L E : ℕ) :
    markedBOneFinite N L E ≤
      ((E + 1 : ℚ) ^ 2 * (2 : ℚ) ^ (2 * E)) *
        steinBOne N (markedCommonRowCount L E)
          (markedPrimeCutoff L E) := by
  have hcount := markedClosedPairCount_le_common N L E
  have hfirst :=
    markedBOneFinite_le_closedPairCount (N := N) (L := L) (E := E)
  rw [steinBOne_eq_card_div]
  have hcountQ :
      (markedClosedPairCount N L E : ℚ) ≤
        ((E + 1 : ℚ) ^ 2) *
          ((closedDependencyPairs
            N (markedCommonRowCount L E)
              (markedPrimeCutoff L E)).card : ℚ) := by
    exact_mod_cast hcount
  calc
    markedBOneFinite N L E ≤
        (markedClosedPairCount N L E : ℚ) /
          (2 : ℚ) ^ (2 * (L + 1)) :=
      hfirst
    _ ≤
        (((E + 1 : ℚ) ^ 2) *
          ((closedDependencyPairs
            N (markedCommonRowCount L E)
              (markedPrimeCutoff L E)).card : ℚ)) /
          (2 : ℚ) ^ (2 * (L + 1)) := by
      exact div_le_div_of_nonneg_right hcountQ (by positivity)
    _ =
        ((E + 1 : ℚ) ^ 2 * (2 : ℚ) ^ (2 * E)) *
          (((closedDependencyPairs
            N (markedCommonRowCount L E)
              (markedPrimeCutoff L E)).card : ℚ) /
            (2 : ℚ) ^ (2 * markedCommonRowCount L E)) := by
      simp only [markedCommonRowCount, commonExactRowCount, excessRowCount]
      rw [show 2 * (L + E + 1) = 2 * (L + 1) + 2 * E by omega,
        pow_add]
      field_simp

/-! ## Exact averaging of the second term -/

/--
Finite law of total probability for one pair of exact marks.
-/
theorem conditionalMarkedJointAverage_eq
    (N L E : ℕ) (α β : MarkedIndex N L E) :
    finiteUniformAverage
        (fun σ :
            SmallSample
              (markedCylinderCutoff N L E) (markedPrimeCutoff L E) ↦
          jointMarginal
            (largeUniformPMF
              (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
            (conditionedMarkedIndicator N L E σ) α β) =
      ((mixedExactLengthProbability
        (markedCylinderCutoff N L E)
        α.1.1 β.1.1 (markedRowCount α) (markedRowCount β) : ℚ) : ℝ) := by
  classical
  let P : SampleSpace (markedCylinderCutoff N L E) → Prop :=
    fun ω ↦
      exactLengthAt ω α.1.1 (markedRowCount α) ∧
        exactLengthAt ω β.1.1 (markedRowCount β)
  have htotal :=
    finiteUniformAverage_largeEventProbability_eq_full
      (markedCylinderCutoff N L E) (markedPrimeCutoff L E) P
  simpa only [jointMarginal, P,
    conditionedMarkedIndicator_eq_true_iff,
    mixedExactLengthProbability] using htotal

/-- Average of the conditional first term. -/
def conditionalMarkedBOneAverage (N L E : ℕ) : ℝ :=
  finiteUniformAverage
    (fun σ :
        SmallSample
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E) ↦
      bOne
        (largeUniformPMF
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
        (conditionedMarkedIndicator N L E σ)
        (markedDependencyGraph N L E))

/-- Average of the conditional second term. -/
def conditionalMarkedBTwoAverage (N L E : ℕ) : ℝ :=
  finiteUniformAverage
    (fun σ :
        SmallSample
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E) ↦
      bTwo
        (largeUniformPMF
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
        (conditionedMarkedIndicator N L E σ)
        (markedDependencyGraph N L E))

theorem conditionalMarkedBOneAverage_eq
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) :
    conditionalMarkedBOneAverage N L E =
      ((markedBOneFinite N L E : ℚ) : ℝ) := by
  unfold conditionalMarkedBOneAverage
  simp_rw [bOne_conditionedMarkedIndicator_eq hN hL]
  unfold finiteUniformAverage
  simp

theorem conditionalMarkedBTwoAverage_eq
    (N L E : ℕ) :
    conditionalMarkedBTwoAverage N L E =
      ((markedBTwoAverage N L E : ℚ) : ℝ) := by
  have havg :
      conditionalMarkedBTwoAverage N L E =
        ∑ α : MarkedIndex N L E,
          ∑ β ∈
              (closedNeighborhood
                (markedDependencyGraph N L E) α).erase α,
            finiteUniformAverage
              (fun σ :
                  SmallSample
                    (markedCylinderCutoff N L E)
                    (markedPrimeCutoff L E) ↦
                jointMarginal
                  (largeUniformPMF
                    (markedCylinderCutoff N L E)
                    (markedPrimeCutoff L E))
                  (conditionedMarkedIndicator N L E σ) α β) := by
    unfold conditionalMarkedBTwoAverage bTwo
    rw [finiteUniformAverage_fintypeSum]
    apply Finset.sum_congr rfl
    intro α _hα
    exact finiteUniformAverage_finsetSum _ _
  rw [havg]
  simp_rw [conditionalMarkedJointAverage_eq N L E]
  unfold markedBTwoAverage
  push_cast
  rfl

/-! ## Pointwise and summed relation-defect bounds -/

theorem mixedExactLengthProbability_same_markedStart_eq_zero
    {N L E : ℕ} (hL : 1 ≤ L)
    {α β : MarkedIndex N L E}
    (hne : α ≠ β) (hsame : α.1.1 = β.1.1) :
    mixedExactLengthProbability
        (markedCylinderCutoff N L E)
        α.1.1 β.1.1 (markedRowCount α) (markedRowCount β) = 0 := by
  have he : α.2 ≠ β.2 := by
    intro he
    apply hne
    apply Prod.ext
    · apply Subtype.ext
      exact hsame
    · exact he
  have hqne : markedRowCount α ≠ markedRowCount β := by
    intro hq
    apply he
    apply Fin.ext
    unfold markedRowCount at hq
    simp only [excessRowCount] at hq
    omega
  have hz :=
    mixedExactLengthProbability_same_start_eq_zero
      (M := markedCylinderCutoff N L E)
      (x := α.1.1)
      (q := markedRowCount α)
      (r := markedRowCount β)
      (two_le_markedRowCount hL α)
      (two_le_markedRowCount hL β) hqne
  simpa only [hsame] using hz

/-- Mixed exact-length probability is symmetric under swapping the marks. -/
theorem mixedExactLengthProbability_swap
    (M x y q r : ℕ) :
    mixedExactLengthProbability M x y q r =
      mixedExactLengthProbability M y x r q := by
  classical
  unfold mixedExactLengthProbability
  congr 1
  funext ω
  apply propext
  exact and_comm

/-- Every strict marked overlap has exactly zero joint mass. -/
theorem mixedExactLengthProbability_eq_zero_of_markedStrictOverlap
    {N L E : ℕ} {α β : MarkedIndex N L E}
    (hoverlap : MarkedStrictOverlap α β) :
    mixedExactLengthProbability
        (markedCylinderCutoff N L E)
        α.1.1 β.1.1 (markedRowCount α) (markedRowCount β) = 0 := by
  rcases hoverlap with hforward | hbackward
  · exact mixedExactLengthProbability_excess_eq_zero_of_left_overlap
      hforward.1 hforward.2
  · rw [mixedExactLengthProbability_swap]
    exact mixedExactLengthProbability_excess_eq_zero_of_left_overlap
      hbackward.1 hbackward.2

/--
Lemma 14.5 gives a common-`Q` pointwise bound for every pair with distinct
starts.
-/
theorem mixedExactLengthProbability_le_commonRelation
    {N L E : ℕ} (hL : 1 ≤ L)
    (α β : MarkedIndex N L E) :
    mixedExactLengthProbability
        (markedCylinderCutoff N L E)
        α.1.1 β.1.1 (markedRowCount α) (markedRowCount β) ≤
      (2 : ℚ) ^
          jointRho N (markedCommonRowCount L E) (α.1.1, β.1.1) /
        (2 : ℚ) ^ (2 * (L + 1)) := by
  rw [mixedExactLengthProbability_eq_eta_mul_two_pow_rho_div
    (markedCylinderCutoff N L E) α.1.1 β.1.1
    (markedRowCount α) (markedRowCount β)
    (two_le_markedRowCount hL α)
    (two_le_markedRowCount hL β)]
  let A :=
    mixedLengthSystem
      (markedCylinderCutoff N L E) α.1.1 β.1.1
      (markedRowCount α) (markedRowCount β)
  let b := mixedLengthRhs (markedRowCount α) (markedRowCount β)
  have hrho :
      relationRho A ≤
        jointRho N (markedCommonRowCount L E) (α.1.1, β.1.1) := by
    dsimp only [A, jointRho, markedCylinderCutoff]
    exact mixed_relationRho_le_common
      (markedRowCount_le_common α) (markedRowCount_le_common β)
  have hpow :
      (2 : ℚ) ^ relationRho A ≤
        (2 : ℚ) ^
          jointRho N (markedCommonRowCount L E) (α.1.1, β.1.1) :=
    pow_le_pow_right₀ (by norm_num) hrho
  have hden :
      (2 : ℚ) ^ (2 * (L + 1)) ≤
        (2 : ℚ) ^ (markedRowCount α + markedRowCount β) := by
    apply pow_le_pow_right₀ (by norm_num)
    simp [markedRowCount, excessRowCount]
    omega
  rcases relationEta_eq_zero_or_one A b with heta | heta
  · dsimp only [A, b] at heta
    rw [heta]
    simp
    positivity
  · dsimp only [A, b] at heta
    rw [heta]
    simp only [Nat.cast_one, one_mul]
    exact div_le_div₀ (by positivity) hpow (by positivity) hden

/--
The common relation bound with the two starts placed in increasing order.
This is equivalent to the preceding estimate by symmetry of the mixed
event, but is the useful form in the local range.
-/
theorem mixedExactLengthProbability_le_orderedCommonRelation
    {N L E : ℕ} (hL : 1 ≤ L)
    (α β : MarkedIndex N L E) :
    mixedExactLengthProbability
        (markedCylinderCutoff N L E)
        α.1.1 β.1.1 (markedRowCount α) (markedRowCount β) ≤
      (2 : ℚ) ^
          jointRho N (markedCommonRowCount L E)
            (orderedMarkedStartPair α β) /
        (2 : ℚ) ^ (2 * (L + 1)) := by
  by_cases hxy : α.1.1 ≤ β.1.1
  · simpa [orderedMarkedStartPair, hxy] using
      mixedExactLengthProbability_le_commonRelation hL α β
  · have hyx : β.1.1 ≤ α.1.1 := Nat.le_of_not_ge hxy
    rw [mixedExactLengthProbability_swap]
    simpa [orderedMarkedStartPair, hxy, hyx] using
      mixedExactLengthProbability_le_commonRelation hL β α

/--
Concrete local form of Lemma 14.7.  For a nonzero marked pair at distance at
most the common length `Q`, the common two-star relation defect is bounded
by the fixed number `E+1`.
-/
theorem jointRho_orderedMarkedStartPair_le
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (α β : MarkedIndex N L E)
    (hstarts : α.1.1 ≠ β.1.1)
    (hcompatible : ¬MarkedStrictOverlap α β)
    (hlocal :
      Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E) :
    jointRho N (markedCommonRowCount L E)
        (orderedMarkedStartPair α β) ≤ E + 1 := by
  have hQ : 2 ≤ markedCommonRowCount L E := by
    simp [markedCommonRowCount, commonExactRowCount, excessRowCount]
    omega
  have hdiam :
      2 * markedCommonRowCount L E < markedPrimeCutoff L E := by
    simpa [markedPrimeCutoff, exactLengthBaseCutoff] using
      (two_mul_lt_terminalPrimeCutoff_succ hQ)
  rcases lt_or_gt_of_ne hstarts with hxy | hyx
  · let d := β.1.1 - α.1.1
    have hd : 0 < d := Nat.sub_pos_of_lt hxy
    have hyEq : α.1.1 + d = β.1.1 := Nat.add_sub_of_le hxy.le
    have hdQ : d ≤ markedCommonRowCount L E := by
      rw [Nat.dist_eq_sub_of_le hxy.le] at hlocal
      exact hlocal
    have hrho :=
      jointRho_le_sub_distance_oriented
        hN (show 0 < markedCommonRowCount L E by omega)
        hd hdQ hdiam α.1.2 (hyEq ▸ β.1.2)
    have hdLower : L + α.2.1 ≤ d := by
      by_contra hnot
      apply hcompatible
      exact Or.inl ⟨hxy, by omega⟩
    rw [orderedMarkedStartPair, if_pos hxy.le, ← hyEq]
    exact hrho.trans (by
      simp only [markedCommonRowCount, commonExactRowCount,
        excessRowCount] at hdQ ⊢
      omega)
  · let d := α.1.1 - β.1.1
    have hd : 0 < d := Nat.sub_pos_of_lt hyx
    have hxEq : β.1.1 + d = α.1.1 := Nat.add_sub_of_le hyx.le
    have hdQ : d ≤ markedCommonRowCount L E := by
      rw [Nat.dist_eq_sub_of_le_right hyx.le] at hlocal
      exact hlocal
    have hrho :=
      jointRho_le_sub_distance_oriented
        hN (show 0 < markedCommonRowCount L E by omega)
        hd hdQ hdiam β.1.2 (hxEq ▸ α.1.2)
    have hdLower : L + β.2.1 ≤ d := by
      by_contra hnot
      apply hcompatible
      exact Or.inr ⟨hyx, by omega⟩
    rw [orderedMarkedStartPair, if_neg (Nat.not_le.mpr hyx)]
    rw [← hxEq]
    exact hrho.trans (by
      simp only [markedCommonRowCount, commonExactRowCount,
        excessRowCount] at hdQ ⊢
      omega)

/-- Local relation weights are bounded by the fixed factor `2^(E+1)`. -/
theorem pow_jointRho_orderedMarkedStartPair_le
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (α β : MarkedIndex N L E)
    (hstarts : α.1.1 ≠ β.1.1)
    (hcompatible : ¬MarkedStrictOverlap α β)
    (hlocal :
      Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E) :
    2 ^ jointRho N (markedCommonRowCount L E)
        (orderedMarkedStartPair α β) ≤ 2 ^ (E + 1) :=
  Nat.pow_le_pow_right (by norm_num)
    (jointRho_orderedMarkedStartPair_le
      hN hL α β hstarts hcompatible hlocal)

/--
Explicit finite upper bound for the averaged marked `b₂`, split into the
local two-star rank estimate and the separated common relation defect.
-/
theorem markedBTwoAverage_le_splitEnvelope
    {N L E : ℕ} (hL : 1 ≤ L) :
    markedBTwoAverage N L E ≤
      markedBTwoSplitEnvelope N L E := by
  classical
  unfold markedBTwoAverage markedBTwoSplitEnvelope
  apply Finset.sum_le_sum
  intro α _hα
  apply Finset.sum_le_sum
  intro β hβ
  by_cases hzero :
      α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β
  · rw [if_pos hzero]
    have hne : α ≠ β :=
      fun h ↦ (Finset.mem_erase.mp hβ).1 h.symm
    rcases hzero with hsame | hoverlap
    · rw [mixedExactLengthProbability_same_markedStart_eq_zero
        hL hne hsame]
    · rw [mixedExactLengthProbability_eq_zero_of_markedStrictOverlap
        hoverlap]
  · rw [if_neg hzero]
    by_cases hlocal :
        Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E
    · rw [if_pos hlocal]
      exact mixedExactLengthProbability_le_orderedCommonRelation
        hL α β
    · rw [if_neg hlocal]
      exact mixedExactLengthProbability_le_commonRelation hL α β

/--
Explicit finite upper bound for the averaged marked `b₂`.
-/
theorem markedBTwoAverage_le_relationEnvelope
    {N L E : ℕ} (hL : 1 ≤ L) :
    markedBTwoAverage N L E ≤
      markedBTwoRelationEnvelope N L E := by
  classical
  unfold markedBTwoAverage markedBTwoRelationEnvelope
  apply Finset.sum_le_sum
  intro α _hα
  apply Finset.sum_le_sum
  intro β hβ
  by_cases hzero :
      α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β
  · rw [if_pos hzero]
    have hne : α ≠ β := by
      exact fun h ↦ (Finset.mem_erase.mp hβ).1 h.symm
    rcases hzero with hsame | hoverlap
    · rw [mixedExactLengthProbability_same_markedStart_eq_zero
        hL hne hsame]
    · rw [mixedExactLengthProbability_eq_zero_of_markedStrictOverlap
        hoverlap]
  · rw [if_neg hzero]
    exact mixedExactLengthProbability_le_commonRelation hL α β

/-! ## Averaged AGG and the retained marked count -/

/-- Conditional law of the retained marked count. -/
noncomputable def conditionalMarkedLaw
    (N L E : ℕ)
    (σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    ℕ → ℝ :=
  indicatorSumLaw
    (largeUniformPMF
      (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
    (conditionedMarkedIndicator N L E σ)

/-- Common matching Poisson law, represented at the zero small assignment. -/
noncomputable def commonMarkedPoissonLaw
    (N L E : ℕ) : ℕ → ℝ :=
  matchingPoissonLaw
    (largeUniformPMF
      (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
    (conditionedMarkedIndicator N L E 0)

/-- Uniform mixture of all conditional marked-count laws. -/
noncomputable def averagedConditionalMarkedLaw
    (N L E : ℕ) : ℕ → ℝ :=
  fun k ↦
    finiteUniformAverage
      (fun σ :
          SmallSample
            (markedCylinderCutoff N L E) (markedPrimeCutoff L E) ↦
        conditionalMarkedLaw N L E σ k)

theorem poissonParameter_conditionedMarkedIndicator_eq
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (σ τ :
      SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    poissonParameter
        (largeUniformPMF
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
        (conditionedMarkedIndicator N L E σ) =
      poissonParameter
        (largeUniformPMF
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
        (conditionedMarkedIndicator N L E τ) := by
  unfold poissonParameter
  apply Finset.sum_congr rfl
  intro α _hα
  rw [marginal_conditionedMarkedIndicator_eq_baseline hN hL σ α,
    marginal_conditionedMarkedIndicator_eq_baseline hN hL τ α]

theorem matchingPoissonLaw_conditionedMarkedIndicator_eq_common
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (σ :
      SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    matchingPoissonLaw
        (largeUniformPMF
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
        (conditionedMarkedIndicator N L E σ) =
      commonMarkedPoissonLaw N L E := by
  have hrate :
      poissonRate
          (largeUniformPMF
            (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
          (conditionedMarkedIndicator N L E σ) =
        poissonRate
          (largeUniformPMF
            (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
          (conditionedMarkedIndicator N L E 0) := by
    apply NNReal.eq
    exact poissonParameter_conditionedMarkedIndicator_eq hN hL σ 0
  funext k
  simp only [commonMarkedPoissonLaw, matchingPoissonLaw, hrate]

theorem conditionalMarkedLaw_eq_finiteNatLaw
    (N L E : ℕ)
    (σ :
      SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    conditionalMarkedLaw N L E σ =
      finiteNatLaw
        (largeUniformPMF
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
        (indicatorSum (conditionedMarkedIndicator N L E σ)) := by
  funext k
  unfold conditionalMarkedLaw indicatorSumLaw finiteNatLaw eventProbability
  apply Finset.sum_congr rfl
  intro η _hη
  split_ifs <;> rfl

theorem summable_abs_conditionalMarkedLaw_sub_commonPoisson
    (N L E : ℕ)
    (σ :
      SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    Summable fun k ↦
      |conditionalMarkedLaw N L E σ k -
        commonMarkedPoissonLaw N L E k| := by
  apply summable_abs_sub_of_nonneg
  · rw [conditionalMarkedLaw_eq_finiteNatLaw]
    exact summable_finiteNatLaw _ _
  · exact (poissonPMFRealSum _).summable
  · intro k
    exact indicatorSumLaw_nonneg _ _ k
  · intro k
    exact poissonPMFReal_nonneg

/--
Finite marked AGG theorem after averaging the conditioning.
-/
theorem averagedConditionalMarked_natTotalVariation_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) :
    natTotalVariation
        (averagedConditionalMarkedLaw N L E)
        (commonMarkedPoissonLaw N L E) ≤
      2 *
        (((markedBOneFinite N L E : ℚ) : ℝ) +
          ((markedBTwoAverage N L E : ℚ) : ℝ)) := by
  have hmixture :=
    natTotalVariation_uniformMixture_le
      (fun σ :
          SmallSample
            (markedCylinderCutoff N L E) (markedPrimeCutoff L E) ↦
        conditionalMarkedLaw N L E σ)
      (commonMarkedPoissonLaw N L E)
      (summable_abs_conditionalMarkedLaw_sub_commonPoisson N L E)
  have hpoint :
      ∀ σ :
          SmallSample
            (markedCylinderCutoff N L E) (markedPrimeCutoff L E),
        natTotalVariation
            (conditionalMarkedLaw N L E σ)
            (commonMarkedPoissonLaw N L E) ≤
          2 *
            (bOne
                (largeUniformPMF
                  (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
                (conditionedMarkedIndicator N L E σ)
                (markedDependencyGraph N L E) +
              bTwo
                (largeUniformPMF
                  (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
                (conditionedMarkedIndicator N L E σ)
                (markedDependencyGraph N L E)) := by
    intro σ
    have hagg :=
      conditionalMarked_totalVariationToPoisson_le hAGG hL σ
    change
      natTotalVariation
          (conditionalMarkedLaw N L E σ)
          (matchingPoissonLaw
            (largeUniformPMF
              (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
            (conditionedMarkedIndicator N L E σ)) ≤ _ at hagg
    rw [matchingPoissonLaw_conditionedMarkedIndicator_eq_common
      hN hL σ] at hagg
    exact hagg
  calc
    natTotalVariation
        (averagedConditionalMarkedLaw N L E)
        (commonMarkedPoissonLaw N L E) ≤
      finiteUniformAverage
        (fun σ :
            SmallSample
              (markedCylinderCutoff N L E) (markedPrimeCutoff L E) ↦
          natTotalVariation
            (conditionalMarkedLaw N L E σ)
            (commonMarkedPoissonLaw N L E)) :=
      hmixture
    _ ≤
      finiteUniformAverage
        (fun σ :
            SmallSample
              (markedCylinderCutoff N L E) (markedPrimeCutoff L E) ↦
          2 *
            (bOne
                (largeUniformPMF
                  (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
                (conditionedMarkedIndicator N L E σ)
                (markedDependencyGraph N L E) +
              bTwo
                (largeUniformPMF
                  (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
                (conditionedMarkedIndicator N L E σ)
                (markedDependencyGraph N L E))) := by
      exact finiteUniformAverage_mono hpoint
    _ =
      2 *
        (conditionalMarkedBOneAverage N L E +
          conditionalMarkedBTwoAverage N L E) := by
      unfold conditionalMarkedBOneAverage conditionalMarkedBTwoAverage
      unfold finiteUniformAverage
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      ring
    _ =
      2 *
        (((markedBOneFinite N L E : ℚ) : ℝ) +
          ((markedBTwoAverage N L E : ℚ) : ℝ)) := by
      rw [conditionalMarkedBOneAverage_eq hN hL,
        conditionalMarkedBTwoAverage_eq]

/--
Displayed finite TV bound using only a closed-pair count and the common
relation envelope.
-/
theorem averagedConditionalMarked_natTotalVariation_le_explicit
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) :
    natTotalVariation
        (averagedConditionalMarkedLaw N L E)
        (commonMarkedPoissonLaw N L E) ≤
      2 *
        (((markedClosedPairCount N L E : ℚ) /
            (2 : ℚ) ^ (2 * (L + 1)) : ℚ) : ℝ) +
      2 * ((markedBTwoRelationEnvelope N L E : ℚ) : ℝ) := by
  have hagg :=
    averagedConditionalMarked_natTotalVariation_le
      (E := E) hAGG hN hL
  have hb1 := markedBOneFinite_le_closedPairCount
    (N := N) (L := L) (E := E)
  have hb2 := markedBTwoAverage_le_relationEnvelope
    (N := N) (E := E) hL
  have hb1R :
      ((markedBOneFinite N L E : ℚ) : ℝ) ≤
        (((markedClosedPairCount N L E : ℚ) /
          (2 : ℚ) ^ (2 * (L + 1)) : ℚ) : ℝ) :=
    Rat.cast_le.mpr hb1
  have hb2R :
      ((markedBTwoAverage N L E : ℚ) : ℝ) ≤
        ((markedBTwoRelationEnvelope N L E : ℚ) : ℝ) :=
    Rat.cast_le.mpr hb2
  linarith

end

end MarkedSteinChenTerms
end PaperC
