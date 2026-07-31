import PaperC.Asymptotics.BoundedRatioSteinChen

set_option maxHeartbeats 1800000

/-!
# The averaged second Stein--Chen term on a bounded-ratio interval

This module supplies the finite part of Lemma 17.37 which is specific to
`[N,M)`.  It does not introduce a new probabilistic bridge.  The coordinate
split and its finite law of total probability are reused from
`ConditionalAGGAverage`.

The main constructions are:

* the conditional good-count laws and their uniform mixture;
* the exact identification of the averaged conditional `b₂` with the
  unconditional joint-start mass on `boundedOrderedDependencyEdges`;
* the exact overlap/touching/separated partition of that mass;
* a finite separated-pair bound whose excess is dominated by
  `PropositionSixteenOne.R2κ`;
* a purely geometric linear bound for the number of touching edges.

The last item deliberately records only the finite geometry.  Upgrading its
joint mass from the elementary one-marginal bound to the manuscript's
`O(M) 2⁻²ᴸ` estimate remains the bounded-ratio touching part of Lemma 17.37.
-/

namespace PaperC
namespace BoundedRatioSteinChenSecondTerm

open scoped BigOperators NNReal

open Affine
open ArratiaGoldsteinGordonInput
open ConditionalAGGInstantiation
open ConditionalAGGAverage
open ConditionalStartProbability
open LargePrimeDependencyGraph
open PropositionSixteenOne
open SectionThirteenFiniteBound
open SectionTwelveMoments

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Conditional laws and the uniform mixture -/

/-- Law of the bounded good-start count after fixing the small coordinates. -/
noncomputable def boundedConditionalGoodLaw
    (N M L Y : ℕ)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    ℕ → ℝ :=
  indicatorSumLaw
    (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
    (BoundedRatioSteinChen.boundedConditionedGoodIndicator
      N M L Y σ)

/-- The common matching Poisson law, represented at the zero assignment. -/
noncomputable def boundedCommonConditionalGoodPoissonLaw
    (N M L Y : ℕ) : ℕ → ℝ :=
  matchingPoissonLaw
    (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
    (BoundedRatioSteinChen.boundedConditionedGoodIndicator
      N M L Y 0)

/-- Uniform mixture of all bounded conditional good-count laws. -/
noncomputable def boundedAveragedConditionalGoodLaw
    (N M L Y : ℕ) : ℕ → ℝ :=
  fun k ↦
    finiteUniformAverage
      (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
        boundedConditionalGoodLaw N M L Y σ k)

/-- Uniform average of the bounded conditional second AGG term. -/
noncomputable def boundedConditionalBTwoAverage
    (N M L Y : ℕ) : ℝ :=
  finiteUniformAverage
    (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
      bTwo
        (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
        (BoundedRatioSteinChen.boundedConditionedGoodIndicator
          N M L Y σ)
        (BoundedRatioSteinChen.boundedLargePrimeDependencyGraph
          N M L Y))

/--
The Poisson parameter, hence the matching Poisson law, is independent of the
fixed small-prime assignment.
-/
theorem boundedPoissonParameter_eq
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ τ : SmallSample (boundedRatioCutoff M L) Y) :
    poissonParameter
        (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
        (BoundedRatioSteinChen.boundedConditionedGoodIndicator
          N M L Y σ) =
      poissonParameter
        (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
        (BoundedRatioSteinChen.boundedConditionedGoodIndicator
          N M L Y τ) := by
  unfold poissonParameter
  apply Finset.sum_congr rfl
  intro x _hx
  rw [
    BoundedRatioSteinChen.marginal_boundedConditionedGoodIndicator_eq_baseline
      hN hL hLY σ x,
    BoundedRatioSteinChen.marginal_boundedConditionedGoodIndicator_eq_baseline
      hN hL hLY τ x]

theorem boundedMatchingPoissonLaw_eq_common
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    matchingPoissonLaw
        (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
        (BoundedRatioSteinChen.boundedConditionedGoodIndicator
          N M L Y σ) =
      boundedCommonConditionalGoodPoissonLaw N M L Y := by
  have hrate :
      poissonRate
          (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
          (BoundedRatioSteinChen.boundedConditionedGoodIndicator
            N M L Y σ) =
        poissonRate
          (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
          (BoundedRatioSteinChen.boundedConditionedGoodIndicator
            N M L Y 0) := by
    apply NNReal.eq
    exact boundedPoissonParameter_eq hN hL hLY σ 0
  funext k
  simp only [boundedCommonConditionalGoodPoissonLaw,
    matchingPoissonLaw, hrate]

/-! ## Unconditional joint probabilities on the adequate bounded cylinder -/

/-- Joint probability of two starts on the full bounded-ratio cylinder. -/
noncomputable def boundedJointStartProbability
    (M L x y : ℕ) : ℚ := by
  classical
  exact uniformEventProbability (M := boundedRatioCutoff M L)
    (fun ω ↦ startAt ω x L ∧ startAt ω y L)

/-- Joint mass on an arbitrary finite population of bounded ordered pairs. -/
noncomputable def boundedJointPairMass
    (M L : ℕ) (pairs : Finset (ℕ × ℕ)) : ℚ :=
  ∑ pair ∈ pairs,
    boundedJointStartProbability M L pair.1 pair.2

/-- The unconditional mass on all bounded ordered dependency edges. -/
noncomputable def boundedSteinBTwoAverage
    (N M L Y : ℕ) : ℚ :=
  boundedJointPairMass M L
    (BoundedRatioSteinChen.boundedOrderedDependencyEdges N M L Y)

/--
Finite law of total probability for a bounded conditional joint marginal.
-/
theorem boundedConditionalJointAverage
    (N M L Y : ℕ)
    (α β :
      {x : ℕ //
        x ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y}) :
    finiteUniformAverage
        (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
          jointMarginal
            (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
            (BoundedRatioSteinChen.boundedConditionedGoodIndicator
              N M L Y σ) α β) =
      ((boundedJointStartProbability M L α.1 β.1 : ℚ) : ℝ) := by
  classical
  let P : SampleSpace (boundedRatioCutoff M L) → Prop :=
    fun ω ↦ startAt ω α.1 L ∧ startAt ω β.1 L
  have htotal :=
    finiteUniformAverage_largeEventProbability_eq_full
      (boundedRatioCutoff M L) Y P
  simpa only [jointMarginal, P,
    BoundedRatioSteinChen.boundedLargeUniformPMF,
    BoundedRatioSteinChen.boundedConditionedGoodIndicator_eq_true_iff,
    boundedJointStartProbability] using htotal

/--
The graph-theoretic open neighborhood is the bounded natural-number edge
relation.
-/
theorem pair_mem_boundedOrderedDependencyEdges_iff
    {N M L Y : ℕ}
    (α β :
      {x : ℕ //
        x ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y}) :
    (α.1, β.1) ∈
        BoundedRatioSteinChen.boundedOrderedDependencyEdges N M L Y ↔
      β ∈
        (closedNeighborhood
          (BoundedRatioSteinChen.boundedLargePrimeDependencyGraph
            N M L Y) α).erase α := by
  rw [BoundedRatioSteinChen.mem_boundedOrderedDependencyEdges,
    Finset.mem_erase, mem_closedNeighborhood]
  constructor
  · rintro ⟨_hα, _hβ, hadj⟩
    have hne : β ≠ α := by
      intro h
      exact hadj.1 (congrArg Subtype.val h).symm
    exact ⟨hne, Or.inr hadj⟩
  · rintro ⟨hne, heq | hadj⟩
    · exact False.elim (hne heq)
    · exact ⟨α.2, β.2, hadj⟩

/-- Dependent presentation of all bounded open-neighborhood pairs. -/
abbrev BoundedOpenNeighborhoodPair
    (N M L Y : ℕ) :=
  Σ α :
      {x : ℕ //
        x ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y},
    {β :
        {x : ℕ //
          x ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y} //
      β ∈
        (closedNeighborhood
          (BoundedRatioSteinChen.boundedLargePrimeDependencyGraph
            N M L Y) α).erase α}

/-- Open-neighborhood pairs are canonically the bounded ordered edges. -/
noncomputable def boundedOpenNeighborhoodPairEquiv
    (N M L Y : ℕ) :
    BoundedOpenNeighborhoodPair N M L Y ≃
      {pair : ℕ × ℕ //
        pair ∈
          BoundedRatioSteinChen.boundedOrderedDependencyEdges
            N M L Y} := by
  classical
  let toPair :
      BoundedOpenNeighborhoodPair N M L Y →
        {pair : ℕ × ℕ //
          pair ∈
            BoundedRatioSteinChen.boundedOrderedDependencyEdges
              N M L Y} :=
    fun pair ↦
      ⟨(pair.1.1, pair.2.1.1),
        (pair_mem_boundedOrderedDependencyEdges_iff
          pair.1 pair.2.1).mpr pair.2.2⟩
  let fromPair :
      {pair : ℕ × ℕ //
        pair ∈
          BoundedRatioSteinChen.boundedOrderedDependencyEdges
            N M L Y} →
        BoundedOpenNeighborhoodPair N M L Y :=
    fun pair ↦ by
      have hmem :=
        BoundedRatioSteinChen.mem_boundedOrderedDependencyEdges.mp
          pair.2
      let α :
          {x : ℕ //
            x ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y} :=
        ⟨pair.1.1, hmem.1⟩
      let β :
          {x : ℕ //
            x ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y} :=
        ⟨pair.1.2, hmem.2.1⟩
      exact
        ⟨α,
          ⟨β,
            (pair_mem_boundedOrderedDependencyEdges_iff α β).mp
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
The average conditional `b₂` is exactly the real cast of the unconditional
joint mass on the bounded ordered dependency edges.
-/
theorem boundedConditionalBTwoAverage_eq_boundedSteinBTwoAverage
    (N M L Y : ℕ) :
    boundedConditionalBTwoAverage N M L Y =
      ((boundedSteinBTwoAverage N M L Y : ℚ) : ℝ) := by
  have havg :
      boundedConditionalBTwoAverage N M L Y =
        ∑ α :
            {x : ℕ //
              x ∈
                BoundedRatioSteinChen.boundedGoodStarts N M L Y},
          ∑ β ∈
              (closedNeighborhood
                (BoundedRatioSteinChen.boundedLargePrimeDependencyGraph
                  N M L Y) α).erase α,
            finiteUniformAverage
              (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
                jointMarginal
                  (BoundedRatioSteinChen.boundedLargeUniformPMF
                    M L Y)
                  (BoundedRatioSteinChen.boundedConditionedGoodIndicator
                    N M L Y σ) α β) := by
    unfold boundedConditionalBTwoAverage bTwo
    rw [finiteUniformAverage_fintypeSum]
    apply Finset.sum_congr rfl
    intro α _hα
    exact finiteUniformAverage_finsetSum _ _
  rw [havg]
  simp_rw [boundedConditionalJointAverage]
  have hsigma :
      (∑ α :
          {x : ℕ //
            x ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y},
        ∑ β ∈
            (closedNeighborhood
              (BoundedRatioSteinChen.boundedLargePrimeDependencyGraph
                N M L Y) α).erase α,
          ((boundedJointStartProbability
            M L α.1 β.1 : ℚ) : ℝ)) =
        ∑ pair : BoundedOpenNeighborhoodPair N M L Y,
          ((boundedJointStartProbability
            M L pair.1.1 pair.2.1.1 : ℚ) : ℝ) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro α _hα
    exact
      Finset.sum_subtype
        ((closedNeighborhood
          (BoundedRatioSteinChen.boundedLargePrimeDependencyGraph
            N M L Y) α).erase α)
        (fun _β ↦ Iff.rfl)
        (fun β ↦
          ((boundedJointStartProbability
            M L α.1 β.1 : ℚ) : ℝ))
  rw [hsigma]
  have hequiv :
      (∑ pair : BoundedOpenNeighborhoodPair N M L Y,
          ((boundedJointStartProbability
            M L pair.1.1 pair.2.1.1 : ℚ) : ℝ)) =
        ∑ pair :
            {pair : ℕ × ℕ //
              pair ∈
                BoundedRatioSteinChen.boundedOrderedDependencyEdges
                  N M L Y},
          ((boundedJointStartProbability
            M L pair.1.1 pair.1.2 : ℚ) : ℝ) := by
    exact Fintype.sum_equiv
      (boundedOpenNeighborhoodPairEquiv N M L Y)
      (fun pair : BoundedOpenNeighborhoodPair N M L Y ↦
        ((boundedJointStartProbability
          M L pair.1.1 pair.2.1.1 : ℚ) : ℝ))
      (fun pair :
          {pair : ℕ × ℕ //
            pair ∈
              BoundedRatioSteinChen.boundedOrderedDependencyEdges
                N M L Y} ↦
        ((boundedJointStartProbability
          M L pair.1.1 pair.1.2 : ℚ) : ℝ))
      (fun _pair ↦ rfl)
  rw [hequiv]
  rw [← Finset.sum_subtype
    (BoundedRatioSteinChen.boundedOrderedDependencyEdges N M L Y)
    (fun _pair ↦ Iff.rfl)
    (fun pair ↦
      ((boundedJointStartProbability
        M L pair.1 pair.2 : ℚ) : ℝ))]
  unfold boundedSteinBTwoAverage boundedJointPairMass
  push_cast
  apply Finset.sum_congr rfl
  intro pair _hpair
  rfl

/-! ## Exact overlap/touching/separated partition -/

/-- Dependency edges at strict overlap distance. -/
noncomputable def boundedOverlapDependencyEdges
    (N M L Y : ℕ) : Finset (ℕ × ℕ) :=
  (BoundedRatioSteinChen.boundedOrderedDependencyEdges N M L Y).filter
    fun pair ↦ Nat.dist pair.1 pair.2 < L

/-- Dependency edges at exactly the touching distance. -/
noncomputable def boundedTouchingDependencyEdges
    (N M L Y : ℕ) : Finset (ℕ × ℕ) :=
  (BoundedRatioSteinChen.boundedOrderedDependencyEdges N M L Y).filter
    fun pair ↦ Nat.dist pair.1 pair.2 = L

/-- Dependency edges beyond the touching distance. -/
noncomputable def boundedSeparatedDependencyEdges
    (N M L Y : ℕ) : Finset (ℕ × ℕ) :=
  (BoundedRatioSteinChen.boundedOrderedDependencyEdges N M L Y).filter
    fun pair ↦ L < Nat.dist pair.1 pair.2

@[simp]
theorem mem_boundedOverlapDependencyEdges
    {N M L Y : ℕ} {pair : ℕ × ℕ} :
    pair ∈ boundedOverlapDependencyEdges N M L Y ↔
      pair ∈
          BoundedRatioSteinChen.boundedOrderedDependencyEdges N M L Y ∧
        Nat.dist pair.1 pair.2 < L := by
  simp [boundedOverlapDependencyEdges]

@[simp]
theorem mem_boundedTouchingDependencyEdges
    {N M L Y : ℕ} {pair : ℕ × ℕ} :
    pair ∈ boundedTouchingDependencyEdges N M L Y ↔
      pair ∈
          BoundedRatioSteinChen.boundedOrderedDependencyEdges N M L Y ∧
        Nat.dist pair.1 pair.2 = L := by
  simp [boundedTouchingDependencyEdges]

@[simp]
theorem mem_boundedSeparatedDependencyEdges
    {N M L Y : ℕ} {pair : ℕ × ℕ} :
    pair ∈ boundedSeparatedDependencyEdges N M L Y ↔
      pair ∈
          BoundedRatioSteinChen.boundedOrderedDependencyEdges N M L Y ∧
        L < Nat.dist pair.1 pair.2 := by
  simp [boundedSeparatedDependencyEdges]

theorem boundedOrderedDependencyEdges_eq_three_parts
    (N M L Y : ℕ) :
    BoundedRatioSteinChen.boundedOrderedDependencyEdges N M L Y =
      boundedOverlapDependencyEdges N M L Y ∪
        (boundedTouchingDependencyEdges N M L Y ∪
          boundedSeparatedDependencyEdges N M L Y) := by
  ext pair
  simp only [Finset.mem_union,
    mem_boundedOverlapDependencyEdges,
    mem_boundedTouchingDependencyEdges,
    mem_boundedSeparatedDependencyEdges]
  constructor
  · intro hedge
    rcases lt_trichotomy (Nat.dist pair.1 pair.2) L with
        hlt | heq | hgt
    · exact Or.inl ⟨hedge, hlt⟩
    · exact Or.inr (Or.inl ⟨hedge, heq⟩)
    · exact Or.inr (Or.inr ⟨hedge, hgt⟩)
  · rintro (hover | htouch | hsep)
    · exact hover.1
    · exact htouch.1
    · exact hsep.1

theorem disjoint_boundedOverlap_touching
    (N M L Y : ℕ) :
    Disjoint (boundedOverlapDependencyEdges N M L Y)
      (boundedTouchingDependencyEdges N M L Y) := by
  rw [Finset.disjoint_left]
  intro pair hover htouch
  have ho := (mem_boundedOverlapDependencyEdges.mp hover).2
  have ht := (mem_boundedTouchingDependencyEdges.mp htouch).2
  omega

theorem disjoint_boundedOverlap_separated
    (N M L Y : ℕ) :
    Disjoint (boundedOverlapDependencyEdges N M L Y)
      (boundedSeparatedDependencyEdges N M L Y) := by
  rw [Finset.disjoint_left]
  intro pair hover hsep
  have ho := (mem_boundedOverlapDependencyEdges.mp hover).2
  have hs := (mem_boundedSeparatedDependencyEdges.mp hsep).2
  omega

theorem disjoint_boundedTouching_separated
    (N M L Y : ℕ) :
    Disjoint (boundedTouchingDependencyEdges N M L Y)
      (boundedSeparatedDependencyEdges N M L Y) := by
  rw [Finset.disjoint_left]
  intro pair htouch hsep
  have ht := (mem_boundedTouchingDependencyEdges.mp htouch).2
  have hs := (mem_boundedSeparatedDependencyEdges.mp hsep).2
  omega

theorem boundedJointPairMass_union
    {M L : ℕ} {s t : Finset (ℕ × ℕ)}
    (hdisj : Disjoint s t) :
    boundedJointPairMass M L (s ∪ t) =
      boundedJointPairMass M L s +
        boundedJointPairMass M L t := by
  unfold boundedJointPairMass
  rw [Finset.sum_union hdisj]

theorem boundedSteinBTwoAverage_eq_three_parts
    (N M L Y : ℕ) :
    boundedSteinBTwoAverage N M L Y =
      boundedJointPairMass M L
          (boundedOverlapDependencyEdges N M L Y) +
        boundedJointPairMass M L
          (boundedTouchingDependencyEdges N M L Y) +
        boundedJointPairMass M L
          (boundedSeparatedDependencyEdges N M L Y) := by
  rw [boundedSteinBTwoAverage,
    boundedOrderedDependencyEdges_eq_three_parts]
  rw [boundedJointPairMass_union
    (Finset.disjoint_union_right.mpr
      ⟨disjoint_boundedOverlap_touching N M L Y,
        disjoint_boundedOverlap_separated N M L Y⟩)]
  rw [boundedJointPairMass_union
    (disjoint_boundedTouching_separated N M L Y)]
  ring

/-- Strict-overlap edges carry zero unconditional joint probability. -/
theorem boundedJointPairMass_overlap_eq_zero
    (N M L Y : ℕ) :
    boundedJointPairMass M L
      (boundedOverlapDependencyEdges N M L Y) = 0 := by
  classical
  unfold boundedJointPairMass
  apply Finset.sum_eq_zero
  intro pair hpair
  unfold boundedJointStartProbability uniformEventProbability
  have hempty :
      Finset.univ.filter
          (fun ω : SampleSpace (boundedRatioCutoff M L) ↦
            startAt ω pair.1 L ∧ startAt ω pair.2 L) =
        ∅ := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.not_mem_empty, iff_false]
    exact startEvents_disjoint_of_dist_lt
      (BoundedRatioSteinChen.ne_of_mem_boundedOrderedDependencyEdges
        (mem_boundedOverlapDependencyEdges.mp hpair).1)
      (mem_boundedOverlapDependencyEdges.mp hpair).2
  rw [hempty]
  simp

/-! ## Affine excess on the separated population -/

/-- The bounded joint event is the canonical affine two-start fiber. -/
theorem boundedJointStartProbability_eq_uniformSolutionProbability
    (M L x y : ℕ) (hL : 0 < L) :
    boundedJointStartProbability M L x y =
      uniformSolutionProbability
        (twoStartSystem (boundedRatioCutoff M L) x y L)
        (twoStartRhs L) := by
  classical
  unfold boundedJointStartProbability uniformEventProbability
    uniformSolutionProbability
  congr 1
  rw [Fintype.card_subtype]
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (twoStartSystem_eq_twoStartRhs_iff ω hL).symm

/-- Exact affine normalization on the bounded full cylinder. -/
theorem boundedJointStartProbability_eq_eta_mul_two_pow_rho_div
    (M L x y : ℕ) (hL : 0 < L) :
    boundedJointStartProbability M L x y =
      ((relationEta
          (twoStartSystem (boundedRatioCutoff M L) x y L)
          (twoStartRhs L) : ℚ) *
        (2 : ℚ) ^
          relationRho
            (twoStartSystem (boundedRatioCutoff M L) x y L)) /
        (2 : ℚ) ^ (2 * L) := by
  rw [boundedJointStartProbability_eq_uniformSolutionProbability
    M L x y hL,
    uniformSolutionProbability_eq_eta_mul_two_pow_rho_div]
  congr 1
  simp [Fintype.card_sum, two_mul]

/-- Relation defect of a bounded ordered pair. -/
noncomputable def boundedJointRho
    (M L : ℕ) (pair : ℕ × ℕ) : ℕ :=
  relationRho
    (twoStartSystem
      (boundedRatioCutoff M L) pair.1 pair.2 L)

/-- Natural affine excess weight `2^ρ-1` on a bounded pair. -/
noncomputable def boundedJointDefectWeight
    (M L : ℕ) (pair : ℕ × ℕ) : ℕ :=
  2 ^ boundedJointRho M L pair - 1

/-- Sum of bounded affine excess weights on a finite pair population. -/
noncomputable def boundedJointDefectMass
    (M L : ℕ) (pairs : Finset (ℕ × ℕ)) : ℕ :=
  ∑ pair ∈ pairs, boundedJointDefectWeight M L pair

/-- Pointwise bounded-cylinder version of the affine defect inequality. -/
theorem abs_boundedJointStartProbability_sub_baseline_le
    (M L x y : ℕ) (hL : 0 < L) :
    |boundedJointStartProbability M L x y -
        (1 : ℚ) / (2 : ℚ) ^ (2 * L)| ≤
      (boundedJointDefectWeight M L (x, y) : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  rw [boundedJointStartProbability_eq_eta_mul_two_pow_rho_div
    M L x y hL]
  let A :=
    twoStartSystem (boundedRatioCutoff M L) x y L
  let b := twoStartRhs L
  have habsZ :=
    abs_eta_mul_two_pow_rho_sub_one_le A b
  have habsQ :
      |(relationEta A b : ℚ) *
          (2 : ℚ) ^ relationRho A - 1| ≤
        (2 : ℚ) ^ relationRho A - 1 := by
    exact_mod_cast habsZ
  have hdenom :
      0 < (2 : ℚ) ^ (2 * L) :=
    pow_pos (by norm_num) (2 * L)
  have hnat :
      ((2 ^ relationRho A - 1 : ℕ) : ℚ) =
        (2 : ℚ) ^ relationRho A - 1 := by
    rw [Nat.cast_sub]
    · norm_num
    · exact Nat.one_le_two_pow
  dsimp only [A, b] at habsQ hnat ⊢
  rw [← sub_div, abs_div, abs_of_pos hdenom]
  rw [boundedJointDefectWeight, boundedJointRho, hnat]
  exact div_le_div_of_nonneg_right habsQ hdenom.le

/-- Summed bounded-cylinder affine defect inequality. -/
theorem abs_boundedJointPairMass_sub_baseline_le
    (M L : ℕ) (hL : 0 < L)
    (pairs : Finset (ℕ × ℕ)) :
    |boundedJointPairMass M L pairs -
        (pairs.card : ℚ) / (2 : ℚ) ^ (2 * L)| ≤
      (boundedJointDefectMass M L pairs : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  classical
  have hbaseline :
      (pairs.card : ℚ) / (2 : ℚ) ^ (2 * L) =
        ∑ _pair ∈ pairs,
          (1 : ℚ) / (2 : ℚ) ^ (2 * L) := by
    simp [div_eq_mul_inv]
  rw [boundedJointPairMass, hbaseline,
    ← Finset.sum_sub_distrib]
  calc
    |∑ pair ∈ pairs,
          (boundedJointStartProbability M L pair.1 pair.2 -
            (1 : ℚ) / (2 : ℚ) ^ (2 * L))| ≤
        ∑ pair ∈ pairs,
          |boundedJointStartProbability M L pair.1 pair.2 -
            (1 : ℚ) / (2 : ℚ) ^ (2 * L)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ pair ∈ pairs,
          (boundedJointDefectWeight M L pair : ℚ) /
            (2 : ℚ) ^ (2 * L) := by
      exact Finset.sum_le_sum fun pair _hpair =>
        abs_boundedJointStartProbability_sub_baseline_le
          M L pair.1 pair.2 hL
    _ =
        (boundedJointDefectMass M L pairs : ℚ) /
          (2 : ℚ) ^ (2 * L) := by
      rw [boundedJointDefectMass, Nat.cast_sum, Finset.sum_div]

/-- Bounded joint probabilities are nonnegative. -/
theorem boundedJointStartProbability_nonneg
    (M L x y : ℕ) :
    0 ≤ boundedJointStartProbability M L x y := by
  classical
  unfold boundedJointStartProbability uniformEventProbability
  positivity

/-- Bounded joint mass is monotone under inclusion of pair populations. -/
theorem boundedJointPairMass_mono
    {M L : ℕ} {s t : Finset (ℕ × ℕ)}
    (hst : s ⊆ t) :
    boundedJointPairMass M L s ≤
      boundedJointPairMass M L t := by
  unfold boundedJointPairMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hst
    (fun pair _ht _hs =>
      boundedJointStartProbability_nonneg
        M L pair.1 pair.2)

/-- Separated dependency edges form a subpopulation of Proposition 16.1. -/
theorem boundedSeparatedDependencyEdges_subset
    (N M L Y : ℕ) :
    boundedSeparatedDependencyEdges N M L Y ⊆
      separatedBoundedRatioPairs N M L := by
  intro pair hpair
  have hedge :=
    (mem_boundedSeparatedDependencyEdges.mp hpair).1
  have hdata :=
    BoundedRatioSteinChen.mem_boundedOrderedDependencyEdges.mp
      hedge
  exact mem_separatedBoundedRatioPairs.mpr
    ⟨(BoundedRatioSteinChen.mem_boundedGoodStarts.mp hdata.1).1,
      (BoundedRatioSteinChen.mem_boundedGoodStarts.mp hdata.2.1).1,
      (mem_boundedSeparatedDependencyEdges.mp hpair).2⟩

/--
The separated affine excess on dependency edges is bounded exactly by the
homogeneous mass `R2κ` from Proposition 16.1.
-/
theorem boundedJointDefectMass_separated_le_R2κ
    (N M L Y : ℕ) :
    (boundedJointDefectMass M L
        (boundedSeparatedDependencyEdges N M L Y) : ℝ) ≤
      R2κ N M L := by
  rw [R2κ_eq_filtered_sum]
  simp only [boundedJointDefectMass, Nat.cast_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (boundedSeparatedDependencyEdges_subset N M L Y)
  intro pair _hfull _hsmall
  positivity

/--
Finite separated-pair majorant.  Its only arithmetic excess is the already
named quantity `R2κ`; the other term is the independent edge baseline.
-/
theorem boundedJointPairMass_separated_le
    {N M L Y : ℕ} (hL : 0 < L) :
    ((boundedJointPairMass M L
      (boundedSeparatedDependencyEdges N M L Y) : ℚ) : ℝ) ≤
      ((boundedSeparatedDependencyEdges N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) +
        R2κ N M L / (2 : ℝ) ^ (2 * L) := by
  have habsQ :=
    abs_boundedJointPairMass_sub_baseline_le
      M L hL (boundedSeparatedDependencyEdges N M L Y)
  have habsR :
      |((boundedJointPairMass M L
            (boundedSeparatedDependencyEdges N M L Y) : ℚ) : ℝ) -
          ((boundedSeparatedDependencyEdges N M L Y).card : ℝ) /
            (2 : ℝ) ^ (2 * L)| ≤
        (boundedJointDefectMass M L
            (boundedSeparatedDependencyEdges N M L Y) : ℝ) /
          (2 : ℝ) ^ (2 * L) := by
    have hcast :
        (((|boundedJointPairMass M L
              (boundedSeparatedDependencyEdges N M L Y) -
            ((boundedSeparatedDependencyEdges N M L Y).card : ℚ) /
              (2 : ℚ) ^ (2 * L)| : ℚ)) : ℝ) ≤
          ((((boundedJointDefectMass M L
              (boundedSeparatedDependencyEdges N M L Y) : ℚ) /
                (2 : ℚ) ^ (2 * L)) : ℚ) : ℝ) :=
      (Rat.cast_le).2 habsQ
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat] using hcast
  have hpoint :
      ((boundedJointPairMass M L
            (boundedSeparatedDependencyEdges N M L Y) : ℚ) : ℝ) -
          ((boundedSeparatedDependencyEdges N M L Y).card : ℝ) /
            (2 : ℝ) ^ (2 * L) ≤
        (boundedJointDefectMass M L
            (boundedSeparatedDependencyEdges N M L Y) : ℝ) /
          (2 : ℝ) ^ (2 * L) :=
    (le_abs_self _).trans habsR
  have hexcess :=
    boundedJointDefectMass_separated_le_R2κ N M L Y
  have hdiv :
      (boundedJointDefectMass M L
          (boundedSeparatedDependencyEdges N M L Y) : ℝ) /
            (2 : ℝ) ^ (2 * L) ≤
        R2κ N M L / (2 : ℝ) ^ (2 * L) :=
    div_le_div_of_nonneg_right hexcess (by positivity)
  linarith

/-! ## Linear touching geometry and the finite combined majorant -/

/-- Forward-oriented touching candidates with lower coordinate below `M`. -/
noncomputable def boundedForwardTouchingCandidates
    (M L : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range M).image fun x ↦ (x, x + L)

/-- Backward-oriented touching candidates with lower coordinate below `M`. -/
noncomputable def boundedBackwardTouchingCandidates
    (M L : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range M).image fun y ↦ (y + L, y)

/-- Every bounded touching edge has one of the two canonical orientations. -/
theorem boundedTouchingDependencyEdges_subset_candidates
    (N M L Y : ℕ) :
    boundedTouchingDependencyEdges N M L Y ⊆
      boundedForwardTouchingCandidates M L ∪
        boundedBackwardTouchingCandidates M L := by
  intro pair hpair
  have htouch :=
    (mem_boundedTouchingDependencyEdges.mp hpair).2
  have hedge :=
    (mem_boundedTouchingDependencyEdges.mp hpair).1
  have hdata :=
    BoundedRatioSteinChen.mem_boundedOrderedDependencyEdges.mp
      hedge
  have hxlt :
      pair.1 < M :=
    (mem_boundedRatioBlock.mp
      (BoundedRatioSteinChen.mem_boundedGoodStarts.mp hdata.1).1).2
  have hylt :
      pair.2 < M :=
    (mem_boundedRatioBlock.mp
      (BoundedRatioSteinChen.mem_boundedGoodStarts.mp hdata.2.1).1).2
  rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq htouch with
      hforward | hbackward
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr
      ⟨pair.1, Finset.mem_range.mpr hxlt, by
        ext <;> simp [hforward]⟩
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨pair.2, Finset.mem_range.mpr hylt, by
        ext <;> simp [hbackward]⟩

/-- The number of ordered touching dependency edges is at most `2M`. -/
theorem card_boundedTouchingDependencyEdges_le
    (N M L Y : ℕ) :
    (boundedTouchingDependencyEdges N M L Y).card ≤
      2 * M := by
  calc
    (boundedTouchingDependencyEdges N M L Y).card ≤
        (boundedForwardTouchingCandidates M L ∪
          boundedBackwardTouchingCandidates M L).card :=
      Finset.card_le_card
        (boundedTouchingDependencyEdges_subset_candidates N M L Y)
    _ ≤
        (boundedForwardTouchingCandidates M L).card +
          (boundedBackwardTouchingCandidates M L).card :=
      Finset.card_union_le _ _
    _ ≤ (Finset.range M).card + (Finset.range M).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * M := by simp [two_mul]

/-- A joint Bernoulli marginal is bounded by either one-point marginal. -/
theorem jointMarginal_le_marginal_left
    {Ω ι : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (α β : ι) :
    jointMarginal μ X α β ≤ marginal μ X α := by
  classical
  unfold jointMarginal marginal eventProbability
  apply Finset.sum_le_sum
  intro ω _hω
  by_cases hα : X α ω = true
  · by_cases hβ : X β ω = true
    · simp [hα, hβ]
    · simp [hα, hβ, μ.nonneg ω]
  · simp [hα]

/--
Elementary pointwise touching bound obtained from one exact conditional
marginal.  This is weaker by one factor `2⁻ᴸ` than the touching estimate
claimed in Lemma 17.37, but requires no new connector.
-/
theorem boundedJointStartProbability_cast_le_marginal
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (α β :
      {x : ℕ //
        x ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y}) :
    ((boundedJointStartProbability M L α.1 β.1 : ℚ) : ℝ) ≤
      (1 : ℝ) / (2 : ℝ) ^ L := by
  calc
    ((boundedJointStartProbability M L α.1 β.1 : ℚ) : ℝ) =
        finiteUniformAverage
          (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
            jointMarginal
              (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
              (BoundedRatioSteinChen.boundedConditionedGoodIndicator
                N M L Y σ) α β) :=
      (boundedConditionalJointAverage N M L Y α β).symm
    _ ≤
        finiteUniformAverage
          (fun σ : SmallSample (boundedRatioCutoff M L) Y ↦
            marginal
              (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
              (BoundedRatioSteinChen.boundedConditionedGoodIndicator
                N M L Y σ) α) := by
      apply finiteUniformAverage_mono
      intro σ
      exact jointMarginal_le_marginal_left
        (BoundedRatioSteinChen.boundedLargeUniformPMF M L Y)
        (BoundedRatioSteinChen.boundedConditionedGoodIndicator
          N M L Y σ) α β
    _ = (1 : ℝ) / (2 : ℝ) ^ L := by
      simp_rw [
        BoundedRatioSteinChen.marginal_boundedConditionedGoodIndicator_eq_baseline
          hN hL hLY]
      unfold finiteUniformAverage
      simp

/-- The complete touching joint mass is bounded by its linear population. -/
theorem boundedJointPairMass_touching_le
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    ((boundedJointPairMass M L
      (boundedTouchingDependencyEdges N M L Y) : ℚ) : ℝ) ≤
      ((boundedTouchingDependencyEdges N M L Y).card : ℝ) /
        (2 : ℝ) ^ L := by
  unfold boundedJointPairMass
  push_cast
  calc
    ∑ pair ∈ boundedTouchingDependencyEdges N M L Y,
        ((boundedJointStartProbability
          M L pair.1 pair.2 : ℚ) : ℝ) ≤
      ∑ _pair ∈ boundedTouchingDependencyEdges N M L Y,
        (1 : ℝ) / (2 : ℝ) ^ L := by
      apply Finset.sum_le_sum
      intro pair hpair
      have hdata :=
        BoundedRatioSteinChen.mem_boundedOrderedDependencyEdges.mp
          (mem_boundedTouchingDependencyEdges.mp hpair).1
      exact boundedJointStartProbability_cast_le_marginal
        hN hL hLY
        ⟨pair.1, hdata.1⟩
        ⟨pair.2, hdata.2.1⟩
    _ =
        ((boundedTouchingDependencyEdges N M L Y).card : ℝ) /
          (2 : ℝ) ^ L := by
      simp [div_eq_mul_inv]

/-- Coarse but fully explicit `2M·2⁻ᴸ` touching majorant. -/
theorem boundedJointPairMass_touching_le_two_mul
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    ((boundedJointPairMass M L
      (boundedTouchingDependencyEdges N M L Y) : ℚ) : ℝ) ≤
      (2 * M : ℝ) / (2 : ℝ) ^ L := by
  refine (boundedJointPairMass_touching_le hN hL hLY).trans ?_
  apply div_le_div_of_nonneg_right
  · exact_mod_cast
      card_boundedTouchingDependencyEdges_le N M L Y
  · positivity

/-! ### The manuscript-strength touching estimate at cutoff `2L ≤ Y` -/

/--
For two touching bounded good starts, every non-root vertex of the double
tree is non-defective at cutoff `2L`, provided `2L ≤ Y`.
-/
theorem touchingDefectIndices_eq_empty_of_boundedGood
    {N M L Y x : ℕ} (h2LY : 2 * L ≤ Y)
    (hx :
      x ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y)
    (hy :
      x + L ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y) :
    Affine.TouchingDefectRank.touchingDefectIndices x L = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro s hs
  have hsDefective :
      DefectivePredicate.HDefective
        (2 * L)
        (Affine.TouchingDefectRank.touchingVertexLabel x L s) := by
    simpa [Affine.TouchingDefectRank.touchingDefectIndices] using hs
  have hsDefectiveY :
      DefectivePredicate.HDefective
        Y (Affine.TouchingDefectRank.touchingVertexLabel x L s) :=
    fun p hp hYp ↦
      hsDefective p hp (lt_of_le_of_lt h2LY hYp)
  cases s with
  | inl i =>
      apply (BoundedRatioSteinChen.mem_boundedGoodStarts.mp hx).2
      rw [BoundedRatioSteinChen.mem_boundedTerminalBadStarts]
      refine
        ⟨(BoundedRatioSteinChen.mem_boundedGoodStarts.mp hx).1,
          i.1, i.2, ?_⟩
      rw [LargeOddKernel.largeOddKernel_eq_one_iff_hDefective]
      simpa [Affine.TouchingDefectRank.touchingVertexLabel] using
        hsDefectiveY
  | inr i =>
      apply (BoundedRatioSteinChen.mem_boundedGoodStarts.mp hy).2
      rw [BoundedRatioSteinChen.mem_boundedTerminalBadStarts]
      refine
        ⟨(BoundedRatioSteinChen.mem_boundedGoodStarts.mp hy).1,
          i.1, i.2, ?_⟩
      rw [LargeOddKernel.largeOddKernel_eq_one_iff_hDefective]
      simpa [Affine.TouchingDefectRank.touchingVertexLabel,
        Nat.add_assoc] using hsDefectiveY

/--
The full two-start relation rank is zero for a forward-oriented touching pair
of bounded good starts.  The proof transports the existing double-tree rank
theorem between two adequate finite cutoffs.
-/
theorem relationRho_bounded_touching_eq_zero
    {N M L Y x : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (h2LY : 2 * L ≤ Y)
    (hx :
      x ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y)
    (hy :
      x + L ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y) :
    relationRho
        (twoStartSystem (boundedRatioCutoff M L)
          x (x + L) L) = 0 := by
  have hx2 :
      2 ≤ x :=
    hN.trans
      (mem_boundedRatioBlock.mp
        (BoundedRatioSteinChen.mem_boundedGoodStarts.mp hx).1).1
  have hxd :
      x ∈ dyadicBlock x := by
    simp [dyadicBlock]
    omega
  have hdefects :=
    touchingDefectIndices_eq_empty_of_boundedGood h2LY hx hy
  have hinjective :=
    Affine.TouchingDefectRank.touchingDefectRestriction_injective
      hx2 hxd hL
  have hrhoDyadic :
      relationRho
          (touchingSystem (dyadicCutoff x (2 * L)) x L) = 0 := by
    unfold relationRho
    apply Nat.eq_zero_of_le_zero
    calc
      Module.finrank F₂
          (RelationSpace
            (touchingSystem (dyadicCutoff x (2 * L)) x L)) ≤
        Module.finrank F₂
          ((s :
            ↥(Affine.TouchingDefectRank.touchingDefectIndices x L)) →
              F₂) :=
        LinearMap.finrank_le_finrank_of_injective hinjective
      _ =
          (Affine.TouchingDefectRank.touchingDefectIndices x L).card := by
        rw [Module.finrank_fintype_fun_eq_card]
        simp
      _ = 0 := by rw [hdefects]; simp
  let G :=
    max (boundedRatioCutoff M L) (dyadicCutoff x (2 * L))
  have hlabelBounded :
      ∀ v : Sum (Fin (L + 1)) (Fin (L + 1)),
        twoStartCompleteVertexLabel x (x + L) L v ≤
          boundedRatioCutoff M L := by
    intro v
    have hylt :
        x + L < M :=
      (mem_boundedRatioBlock.mp
        (BoundedRatioSteinChen.mem_boundedGoodStarts.mp hy).1).2
    cases v with
    | inl v =>
        simp only [twoStartCompleteVertexLabel]
        unfold startCompleteVertexLabel boundedRatioCutoff
        split
        · omega
        · have hv := v.2
          omega
    | inr v =>
        simp only [twoStartCompleteVertexLabel]
        unfold startCompleteVertexLabel boundedRatioCutoff
        split
        · omega
        · have hv := v.2
          omega
  have hlabelDyadic :
      ∀ v : Sum (Fin (L + 1)) (Fin (L + 1)),
        twoStartCompleteVertexLabel x (x + L) L v ≤
          dyadicCutoff x (2 * L) := by
    intro v
    cases v with
    | inl v =>
        simp only [twoStartCompleteVertexLabel]
        unfold startCompleteVertexLabel dyadicCutoff
        split
        · omega
        · have hv := v.2
          omega
    | inr v =>
        simp only [twoStartCompleteVertexLabel]
        unfold startCompleteVertexLabel dyadicCutoff
        split
        · omega
        · have hv := v.2
          omega
  have hboundedToG :
      relationRho
          (twoStartSystem (boundedRatioCutoff M L)
            x (x + L) L) =
        relationRho (twoStartSystem G x (x + L) L) := by
    apply relationRho_twoStartSystem_cutoff_invariant
    · exact le_max_left _ _
    · exact hx2
    · omega
    · exact hlabelBounded
  have hdyadicToG :
      relationRho
          (twoStartSystem (dyadicCutoff x (2 * L))
            x (x + L) L) =
        relationRho (twoStartSystem G x (x + L) L) := by
    apply relationRho_twoStartSystem_cutoff_invariant
    · exact le_max_right _ _
    · exact hx2
    · omega
    · exact hlabelDyadic
  calc
    relationRho
        (twoStartSystem (boundedRatioCutoff M L)
          x (x + L) L) =
      relationRho (twoStartSystem G x (x + L) L) :=
        hboundedToG
    _ =
      relationRho
        (twoStartSystem (dyadicCutoff x (2 * L))
          x (x + L) L) :=
        hdyadicToG.symm
    _ =
      relationRho
        (touchingSystem (dyadicCutoff x (2 * L)) x L) := by
        rw [touchingSystem_eq_twoStartSystem]
    _ = 0 := hrhoDyadic

/-- Joint start probability is symmetric on the bounded full cylinder. -/
theorem boundedJointStartProbability_comm
    (M L x y : ℕ) :
    boundedJointStartProbability M L x y =
      boundedJointStartProbability M L y x := by
  classical
  unfold boundedJointStartProbability uniformEventProbability
  have hfilter :
      Finset.univ.filter
          (fun ω : SampleSpace (boundedRatioCutoff M L) ↦
            startAt ω x L ∧ startAt ω y L) =
        Finset.univ.filter
          (fun ω : SampleSpace (boundedRatioCutoff M L) ↦
            startAt ω y L ∧ startAt ω x L) := by
    ext ω
    simp [and_comm]
  rw [hfilter]

/-- A forward touching good pair has at most the independent baseline mass. -/
theorem boundedJointStartProbability_touching_forward_le
    {N M L Y x : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (h2LY : 2 * L ≤ Y)
    (hx :
      x ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y)
    (hy :
      x + L ∈ BoundedRatioSteinChen.boundedGoodStarts N M L Y) :
    boundedJointStartProbability M L x (x + L) ≤
      (1 : ℚ) / (2 : ℚ) ^ (2 * L) := by
  rw [boundedJointStartProbability_eq_eta_mul_two_pow_rho_div
    M L x (x + L) hL,
    relationRho_bounded_touching_eq_zero hN hL h2LY hx hy,
    pow_zero, mul_one]
  rcases relationEta_eq_zero_or_one
      (twoStartSystem (boundedRatioCutoff M L) x (x + L) L)
      (twoStartRhs L) with heta | heta
  · rw [heta]
    norm_num
  · rw [heta]
    norm_num

/-- Every bounded touching dependency edge has baseline joint mass. -/
theorem boundedJointStartProbability_touching_le
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (h2LY : 2 * L ≤ Y)
    {pair : ℕ × ℕ}
    (hpair : pair ∈ boundedTouchingDependencyEdges N M L Y) :
    boundedJointStartProbability M L pair.1 pair.2 ≤
      (1 : ℚ) / (2 : ℚ) ^ (2 * L) := by
  have hdata :=
    BoundedRatioSteinChen.mem_boundedOrderedDependencyEdges.mp
      (mem_boundedTouchingDependencyEdges.mp hpair).1
  rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq
      (mem_boundedTouchingDependencyEdges.mp hpair).2 with
      hforward | hbackward
  · have hy :
        pair.1 + L ∈
          BoundedRatioSteinChen.boundedGoodStarts N M L Y := by
      simpa only [hforward] using hdata.2.1
    rw [hforward]
    exact boundedJointStartProbability_touching_forward_le
      hN hL h2LY hdata.1 hy
  · have hx :
        pair.2 + L ∈
          BoundedRatioSteinChen.boundedGoodStarts N M L Y := by
      simpa only [hbackward] using hdata.1
    rw [boundedJointStartProbability_comm, hbackward]
    exact boundedJointStartProbability_touching_forward_le
      hN hL h2LY hdata.2.1 hx

/-- Manuscript-strength finite touching mass bound. -/
theorem boundedJointPairMass_touching_le_baseline
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (h2LY : 2 * L ≤ Y) :
    boundedJointPairMass M L
        (boundedTouchingDependencyEdges N M L Y) ≤
      ((boundedTouchingDependencyEdges N M L Y).card : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  unfold boundedJointPairMass
  calc
    ∑ pair ∈ boundedTouchingDependencyEdges N M L Y,
        boundedJointStartProbability M L pair.1 pair.2 ≤
      ∑ _pair ∈ boundedTouchingDependencyEdges N M L Y,
        (1 : ℚ) / (2 : ℚ) ^ (2 * L) := by
      exact Finset.sum_le_sum fun pair hpair =>
        boundedJointStartProbability_touching_le
          hN hL h2LY hpair
    _ =
        ((boundedTouchingDependencyEdges N M L Y).card : ℚ) /
          (2 : ℚ) ^ (2 * L) := by
      simp [div_eq_mul_inv]

/-- Touching mass is at most `2M / 2^(2L)`. -/
theorem boundedJointPairMass_touching_le_two_mul_baseline
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (h2LY : 2 * L ≤ Y) :
    ((boundedJointPairMass M L
      (boundedTouchingDependencyEdges N M L Y) : ℚ) : ℝ) ≤
      (2 * M : ℝ) / (2 : ℝ) ^ (2 * L) := by
  have hmassQ :=
    boundedJointPairMass_touching_le_baseline
      (N := N) (M := M) (L := L) (Y := Y)
      hN hL h2LY
  have hmassR :
      ((boundedJointPairMass M L
          (boundedTouchingDependencyEdges N M L Y) : ℚ) : ℝ) ≤
        ((boundedTouchingDependencyEdges N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) := by
    have hcast :
        ((boundedJointPairMass M L
            (boundedTouchingDependencyEdges N M L Y) : ℚ) : ℝ) ≤
          ((((boundedTouchingDependencyEdges N M L Y).card : ℚ) /
            (2 : ℚ) ^ (2 * L) : ℚ) : ℝ) :=
      (Rat.cast_le).2 hmassQ
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
      Rat.cast_ofNat] using hcast
  refine hmassR.trans ?_
  apply div_le_div_of_nonneg_right
  · exact_mod_cast
      card_boundedTouchingDependencyEdges_le N M L Y
  · positivity

/--
Exact manuscript-strength finite majorant for the averaged bounded-ratio
second term.

The overlap contribution vanishes, every touching edge contributes at most
the independent baseline, and the separated excess is controlled by `R2κ`.
-/
theorem boundedConditionalBTwoAverage_le_exactFiniteMajorant
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (h2LY : 2 * L ≤ Y) :
    boundedConditionalBTwoAverage N M L Y ≤
      ((boundedTouchingDependencyEdges N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) +
        ((boundedSeparatedDependencyEdges N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) +
        R2κ N M L / (2 : ℝ) ^ (2 * L) := by
  have htouchQ :=
    boundedJointPairMass_touching_le_baseline
      (N := N) (M := M) (L := L) (Y := Y)
      hN hL h2LY
  have htouch :
      ((boundedJointPairMass M L
          (boundedTouchingDependencyEdges N M L Y) : ℚ) : ℝ) ≤
        ((boundedTouchingDependencyEdges N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) := by
    have hcast :
        ((boundedJointPairMass M L
            (boundedTouchingDependencyEdges N M L Y) : ℚ) : ℝ) ≤
          ((((boundedTouchingDependencyEdges N M L Y).card : ℚ) /
            (2 : ℚ) ^ (2 * L) : ℚ) : ℝ) :=
      (Rat.cast_le).2 htouchQ
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
      Rat.cast_ofNat] using hcast
  have hsep :=
    boundedJointPairMass_separated_le
      (N := N) (M := M) (Y := Y) hL
  calc
    boundedConditionalBTwoAverage N M L Y =
        (((boundedJointPairMass M L
              (boundedOverlapDependencyEdges N M L Y) +
            boundedJointPairMass M L
              (boundedTouchingDependencyEdges N M L Y) +
            boundedJointPairMass M L
              (boundedSeparatedDependencyEdges N M L Y) : ℚ) : ℝ)) := by
      rw [boundedConditionalBTwoAverage_eq_boundedSteinBTwoAverage,
        boundedSteinBTwoAverage_eq_three_parts]
    _ =
        ((boundedJointPairMass M L
          (boundedTouchingDependencyEdges N M L Y) : ℚ) : ℝ) +
        ((boundedJointPairMass M L
          (boundedSeparatedDependencyEdges N M L Y) : ℚ) : ℝ) := by
      rw [boundedJointPairMass_overlap_eq_zero]
      push_cast
      ring
    _ ≤
        ((boundedTouchingDependencyEdges N M L Y).card : ℝ) /
            (2 : ℝ) ^ (2 * L) +
          (((boundedSeparatedDependencyEdges N M L Y).card : ℝ) /
              (2 : ℝ) ^ (2 * L) +
            R2κ N M L / (2 : ℝ) ^ (2 * L)) :=
      add_le_add htouch hsep
    _ =
        ((boundedTouchingDependencyEdges N M L Y).card : ℝ) /
            (2 : ℝ) ^ (2 * L) +
          ((boundedSeparatedDependencyEdges N M L Y).card : ℝ) /
            (2 : ℝ) ^ (2 * L) +
          R2κ N M L / (2 : ℝ) ^ (2 * L) := by
      ring

/--
Coarse manuscript-strength finite majorant.  The touching population is at
most `2M`, while the separated population is bounded by the full dependency
edge population.
-/
theorem boundedConditionalBTwoAverage_le_strongFiniteMajorant
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (h2LY : 2 * L ≤ Y) :
    boundedConditionalBTwoAverage N M L Y ≤
      (2 * M : ℝ) / (2 : ℝ) ^ (2 * L) +
        ((BoundedRatioSteinChen.boundedOrderedDependencyEdges
            N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) +
        R2κ N M L / (2 : ℝ) ^ (2 * L) := by
  have hexact :=
    boundedConditionalBTwoAverage_le_exactFiniteMajorant
      (N := N) (M := M) (L := L) (Y := Y)
      hN hL h2LY
  have htouchCard :
      ((boundedTouchingDependencyEdges N M L Y).card : ℝ) ≤
        (2 * M : ℝ) := by
    exact_mod_cast
      card_boundedTouchingDependencyEdges_le N M L Y
  have htouchDiv :
      ((boundedTouchingDependencyEdges N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) ≤
        (2 * M : ℝ) / (2 : ℝ) ^ (2 * L) :=
    div_le_div_of_nonneg_right htouchCard (by positivity)
  have hseparatedCard :
      (boundedSeparatedDependencyEdges N M L Y).card ≤
        (BoundedRatioSteinChen.boundedOrderedDependencyEdges
          N M L Y).card :=
    Finset.card_filter_le _ _
  have hseparatedCardReal :
      ((boundedSeparatedDependencyEdges N M L Y).card : ℝ) ≤
        ((BoundedRatioSteinChen.boundedOrderedDependencyEdges
          N M L Y).card : ℝ) := by
    exact_mod_cast hseparatedCard
  have hseparatedDiv :
      ((boundedSeparatedDependencyEdges N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) ≤
        ((BoundedRatioSteinChen.boundedOrderedDependencyEdges
          N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) :=
    div_le_div_of_nonneg_right hseparatedCardReal (by positivity)
  linarith

/--
Fallback finite majorant for the averaged bounded-ratio second term.

The overlap contribution is zero and the separated excess is exactly
controlled by `R2κ`.  Only the displayed touching summand is weaker than
the `O(M)2⁻²ᴸ` estimate asserted in Lemma 17.37.
-/
theorem boundedConditionalBTwoAverage_le_finiteMajorant
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    boundedConditionalBTwoAverage N M L Y ≤
      (2 * M : ℝ) / (2 : ℝ) ^ L +
        ((BoundedRatioSteinChen.boundedOrderedDependencyEdges
            N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) +
        R2κ N M L / (2 : ℝ) ^ (2 * L) := by
  have htouch :=
    boundedJointPairMass_touching_le_two_mul
      (N := N) (M := M) (Y := Y) hN hL hLY
  have hsep :=
    boundedJointPairMass_separated_le
      (N := N) (M := M) (Y := Y) hL
  have hcard :
      (boundedSeparatedDependencyEdges N M L Y).card ≤
        (BoundedRatioSteinChen.boundedOrderedDependencyEdges
          N M L Y).card :=
    Finset.card_filter_le _ _
  have hcardR :
      ((boundedSeparatedDependencyEdges N M L Y).card : ℝ) ≤
        ((BoundedRatioSteinChen.boundedOrderedDependencyEdges
          N M L Y).card : ℝ) := by
    exact_mod_cast hcard
  have hcardDiv :
      ((boundedSeparatedDependencyEdges N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) ≤
        ((BoundedRatioSteinChen.boundedOrderedDependencyEdges
          N M L Y).card : ℝ) /
          (2 : ℝ) ^ (2 * L) :=
    div_le_div_of_nonneg_right hcardR (by positivity)
  calc
    boundedConditionalBTwoAverage N M L Y =
        (((boundedJointPairMass M L
              (boundedOverlapDependencyEdges N M L Y) +
            boundedJointPairMass M L
              (boundedTouchingDependencyEdges N M L Y) +
            boundedJointPairMass M L
              (boundedSeparatedDependencyEdges N M L Y) : ℚ) : ℝ)) := by
      rw [boundedConditionalBTwoAverage_eq_boundedSteinBTwoAverage,
        boundedSteinBTwoAverage_eq_three_parts]
    _ =
        ((boundedJointPairMass M L
          (boundedTouchingDependencyEdges N M L Y) : ℚ) : ℝ) +
        ((boundedJointPairMass M L
          (boundedSeparatedDependencyEdges N M L Y) : ℚ) : ℝ) := by
      rw [boundedJointPairMass_overlap_eq_zero]
      push_cast
      ring
    _ ≤
        (2 * M : ℝ) / (2 : ℝ) ^ L +
          (((boundedSeparatedDependencyEdges N M L Y).card : ℝ) /
              (2 : ℝ) ^ (2 * L) +
            R2κ N M L / (2 : ℝ) ^ (2 * L)) := by
      linarith
    _ ≤
        (2 * M : ℝ) / (2 : ℝ) ^ L +
          ((BoundedRatioSteinChen.boundedOrderedDependencyEdges
              N M L Y).card : ℝ) /
            (2 : ℝ) ^ (2 * L) +
          R2κ N M L / (2 : ℝ) ^ (2 * L) := by
      linarith

end

end BoundedRatioSteinChenSecondTerm
end PaperC
