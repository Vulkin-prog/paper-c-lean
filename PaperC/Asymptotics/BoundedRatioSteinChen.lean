import PaperC.Analysis.DependencyEdgeBound
import PaperC.Asymptotics.DependencyEdgesCritical
import PaperC.Asymptotics.PropositionSixteenOneCore
import PaperC.Probability.ConditionalAGGAverage

set_option maxHeartbeats 1800000

/-!
# Stein--Chen on a bounded-ratio interval

This module transports the finite probability infrastructure of Section 13
from the dyadic block `[N,2N)` to the literal bounded-ratio interval
`[N,M)` used in Proposition 16.1.  Its scope is the finite kernel of
Lemma 17.35 and the uniform little-oh conclusion for the dependency edges
in Lemma 17.36.  It does not claim Lemma 17.35 in full, nor the sharper
displayed quantitative majorant preceding the conclusion of Lemma 17.36.

The construction is intentionally independent of Theorem 16.2.  In
particular, it does not use the aggregate
the bounded-ratio Poisson closure.  It proves:

* the exact conditional marginal `2⁻ᴸ` at every good start;
* the exact conditional dependency graph on the complete interval;
* the pointwise Arratia--Goldstein--Gordon estimate;
* the exact first Stein--Chen term and the good/bad parameter identity;
* the finite prime-witness edge estimate on `[N,M)`;
* the `o_C(M²)` edge conclusion for
  `[M/2^j,M)` at every fixed `j`.

The still absent connectors are the bounded-ratio bad-start cardinal and
probability-mass estimates from Lemmas 17.33--17.34, the mixture/coupling
from the conditioned cylinder back to the literal retained law, and the
identification and estimation of the averaged second Stein--Chen term in
Lemma 17.37.  Its separated contribution is governed by Proposition 16.1.
No cylinder-alignment assertion is made here.
-/

namespace PaperC
namespace BoundedRatioSteinChen

open scoped BigOperators NNReal

open ArratiaGoldsteinGordonInput
open ConditionalAGGInstantiation
open ConditionalAGGAverage
open ConditionalDependencyGraph
open ConditionalStartProbability
open LargeOddKernel
open LargePrimeDependencyGraph
open PropositionSixteenOne
open SectionThirteenFiniteBound

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Good starts and the bounded-ratio graph -/

/--
The terminal bad starts in `[N,M)`: at least one non-root vertex has
trivial odd kernel above `Y`.
-/
noncomputable def boundedTerminalBadStarts
    (N M L Y : ℕ) : Finset ℕ :=
  (boundedRatioBlock N M).filter fun x ↦
    ∃ j ∈ Finset.range L, largeOddKernel Y (x + j) = 1

@[simp]
theorem mem_boundedTerminalBadStarts
    {N M L Y x : ℕ} :
    x ∈ boundedTerminalBadStarts N M L Y ↔
      x ∈ boundedRatioBlock N M ∧
        ∃ j < L, largeOddKernel Y (x + j) = 1 := by
  simp [boundedTerminalBadStarts]

/-- Good starts in `[N,M)`. -/
noncomputable def boundedGoodStarts
    (N M L Y : ℕ) : Finset ℕ :=
  boundedRatioBlock N M \ boundedTerminalBadStarts N M L Y

@[simp]
theorem mem_boundedGoodStarts
    {N M L Y x : ℕ} :
    x ∈ boundedGoodStarts N M L Y ↔
      x ∈ boundedRatioBlock N M ∧
        x ∉ boundedTerminalBadStarts N M L Y := by
  simp [boundedGoodStarts]

/-- The literal large-prime graph on the good starts of `[N,M)`. -/
def boundedLargePrimeDependencyGraph
    (N M L Y : ℕ) :
    SimpleGraph {x : ℕ // x ∈ boundedGoodStarts N M L Y} where
  Adj x y := LargePrimeAdjacent L Y x.1 y.1
  symm := fun _ _ h ↦ largePrimeAdjacent_symm h
  loopless := fun x h ↦ not_largePrimeAdjacent_self L Y x.1 h

@[simp]
theorem boundedLargePrimeDependencyGraph_adj
    {N M L Y : ℕ}
    {x y : {z : ℕ // z ∈ boundedGoodStarts N M L Y}} :
    (boundedLargePrimeDependencyGraph N M L Y).Adj x y ↔
      LargePrimeAdjacent L Y x.1 y.1 :=
  Iff.rfl

/-- Ordered distinct dependency edges on `[N,M)`. -/
noncomputable def boundedOrderedDependencyEdges
    (N M L Y : ℕ) : Finset (ℕ × ℕ) :=
  ((boundedGoodStarts N M L Y).product
    (boundedGoodStarts N M L Y)).filter
      fun xy ↦ LargePrimeAdjacent L Y xy.1 xy.2

@[simp]
theorem mem_boundedOrderedDependencyEdges
    {N M L Y : ℕ} {xy : ℕ × ℕ} :
    xy ∈ boundedOrderedDependencyEdges N M L Y ↔
      xy.1 ∈ boundedGoodStarts N M L Y ∧
        xy.2 ∈ boundedGoodStarts N M L Y ∧
          LargePrimeAdjacent L Y xy.1 xy.2 := by
  classical
  rcases xy with ⟨x, y⟩
  simp [boundedOrderedDependencyEdges, and_assoc]

theorem ne_of_mem_boundedOrderedDependencyEdges
    {N M L Y x y : ℕ}
    (hxy : (x, y) ∈ boundedOrderedDependencyEdges N M L Y) :
    x ≠ y :=
  (mem_boundedOrderedDependencyEdges.mp hxy).2.2.1

/-! ## The exact conditional system (Lemma 17.35) -/

/-- Uniform law on the unfixed coordinates of the bounded-ratio cylinder. -/
noncomputable def boundedLargeUniformPMF
    (M L Y : ℕ) :
    FinitePMF (LargeSample (boundedRatioCutoff M L) Y) :=
  largeUniformPMF (boundedRatioCutoff M L) Y

/-- Conditioned indicators indexed by all bounded-ratio good starts. -/
noncomputable def boundedConditionedGoodIndicator
    (N M L Y : ℕ)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    {x : ℕ // x ∈ boundedGoodStarts N M L Y} →
      LargeSample (boundedRatioCutoff M L) Y → Bool := by
  classical
  exact fun x η ↦
    decide
      (startAt
        (assemble (boundedRatioCutoff M L) Y σ η) x.1 L)

@[simp]
theorem boundedConditionedGoodIndicator_eq_true_iff
    {N M L Y : ℕ}
    {σ : SmallSample (boundedRatioCutoff M L) Y}
    {x : {x : ℕ // x ∈ boundedGoodStarts N M L Y}}
    {η : LargeSample (boundedRatioCutoff M L) Y} :
    boundedConditionedGoodIndicator N M L Y σ x η = true ↔
      startAt
        (assemble (boundedRatioCutoff M L) Y σ η) x.1 L := by
  simp [boundedConditionedGoodIndicator]

theorem boundedConditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates
    {N M L Y : ℕ}
    (hL : 0 < L)
    (σ : SmallSample (boundedRatioCutoff M L) Y)
    (x : {x : ℕ // x ∈ boundedGoodStarts N M L Y})
    (η θ : LargeSample (boundedRatioCutoff M L) Y)
    (heq :
      ∀ q : LargePrimeCoordinate (boundedRatioCutoff M L) Y,
        largeCoordinatePrime q ∈
            largePrimeCoordinates x.1 L Y →
          η q = θ q) :
    boundedConditionedGoodIndicator N M L Y σ x η =
      boundedConditionedGoodIndicator N M L Y σ x θ := by
  classical
  unfold boundedConditionedGoodIndicator
  exact Bool.decide_congr
    (conditionedStartAt_iff_of_eqOn_largePrimeCoordinates
      hL σ η θ heq)

/--
Every good start in the bounded-ratio interval has exact conditional
marginal `2⁻ᴸ`, for every small-prime assignment.
-/
theorem marginal_boundedConditionedGoodIndicator_eq_baseline
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (boundedRatioCutoff M L) Y)
    (x : {x : ℕ // x ∈ boundedGoodStarts N M L Y}) :
    marginal
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y σ) x =
      (1 : ℝ) / (2 : ℝ) ^ L := by
  unfold boundedLargeUniformPMF
  rw [marginal,
    ConditionalAGGInstantiation.eventProbability_largeUniformPMF_eq]
  have hevent :
      (fun η : LargeSample (boundedRatioCutoff M L) Y ↦
          boundedConditionedGoodIndicator N M L Y σ x η = true) =
        (fun η : LargeSample (boundedRatioCutoff M L) Y ↦
          startAt
            (assemble (boundedRatioCutoff M L) Y σ η) x.1 L) := by
    funext η
    apply propext
    exact boundedConditionedGoodIndicator_eq_true_iff
  rw [hevent]
  rw [finiteUniformProbability_conditionedStart_eq
    (boundedRatioCutoff M L) Y x.1 L hL σ]
  rw [conditionedStartProbability_eq_baseline
    (hN.trans (mem_boundedRatioBlock.mp
      (mem_boundedGoodStarts.mp x.2).1).1)
    hL hLY]
  · norm_num
  · intro j
    exact startWindow_le_boundedRatioCutoff
      (mem_boundedGoodStarts.mp x.2).1 j.2.le
  · intro j hjDef
    apply (mem_boundedGoodStarts.mp x.2).2
    rw [mem_boundedTerminalBadStarts]
    refine ⟨(mem_boundedGoodStarts.mp x.2).1,
      j.1, j.2, ?_⟩
    exact
      (largeOddKernel_eq_one_iff_hDefective
        Y (x.1 + j.1)).mpr hjDef

/--
The large-prime graph on `[N,M)` is an exact dependency graph after every
fixed small-prime assignment.
-/
theorem hasExactDependencyGraph_boundedConditionedGoodIndicator
    {N M L Y : ℕ}
    (hL : 0 < L)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    HasExactDependencyGraph
      (boundedLargeUniformPMF M L Y)
      (boundedConditionedGoodIndicator N M L Y σ)
      (boundedLargePrimeDependencyGraph N M L Y) := by
  classical
  unfold boundedLargeUniformPMF
  intro α value pattern
  rw [ConditionalAGGInstantiation.eventProbability_largeUniformPMF_eq,
    ConditionalAGGInstantiation.eventProbability_largeUniformPMF_eq,
    ConditionalAGGInstantiation.eventProbability_largeUniformPMF_eq]
  norm_cast
  let e :=
    startCoordinateSplit
      (boundedRatioCutoff M L) Y α.1 L
  let P : LargeSample (boundedRatioCutoff M L) Y → Prop :=
    fun η ↦
      boundedConditionedGoodIndicator N M L Y σ α η = value
  let Q : LargeSample (boundedRatioCutoff M L) Y → Prop :=
    fun η ↦
      HasOutsidePattern
        (boundedConditionedGoodIndicator N M L Y σ)
        (boundedLargePrimeDependencyGraph N M L Y)
        α pattern η
  let PA :
      StartSupportSample (boundedRatioCutoff M L) Y α.1 L → Prop :=
    fun a ↦ P (e.symm (a, 0))
  let QB :
      StartComplementSample (boundedRatioCutoff M L) Y α.1 L → Prop :=
    fun b ↦ Q (e.symm (0, b))
  apply finiteUniformProbability_and_eq_mul_of_product_support
    e P Q PA QB
  · intro η
    dsimp only [P, PA]
    have hindicator :
        boundedConditionedGoodIndicator N M L Y σ α η =
          boundedConditionedGoodIndicator N M L Y σ α
            (e.symm ((e η).1, 0)) := by
      apply
        boundedConditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates
          hL σ α
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
            (boundedLargePrimeDependencyGraph N M L Y) α,
          boundedConditionedGoodIndicator N M L Y σ β.1 η =
            boundedConditionedGoodIndicator N M L Y σ β.1 θ := by
      intro β
      have hnotMem :
          β.1 ∉
            closedNeighborhood
              (boundedLargePrimeDependencyGraph N M L Y) α :=
        β.2
      have hne : α ≠ β.1 := by
        intro h
        apply hnotMem
        rw [← h]
        exact self_mem_closedNeighborhood
          (boundedLargePrimeDependencyGraph N M L Y) α
      have hneNat : α.1 ≠ β.1.1 := by
        intro h
        apply hne
        apply Subtype.ext
        exact h
      have hnotAdj :
          ¬(boundedLargePrimeDependencyGraph N M L Y).Adj
            α β.1 := by
        intro hadj
        exact hnotMem
          (mem_closedNeighborhood.mpr (Or.inr hadj))
      have hnotLarge :
          ¬LargePrimeAdjacent L Y α.1 β.1.1 := by
        simpa only [boundedLargePrimeDependencyGraph_adj] using hnotAdj
      have hdisjoint :
          Disjoint
            (largePrimeCoordinates α.1 L Y)
            (largePrimeCoordinates β.1.1 L Y) :=
        disjoint_largePrimeCoordinates_of_not_adjacent
          hneNat hnotLarge
      apply
        boundedConditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates
          hL σ β.1
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

/--
Direct bounded-ratio instance of Theorem 13.7.  There is no new bridge:
the only hypothesis is the published AGG theorem already present in the
Section 13 interface.
-/
theorem boundedConditionalGood_totalVariationToPoisson_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N M L Y : ℕ}
    (hL : 0 < L)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    totalVariationToPoisson
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y σ) ≤
      2 *
        (bOne
            (boundedLargeUniformPMF M L Y)
            (boundedConditionedGoodIndicator N M L Y σ)
            (boundedLargePrimeDependencyGraph N M L Y) +
          bTwo
            (boundedLargeUniformPMF M L Y)
            (boundedConditionedGoodIndicator N M L Y σ)
            (boundedLargePrimeDependencyGraph N M L Y)) := by
  exact totalVariationToPoisson_le
    hAGG
    (boundedLargeUniformPMF M L Y)
    (boundedConditionedGoodIndicator N M L Y σ)
    (boundedLargePrimeDependencyGraph N M L Y)
    (hasExactDependencyGraph_boundedConditionedGoodIndicator hL σ)

/-- Exact deterministic conditional Poisson parameter on `[N,M)`. -/
theorem poissonParameter_boundedConditionedGoodIndicator_eq
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    poissonParameter
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y σ) =
      ((boundedGoodStarts N M L Y).card : ℝ) /
        (2 : ℝ) ^ L := by
  unfold poissonParameter
  simp_rw [marginal_boundedConditionedGoodIndicator_eq_baseline
    hN hL hLY σ]
  simp
  ring

/-! ## Closed neighborhoods and the exact first Stein--Chen term -/

/--
Ordered closed-neighborhood pairs: the diagonal of the bounded good-start
set together with all ordered dependency edges.
-/
noncomputable def boundedClosedDependencyPairs
    (N M L Y : ℕ) : Finset (ℕ × ℕ) :=
  (boundedGoodStarts N M L Y).diag ∪
    boundedOrderedDependencyEdges N M L Y

@[simp]
theorem mem_boundedClosedDependencyPairs
    {N M L Y : ℕ} {pair : ℕ × ℕ} :
    pair ∈ boundedClosedDependencyPairs N M L Y ↔
      (pair.1 ∈ boundedGoodStarts N M L Y ∧
        pair.1 = pair.2) ∨
      pair ∈ boundedOrderedDependencyEdges N M L Y := by
  simp [boundedClosedDependencyPairs]

theorem disjoint_boundedGoodDiag_orderedEdges
    (N M L Y : ℕ) :
    Disjoint (boundedGoodStarts N M L Y).diag
      (boundedOrderedDependencyEdges N M L Y) := by
  refine Finset.disjoint_left.mpr ?_
  intro pair hdiag hedge
  have heq : pair.1 = pair.2 :=
    (Finset.mem_diag.mp hdiag).2
  exact ne_of_mem_boundedOrderedDependencyEdges hedge heq

/-- Exact cardinal of the bounded closed-neighborhood relation. -/
theorem card_boundedClosedDependencyPairs
    (N M L Y : ℕ) :
    (boundedClosedDependencyPairs N M L Y).card =
      (boundedGoodStarts N M L Y).card +
        (boundedOrderedDependencyEdges N M L Y).card := by
  rw [boundedClosedDependencyPairs,
    Finset.card_union_of_disjoint
      (disjoint_boundedGoodDiag_orderedEdges N M L Y)]
  rw [Finset.diag_card]

/--
Membership in a graph-theoretic closed neighborhood agrees with membership
of the corresponding natural-number pair in the finite relation above.
-/
theorem pair_mem_boundedClosedDependencyPairs_iff
    {N M L Y : ℕ}
    (α β : {x : ℕ // x ∈ boundedGoodStarts N M L Y}) :
    (α.1, β.1) ∈ boundedClosedDependencyPairs N M L Y ↔
      β ∈ closedNeighborhood
        (boundedLargePrimeDependencyGraph N M L Y) α := by
  rw [mem_boundedClosedDependencyPairs, mem_closedNeighborhood]
  constructor
  · rintro (hdiag | hedge)
    · exact Or.inl (Subtype.ext hdiag.2.symm)
    · exact Or.inr
        (mem_boundedOrderedDependencyEdges.mp hedge).2.2
  · rintro (rfl | hadj)
    · exact Or.inl ⟨β.2, rfl⟩
    · exact Or.inr
        (mem_boundedOrderedDependencyEdges.mpr
          ⟨α.2, β.2, hadj⟩)

/-- Dependent presentation of all bounded closed-neighborhood pairs. -/
abbrev BoundedClosedNeighborhoodPair
    (N M L Y : ℕ) :=
  Σ α : {x : ℕ // x ∈ boundedGoodStarts N M L Y},
    {β : {x : ℕ // x ∈ boundedGoodStarts N M L Y} //
      β ∈ closedNeighborhood
        (boundedLargePrimeDependencyGraph N M L Y) α}

/-- Canonical equivalence between the two presentations of closed pairs. -/
noncomputable def boundedClosedNeighborhoodPairEquiv
    (N M L Y : ℕ) :
    BoundedClosedNeighborhoodPair N M L Y ≃
      {pair : ℕ × ℕ //
        pair ∈ boundedClosedDependencyPairs N M L Y} := by
  classical
  let toPair :
      BoundedClosedNeighborhoodPair N M L Y →
        {pair : ℕ × ℕ //
          pair ∈ boundedClosedDependencyPairs N M L Y} :=
    fun pair ↦
      ⟨(pair.1.1, pair.2.1.1),
        (pair_mem_boundedClosedDependencyPairs_iff
          pair.1 pair.2.1).mpr pair.2.2⟩
  let fromPair :
      {pair : ℕ × ℕ //
        pair ∈ boundedClosedDependencyPairs N M L Y} →
        BoundedClosedNeighborhoodPair N M L Y :=
    fun pair ↦ by
      have hmem :=
        mem_boundedClosedDependencyPairs.mp pair.2
      have hx : pair.1.1 ∈ boundedGoodStarts N M L Y := by
        rcases hmem with hdiag | hedge
        · exact hdiag.1
        · exact
            (mem_boundedOrderedDependencyEdges.mp hedge).1
      have hy : pair.1.2 ∈ boundedGoodStarts N M L Y := by
        rcases hmem with hdiag | hedge
        · rw [← hdiag.2]
          exact hdiag.1
        · exact
            (mem_boundedOrderedDependencyEdges.mp hedge).2.1
      let α :
          {x : ℕ // x ∈ boundedGoodStarts N M L Y} :=
        ⟨pair.1.1, hx⟩
      let β :
          {x : ℕ // x ∈ boundedGoodStarts N M L Y} :=
        ⟨pair.1.2, hy⟩
      exact
        ⟨α,
          ⟨β,
            (pair_mem_boundedClosedDependencyPairs_iff
              α β).mp pair.2⟩⟩
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

/-- Exact total size of all bounded closed graph neighborhoods. -/
theorem sum_card_boundedClosedNeighborhood_eq
    (N M L Y : ℕ) :
    (∑ α :
        {x : ℕ // x ∈ boundedGoodStarts N M L Y},
      (closedNeighborhood
        (boundedLargePrimeDependencyGraph N M L Y) α).card) =
      (boundedClosedDependencyPairs N M L Y).card := by
  calc
    (∑ α :
        {x : ℕ // x ∈ boundedGoodStarts N M L Y},
      (closedNeighborhood
        (boundedLargePrimeDependencyGraph N M L Y) α).card) =
        ∑ α :
            {x : ℕ // x ∈ boundedGoodStarts N M L Y},
          Fintype.card
            {β :
                {x : ℕ //
                  x ∈ boundedGoodStarts N M L Y} //
              β ∈ closedNeighborhood
                (boundedLargePrimeDependencyGraph N M L Y)
                α} := by
      simp only [Fintype.card_coe]
    _ =
        Fintype.card
          (BoundedClosedNeighborhoodPair N M L Y) :=
      Fintype.card_sigma.symm
    _ =
        Fintype.card
          {pair : ℕ × ℕ //
            pair ∈ boundedClosedDependencyPairs N M L Y} :=
      Fintype.card_congr
        (boundedClosedNeighborhoodPairEquiv N M L Y)
    _ = (boundedClosedDependencyPairs N M L Y).card :=
      Fintype.card_coe _

/--
Exact `b₁` identity on the bounded interval.  This is the finite content of
the first estimate in Lemma 17.37 once the marginal part of Lemma 17.35 is
available.
-/
theorem bOne_boundedConditionedGoodIndicator_eq_card_div
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    bOne
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y σ)
        (boundedLargePrimeDependencyGraph N M L Y) =
      (((boundedGoodStarts N M L Y).card +
        (boundedOrderedDependencyEdges N M L Y).card : ℕ) : ℝ) /
        (2 : ℝ) ^ (2 * L) := by
  unfold bOne
  simp_rw [marginal_boundedConditionedGoodIndicator_eq_baseline
    hN hL hLY σ]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  have hcountR :
      (∑ α :
          {x : ℕ // x ∈ boundedGoodStarts N M L Y},
        ((closedNeighborhood
          (boundedLargePrimeDependencyGraph N M L Y)
          α).card : ℝ)) =
        ((boundedClosedDependencyPairs N M L Y).card : ℝ) := by
    exact_mod_cast
      sum_card_boundedClosedNeighborhood_eq N M L Y
  rw [hcountR, card_boundedClosedDependencyPairs]
  push_cast
  rw [show 2 * L = L + L by omega, pow_add]
  ring

/-- Manuscript-facing `b₁` majorant, here obtained as an exact equality. -/
theorem bOne_boundedConditionedGoodIndicator_le_card_div
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    bOne
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y σ)
        (boundedLargePrimeDependencyGraph N M L Y) ≤
      (((boundedGoodStarts N M L Y).card +
        (boundedOrderedDependencyEdges N M L Y).card : ℕ) : ℝ) /
        (2 : ℝ) ^ (2 * L) :=
  (bOne_boundedConditionedGoodIndicator_eq_card_div
    hN hL hLY σ).le

/-! ## Exact good/bad partition and parameter recentering -/

theorem boundedTerminalBadStarts_subset_block
    (N M L Y : ℕ) :
    boundedTerminalBadStarts N M L Y ⊆
      boundedRatioBlock N M := by
  intro x hx
  exact (mem_boundedTerminalBadStarts.mp hx).1

/-- Good and terminal-bad starts partition `[N,M)` exactly. -/
theorem card_boundedGood_add_card_boundedBad
    {N M L Y : ℕ} (_hNM : N ≤ M) :
    (boundedGoodStarts N M L Y).card +
        (boundedTerminalBadStarts N M L Y).card =
      M - N := by
  unfold boundedGoodStarts
  rw [Finset.card_sdiff_add_card_eq_card
    (boundedTerminalBadStarts_subset_block N M L Y)]
  exact BoundedRatioGeometry.card_boundedRatioBlock N M

/--
The target rate `|[N,M)|2⁻ᴸ` exceeds the conditional good-start parameter
by exactly the normalized number of terminal bad starts.
-/
theorem boundedTarget_sub_goodPoissonParameter_eq_badCard
    {N M L Y : ℕ}
    (hNM : N ≤ M)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    ((M - N : ℕ) : ℝ) / (2 : ℝ) ^ L -
        poissonParameter
          (boundedLargeUniformPMF M L Y)
          (boundedConditionedGoodIndicator N M L Y σ) =
      ((boundedTerminalBadStarts N M L Y).card : ℝ) /
        (2 : ℝ) ^ L := by
  rw [poissonParameter_boundedConditionedGoodIndicator_eq
    hN hL hLY σ]
  have hcardR :
      ((boundedGoodStarts N M L Y).card : ℝ) +
          ((boundedTerminalBadStarts N M L Y).card : ℝ) =
        ((M - N : ℕ) : ℝ) := by
    exact_mod_cast card_boundedGood_add_card_boundedBad
      (L := L) (Y := Y) hNM
  rw [← sub_div]
  congr 1
  linarith

/-- Absolute rate discrepancy in the orientation used by Poisson coupling. -/
theorem abs_goodPoissonParameter_sub_boundedTarget_eq_badCard
    {N M L Y : ℕ}
    (hNM : N ≤ M)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (boundedRatioCutoff M L) Y) :
    |poissonParameter
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y σ) -
      ((M - N : ℕ) : ℝ) / (2 : ℝ) ^ L| =
      ((boundedTerminalBadStarts N M L Y).card : ℝ) /
        (2 : ℝ) ^ L := by
  rw [abs_sub_comm,
    boundedTarget_sub_goodPoissonParameter_eq_badCard
      hNM hN hL hLY σ]
  exact abs_of_nonneg
    (div_nonneg (by positivity) (by positivity))

/-! ## Prime-witness counting from Lemma 17.36 -/

/-- Good starts in `[N,M)` using a prescribed large prime. -/
noncomputable def boundedStartsUsingPrime
    (N M L Y p : ℕ) : Finset ℕ :=
  (boundedGoodStarts N M L Y).filter fun x ↦
    p ∈ largePrimeCoordinates x L Y

@[simp]
theorem mem_boundedStartsUsingPrime
    {N M L Y p x : ℕ} :
    x ∈ boundedStartsUsingPrime N M L Y p ↔
      x ∈ boundedGoodStarts N M L Y ∧
        p ∈ largePrimeCoordinates x L Y := by
  simp [boundedStartsUsingPrime]

/-- Ordered start pairs sharing a prescribed prime. -/
noncomputable def boundedOrderedPairsUsingPrime
    (N M L Y p : ℕ) : Finset (ℕ × ℕ) :=
  (boundedStartsUsingPrime N M L Y p).product
    (boundedStartsUsingPrime N M L Y p)

/-- Prime-witness cover for all bounded-ratio dependency edges. -/
noncomputable def boundedOrderedPrimeWitnessCover
    (N M L Y : ℕ) : Finset (ℕ × ℕ) :=
  (largePrimesInRange Y (3 * M)).biUnion fun p ↦
    boundedOrderedPairsUsingPrime N M L Y p

theorem mem_largePrimesInRange_of_mem_bounded_coordinates
    {N M L Y x p : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M) (hL : L ≤ M)
    (hx : x ∈ boundedGoodStarts N M L Y)
    (hp : p ∈ largePrimeCoordinates x L Y) :
    p ∈ largePrimesInRange Y (3 * M) := by
  obtain ⟨n, hnTree, hpn⟩ :=
    mem_largePrimeCoordinates.mp hp
  have hpData :=
    prime_and_large_of_mem_largeOddPrimeSupport hpn
  have hxBlock := (mem_boundedGoodStarts.mp hx).1
  have hxBounds := mem_boundedRatioBlock.mp hxBlock
  have hnPos : 0 < n := by
    rcases mem_startTreeSupport.mp hnTree with
      hroot | ⟨j, hj, hlabel⟩
    · rw [hroot]
      omega
    · rw [← hlabel]
      omega
  have hnUpper : n ≤ 3 * M := by
    rcases mem_startTreeSupport.mp hnTree with
      hroot | ⟨j, hj, hlabel⟩
    · rw [hroot]
      omega
    · rw [← hlabel]
      omega
  have hpDvd : p ∣ n :=
    Nat.dvd_of_mem_primeFactors
      (largeOddPrimeSupport_subset_primeFactors Y n hpn)
  exact mem_largePrimesInRange.mpr
    ⟨hpData.1, hpData.2,
      (Nat.le_of_dvd hnPos hpDvd).trans hnUpper⟩

theorem boundedOrderedDependencyEdges_subset_primeWitnessCover
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M) (hL : L ≤ M) :
    boundedOrderedDependencyEdges N M L Y ⊆
      boundedOrderedPrimeWitnessCover N M L Y := by
  intro xy hxy
  have hedge := mem_boundedOrderedDependencyEdges.mp hxy
  obtain ⟨p, hpx, hpy⟩ :=
    (largePrimeAdjacent_iff.mp hedge.2.2).2
  rw [boundedOrderedPrimeWitnessCover, Finset.mem_biUnion]
  refine ⟨p,
    mem_largePrimesInRange_of_mem_bounded_coordinates
      hN hNM hL hedge.1 hpx, ?_⟩
  change
    xy ∈
      (boundedStartsUsingPrime N M L Y p) ×ˢ
        (boundedStartsUsingPrime N M L Y p)
  exact Finset.mem_product.mpr
    ⟨mem_boundedStartsUsingPrime.mpr ⟨hedge.1, hpx⟩,
      mem_boundedStartsUsingPrime.mpr ⟨hedge.2.1, hpy⟩⟩

theorem card_boundedOrderedDependencyEdges_le_sum_sq
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M) (hL : L ≤ M) :
    (boundedOrderedDependencyEdges N M L Y).card ≤
      ∑ p ∈ largePrimesInRange Y (3 * M),
        (boundedStartsUsingPrime N M L Y p).card ^ 2 := by
  calc
    (boundedOrderedDependencyEdges N M L Y).card ≤
        (boundedOrderedPrimeWitnessCover N M L Y).card :=
      Finset.card_le_card
        (boundedOrderedDependencyEdges_subset_primeWitnessCover
          hN hNM hL)
    _ ≤ ∑ p ∈ largePrimesInRange Y (3 * M),
          (boundedOrderedPairsUsingPrime N M L Y p).card :=
      Finset.card_biUnion_le
    _ = ∑ p ∈ largePrimesInRange Y (3 * M),
          (boundedStartsUsingPrime N M L Y p).card ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp [boundedOrderedPairsUsingPrime, pow_two]

/-- Starts whose complete-tree offset `j` is divisible by `p`. -/
noncomputable def boundedStartsWithDivisibleOffset
    (N M p j : ℕ) : Finset ℕ :=
  (boundedRatioBlock N M).filter fun x ↦
    p ∣ x - 1 + j

@[simp]
theorem mem_boundedStartsWithDivisibleOffset
    {N M p j x : ℕ} :
    x ∈ boundedStartsWithDivisibleOffset N M p j ↔
      x ∈ boundedRatioBlock N M ∧ p ∣ x - 1 + j := by
  simp [boundedStartsWithDivisibleOffset]

/--
A fixed complete-tree offset contributes at most `M/p+1` starts.  This
coarser form, independent of the lower endpoint, is exactly what is needed
for uniform fixed-ratio estimates.
-/
theorem card_boundedStartsWithDivisibleOffset_cast_le
    {N M p j : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M)
    (hp : 0 < p) (hj : j ≤ p + 1) :
    ((boundedStartsWithDivisibleOffset N M p j).card : ℚ) ≤
      (M : ℚ) / (p : ℚ) + 1 := by
  let target :=
    (Finset.Ico 0 M).filter fun x ↦
      x ≡ p + 1 - j [MOD p]
  have hsubset :
      boundedStartsWithDivisibleOffset N M p j ⊆ target := by
    intro x hx
    have hxData := mem_boundedStartsWithDivisibleOffset.mp hx
    have hxBounds := mem_boundedRatioBlock.mp hxData.1
    rw [show target =
      (Finset.Ico 0 M).filter fun x ↦
        x ≡ p + 1 - j [MOD p] by rfl]
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact
      ⟨⟨Nat.zero_le x, hxBounds.2⟩,
        (dvd_sub_one_add_iff_modEq
          (hN.trans hxBounds.1) hj).mp hxData.2⟩
  calc
    ((boundedStartsWithDivisibleOffset N M p j).card : ℚ) ≤
        (target.card : ℚ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (M : ℚ) / (p : ℚ) + 1 := by
      dsimp only [target]
      simpa using
        (card_nat_Ico_modEq_cast_le_div_add_one
          0 M (p + 1 - j) p hp (Nat.zero_le M))

theorem boundedStartsUsingPrime_subset_offsetUnion
    {N M L Y p : ℕ}
    (hN : 1 ≤ N) :
    boundedStartsUsingPrime N M L Y p ⊆
      (Finset.range (L + 1)).biUnion fun j ↦
        boundedStartsWithDivisibleOffset N M p j := by
  intro x hx
  have hxData := mem_boundedStartsUsingPrime.mp hx
  obtain ⟨n, hnTree, hpn⟩ :=
    mem_largePrimeCoordinates.mp hxData.2
  have hpDvd : p ∣ n :=
    Nat.dvd_of_mem_primeFactors
      (largeOddPrimeSupport_subset_primeFactors Y n hpn)
  have hxBlock := (mem_boundedGoodStarts.mp hxData.1).1
  rw [Finset.mem_biUnion]
  rcases mem_startTreeSupport.mp hnTree with
    hroot | ⟨j, hj, hlabel⟩
  · refine ⟨0, by simp, ?_⟩
    rw [mem_boundedStartsWithDivisibleOffset]
    simpa [hroot] using And.intro hxBlock hpDvd
  · refine ⟨j + 1, by simpa using Nat.succ_lt_succ hj, ?_⟩
    rw [mem_boundedStartsWithDivisibleOffset]
    have hvertex : x - 1 + (j + 1) = n := by
      rw [← hlabel]
      have hxPos : 1 ≤ x :=
        hN.trans (mem_boundedRatioBlock.mp hxBlock).1
      omega
    exact ⟨hxBlock, hvertex ▸ hpDvd⟩

theorem card_boundedStartsUsingPrime_cast_le
    {N M L Y p : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M)
    (hLY : L ≤ Y) (hpY : Y < p) :
    ((boundedStartsUsingPrime N M L Y p).card : ℚ) ≤
      (L + 1 : ℚ) * ((M : ℚ) / (p : ℚ) + 1) := by
  have hp : 0 < p := by omega
  calc
    ((boundedStartsUsingPrime N M L Y p).card : ℚ) ≤
        (((Finset.range (L + 1)).biUnion fun j ↦
          boundedStartsWithDivisibleOffset N M p j).card : ℚ) := by
      exact_mod_cast
        Finset.card_le_card
          (boundedStartsUsingPrime_subset_offsetUnion hN)
    _ ≤ ∑ j ∈ Finset.range (L + 1),
          ((boundedStartsWithDivisibleOffset N M p j).card : ℚ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (L + 1),
          ((M : ℚ) / (p : ℚ) + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      apply card_boundedStartsWithDivisibleOffset_cast_le
        hN hNM hp
      have hj' : j < L + 1 := by simpa using hj
      omega
    _ = (L + 1 : ℚ) * ((M : ℚ) / (p : ℚ) + 1) := by
      simp
      ring

/--
Exact pre-analytic bounded-ratio edge estimate:

`E_{Y,[N,M)} ≤ (L+1)² ∑_{Y<p≤3M} (M/p+1)²`.
-/
theorem card_boundedOrderedDependencyEdges_cast_le_prime_sum
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M)
    (hLM : L ≤ M) (hLY : L ≤ Y) :
    ((boundedOrderedDependencyEdges N M L Y).card : ℚ) ≤
      (L + 1 : ℚ) ^ 2 *
        ∑ p ∈ largePrimesInRange Y (3 * M),
          ((M : ℚ) / (p : ℚ) + 1) ^ 2 := by
  have hedge :=
    card_boundedOrderedDependencyEdges_le_sum_sq
      (N := N) (M := M) (L := L) (Y := Y)
      hN hNM hLM
  calc
    ((boundedOrderedDependencyEdges N M L Y).card : ℚ) ≤
        ∑ p ∈ largePrimesInRange Y (3 * M),
          ((boundedStartsUsingPrime N M L Y p).card : ℚ) ^ 2 := by
      exact_mod_cast hedge
    _ ≤ ∑ p ∈ largePrimesInRange Y (3 * M),
          ((L + 1 : ℚ) *
            ((M : ℚ) / (p : ℚ) + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply pow_le_pow_left₀
      · positivity
      · exact card_boundedStartsUsingPrime_cast_le
          (by omega) hNM hLY
          (mem_largePrimesInRange.mp hp).2.1
    _ = (L + 1 : ℚ) ^ 2 *
        ∑ p ∈ largePrimesInRange Y (3 * M),
          ((M : ℚ) / (p : ℚ) + 1) ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]

/-- Explicit finite analytic edge envelope on `[N,M)`. -/
theorem card_boundedOrderedDependencyEdges_cast_le
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M)
    (hLM : L ≤ M) (hLY : L ≤ Y) (hY : 4 ≤ Y) :
    ((boundedOrderedDependencyEdges N M L Y).card : ℚ) ≤
      (L + 1 : ℚ) ^ 2 *
        (28 * (M : ℚ) ^ 2 /
            ((Y : ℚ) * (Nat.log 2 Y : ℚ)) +
          6 * (M : ℚ) ^ 2 / (Y : ℚ) +
          3 * (M : ℚ)) := by
  exact
    (card_boundedOrderedDependencyEdges_cast_le_prime_sum
      hN hNM hLM hLY).trans
      (mul_le_mul_of_nonneg_left
        (DependencyEdgeBound.sum_div_add_one_sq_le
          (N := M) hY)
        (sq_nonneg (L + 1 : ℚ)))

/-! ## Uniform edge-count consequences on bounded-ratio intervals -/

theorem card_boundedOrderedDependencyEdges_cast_le_div
    {N M L Y m : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M)
    (hm : 1 ≤ m)
    (hB : 2 ≤ L + 1)
    (hMY : m * (L + 1) ^ 2 ≤ Y)
    (hBcube : (L + 1) ^ 3 ≤ M)
    (hmB : m ≤ L + 1) :
    ((boundedOrderedDependencyEdges N M L Y).card : ℚ) ≤
      37 * (M : ℚ) ^ 2 / (m : ℚ) := by
  have hLM : L ≤ M := by
    have hLB : L ≤ L + 1 := by omega
    have hBcube_ge : L + 1 ≤ (L + 1) ^ 3 := by
      nlinarith [show 1 ≤ L + 1 by omega]
    exact hLB.trans (hBcube_ge.trans hBcube)
  have hLY : L ≤ Y := by
    have hmBsq : (L + 1) ^ 2 ≤ m * (L + 1) ^ 2 :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hBsq : L ≤ (L + 1) ^ 2 := by nlinarith
    exact hBsq.trans (hmBsq.trans hMY)
  have hY : 4 ≤ Y := by
    have hmBsq : (L + 1) ^ 2 ≤ m * (L + 1) ^ 2 :=
      Nat.le_mul_of_pos_left _ (by omega)
    have : 4 ≤ (L + 1) ^ 2 := by nlinarith
    exact this.trans (hmBsq.trans hMY)
  have hlogY : 1 ≤ Nat.log 2 Y :=
    Nat.log_pos (by norm_num) (by omega)
  have hmQ : (0 : ℚ) < (m : ℚ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hYQ : (0 : ℚ) < (Y : ℚ) := by
    exact_mod_cast (show 0 < Y by omega)
  have hBsq_div_Y :
      ((L + 1 : ℕ) : ℚ) ^ 2 / (Y : ℚ) ≤
        1 / (m : ℚ) := by
    apply (div_le_div_iff₀ hYQ hmQ).2
    have hMY' : (L + 1) ^ 2 * m ≤ Y := by
      simpa only [mul_comm] using hMY
    have hMYQ :
        ((((L + 1) ^ 2 * m : ℕ) : ℚ)) ≤ (Y : ℚ) := by
      exact_mod_cast hMY'
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, one_mul] using hMYQ
  have hY_le_Ylog :
      (Y : ℚ) ≤ (Y : ℚ) * (Nat.log 2 Y : ℚ) := by
    calc
      (Y : ℚ) = (Y : ℚ) * 1 := by ring
      _ ≤ (Y : ℚ) * (Nat.log 2 Y : ℚ) := by
        gcongr
        exact_mod_cast hlogY
  have hBsq_div_Ylog :
      ((L + 1 : ℕ) : ℚ) ^ 2 /
          ((Y : ℚ) * (Nat.log 2 Y : ℚ)) ≤
        1 / (m : ℚ) := by
    calc
      ((L + 1 : ℕ) : ℚ) ^ 2 /
          ((Y : ℚ) * (Nat.log 2 Y : ℚ)) ≤
          ((L + 1 : ℕ) : ℚ) ^ 2 / (Y : ℚ) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hYQ
        · exact hY_le_Ylog
      _ ≤ 1 / (m : ℚ) := hBsq_div_Y
  have hmBsqM :
      (m : ℚ) * ((L + 1 : ℕ) : ℚ) ^ 2 ≤
        (M : ℚ) := by
    have hmBsqNat :
        m * (L + 1) ^ 2 ≤ (L + 1) ^ 3 := by
      calc
        m * (L + 1) ^ 2 ≤
            (L + 1) * (L + 1) ^ 2 :=
          Nat.mul_le_mul_right _ hmB
        _ = (L + 1) ^ 3 := by ring
    exact_mod_cast hmBsqNat.trans hBcube
  have hBsqM_div :
      ((L + 1 : ℕ) : ℚ) ^ 2 * (M : ℚ) ≤
        (M : ℚ) ^ 2 / (m : ℚ) := by
    apply (le_div_iff₀ hmQ).2
    calc
      ((L + 1 : ℕ) : ℚ) ^ 2 * (M : ℚ) * (m : ℚ) =
          ((m : ℚ) * ((L + 1 : ℕ) : ℚ) ^ 2) * (M : ℚ) := by
        ring
      _ ≤ (M : ℚ) * (M : ℚ) :=
        mul_le_mul_of_nonneg_right hmBsqM (by positivity)
      _ = (M : ℚ) ^ 2 := by ring
  have hedge :=
    card_boundedOrderedDependencyEdges_cast_le
      (N := N) (M := M) (L := L) (Y := Y)
      hN hNM hLM hLY hY
  calc
    ((boundedOrderedDependencyEdges N M L Y).card : ℚ) ≤
        ((L + 1 : ℕ) : ℚ) ^ 2 *
          (28 * (M : ℚ) ^ 2 /
              ((Y : ℚ) * (Nat.log 2 Y : ℚ)) +
            6 * (M : ℚ) ^ 2 / (Y : ℚ) +
            3 * (M : ℚ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hedge
    _ =
        28 * (M : ℚ) ^ 2 *
            (((L + 1 : ℕ) : ℚ) ^ 2 /
              ((Y : ℚ) * (Nat.log 2 Y : ℚ))) +
          6 * (M : ℚ) ^ 2 *
            (((L + 1 : ℕ) : ℚ) ^ 2 / (Y : ℚ)) +
          3 * (((L + 1 : ℕ) : ℚ) ^ 2 * (M : ℚ)) := by
      ring
    _ ≤
        28 * (M : ℚ) ^ 2 * (1 / (m : ℚ)) +
          6 * (M : ℚ) ^ 2 * (1 / (m : ℚ)) +
          3 * ((M : ℚ) ^ 2 / (m : ℚ)) := by
      gcongr
    _ = 37 * (M : ℚ) ^ 2 / (m : ℚ) := by
      ring

theorem card_boundedOrderedDependencyEdges_terminalCutoff_cast_le_div
    {N M L m : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M)
    (hm : 1 ≤ m)
    (hlog : (m : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ))
    (hBcube : (L + 1) ^ 3 ≤ M) :
    ((boundedOrderedDependencyEdges N M L
        (TerminalPrimeCutoff.terminalPrimeCutoff (L + 1))).card : ℚ) ≤
      37 * (M : ℚ) ^ 2 / (m : ℚ) := by
  have hB : 2 ≤ L + 1 := by
    have honeLog :
        (1 : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ) := by
      have h1m : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hm
      exact h1m.trans hlog
    have hlogPos :
        0 < Real.log ((L + 1 : ℕ) : ℝ) :=
      zero_lt_one.trans_le honeLog
    have hone :
        (1 : ℝ) < ((L + 1 : ℕ) : ℝ) :=
      (Real.log_pos_iff (by positivity)).mp hlogPos
    exact_mod_cast hone
  have hmB : m ≤ L + 1 := by
    exact_mod_cast hlog.trans (Real.log_le_self (by positivity))
  exact card_boundedOrderedDependencyEdges_cast_le_div
    hN hNM hm hB
      (DependencyEdgesCritical.mul_sq_le_terminalPrimeCutoff hlog)
      hBcube hmB

/--
The bounded-ratio form of the edge estimate, with the exact quantifiers of
Lemma 17.36: uniformly for `2N ≤ M ≤ κ₀N`, the number of ordered edges is
`o_{C,κ₀}(N²)`.

This theorem uses only the finite prime-witness envelope above.  The factor
`κ₀²` converting `M²` to `N²` is absorbed before the accuracy parameter is
chosen.
-/
theorem
    boundedOrderedDependencyEdges_terminalCutoff_uniformLittleOInBoundedRatioWindow
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (fun N M L =>
        ((boundedOrderedDependencyEdges N M L
          (TerminalPrimeCutoff.terminalPrimeCutoff
            (L + 1))).card : ℝ)) := by
  have hsubpoly :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial hC
  intro ε hε
  obtain ⟨m : ℕ, hmLarge⟩ :=
    exists_nat_gt
      (37 * (κ₀ : ℝ) ^ 2 / ε)
  have hm : 1 ≤ m := by
    have hnonneg :
        (0 : ℝ) ≤ 37 * (κ₀ : ℝ) ^ 2 / ε := by
      positivity
    have hmPos : (0 : ℝ) < (m : ℝ) :=
      hnonneg.trans_lt hmLarge
    exact_mod_cast hmPos
  let H : ℕ := ⌈Real.exp (m : ℝ)⌉₊
  obtain ⟨Nheight, hheight⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity hC H
  obtain ⟨Ncube, hcube⟩ := hsubpoly 3 (by omega)
  refine ⟨max 2 (max Nheight Ncube), ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nheight Ncube)).trans hN
  have hNleM : N ≤ M := by omega
  have htail :
      max Nheight Ncube ≤ N :=
    (le_max_right 2 (max Nheight Ncube)).trans hN
  have hHN :
      H ≤ L + 1 :=
    hheight N ((le_max_left _ _).trans htail) L hrun
  have hexp :
      Real.exp (m : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
    calc
      Real.exp (m : ℝ) ≤ (H : ℝ) := by
        exact Nat.le_ceil _
      _ ≤ ((L + 1 : ℕ) : ℝ) := by
        exact_mod_cast hHN
  have hlog :
      (m : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ) := by
    have hlogMono :=
      Real.log_le_log (Real.exp_pos (m : ℝ)) hexp
    simpa only [Real.log_exp] using hlogMono
  have hcubeReal :=
    hcube N ((le_max_right _ _).trans htail) L hrun
  have hcubeN : (L + 1) ^ 3 ≤ N := by
    have hnonneg :
        (0 : ℝ) ≤ (((L + 1 : ℕ) : ℝ)) := by
      positivity
    rw [abs_of_nonneg hnonneg] at hcubeReal
    exact_mod_cast hcubeReal
  have hfiniteQ :=
    card_boundedOrderedDependencyEdges_terminalCutoff_cast_le_div
      hNtwo hNleM hm hlog (hcubeN.trans hNleM)
  have hfinite :
      ((boundedOrderedDependencyEdges N M L
          (TerminalPrimeCutoff.terminalPrimeCutoff
            (L + 1))).card : ℝ) ≤
        37 * (M : ℝ) ^ 2 / (m : ℝ) := by
    have hcast :
        ((((boundedOrderedDependencyEdges N M L
            (TerminalPrimeCutoff.terminalPrimeCutoff
              (L + 1))).card : ℕ) : ℚ) : ℝ) ≤
          (↑((37 * (M : ℚ) ^ 2 / (m : ℚ)) : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr hfiniteQ
    push_cast at hcast
    simpa using hcast
  have hMκR :
      (M : ℝ) ≤ (κ₀ : ℝ) * (N : ℝ) := by
    exact_mod_cast hMκ
  have hsq :
      (M : ℝ) ^ 2 ≤
        (κ₀ : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
    have hsq' :
        (M : ℝ) ^ 2 ≤
          ((κ₀ : ℝ) * (N : ℝ)) ^ 2 := by
      apply pow_le_pow_left₀
      · positivity
      · exact hMκR
    simpa only [mul_pow] using hsq'
  have hmPos : (0 : ℝ) < m := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hcoef :
      37 * (κ₀ : ℝ) ^ 2 / (m : ℝ) ≤ ε := by
    apply le_of_lt
    apply (div_lt_iff₀ hmPos).2
    have hmLarge' :
        37 * (κ₀ : ℝ) ^ 2 / ε < (m : ℝ) :=
      hmLarge
    have hcross :=
      (div_lt_iff₀ hε).mp hmLarge'
    nlinarith
  rw [abs_of_nonneg (by positivity :
    0 ≤ ((boundedOrderedDependencyEdges N M L
      (TerminalPrimeCutoff.terminalPrimeCutoff
        (L + 1))).card : ℝ))]
  rw [abs_of_nonneg (sq_nonneg (N : ℝ))]
  calc
    ((boundedOrderedDependencyEdges N M L
        (TerminalPrimeCutoff.terminalPrimeCutoff
          (L + 1))).card : ℝ) ≤
        37 * (M : ℝ) ^ 2 / (m : ℝ) :=
      hfinite
    _ = (37 / (m : ℝ)) * (M : ℝ) ^ 2 := by
      ring
    _ ≤ (37 / (m : ℝ)) *
        ((κ₀ : ℝ) ^ 2 * (N : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ =
        (37 * (κ₀ : ℝ) ^ 2 / (m : ℝ)) *
          (N : ℝ) ^ 2 := by
      ring
    _ ≤ ε * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg (N : ℝ))

/--
Fixed-`j` edge-count consequence extracted from Lemma 17.36 for the literal
retained interval `[M/2^j,M)`.  This is not the full Poisson conclusion of
Lemmas 17.35--17.37.
-/
theorem retainedOrderedDependencyEdges_terminalCutoff_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L =>
        ((boundedOrderedDependencyEdges (M / 2 ^ j) M L
          (TerminalPrimeCutoff.terminalPrimeCutoff (L + 1))).card : ℝ))
      (fun M _ ↦ (M : ℝ) ^ 2) := by
  have hsubpoly :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial hC
  intro ε hε
  obtain ⟨m : ℕ, hmLarge⟩ :=
    exists_nat_gt (37 / ε)
  have hm : 1 ≤ m := by
    have hpositive : (0 : ℝ) < 37 / ε := by positivity
    have : (0 : ℝ) < (m : ℝ) := hpositive.trans hmLarge
    exact_mod_cast this
  let H : ℕ := ⌈Real.exp (m : ℝ)⌉₊
  obtain ⟨Mheight, hheight⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity hC H
  obtain ⟨Mcube, hcube⟩ := hsubpoly 3 (by omega)
  refine
    ⟨max (2 ^ (j + 1)) (max Mheight Mcube), ?_⟩
  intro M hM L hrun
  have hbase : 2 ≤ M / 2 ^ j := by
    rw [Nat.le_div_iff_mul_le (pow_pos (by norm_num) j)]
    calc
      2 * 2 ^ j = 2 ^ (j + 1) := by
        rw [pow_succ]
        ring
      _ ≤ M := (le_max_left _ _).trans hM
  have hbaseM : M / 2 ^ j ≤ M :=
    Nat.div_le_self M _
  have htail :
      max Mheight Mcube ≤ M :=
    (le_max_right (2 ^ (j + 1)) (max Mheight Mcube)).trans hM
  have hHM :
      H ≤ L + 1 :=
    hheight M ((le_max_left _ _).trans htail) L hrun
  have hexp :
      Real.exp (m : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
    calc
      Real.exp (m : ℝ) ≤ (H : ℝ) := by
        exact Nat.le_ceil _
      _ ≤ ((L + 1 : ℕ) : ℝ) := by
        exact_mod_cast hHM
  have hlog :
      (m : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ) := by
    have hlogMono :=
      Real.log_le_log (Real.exp_pos (m : ℝ)) hexp
    simpa only [Real.log_exp] using hlogMono
  have hcubeReal :=
    hcube M ((le_max_right _ _).trans htail) L hrun
  have hcubeNat : (L + 1) ^ 3 ≤ M := by
    have hnonneg :
        (0 : ℝ) ≤ (((L + 1 : ℕ) : ℝ)) := by positivity
    rw [abs_of_nonneg hnonneg] at hcubeReal
    exact_mod_cast hcubeReal
  have hfiniteQ :=
    card_boundedOrderedDependencyEdges_terminalCutoff_cast_le_div
      hbase hbaseM hm hlog hcubeNat
  have hfinite :
      ((boundedOrderedDependencyEdges (M / 2 ^ j) M L
          (TerminalPrimeCutoff.terminalPrimeCutoff (L + 1))).card : ℝ) ≤
        37 * (M : ℝ) ^ 2 / (m : ℝ) := by
    have hcast :
        ((((boundedOrderedDependencyEdges (M / 2 ^ j) M L
            (TerminalPrimeCutoff.terminalPrimeCutoff
              (L + 1))).card : ℕ) : ℚ) : ℝ) ≤
          (↑((37 * (M : ℚ) ^ 2 / (m : ℚ)) : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr hfiniteQ
    push_cast at hcast
    exact hcast
  rw [abs_of_nonneg (by positivity :
    0 ≤ ((boundedOrderedDependencyEdges (M / 2 ^ j) M L
      (TerminalPrimeCutoff.terminalPrimeCutoff (L + 1))).card : ℝ))]
  calc
    ((boundedOrderedDependencyEdges (M / 2 ^ j) M L
        (TerminalPrimeCutoff.terminalPrimeCutoff (L + 1))).card : ℝ) ≤
        37 * (M : ℝ) ^ 2 / (m : ℝ) := hfinite
    _ ≤ ε * |(M : ℝ) ^ 2| := by
      have hmPos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
      have hcoef : 37 / (m : ℝ) ≤ ε := by
        apply le_of_lt
        apply (div_lt_iff₀ hmPos).2
        have hmLarge' : 37 / ε < (m : ℝ) := hmLarge
        simpa [mul_comm] using (div_lt_iff₀ hε).mp hmLarge'
      rw [abs_of_nonneg (sq_nonneg (M : ℝ))]
      have hMsqPos : 0 < (M : ℝ) ^ 2 := by
        have : 0 < M := by omega
        positivity
      calc
        37 * (M : ℝ) ^ 2 / (m : ℝ) =
            (37 / (m : ℝ)) * (M : ℝ) ^ 2 := by ring
        _ ≤ ε * (M : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef hMsqPos.le

/-! ## Certified antecedents for the remaining Section 17 assembly -/

/--
The finite conditional core already discharged for every bounded interval:
exact marginals, the exact dependency graph, the exact conditional
parameter and its good/bad correction, and the exact first Stein--Chen
term.  Packaging these results as one proposition lets the remaining
bridge state explicitly that this core is an antecedent rather than part
of its debt.
-/
def BoundedRatioFiniteSteinChenCoreStatement : Prop :=
  ∀ (N M L Y : ℕ), 2 ≤ N → N ≤ M → 0 < L → L + 1 ≤ Y →
    (∀ (σ : SmallSample (boundedRatioCutoff M L) Y)
        (x : {x : ℕ // x ∈ boundedGoodStarts N M L Y}),
      marginal
          (boundedLargeUniformPMF M L Y)
          (boundedConditionedGoodIndicator N M L Y σ) x =
        (1 : ℝ) / (2 : ℝ) ^ L) ∧
    (∀ σ : SmallSample (boundedRatioCutoff M L) Y,
      HasExactDependencyGraph
        (boundedLargeUniformPMF M L Y)
        (boundedConditionedGoodIndicator N M L Y σ)
        (boundedLargePrimeDependencyGraph N M L Y)) ∧
    (∀ σ : SmallSample (boundedRatioCutoff M L) Y,
      poissonParameter
          (boundedLargeUniformPMF M L Y)
          (boundedConditionedGoodIndicator N M L Y σ) =
        ((boundedGoodStarts N M L Y).card : ℝ) /
          (2 : ℝ) ^ L) ∧
    (∀ σ : SmallSample (boundedRatioCutoff M L) Y,
      ((M - N : ℕ) : ℝ) / (2 : ℝ) ^ L -
          poissonParameter
            (boundedLargeUniformPMF M L Y)
            (boundedConditionedGoodIndicator N M L Y σ) =
        ((boundedTerminalBadStarts N M L Y).card : ℝ) /
          (2 : ℝ) ^ L) ∧
    (∀ σ : SmallSample (boundedRatioCutoff M L) Y,
      bOne
          (boundedLargeUniformPMF M L Y)
          (boundedConditionedGoodIndicator N M L Y σ)
          (boundedLargePrimeDependencyGraph N M L Y) =
        (((boundedGoodStarts N M L Y).card +
          (boundedOrderedDependencyEdges N M L Y).card : ℕ) : ℝ) /
          (2 : ℝ) ^ (2 * L))

/-- The bundled finite core is proved without an additional bridge. -/
theorem boundedRatioFiniteSteinChenCore :
    BoundedRatioFiniteSteinChenCoreStatement := by
  intro N M L Y hN hNM hL hLY
  exact
    ⟨fun σ x ↦
        marginal_boundedConditionedGoodIndicator_eq_baseline
          hN hL hLY σ x,
      fun σ ↦
        hasExactDependencyGraph_boundedConditionedGoodIndicator hL σ,
      fun σ ↦
        poissonParameter_boundedConditionedGoodIndicator_eq
          hN hL hLY σ,
      fun σ ↦
        boundedTarget_sub_goodPoissonParameter_eq_badCard
          hNM hN hL hLY σ,
      fun σ ↦
        bOne_boundedConditionedGoodIndicator_eq_card_div
          hN hL hLY σ⟩

/-- Exact uniformly quantified edge conclusion consumed by Lemma 17.37. -/
def BoundedRatioDependencyEdgeStatement (C : ℝ) : Prop :=
  ∀ κ₀ : ℕ,
    UniformLittleOInBoundedRatioWindow C κ₀
      (fun N M L =>
        ((boundedOrderedDependencyEdges N M L
          (TerminalPrimeCutoff.terminalPrimeCutoff
            (L + 1))).card : ℝ))

/-- The dependency-edge antecedent follows from the prime-witness count. -/
theorem boundedRatioDependencyEdgeStatement
    {C : ℝ} (hC : 0 ≤ C) :
    BoundedRatioDependencyEdgeStatement C :=
  fun κ₀ ↦
    boundedOrderedDependencyEdges_terminalCutoff_uniformLittleOInBoundedRatioWindow
      hC κ₀

end

end BoundedRatioSteinChen
end PaperC
