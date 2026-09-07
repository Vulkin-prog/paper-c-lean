import PaperCV282.MaskedBadMass
import PaperC.Probability.ConditionalAGGAverage

/-!
# Exact conditional dependency on all dyadic sites

The index type includes every dyadic start, including all defective sites.
Small-prime signs are fixed and the remaining coordinates are uniform.
The literal shared-coordinate graph proves independence of every Boolean
pattern outside a closed neighborhood. No baseline marginal is assumed for
bad sites. Deterministic masking is allowed without removing these sites
from the graph.
-/

namespace PaperC.V282.AllStartConditionalDependency

open ArratiaGoldsteinGordonInput ConditionalDependencyGraph ConditionalAGGInstantiation
open ConditionalAGGAverage ConditionalStartProbability LargePrimeDependencyGraph
open SectionTwelveMoments SectionThirteenFiniteBound MaskedArithmeticGeometry
open scoped BigOperators

noncomputable section

/-- Shared large-prime coordinates on the entire dyadic population. -/
def allStartDependencyGraph (N L Y : ℕ) :
    SimpleGraph {x : ℕ // x ∈ dyadicBlock N} where
  Adj x y := LargePrimeAdjacent L Y x.val y.val
  symm := ⟨fun _ _ h => largePrimeAdjacent_symm h⟩
  loopless := ⟨fun x h => not_largePrimeAdjacent_self L Y x.val h⟩

@[simp]
theorem allStartDependencyGraph_adj {N L Y : ℕ}
    {x y : {x : ℕ // x ∈ dyadicBlock N}} :
    (allStartDependencyGraph N L Y).Adj x y ↔
      LargePrimeAdjacent L Y x.val y.val := Iff.rfl

/-- Boolean indicator of any dyadic start after fixing the small-prime signs. -/
def conditionedAllStartIndicator
    (N L Y : ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    {x : ℕ // x ∈ dyadicBlock N} →
      LargeSample (dyadicCutoff N L) Y → Bool := by
  classical
  exact fun x η ↦
    decide
      (startAt
        (assemble (dyadicCutoff N L) Y σ η) x.1 L)

@[simp]
theorem conditionedAllStartIndicator_eq_true_iff
    {N L Y : ℕ}
    {σ : SmallSample (dyadicCutoff N L) Y}
    {x : {x : ℕ // x ∈ dyadicBlock N}}
    {η : LargeSample (dyadicCutoff N L) Y} :
    conditionedAllStartIndicator N L Y σ x η = true ↔
      startAt
        (assemble (dyadicCutoff N L) Y σ η) x.1 L := by
  simp [conditionedAllStartIndicator]

@[simp]
theorem conditionedAllStartIndicator_eq_false_iff
    {N L Y : ℕ}
    {σ : SmallSample (dyadicCutoff N L) Y}
    {x : {x : ℕ // x ∈ dyadicBlock N}}
    {η : LargeSample (dyadicCutoff N L) Y} :
    conditionedAllStartIndicator N L Y σ x η = false ↔
      ¬startAt
        (assemble (dyadicCutoff N L) Y σ η) x.1 L := by
  simp [conditionedAllStartIndicator]

theorem conditionedAllStartIndicator_eq_of_eqOn_largePrimeCoordinates
    {N L Y : ℕ}
    (hL : 0 < L)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (x : {x : ℕ // x ∈ dyadicBlock N})
    (η θ : LargeSample (dyadicCutoff N L) Y)
    (heq :
      ∀ q : LargePrimeCoordinate (dyadicCutoff N L) Y,
        largeCoordinatePrime q ∈
            largePrimeCoordinates x.1 L Y →
          η q = θ q) :
    conditionedAllStartIndicator N L Y σ x η =
      conditionedAllStartIndicator N L Y σ x θ := by
  classical
  unfold conditionedAllStartIndicator
  exact Bool.decide_congr
    (conditionedStartAt_iff_of_eqOn_largePrimeCoordinates
      hL σ η θ heq)

/--
The conditioned all-start indicator, set identically to false away from
the deterministic mask.
-/
def maskedConditionedAllStartIndicator
    (N L Y : ℕ) (mask : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    {x : ℕ // x ∈ dyadicBlock N} →
      LargeSample (dyadicCutoff N L) Y → Bool := by
  classical
  exact fun x η ↦
    if x.1 ∈ mask then
      conditionedAllStartIndicator N L Y σ x η
    else false

@[simp]
theorem maskedConditionedAllStartIndicator_eq_true_iff
    {N L Y : ℕ} {mask : Finset ℕ}
    {σ : SmallSample (dyadicCutoff N L) Y}
    {x : {x : ℕ // x ∈ dyadicBlock N}}
    {η : LargeSample (dyadicCutoff N L) Y} :
    maskedConditionedAllStartIndicator N L Y mask σ x η = true ↔
      x.1 ∈ mask ∧
        startAt
          (assemble (dyadicCutoff N L) Y σ η) x.1 L := by
  simp [maskedConditionedAllStartIndicator,
    conditionedAllStartIndicator_eq_true_iff]

theorem maskedConditionedAllStartIndicator_eq_of_eqOn_largePrimeCoordinates
    {N L Y : ℕ} (mask : Finset ℕ)
    (hL : 0 < L)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (x : {x : ℕ // x ∈ dyadicBlock N})
    (η θ : LargeSample (dyadicCutoff N L) Y)
    (heq :
      ∀ q : LargePrimeCoordinate (dyadicCutoff N L) Y,
        largeCoordinatePrime q ∈
            largePrimeCoordinates x.1 L Y →
          η q = θ q) :
    maskedConditionedAllStartIndicator N L Y mask σ x η =
      maskedConditionedAllStartIndicator N L Y mask σ x θ := by
  unfold maskedConditionedAllStartIndicator
  split_ifs
  · exact
      conditionedAllStartIndicator_eq_of_eqOn_largePrimeCoordinates
        hL σ x η θ heq
  · rfl

/--
The original graph remains an exact dependency graph after deterministic
masking.  Keeping this supergraph avoids any measurable-space bookkeeping
for induced subtypes; its `b₁,b₂` terms can only be larger.
-/
theorem hasExactDependencyGraph_maskedConditionedAllStartIndicator
    {N L Y : ℕ} (mask : Finset ℕ)
    (hL : 0 < L)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    HasExactDependencyGraph
      (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedAllStartIndicator N L Y mask σ)
      (allStartDependencyGraph N L Y) := by
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
      maskedConditionedAllStartIndicator N L Y mask σ α η = value
  let Q : LargeSample (dyadicCutoff N L) Y → Prop :=
    fun η ↦
      HasOutsidePattern
        (maskedConditionedAllStartIndicator N L Y mask σ)
        (allStartDependencyGraph N L Y)
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
        maskedConditionedAllStartIndicator N L Y mask σ α η =
          maskedConditionedAllStartIndicator N L Y mask σ α
            (e.symm ((e η).1, 0)) := by
      apply
        maskedConditionedAllStartIndicator_eq_of_eqOn_largePrimeCoordinates
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
            (allStartDependencyGraph N L Y) α,
          maskedConditionedAllStartIndicator N L Y mask σ β.1 η =
            maskedConditionedAllStartIndicator N L Y mask σ β.1 θ := by
      intro β
      have hnotMem :
          β.1 ∉
            closedNeighborhood
              (allStartDependencyGraph N L Y) α :=
        β.2
      have hne : α ≠ β.1 := by
        intro h
        apply hnotMem
        rw [← h]
        exact
          self_mem_closedNeighborhood
            (allStartDependencyGraph N L Y) α
      have hneNat : α.1 ≠ β.1.1 := by
        intro h
        apply hne
        apply Subtype.ext
        exact h
      have hnotAdj :
          ¬(allStartDependencyGraph N L Y).Adj α β.1 := by
        intro hadj
        exact hnotMem
          (mem_closedNeighborhood.mpr (Or.inr hadj))
      have hnotLarge :
          ¬LargePrimeAdjacent L Y α.1 β.1.1 := by
        simpa only [allStartDependencyGraph_adj] using hnotAdj
      have hdisjoint :
          Disjoint
            (largePrimeCoordinates α.1 L Y)
            (largePrimeCoordinates β.1.1 L Y) :=
        disjoint_largePrimeCoordinates_of_not_adjacent
          hneNat hnotLarge
      apply
        maskedConditionedAllStartIndicator_eq_of_eqOn_largePrimeCoordinates
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


/-- Masking by the entire index population leaves the family unchanged. -/
theorem maskedConditionedAllStartIndicator_block (N L Y : ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    maskedConditionedAllStartIndicator N L Y (dyadicBlock N) sigma =
      conditionedAllStartIndicator N L Y sigma := by
  classical
  funext x eta
  simp [maskedConditionedAllStartIndicator,x.property]

/-- The entire conditional field has this exact graph, including defective sites. -/
theorem hasExactDependencyGraph_conditionedAllStartIndicator {N L Y : ℕ}
    (hL : 0 < L) (sigma : SmallSample (dyadicCutoff N L) Y) :
    HasExactDependencyGraph (largeUniformPMF (dyadicCutoff N L) Y)
      (conditionedAllStartIndicator N L Y sigma) (allStartDependencyGraph N L Y) := by
  simpa only [maskedConditionedAllStartIndicator_block] using
    hasExactDependencyGraph_maskedConditionedAllStartIndicator (dyadicBlock N) hL sigma


/-- Deterministic masking preserves the true marginal at each retained site. -/
theorem marginal_maskedConditionedAllStartIndicator {N L Y : ℕ} (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y)
    (x : {x : ℕ // x ∈ dyadicBlock N}) :
    marginal (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedAllStartIndicator N L Y mask sigma) x =
        if x.val ∈ mask then marginal (largeUniformPMF (dyadicCutoff N L) Y)
          (conditionedAllStartIndicator N L Y sigma) x else 0 := by
  classical
  by_cases hx : x.val ∈ mask
  · simp [marginal,maskedConditionedAllStartIndicator,hx]
  · simp [marginal,eventProbability,maskedConditionedAllStartIndicator,hx]

/-- Baseline marginals are proved only for good sites; defective marginals stay arbitrary. -/
theorem marginal_conditionedAllStartIndicator_of_not_fullBad {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y)
    (x : {x : ℕ // x ∈ dyadicBlock N})
    (hx : x.val ∉ fullBadStarts N L Y) :
    marginal (largeUniformPMF (dyadicCutoff N L) Y)
      (conditionedAllStartIndicator N L Y sigma) x = (1 : ℝ) / 2 ^ L := by
  have hxold : x.val ∈ goodStarts N L Y :=
    mem_goodStarts.mpr ⟨x.property,fun h => hx (terminalBadStarts_subset_fullBadStarts N L Y h)⟩
  exact marginal_conditionedGoodIndicator_eq_baseline hN hL hLY sigma ⟨x.val,hxold⟩

/-- Averaging a true all-site marginal gives its actual unconditional start probability. -/
theorem average_marginal_conditionedAllStartIndicator_eq (N L Y : ℕ)
    (x : {x : ℕ // x ∈ dyadicBlock N}) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      marginal (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedAllStartIndicator N L Y sigma) x) =
      (startProbability N L x.val : ℝ) := by
  classical
  have h := finiteUniformAverage_largeEventProbability_eq_full (dyadicCutoff N L) Y
    (fun omega => startAt omega x.val L)
  simpa only [marginal,conditionedAllStartIndicator_eq_true_iff,startProbability] using h

/-- The law of total probability retains the literal mask and all bad-site marginals. -/
theorem average_marginal_maskedConditionedAllStartIndicator_eq (N L Y : ℕ)
    (mask : Finset ℕ) (x : {x : ℕ // x ∈ dyadicBlock N}) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      marginal (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedAllStartIndicator N L Y mask sigma) x) =
      if x.val ∈ mask then (startProbability N L x.val : ℝ) else 0 := by
  classical
  simp_rw [marginal_maskedConditionedAllStartIndicator]
  by_cases hx : x.val ∈ mask
  · simp only [if_pos hx]
    exact average_marginal_conditionedAllStartIndicator_eq N L Y x
  · simp [hx,finiteUniformAverage]

/-- The same exact averaging identity holds for pairs, including defective sites. -/
theorem average_jointMarginal_conditionedAllStartIndicator_eq (N L Y : ℕ)
    (x y : {x : ℕ // x ∈ dyadicBlock N}) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      jointMarginal (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedAllStartIndicator N L Y sigma) x y) =
      (jointStartProbability N L x.val y.val : ℝ) := by
  classical
  have h := finiteUniformAverage_largeEventProbability_eq_full (dyadicCutoff N L) Y
    (fun omega => startAt omega x.val L ∧ startAt omega y.val L)
  simpa only [jointMarginal,conditionedAllStartIndicator_eq_true_iff,jointStartProbability] using h

/-- The average bad-site marginal budget is exactly the actual masked bad mass. -/
theorem average_bad_marginal_sum_eq (N L Y : ℕ) (mask : Finset ℕ) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      ∑ x : {x : ℕ // x ∈ dyadicBlock N},
        if x.val ∈ fullBadMask N L Y mask then
          marginal (largeUniformPMF (dyadicCutoff N L) Y)
            (maskedConditionedAllStartIndicator N L Y mask sigma) x else 0) =
      (MaskedBadMass.maskedBadStartMass N L Y mask : ℝ) := by
  classical
  rw [finiteUniformAverage_fintypeSum]
  have heach (x : {x : ℕ // x ∈ dyadicBlock N}) :
      finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
        if x.val ∈ fullBadMask N L Y mask then
          marginal (largeUniformPMF (dyadicCutoff N L) Y)
            (maskedConditionedAllStartIndicator N L Y mask sigma) x else 0) =
        if x.val ∈ fullBadMask N L Y mask then (startProbability N L x.val : ℝ) else 0 := by
    by_cases hx : x.val ∈ fullBadMask N L Y mask
    · simp only [if_pos hx,average_marginal_maskedConditionedAllStartIndicator_eq,
        if_pos (fullBadMask_subset_mask N L Y mask hx)]
    · simp [hx,finiteUniformAverage]
  simp_rw [heach]
  rw [← Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl)
    (fun x => if x ∈ fullBadMask N L Y mask then (startProbability N L x : ℝ) else 0)]
  rw [← Finset.sum_filter]
  have hfilter : (dyadicBlock N).filter (fun x => x ∈ fullBadMask N L Y mask) =
      fullBadMask N L Y mask := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hx
      exact ⟨fullBadStarts_subset_block N L Y (mem_fullBadMask.mp hx).2,hx⟩
  rw [hfilter]
  simp [MaskedBadMass.maskedBadStartMass]

end
end PaperC.V282.AllStartConditionalDependency
