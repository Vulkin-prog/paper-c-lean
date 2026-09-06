import PaperCV282.AllStartConditionalDependency
import PaperCV282.MaskedArithmeticCosts

/-!
# Exact invariance of retained graph costs under the all-site extension

Both graph carriers use the same arithmetic adjacency on natural starts.
Coordinates outside the retained mask are identically false. Their first and
second graph costs therefore vanish, including all edges to those coordinates.
-/

namespace PaperC.V282.AllStartFieldCosts

open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalDependencyGraph
open ConditionalAGGInstantiation ConditionalAGGAverage MaskedPoissonCritical
open LargePrimeDependencyGraph SectionTwelveMoments SectionThirteenFiniteBound
open MaskedArithmeticGeometry MaskedArithmeticCosts AllStartConditionalDependency
open scoped BigOperators

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def arithmeticGraphOn (s : Finset ℕ) (L Y : ℕ) : SimpleGraph {x : ℕ // x ∈ s} where
  Adj x y := LargePrimeAdjacent L Y x.val y.val
  symm := ⟨fun _ _ h => largePrimeAdjacent_symm h⟩
  loopless := ⟨fun x h => not_largePrimeAdjacent_self L Y x.val h⟩

theorem sum_subtype_pair_eq (s : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ x : {x : ℕ // x ∈ s}, ∑ y : {y : ℕ // y ∈ s}, f x.val y.val) =
      ∑ x ∈ s, ∑ y ∈ s, f x y := by
  classical
  simp_rw [← Finset.sum_subtype s (fun _ => Iff.rfl)]
  exact (Finset.sum_subtype s (fun _ => Iff.rfl) (fun x => ∑ y ∈ s, f x y)).symm

theorem sum_pair_subset_of_zero {s t : Finset ℕ} (hst : s ⊆ t) (f : ℕ → ℕ → ℝ)
    (hleft : ∀ x ∈ t, x ∉ s → ∀ y, f x y = 0)
    (hright : ∀ y ∈ t, y ∉ s → ∀ x, f x y = 0) :
    (∑ x ∈ t, ∑ y ∈ t, f x y) = ∑ x ∈ s, ∑ y ∈ s, f x y := by
  classical
  rw [← Finset.sum_subset hst (fun x hx hxs => by simp [hleft x hx hxs])]
  apply Finset.sum_congr rfl
  intro x hx
  exact (Finset.sum_subset hst (fun y hy hys => hright y hy hys x)).symm

theorem bOne_arithmeticGraphOn {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ℕ → Ω → Bool) (s : Finset ℕ) (L Y : ℕ) :
    bOne μ (fun x : {x : ℕ // x ∈ s} => X x.val) (arithmeticGraphOn s L Y) =
      ∑ x ∈ s, ∑ y ∈ s, if y = x ∨ LargePrimeAdjacent L Y x y then
        marginal μ X x * marginal μ X y else 0 := by
  classical
  unfold bOne closedNeighborhood
  simp_rw [Finset.sum_filter]
  have h := sum_subtype_pair_eq s (fun x y =>
    if y = x ∨ LargePrimeAdjacent L Y x y then marginal μ X x * marginal μ X y else 0)
  convert h using 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [arithmeticGraphOn, Subtype.ext_iff]
  rfl

theorem openNeighborhood_arithmeticGraphOn (s : Finset ℕ) (L Y : ℕ)
    (x : {x : ℕ // x ∈ s}) :
    (closedNeighborhood (arithmeticGraphOn s L Y) x).erase x =
      Finset.univ.filter (fun y : {y : ℕ // y ∈ s} => LargePrimeAdjacent L Y x.val y.val) := by
  classical
  ext y
  simp only [Finset.mem_erase, mem_closedNeighborhood, arithmeticGraphOn,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, heq | hadj⟩
    · exact (hne heq).elim
    · exact hadj
  · intro hadj
    exact ⟨fun heq => hadj.1 (congrArg Subtype.val heq).symm, Or.inr hadj⟩

theorem bTwo_arithmeticGraphOn {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ℕ → Ω → Bool) (s : Finset ℕ) (L Y : ℕ) :
    bTwo μ (fun x : {x : ℕ // x ∈ s} => X x.val) (arithmeticGraphOn s L Y) =
      ∑ x ∈ s, ∑ y ∈ s, if LargePrimeAdjacent L Y x y then
        jointMarginal μ X x y else 0 := by
  classical
  unfold bTwo
  simp_rw [openNeighborhood_arithmeticGraphOn, Finset.sum_filter]
  exact sum_subtype_pair_eq s (fun x y =>
    if LargePrimeAdjacent L Y x y then jointMarginal μ X x y else 0)

theorem bOne_arithmeticGraphOn_subset {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ℕ → Ω → Bool) {s t : Finset ℕ}
    (hst : s ⊆ t) (hzero : ∀ x ∈ t, x ∉ s → ∀ ω, X x ω = false) (L Y : ℕ) :
    bOne μ (fun x : {x : ℕ // x ∈ t} => X x.val) (arithmeticGraphOn t L Y) =
      bOne μ (fun x : {x : ℕ // x ∈ s} => X x.val) (arithmeticGraphOn s L Y) := by
  classical
  rw [bOne_arithmeticGraphOn, bOne_arithmeticGraphOn]
  apply sum_pair_subset_of_zero hst
  · intro x hx hxs y
    simp [marginal, eventProbability, hzero x hx hxs]
  · intro y hy hys x
    simp [marginal, eventProbability, hzero y hy hys]

theorem bTwo_arithmeticGraphOn_subset {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ℕ → Ω → Bool) {s t : Finset ℕ}
    (hst : s ⊆ t) (hzero : ∀ x ∈ t, x ∉ s → ∀ ω, X x ω = false) (L Y : ℕ) :
    bTwo μ (fun x : {x : ℕ // x ∈ t} => X x.val) (arithmeticGraphOn t L Y) =
      bTwo μ (fun x : {x : ℕ // x ∈ s} => X x.val) (arithmeticGraphOn s L Y) := by
  classical
  rw [bTwo_arithmeticGraphOn, bTwo_arithmeticGraphOn]
  apply sum_pair_subset_of_zero hst
  · intro x hx hxs y
    simp [jointMarginal, eventProbability, hzero x hx hxs]
  · intro y hy hys x
    simp [jointMarginal, eventProbability, hzero y hy hys]

def maskedNatIndicator (N L Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y) (x : ℕ)
    (eta : LargeSample (dyadicCutoff N L) Y) : Bool := by
  classical
  exact if x ∈ mask then decide (startAt (assemble (dyadicCutoff N L) Y sigma eta) x L) else false

theorem bOne_fullGood_allStart_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (sigma : SmallSample (dyadicCutoff N L) Y) :
    bOne (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedAllStartIndicator N L Y (fullGoodMask N L Y mask) sigma)
      (allStartDependencyGraph N L Y) =
    bOne (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
      (largePrimeDependencyGraph N L Y) := by
  classical
  apply bOne_arithmeticGraphOn_subset (X := maskedNatIndicator N L Y (fullGoodMask N L Y mask) sigma)
    (s := goodStarts N L Y) (t := dyadicBlock N)
    (largeUniformPMF (dyadicCutoff N L) Y) Finset.sdiff_subset
  intro x hx hxs omega
  have hnot : x ∉ fullGoodMask N L Y mask := fun h => hxs (fullGoodMask_subset_historical_good hmask h)
  simp [maskedNatIndicator, hnot]

theorem bTwo_fullGood_allStart_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (sigma : SmallSample (dyadicCutoff N L) Y) :
    bTwo (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedAllStartIndicator N L Y (fullGoodMask N L Y mask) sigma)
      (allStartDependencyGraph N L Y) =
    bTwo (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
      (largePrimeDependencyGraph N L Y) := by
  classical
  apply bTwo_arithmeticGraphOn_subset (X := maskedNatIndicator N L Y (fullGoodMask N L Y mask) sigma)
    (s := goodStarts N L Y) (t := dyadicBlock N)
    (largeUniformPMF (dyadicCutoff N L) Y) Finset.sdiff_subset
  intro x hx hxs omega
  have hnot : x ∉ fullGoodMask N L Y mask := fun h => hxs (fullGoodMask_subset_historical_good hmask h)
  simp [maskedNatIndicator, hnot]

end

end PaperC.V282.AllStartFieldCosts
