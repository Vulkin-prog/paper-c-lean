import PaperC.Probability.BadStartMass
import PaperC.Probability.SteinChenTerms

/-!
# Finite Stein--Chen terms under a deterministic mask

This file is the finite restriction core of Proposition 14.2.  A
deterministic mask is imposed by intersecting the already constructed good
vertex set, ordered dependency-edge set, and closed-neighbour pair set with
the corresponding finite products of the mask.

All summands in `b₁` and the averaged `b₂` are nonnegative.  Consequently
the masked terms are bounded literally by the unmasked terms of
`SteinChenTerms`.  The removed-start probability mass and the difference
between the target and conditional Poisson parameters are likewise bounded
by their full-block counterparts.

There is no asymptotic or external input in this module.
-/

namespace PaperC
namespace MaskedSteinChen

open scoped BigOperators

open BadStartCount
open LargePrimeDependencyGraph

noncomputable section

/-! ## Induced good-start population and dependency relation -/

/-- Good starts retained by a deterministic mask. -/
def maskedGoodStarts
    (N L Y : ℕ) (mask : Finset ℕ) : Finset ℕ :=
  goodStarts N L Y ∩ mask

@[simp]
theorem mem_maskedGoodStarts
    {N L Y x : ℕ} {mask : Finset ℕ} :
    x ∈ maskedGoodStarts N L Y mask ↔
      x ∈ goodStarts N L Y ∧ x ∈ mask := by
  simp [maskedGoodStarts]

/-- Restricting to a mask cannot create a new good start. -/
theorem maskedGoodStarts_subset_goodStarts
    (N L Y : ℕ) (mask : Finset ℕ) :
    maskedGoodStarts N L Y mask ⊆ goodStarts N L Y :=
  Finset.inter_subset_left

/-- The masked population has at most as many vertices as the full one. -/
theorem card_maskedGoodStarts_le
    (N L Y : ℕ) (mask : Finset ℕ) :
    (maskedGoodStarts N L Y mask).card ≤
      (goodStarts N L Y).card :=
  Finset.card_le_card
    (maskedGoodStarts_subset_goodStarts N L Y mask)

/-- Ordered dependency edges of the subgraph induced by the mask. -/
def maskedDependencyEdges
    (N L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  orderedDependencyEdges N L Y ∩ mask.product mask

@[simp]
theorem mem_maskedDependencyEdges
    {N L Y : ℕ} {mask : Finset ℕ} {pair : ℕ × ℕ} :
    pair ∈ maskedDependencyEdges N L Y mask ↔
      pair ∈ orderedDependencyEdges N L Y ∧
        pair.1 ∈ mask ∧ pair.2 ∈ mask := by
  simp [maskedDependencyEdges]

/-- Masking only removes ordered dependency edges. -/
theorem maskedDependencyEdges_subset
    (N L Y : ℕ) (mask : Finset ℕ) :
    maskedDependencyEdges N L Y mask ⊆
      orderedDependencyEdges N L Y :=
  Finset.inter_subset_left

/--
The closed-neighbour relation of the subgraph induced by the mask, written
as ordered pairs.
-/
def maskedClosedDependencyPairs
    (N L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  SteinChenTerms.closedDependencyPairs N L Y ∩ mask.product mask

@[simp]
theorem mem_maskedClosedDependencyPairs
    {N L Y : ℕ} {mask : Finset ℕ} {pair : ℕ × ℕ} :
    pair ∈ maskedClosedDependencyPairs N L Y mask ↔
      pair ∈ SteinChenTerms.closedDependencyPairs N L Y ∧
        pair.1 ∈ mask ∧ pair.2 ∈ mask := by
  simp [maskedClosedDependencyPairs]

/-- Masking only removes closed-neighbour pairs. -/
theorem maskedClosedDependencyPairs_subset
    (N L Y : ℕ) (mask : Finset ℕ) :
    maskedClosedDependencyPairs N L Y mask ⊆
      SteinChenTerms.closedDependencyPairs N L Y :=
  Finset.inter_subset_left

/-- The literal closed neighbourhood of one start in the induced graph. -/
def maskedClosedNeighborhood
    (N L Y : ℕ) (mask : Finset ℕ) (x : ℕ) : Finset ℕ := by
  classical
  exact
    (maskedGoodStarts N L Y mask).filter fun y ↦
      y = x ∨ LargePrimeAdjacent L Y x y

@[simp]
theorem mem_maskedClosedNeighborhood
    {N L Y x y : ℕ} {mask : Finset ℕ} :
    y ∈ maskedClosedNeighborhood N L Y mask x ↔
      y ∈ maskedGoodStarts N L Y mask ∧
        (y = x ∨ LargePrimeAdjacent L Y x y) := by
  classical
  simp [maskedClosedNeighborhood]

/--
The pair-based closed relation is exactly the diagonal of the masked good
set together with the masked open-edge relation.
-/
theorem maskedClosedDependencyPairs_eq_diag_union_edges
    (N L Y : ℕ) (mask : Finset ℕ) :
    maskedClosedDependencyPairs N L Y mask =
      (maskedGoodStarts N L Y mask).diag ∪
        maskedDependencyEdges N L Y mask := by
  ext pair
  simp only [mem_maskedClosedDependencyPairs,
    SteinChenTerms.mem_closedDependencyPairs,
    Finset.mem_product, Finset.mem_union, Finset.mem_diag,
    mem_maskedGoodStarts, mem_maskedDependencyEdges]
  constructor
  · rintro ⟨hclosed, hxmask, hymask⟩
    rcases hclosed with hdiag | hedge
    · left
      exact ⟨⟨hdiag.1, hxmask⟩, hdiag.2⟩
    · right
      exact ⟨hedge, hxmask, hymask⟩
  · rintro (hdiag | hedge)
    · exact
        ⟨Or.inl ⟨hdiag.1.1, hdiag.2⟩,
          hdiag.1.2,
          hdiag.2 ▸ hdiag.1.2⟩
    · exact ⟨Or.inr hedge.1, hedge.2.1, hedge.2.2⟩

/-! ## Masked Stein--Chen terms -/

/-- First conditional Stein--Chen term after restriction to the mask. -/
def maskedSteinBOne
    (N L Y : ℕ) (mask : Finset ℕ) : ℚ :=
  ∑ _pair ∈ maskedClosedDependencyPairs N L Y mask,
    SteinChenTerms.conditionalMarginal L *
      SteinChenTerms.conditionalMarginal L

/-- Exact cardinal form of the masked first term. -/
theorem maskedSteinBOne_eq_card_div
    (N L Y : ℕ) (mask : Finset ℕ) :
    maskedSteinBOne N L Y mask =
      ((maskedClosedDependencyPairs N L Y mask).card : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  unfold maskedSteinBOne SteinChenTerms.conditionalMarginal
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [show 2 * L = L + L by omega, pow_add]
  ring

/-- The masked first Stein--Chen term is bounded by the unmasked term. -/
theorem maskedSteinBOne_le_unmasked
    (N L Y : ℕ) (mask : Finset ℕ) :
    maskedSteinBOne N L Y mask ≤
      SteinChenTerms.steinBOne N L Y := by
  unfold maskedSteinBOne SteinChenTerms.steinBOne
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (maskedClosedDependencyPairs_subset N L Y mask)
  intro _pair _hfull _hmasked
  unfold SteinChenTerms.conditionalMarginal
  positivity

/--
The averaged second conditional term after restriction to the mask.
Its summands are the same unconditional joint probabilities as before.
-/
def maskedSteinBTwoAverage
    (N L Y : ℕ) (mask : Finset ℕ) : ℚ :=
  SectionTwelveMoments.jointPairMass N L
    (maskedDependencyEdges N L Y mask)

/-- The masked averaged second term is bounded by the unmasked term. -/
theorem maskedSteinBTwoAverage_le_unmasked
    (N L Y : ℕ) (mask : Finset ℕ) :
    maskedSteinBTwoAverage N L Y mask ≤
      SteinChenTerms.steinBTwoAverage N L Y := by
  unfold maskedSteinBTwoAverage SteinChenTerms.steinBTwoAverage
  exact
    SteinChenTerms.jointPairMass_mono
      (maskedDependencyEdges_subset N L Y mask)

/-! ## Removed starts and Poisson parameters -/

/-- Bad starts which lie in the deterministic mask. -/
def maskedTerminalBadStarts
    (N L Y : ℕ) (mask : Finset ℕ) : Finset ℕ :=
  terminalBadStarts N L Y ∩ mask

@[simp]
theorem mem_maskedTerminalBadStarts
    {N L Y x : ℕ} {mask : Finset ℕ} :
    x ∈ maskedTerminalBadStarts N L Y mask ↔
      x ∈ terminalBadStarts N L Y ∧ x ∈ mask := by
  simp [maskedTerminalBadStarts]

/-- Masked bad starts form a subset of the full bad-start population. -/
theorem maskedTerminalBadStarts_subset
    (N L Y : ℕ) (mask : Finset ℕ) :
    maskedTerminalBadStarts N L Y mask ⊆
      terminalBadStarts N L Y :=
  Finset.inter_subset_left

/-- The number of removed masked starts is bounded by the full count. -/
theorem card_maskedTerminalBadStarts_le
    (N L Y : ℕ) (mask : Finset ℕ) :
    (maskedTerminalBadStarts N L Y mask).card ≤
      (terminalBadStarts N L Y).card :=
  Finset.card_le_card
    (maskedTerminalBadStarts_subset N L Y mask)

/-- Probability mass of the bad starts which lie in the mask. -/
def maskedBadStartProbabilityMass
    (N L Y : ℕ) (mask : Finset ℕ) : ℚ :=
  BadStartMass.startProbabilityMass N L
    (maskedTerminalBadStarts N L Y mask)

/-- Restriction to a mask cannot increase the removed probability mass. -/
theorem maskedBadStartProbabilityMass_le_unmasked
    (N L Y : ℕ) (mask : Finset ℕ) :
    maskedBadStartProbabilityMass N L Y mask ≤
      BadStartMass.startProbabilityMass N L
        (terminalBadStarts N L Y) := by
  unfold maskedBadStartProbabilityMass BadStartMass.startProbabilityMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (maskedTerminalBadStarts_subset N L Y mask)
  intro x _hfull _hmasked
  exact BadStartMass.startProbability_nonneg N L x

/--
The full two-cutoff bad-start estimate therefore applies verbatim under
every deterministic mask.
-/
theorem maskedBadStartProbabilityMass_le_two_cutoffs
    {N L B Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L)
    (hLB : L + 1 ≤ B) (hBY : B ≤ Y) :
    maskedBadStartProbabilityMass N L Y mask ≤
      2 * BadStartMass.terminalDefectWeightMass N L B /
          (2 : ℚ) ^ L +
        ((terminalBadStarts N L Y).card : ℚ) /
          (2 : ℚ) ^ L := by
  exact
    (maskedBadStartProbabilityMass_le_unmasked N L Y mask).trans
      (BadStartMass.startProbabilityMass_terminalBadStarts_le_two_cutoffs
        hN hL hLB hBY)

/-- Target Poisson parameter `|A_N| 2⁻ᴸ` of the masked count. -/
def maskedPoissonParameter
    (L : ℕ) (mask : Finset ℕ) : ℚ :=
  (mask.card : ℚ) / (2 : ℚ) ^ L

/--
Conditional parameter after the bad starts have been removed from the mask.
-/
def maskedGoodPoissonParameter
    (N L Y : ℕ) (mask : Finset ℕ) : ℚ :=
  ((maskedGoodStarts N L Y mask).card : ℚ) /
    (2 : ℚ) ^ L

/--
Inside the dyadic block, the masked good set is literally the mask minus
the bad-start set.
-/
theorem maskedGoodStarts_eq_sdiff
    {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    maskedGoodStarts N L Y mask =
      mask \ terminalBadStarts N L Y := by
  ext x
  simp only [mem_maskedGoodStarts, mem_goodStarts,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨_hxblock, hxbad⟩, hxmask⟩
    exact ⟨hxmask, hxbad⟩
  · rintro ⟨hxmask, hxbad⟩
    exact ⟨⟨hmask hxmask, hxbad⟩, hxmask⟩

/-- Masked bad starts are the same intersection in the opposite order. -/
theorem maskedTerminalBadStarts_eq_inter
    (N L Y : ℕ) (mask : Finset ℕ) :
    maskedTerminalBadStarts N L Y mask =
      mask ∩ terminalBadStarts N L Y := by
  ext x
  simp [maskedTerminalBadStarts, and_left_comm, and_comm]

/-- Exact decomposition of the cardinality of an arbitrary dyadic mask. -/
theorem card_maskedGood_add_card_bad
    {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    (maskedGoodStarts N L Y mask).card +
        (maskedTerminalBadStarts N L Y mask).card =
      mask.card := by
  rw [maskedGoodStarts_eq_sdiff hmask,
    maskedTerminalBadStarts_eq_inter]
  exact Finset.card_sdiff_add_card_inter mask
    (terminalBadStarts N L Y)

/--
Exact parameter loss: deleting bad starts changes `|A_N|2⁻ᴸ` by precisely
`|A_N ∩ D_Y|2⁻ᴸ`.
-/
theorem maskedPoissonParameter_sub_good_eq
    {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    maskedPoissonParameter L mask -
        maskedGoodPoissonParameter N L Y mask =
      ((maskedTerminalBadStarts N L Y mask).card : ℚ) /
        (2 : ℚ) ^ L := by
  have hcard :=
    card_maskedGood_add_card_bad
      (N := N) (L := L) (Y := Y) hmask
  unfold maskedPoissonParameter maskedGoodPoissonParameter
  have hcardQ :
      (mask.card : ℚ) =
        ((maskedGoodStarts N L Y mask).card : ℚ) +
          ((maskedTerminalBadStarts N L Y mask).card : ℚ) := by
    exact_mod_cast hcard.symm
  rw [hcardQ]
  ring

/-- The conditional parameter never exceeds the target parameter. -/
theorem maskedGoodPoissonParameter_le
    {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    maskedGoodPoissonParameter N L Y mask ≤
      maskedPoissonParameter L mask := by
  have hdiff :=
    maskedPoissonParameter_sub_good_eq
      (N := N) (L := L) (Y := Y) hmask
  have hnonneg :
      0 ≤
        ((maskedTerminalBadStarts N L Y mask).card : ℚ) /
          (2 : ℚ) ^ L := by
    positivity
  linarith

/--
The masked parameter loss is bounded by the full-block bad-start count,
exactly as used in Proposition 14.2.
-/
theorem abs_maskedPoissonParameter_sub_good_le
    {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    |maskedPoissonParameter L mask -
        maskedGoodPoissonParameter N L Y mask| ≤
      ((terminalBadStarts N L Y).card : ℚ) /
        (2 : ℚ) ^ L := by
  rw [maskedPoissonParameter_sub_good_eq hmask]
  rw [abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast
      card_maskedTerminalBadStarts_le N L Y mask
  · positivity

end

end MaskedSteinChen
end PaperC
