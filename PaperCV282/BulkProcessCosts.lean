import PaperCV282.BulkSupportGraph
import PaperCV282.DictionaryFieldFirstCost

/-!
# Exact label costs on an arbitrary finite population

Rates may depend on the label. The first cost sees their sum squared,
not the cardinality of the label set. Distinct labels at the same site
are removed from the second cost by actual event disjointness.
-/

namespace PaperC.V282.BulkProcessCosts

open BulkSupportGraph DictionaryFieldFirstCost AllStartFieldCosts
open ConditionalStartProbability ArratiaGoldsteinGordonInput LargePrimeDependencyGraph
open MaskedArithmeticGeometry MaskedPairGeometry SectionThirteenFiniteBound
open scoped BigOperators

noncomputable section

local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def labelledFamily {κ S : Type*} (sites : Finset ℕ) (X : ℕ → κ → S → Bool) : LabelledIndex sites κ → S → Bool :=
  fun i => X i.1.val i.2

def maskedLabelledFamily {κ S : Type*} (sites : Finset ℕ) (X : ℕ → κ → S → Bool) (mask : Finset ℕ) :=
  maskedLabelIndicator sites (labelledFamily sites X) mask

theorem sum_labelledIndex {κ : Type*} [Fintype κ] [DecidableEq κ] (sites : Finset ℕ) (f : ℕ → κ → ℝ) :
    (∑ i : LabelledIndex sites κ, f i.1.val i.2) = ∑ x ∈ sites, ∑ a : κ, f x a := by
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_subtype (sites) (fun _ => Iff.rfl) (fun x => ∑ a : κ, f x a)).symm

theorem sum_labelledIndex_pair {κ : Type*} [Fintype κ] [DecidableEq κ] (sites : Finset ℕ) (f : ℕ → ℕ → κ → κ → ℝ) :
    (∑ i : LabelledIndex sites κ, ∑ j : LabelledIndex sites κ, f i.1.val j.1.val i.2 j.2) =
      ∑ xy ∈ sites ×ˢ sites, ∑ a : κ, ∑ b : κ, f xy.1 xy.2 a b := by
  have hinner (i : LabelledIndex sites κ) := sum_labelledIndex sites (fun y b => f i.1.val y i.2 b)
  simp_rw [hinner]
  rw [sum_labelledIndex sites (fun x a => ∑ y ∈ sites, ∑ b : κ, f x y a b)]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]

/-- Variable label rates aggregate exactly to a single site rate in the first cost. -/
theorem bOne_labelled_eq {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S]
    (μ : FinitePMF S) (X : ℕ → κ → S → Bool) (sites : Finset ℕ) (Q Y : ℕ)
    (mask : Finset ℕ) (hmask : mask ⊆ sites) (rate : κ → ℝ)
    (hm : ∀ i : LabelledIndex sites κ,
      marginal μ (maskedLabelledFamily sites X mask) i = if i.1.val ∈ mask then rate i.2 else 0) :
    bOne μ (maskedLabelledFamily sites X mask) (labelledGraph sites Q Y κ) =
      (∑ a, rate a)^2 * (closedDictionarySitePairs Q Y mask).card := by
  let f : ℕ → ℕ → κ → κ → ℝ := fun x y a b =>
    if x ∈ mask ∧ y ∈ mask ∧ (Nat.dist x y ≤ Q ∨ LargePrimeAdjacent Q Y x y)
      then rate a * rate b else 0
  have hc (i : LabelledIndex sites κ) : closedNeighborhood (labelledGraph sites Q Y κ) i =
      Finset.univ.filter (fun j => Nat.dist i.1.val j.1.val ≤ Q ∨ LargePrimeAdjacent Q Y i.1.val j.1.val) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_closedNeighborhood_labelledGraph]
  have hb : bOne μ (maskedLabelledFamily sites X mask) (labelledGraph sites Q Y κ) =
      ∑ i : LabelledIndex sites κ, ∑ j : LabelledIndex sites κ, f i.1.val j.1.val i.2 j.2 := by
    unfold bOne
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hm,hm]
    by_cases hx : i.1.val ∈ mask <;> by_cases hy : j.1.val ∈ mask <;>
      by_cases ha : Nat.dist i.1.val j.1.val ≤ Q ∨ LargePrimeAdjacent Q Y i.1.val j.1.val <;>
      simp [f,hx,hy,ha]
  rw [hb,sum_labelledIndex_pair]
  have hs (x y : ℕ) : (∑ a : κ, ∑ b : κ, f x y a b) =
      if x ∈ mask ∧ y ∈ mask ∧ (Nat.dist x y ≤ Q ∨ LargePrimeAdjacent Q Y x y)
        then (∑ a, rate a)^2 else 0 := by
    dsimp only [f]
    split_ifs <;> simp [← Finset.mul_sum,← Finset.sum_mul,pow_two]
  simp_rw [hs]
  rw [Finset.sum_product,sum_pair_subset_of_zero hmask _
    (by intro x hx hnot y; simp [hnot]) (by intro y hy hnot x; simp [hnot])]
  rw [← Finset.sum_product']
  have hf : (∑ xy ∈ mask ×ˢ mask,
      if xy.1 ∈ mask ∧ xy.2 ∈ mask ∧ (Nat.dist xy.1 xy.2 ≤ Q ∨ LargePrimeAdjacent Q Y xy.1 xy.2)
        then (∑ a, rate a)^2 else 0) =
      ∑ xy ∈ closedDictionarySitePairs Q Y mask, (∑ a, rate a)^2 := by
    rw [closedDictionarySitePairs,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro xy hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    simp [hx,hy]
  rw [hf]
  simp [mul_comm]

/-- Actual joint mass after summing all label alternatives at a site pair. -/
def labelPairMass {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S]
    (μ : FinitePMF S) (X : ℕ → κ → S → Bool) (pairs : Finset (ℕ × ℕ)) : ℝ :=
  ∑ xy ∈ pairs, ∑ a : κ, ∑ b : κ,
    eventProbability μ (fun omega => X xy.1 a omega = true ∧ X xy.2 b omega = true)

def labelledNeighborPairs (Q Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  mask.offDiag.filter fun xy => Nat.dist xy.1 xy.2 ≤ Q ∨ LargePrimeAdjacent Q Y xy.1 xy.2

theorem mem_labelledNeighborPairs (Q Y : ℕ) (mask : Finset ℕ) (x y : ℕ) :
    (x,y) ∈ labelledNeighborPairs Q Y mask ↔
      x ∈ mask ∧ y ∈ mask ∧ x ≠ y ∧
        (Nat.dist x y ≤ Q ∨ LargePrimeAdjacent Q Y x y) := by
  simp [labelledNeighborPairs,Finset.mem_offDiag,and_assoc]

/-- Distinct alternatives at one site have exactly zero joint probability. -/
theorem joint_labelled_same_site_zero {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S]
    (μ : FinitePMF S) (X : ℕ → κ → S → Bool) (sites : Finset ℕ)
    (hdisj : ∀ x ∈ sites, ∀ a b : κ, a ≠ b → ∀ omega,
      ¬(X x a omega = true ∧ X x b omega = true))
    (i j : LabelledIndex sites κ) (hsite : i.1.val = j.1.val) (hne : i ≠ j) :
    jointMarginal μ (labelledFamily sites X) i j = 0 := by
  have hab : i.2 ≠ j.2 := by
    intro h
    exact hne (Prod.ext (Subtype.ext hsite) h)
  have he : (fun omega => labelledFamily sites X i omega = true ∧
      labelledFamily sites X j omega = true) = fun _ => False := by
    funext omega
    apply propext
    simp only [iff_false,labelledFamily,← hsite]
    exact hdisj i.1.val i.1.property i.2 j.2 hab omega
  rw [jointMarginal,he]
  simp [eventProbability]

/-- The second cost is the genuine summed joint mass on distinct neighbouring sites. -/
theorem bTwo_labelled_eq {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S]
    (μ : FinitePMF S) (X : ℕ → κ → S → Bool) (sites : Finset ℕ) (Q Y : ℕ)
    (mask : Finset ℕ) (hmask : mask ⊆ sites)
    (hdisj : ∀ x ∈ sites, ∀ a b : κ, a ≠ b → ∀ omega,
      ¬(X x a omega = true ∧ X x b omega = true)) :
    bTwo μ (maskedLabelledFamily sites X mask) (labelledGraph sites Q Y κ) =
      labelPairMass μ X (labelledNeighborPairs Q Y mask) := by
  have ht (i j : LabelledIndex sites κ) :
      (if j ∈ (closedNeighborhood (labelledGraph sites Q Y κ) i).erase i then
        jointMarginal μ (maskedLabelledFamily sites X mask) i j else 0) =
      if (i.1.val,j.1.val) ∈ labelledNeighborPairs Q Y mask then
        eventProbability μ (fun omega => X i.1.val i.2 omega = true ∧ X j.1.val j.2 omega = true)
      else 0 := by
    by_cases hx : i.1.val ∈ mask
    · by_cases hy : j.1.val ∈ mask
      · have hjoint : jointMarginal μ (maskedLabelledFamily sites X mask) i j =
          jointMarginal μ (labelledFamily sites X) i j := by
          simp only [jointMarginal,maskedLabelledFamily,maskedLabelIndicator,if_pos hx,if_pos hy]
        rw [hjoint]
        by_cases hsite : i.1.val = j.1.val
        · by_cases heq : i = j
          · subst j
            simp [mem_labelledNeighborPairs]
          · rw [joint_labelled_same_site_zero μ X sites hdisj i j hsite heq]
            simp [mem_labelledNeighborPairs,hsite]
        · have hne : j ≠ i := fun h => hsite (congrArg (fun z : LabelledIndex sites κ => z.1.val) h.symm)
          simp [Finset.mem_erase,labelledGraph,
            mem_labelledNeighborPairs,hx,hy,hsite,hne,Ne.symm hne,jointMarginal,labelledFamily]
      · simp [jointMarginal,maskedLabelledFamily,maskedLabelIndicator,hy,
          mem_labelledNeighborPairs,eventProbability]
    · simp [jointMarginal,maskedLabelledFamily,maskedLabelIndicator,hx,
        mem_labelledNeighborPairs,eventProbability]
  unfold bTwo
  have hs (i : LabelledIndex sites κ) :
      (∑ j ∈ (closedNeighborhood (labelledGraph sites Q Y κ) i).erase i,
        jointMarginal μ (maskedLabelledFamily sites X mask) i j) =
      ∑ j : LabelledIndex sites κ, if (i.1.val,j.1.val) ∈ labelledNeighborPairs Q Y mask then
        eventProbability μ (fun omega => X i.1.val i.2 omega = true ∧ X j.1.val j.2 omega = true) else 0 := by
    have hf : Finset.univ.filter (fun j => j ∈ (closedNeighborhood (labelledGraph sites Q Y κ) i).erase i) =
        (closedNeighborhood (labelledGraph sites Q Y κ) i).erase i := by ext j; simp
    rw [← hf,Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => ht i j
  simp_rw [hs]
  rw [sum_labelledIndex_pair sites (fun x y a b => if (x,y) ∈ labelledNeighborPairs Q Y mask then
    eventProbability μ (fun omega => X x a omega = true ∧ X y b omega = true) else 0)]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  have hf : (sites ×ˢ sites).filter
      (fun xy => xy ∈ labelledNeighborPairs Q Y mask) = labelledNeighborPairs Q Y mask := by
    ext xy
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro h
      have hh := (mem_labelledNeighborPairs Q Y mask xy.1 xy.2).mp h
      exact ⟨Finset.mem_product.mpr ⟨hmask hh.1,hmask hh.2.1⟩,h⟩
  rw [hf]
  rfl

end
end PaperC.V282.BulkProcessCosts
