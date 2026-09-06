import PaperCV282.LabelledProcessCosts
import PaperCV282.DirectionalSteinComparison

/-! # Exact label-weighted costs on the genuine maximal-support graph -/
namespace PaperC.V282.WeightedLabelledCosts

open LabelledSupportGraph LabelledProcessCosts DictionaryFieldFirstCost AllStartFieldCosts
open DirectionalSteinComparison ConditionalStartProbability ArratiaGoldsteinGordonInput
open LargePrimeDependencyGraph MaskedArithmeticGeometry MaskedPairGeometry SectionThirteenFiniteBound
open scoped BigOperators

noncomputable section

local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def weightedLabelPairMass {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S]
    (μ : FinitePMF S) (X : ℕ → κ → S → Bool) (weight : κ → κ → ℝ)
    (pairs : Finset (ℕ × ℕ)) : ℝ :=
  ∑ xy ∈ pairs, ∑ a, ∑ b, weight a b *
    eventProbability μ (fun omega => X xy.1 a omega = true ∧ X xy.2 b omega = true)

theorem typedBOne_labelled_eq {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S]
    (μ : FinitePMF S) (X : ℕ → κ → S → Bool) (N Q Y : ℕ)
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (rate : κ → ℝ) (weight : κ → κ → ℝ)
    (hm : ∀ i : LabelledIndex N κ,
      marginal μ (maskedLabelledFamily N X mask) i = if i.1.val ∈ mask then rate i.2 else 0) :
    typedBOne μ (maskedLabelledFamily N X mask) Prod.snd (labelledGraph N Q Y κ) weight =
      (∑ a, ∑ b, weight a b*rate a*rate b) * (closedDictionarySitePairs Q Y mask).card := by
  let f : ℕ → ℕ → κ → κ → ℝ := fun x y a b =>
    if x ∈ mask ∧ y ∈ mask ∧ (Nat.dist x y ≤ Q ∨ LargePrimeAdjacent Q Y x y)
      then weight a b * rate a * rate b else 0
  have hc (i : LabelledIndex N κ) : closedNeighborhood (labelledGraph N Q Y κ) i =
      Finset.univ.filter (fun j => Nat.dist i.1.val j.1.val ≤ Q ∨ LargePrimeAdjacent Q Y i.1.val j.1.val) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_closedNeighborhood_labelledGraph]
  have hb : typedBOne μ (maskedLabelledFamily N X mask) Prod.snd (labelledGraph N Q Y κ) weight =
      ∑ i : LabelledIndex N κ, ∑ j : LabelledIndex N κ, f i.1.val j.1.val i.2 j.2 := by
    unfold typedBOne
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
        then (∑ a, ∑ b, weight a b*rate a*rate b) else 0 := by
    dsimp only [f]
    split_ifs <;> simp
  simp_rw [hs]
  rw [Finset.sum_product,sum_pair_subset_of_zero hmask _
    (by intro x hx hnot y; simp [hnot]) (by intro y hy hnot x; simp [hnot])]
  rw [← Finset.sum_product']
  have hf : (∑ xy ∈ mask ×ˢ mask,
      if xy.1 ∈ mask ∧ xy.2 ∈ mask ∧ (Nat.dist xy.1 xy.2 ≤ Q ∨ LargePrimeAdjacent Q Y xy.1 xy.2)
        then (∑ a, ∑ b, weight a b*rate a*rate b) else 0) =
      ∑ xy ∈ closedDictionarySitePairs Q Y mask, (∑ a, ∑ b, weight a b*rate a*rate b) := by
    rw [closedDictionarySitePairs,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro xy hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    simp [hx,hy]
  rw [hf]
  simp [mul_comm]

theorem typedBTwo_labelled_eq {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S]
    (μ : FinitePMF S) (X : ℕ → κ → S → Bool) (N Q Y : ℕ)
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (weight : κ → κ → ℝ)
    (hdisj : ∀ x ∈ dyadicBlock N, ∀ a b : κ, a ≠ b → ∀ omega,
      ¬(X x a omega = true ∧ X x b omega = true)) :
    typedBTwo μ (maskedLabelledFamily N X mask) Prod.snd (labelledGraph N Q Y κ) weight =
      weightedLabelPairMass μ X weight (labelledNeighborPairs Q Y mask) := by
  have ht (i j : LabelledIndex N κ) :
      (if j ∈ (closedNeighborhood (labelledGraph N Q Y κ) i).erase i then
        weight i.2 j.2 * jointMarginal μ (maskedLabelledFamily N X mask) i j else 0) =
      if (i.1.val,j.1.val) ∈ labelledNeighborPairs Q Y mask then
        weight i.2 j.2 * eventProbability μ (fun omega => X i.1.val i.2 omega = true ∧ X j.1.val j.2 omega = true)
      else 0 := by
    by_cases hx : i.1.val ∈ mask
    · by_cases hy : j.1.val ∈ mask
      · have hjoint : jointMarginal μ (maskedLabelledFamily N X mask) i j =
          jointMarginal μ (labelledFamily N X) i j := by
          simp only [jointMarginal,maskedLabelledFamily,maskedLabelIndicator,if_pos hx,if_pos hy]
        rw [hjoint]
        by_cases hsite : i.1.val = j.1.val
        · by_cases heq : i = j
          · subst j
            simp [mem_labelledNeighborPairs]
          · rw [joint_labelled_same_site_zero μ X N hdisj i j hsite heq]
            simp [mem_labelledNeighborPairs,hsite]
        · have hne : j ≠ i := fun h => hsite (congrArg (fun z : LabelledIndex N κ => z.1.val) h.symm)
          simp [Finset.mem_erase,labelledGraph,
            mem_labelledNeighborPairs,hx,hy,hsite,hne,Ne.symm hne,jointMarginal,labelledFamily]
      · simp [jointMarginal,maskedLabelledFamily,maskedLabelIndicator,hy,
          mem_labelledNeighborPairs,eventProbability]
    · simp [jointMarginal,maskedLabelledFamily,maskedLabelIndicator,hx,
        mem_labelledNeighborPairs,eventProbability]
  unfold typedBTwo
  have hs (i : LabelledIndex N κ) :
      (∑ j ∈ (closedNeighborhood (labelledGraph N Q Y κ) i).erase i,
        weight i.2 j.2 * jointMarginal μ (maskedLabelledFamily N X mask) i j) =
      ∑ j : LabelledIndex N κ, if (i.1.val,j.1.val) ∈ labelledNeighborPairs Q Y mask then
        weight i.2 j.2 * eventProbability μ (fun omega => X i.1.val i.2 omega = true ∧ X j.1.val j.2 omega = true) else 0 := by
    have hf : Finset.univ.filter (fun j => j ∈ (closedNeighborhood (labelledGraph N Q Y κ) i).erase i) =
        (closedNeighborhood (labelledGraph N Q Y κ) i).erase i := by ext j; simp
    rw [← hf,Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => ht i j
  simp_rw [hs]
  rw [sum_labelledIndex_pair N (fun x y a b => if (x,y) ∈ labelledNeighborPairs Q Y mask then
    weight a b * eventProbability μ (fun omega => X x a omega = true ∧ X y b omega = true) else 0)]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  have hf : (dyadicBlock N ×ˢ dyadicBlock N).filter
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
end PaperC.V282.WeightedLabelledCosts
