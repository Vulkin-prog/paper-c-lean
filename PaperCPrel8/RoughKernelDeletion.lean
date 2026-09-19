import PaperCPrel8.RoughKernelRankin

/-! # Finite cost of the stronger rough-kernel good set

The threshold acts on the whole odd rough kernel, not on the largest prime.
The original good set is arbitrary and is only required to lie in the grid.
-/
namespace PaperC.Prel8.RoughKernelDeletion

open scoped BigOperators
open LargeOddKernel TerminalKernelCount V282.DefectiveRankinCount
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Retain original good sites whose every raw vertex has kernel above T. -/
def strongGood (G : Finset ℕ) (Y Q T : ℕ) : Finset ℕ :=
  G.filter (fun j ↦ ∀ a : Fin (Q+1), T < largeOddKernel Y (j+a.val))

theorem mem_strongGood (G : Finset ℕ) (Y Q T j : ℕ) :
    j ∈ strongGood G Y Q T ↔ j ∈ G ∧ ∀ a : Fin (Q+1), T < largeOddKernel Y (j+a.val) := by
  simp [strongGood]

/-- Flooring the real threshold leaves the paper's strict kernel condition unchanged. -/
theorem mem_strongGood_floor (G : Finset ℕ) (Y Q j : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    j ∈ strongGood G Y Q ⌊T⌋₊ ↔
      j ∈ G ∧ ∀ a : Fin (Q+1), T < (largeOddKernel Y (j+a.val) : ℝ) := by
  simp only [mem_strongGood, Nat.floor_lt hT]

theorem strongGood_subset (G : Finset ℕ) (Y Q T : ℕ) : strongGood G Y Q T ⊆ G :=
  Finset.filter_subset _ _

/-- Translation of one offset injects into the actual small-kernel population. -/
theorem displacement_card_le (n Q Y T : ℕ) (a : Fin (Q+1)) :
    ((Finset.Icc 1 n).filter (fun j ↦ largeOddKernel Y (j+a.val) ≤ T)).card ≤
      (boundedLargeKernelValues Y T (n+Q)).card := by
  apply Finset.card_le_card_of_injOn (fun j ↦ j+a.val)
  · intro j hj
    obtain ⟨hj, hk⟩ := Finset.mem_filter.mp hj
    have hj := Finset.mem_Icc.mp hj
    have ha := a.isLt
    change j+a.val ∈ boundedLargeKernelValues Y T (n+Q)
    exact mem_boundedLargeKernelValues.mpr ⟨by omega, by omega, hk⟩
  · intro j _ k _ h
    exact Nat.add_right_cancel h

/-- Each small-kernel integer is charged at most Q+1 times. -/
theorem added_deletion_card_le (G : Finset ℕ) (n Y Q T : ℕ)
    (hG : G ⊆ Finset.Icc 1 n) :
    (G \ strongGood G Y Q T).card ≤
      (Q+1) * (boundedLargeKernelValues Y T (n+Q)).card := by
  let f := fun a : Fin (Q+1) ↦ (Finset.Icc 1 n).filter
    (fun j ↦ largeOddKernel Y (j+a.val) ≤ T)
  have hsub : G \ strongGood G Y Q T ⊆ Finset.univ.biUnion f := by
    intro j hj
    obtain ⟨hj, hnot⟩ := Finset.mem_sdiff.mp hj
    have hex : ∃ a : Fin (Q+1), largeOddKernel Y (j+a.val) ≤ T := by
      by_contra h
      apply hnot
      rw [mem_strongGood]
      refine ⟨hj, ?_⟩
      intro a
      have : ¬largeOddKernel Y (j+a.val) ≤ T := fun ha ↦ h ⟨a, ha⟩
      omega
    obtain ⟨a, ha⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hG hj, ha⟩⟩
  calc
    _ ≤ (Finset.univ.biUnion f).card := Finset.card_le_card hsub
    _ ≤ ∑ a : Fin (Q+1), (f a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a : Fin (Q+1), (boundedLargeKernelValues Y T (n+Q)).card := by
      apply Finset.sum_le_sum
      intro a _
      exact displacement_card_le n Q Y T a
    _ = _ := by simp

/-- Fully explicit finite Rankin cost of the additional deletion. -/
theorem added_deletion_rankin (G : Finset ℕ) (n Y Q T : ℕ)
    (hG : G ⊆ Finset.Icc 1 n) {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 2) :
    ((G \ strongGood G Y Q T).card : ℝ) ≤
      (Q+1 : ℝ) * ((n+Q : ℕ) : ℝ) ^ (1 - σ) * rankinEulerProduct Y σ *
        (1 + (T : ℝ) ^ σ / σ) := by
  have hc : ((G \ strongGood G Y Q T).card : ℝ) ≤
      (Q+1 : ℝ) * ((boundedLargeKernelValues Y T (n+Q)).card : ℝ) := by
    exact_mod_cast added_deletion_card_le G n Y Q T hG
  have hr := mul_le_mul_of_nonneg_left (RoughKernelRankin.count_le Y T (n+Q) hσ0 hσ)
    (show (0 : ℝ) ≤ Q+1 by positivity)
  exact hc.trans (by simpa only [mul_assoc] using hr)

/-- Original and additional losses partition the complete deleted grid. -/
theorem total_deleted_card (G : Finset ℕ) (n Y Q T : ℕ)
    (hG : G ⊆ Finset.Icc 1 n) :
    ((Finset.Icc 1 n) \ strongGood G Y Q T).card =
      ((Finset.Icc 1 n) \ G).card + (G \ strongGood G Y Q T).card := by
  have hs := strongGood_subset G Y Q T
  have he : (Finset.Icc 1 n) \ strongGood G Y Q T =
      ((Finset.Icc 1 n) \ G) ∪ (G \ strongGood G Y Q T) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hj, hn⟩
      by_cases hg : j ∈ G
      · exact Or.inr ⟨hg, hn⟩
      · exact Or.inl ⟨hj, hg⟩
    · rintro (⟨hj, hn⟩ | ⟨hj, hn⟩)
      · exact ⟨hj, fun h ↦ hn (hs h)⟩
      · exact ⟨hG hj, hn⟩
  rw [he, Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (fun j hj hk ↦
    (Finset.mem_sdiff.mp hj).2 (Finset.mem_sdiff.mp hk).1)

end
end PaperC.Prel8.RoughKernelDeletion
