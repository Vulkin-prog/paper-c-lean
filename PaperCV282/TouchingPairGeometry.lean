import PaperC.Probability.SectionTwelveMoments
import PaperCV282.TerminalSliceGeometry

namespace PaperC.V282.TouchingPairGeometry

open Affine SectionTwelveMoments
open scoped BigOperators

noncomputable section

def touchingPairsOn (s : Finset ℕ) (L : ℕ) : Finset (ℕ × ℕ) :=
  (s ×ˢ s).filter fun p => Nat.dist p.1 p.2 = L

theorem mem_touchingPairsOn {s : Finset ℕ} {L : ℕ} {p : ℕ × ℕ} :
    p ∈ touchingPairsOn s L ↔ p.1 ∈ s ∧ p.2 ∈ s ∧ Nat.dist p.1 p.2 = L := by
  simp [touchingPairsOn, and_assoc]

theorem card_touchingPairsOn_le (s : Finset ℕ) (L : ℕ) :
    (touchingPairsOn s L).card ≤ 2 * s.card := by
  have hs : touchingPairsOn s L ⊆
      s.image (fun x => (x, x + L)) ∪ s.image (fun x => (x + L, x)) := by
    intro p hp
    obtain ⟨hx, hy, hd⟩ := mem_touchingPairsOn.mp hp
    rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq hd with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p.1, hx, Prod.ext rfl h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.2, hy, Prod.ext h.symm rfl⟩)
  exact (Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans
    ((Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans (by omega)))

def swapRelations (K x y L : ℕ) :
    RelationSpace (twoStartSystem K x y L) →ₗ[F₂]
      RelationSpace (twoStartSystem K y x L) where
  toFun u := ⟨fun i => (u : Sum (Fin L) (Fin L) → F₂) (Sum.swap i), by
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro w
    have h := DFunLike.congr_fun (LinearMap.mem_ker.mp u.2) w
    change relationFunctional (twoStartSystem K x y L) u w = 0 at h
    change relationFunctional (twoStartSystem K y x L)
      (fun i => (u : Sum (Fin L) (Fin L) → F₂) (Sum.swap i)) w = 0
    simpa only [relationFunctional_apply, dotProduct, Fintype.sum_sum_type, Sum.swap_inl,
      Sum.swap_inr, twoStartSystem_apply_inl, twoStartSystem_apply_inr, add_comm] using h⟩
  map_add' u v := by rfl
  map_smul' c u := by rfl

theorem relationRho_comm (K x y L : ℕ) :
    relationRho (twoStartSystem K x y L) = relationRho (twoStartSystem K y x L) := by
  let e : RelationSpace (twoStartSystem K x y L) ≃ₗ[F₂]
      RelationSpace (twoStartSystem K y x L) :=
    { swapRelations K x y L with
      invFun := swapRelations K y x L
      left_inv := by intro u; apply Subtype.ext; funext i; cases i <;> rfl
      right_inv := by intro u; apply Subtype.ext; funext i; cases i <;> rfl }
  exact e.finrank_eq

theorem relationRho_cutoff_eq {K K' x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hK : x + L ≤ K ∧ y + L ≤ K) (hK' : x + L ≤ K' ∧ y + L ≤ K') :
    relationRho (twoStartSystem K x y L) = relationRho (twoStartSystem K' x y L) := by
  have hlabel (C : ℕ) (hC : x + L ≤ C ∧ y + L ≤ C)
      (i : Sum (Fin (L + 1)) (Fin (L + 1))) :
      twoStartCompleteVertexLabel x y L i ≤ C := by
    cases i with
    | inl i =>
      simp only [twoStartCompleteVertexLabel, startCompleteVertexLabel]
      split_ifs <;> omega
    | inr i =>
      simp only [twoStartCompleteVertexLabel, startCompleteVertexLabel]
      split_ifs <;> omega
  rcases le_total K K' with h | h
  · exact relationRho_twoStartSystem_cutoff_invariant h hx hy (hlabel K hK)
  · exact (relationRho_twoStartSystem_cutoff_invariant h hx hy (hlabel K' hK')).symm

theorem relationRho_touching_le_defects {K x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hL : 0 < L) (hd : Nat.dist x y = L) (hK : x + L ≤ K ∧ y + L ≤ K) :
    relationRho (twoStartSystem K x y L) ≤
      (IntervalDefectBound.defectsInInterval (2 * L) (min x y)).card := by
  have hforward {a b : ℕ} (ha : 2 ≤ a) (hab : b = a + L)
      (hcut : a + L ≤ K ∧ b + L ≤ K) :
      relationRho (twoStartSystem K a b L) ≤
        (IntervalDefectBound.defectsInInterval (2 * L) a).card := by
    subst b
    have heq := relationRho_cutoff_eq ha (by omega : 2 ≤ a + L) hcut
      (K' := dyadicCutoff a (2 * L)) (by unfold dyadicCutoff; omega)
    rw [heq]
    exact TouchingDefectRank.relationRho_touchingSystem_le_card_defectsInInterval ha
      (by simp only [dyadicBlock, Finset.mem_Ico]; omega) hL
  rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq hd with h | h
  · simpa only [min_eq_left (by omega : x ≤ y)] using hforward hx h hK
  · rw [relationRho_comm]
    simpa only [min_eq_right (by omega : y ≤ x)] using hforward hy h hK.symm

theorem touching_defects_subset_root (x L : ℕ) :
    IntervalDefectBound.defectsInInterval (2 * L) x ⊆
      IntervalDefectBound.defectsInInterval (2 * (L + 1)) (x - 1) := by
  intro n hn
  obtain ⟨hrep, hlo, hhi⟩ := IntervalDefectBound.mem_defectsInInterval.mp hn
  obtain ⟨hncut, S, hS, a, ha, heq⟩ := DefectCounting.mem_defectValues_iff.mp hrep
  apply IntervalDefectBound.mem_defectsInInterval.mpr
  refine ⟨DefectCounting.mem_defectValues_iff.mpr ⟨by omega, S, ?_, a, ?_, heq⟩,
    by omega, by omega⟩
  · intro p hp
    have h := DefectCounting.mem_smallPrimesUpTo.mp (hS hp)
    exact DefectCounting.mem_smallPrimesUpTo.mpr ⟨h.1, by omega⟩
  · exact ha.trans (Nat.sqrt_le_sqrt (by omega))

theorem relationRho_touching_le_root_defects {K x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hL : 0 < L) (hd : Nat.dist x y = L) (hK : x + L ≤ K ∧ y + L ≤ K) :
    relationRho (twoStartSystem K x y L) ≤
      (IntervalDefectBound.defectsInInterval (2 * (L + 1)) (min x y - 1)).card :=
  (relationRho_touching_le_defects hx hy hL hd hK).trans
    (Finset.card_le_card (touching_defects_subset_root (min x y) L))

end

end PaperC.V282.TouchingPairGeometry
