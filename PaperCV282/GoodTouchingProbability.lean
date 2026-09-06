import PaperCV282.MaskedArithmeticGeometry
import PaperCV282.TouchingPairGeometry
import PaperC.Probability.BadStartMass

/-!
# Exact touching probabilities on the retained mask

Two good whole supports at distance L cover every non-root vertex of the
double tree. Since Y>=2L, its private-prime defect set is empty. The actual
unconditional joint probability is therefore exactly 2^(-2L); this is the
quantity obtained when conditional joint probabilities are averaged.
-/

namespace PaperC.V282.GoodTouchingProbability

open Affine Affine.TouchingDefectRank DefectivePredicate BadStartMass
open MaskedArithmeticGeometry LargePrimeDependencyGraph SectionTwelveMoments

noncomputable section

theorem touchingDefectIndices_eq_empty {x L Y : ℕ} (hY : 2 * L ≤ Y)
    (hx : ∀ i : Fin L, ¬HDefective Y (x + i.val))
    (hy : ∀ i : Fin L, ¬HDefective Y (x + L + i.val)) :
    touchingDefectIndices x L = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hd : HDefective (2 * L) (touchingVertexLabel x L i) := by
    simpa [touchingDefectIndices] using hi
  have hbig := hDefective_mono hY hd
  cases i with
  | inl i => exact hx i hbig
  | inr i => exact hy i hbig

theorem touchingRho_eq_zero_of_good {N x L Y : ℕ} (hN : 2 ≤ N)
    (hxN : x ∈ dyadicBlock N) (hL : 0 < L) (hY : 2 * L ≤ Y)
    (hx : ∀ i : Fin L, ¬HDefective Y (x + i.val))
    (hy : ∀ i : Fin L, ¬HDefective Y (x + L + i.val)) :
    relationRho (touchingSystem (dyadicCutoff N (2 * L)) x L) = 0 := by
  classical
  have hd := touchingDefectIndices_eq_empty hY hx hy
  have hf := LinearMap.finrank_le_finrank_of_injective (touchingDefectRestriction_injective hN hxN hL)
  have hzero : relationRho (touchingSystem (dyadicCutoff N (2 * L)) x L) ≤ 0 := by
    simpa only [relationRho, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hd, Finset.card_empty] using hf
  omega

/-- The touching rank vanishes in any adequate cylinder. -/
theorem twoStartRho_eq_zero_of_touching_good {K x y L Y : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hL : 0 < L) (hY : 2 * L ≤ Y)
    (hd : Nat.dist x y = L) (hK : x + L ≤ K ∧ y + L ≤ K)
    (hxgood : ∀ i : Fin L, ¬HDefective Y (x + i.val))
    (hygood : ∀ i : Fin L, ¬HDefective Y (y + i.val)) :
    relationRho (twoStartSystem K x y L) = 0 := by
  have hf {a b : ℕ} (ha : 2 ≤ a) (hab : b = a + L)
      (hcut : a + L ≤ K ∧ b + L ≤ K)
      (hag : ∀ i : Fin L, ¬HDefective Y (a + i.val))
      (hbg : ∀ i : Fin L, ¬HDefective Y (b + i.val)) :
      relationRho (twoStartSystem K a b L) = 0 := by
    subst b
    have hamem : a ∈ dyadicBlock a := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hz := touchingRho_eq_zero_of_good ha hamem hL hY hag hbg
    rw [touchingSystem_eq_twoStartSystem] at hz
    rw [TouchingPairGeometry.relationRho_cutoff_eq ha (by omega) hcut
      (show a + L ≤ dyadicCutoff a (2 * L) ∧ a + L + L ≤ dyadicCutoff a (2 * L) by
        unfold dyadicCutoff; constructor <;> omega)]
    exact hz
  rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq hd with h | h
  · exact hf hx h hK hxgood hygood
  · rw [TouchingPairGeometry.relationRho_comm]
    exact hf hy h ⟨hK.2,hK.1⟩ hygood hxgood

/-- The actual touching joint probability on the whole-support good mask. -/
theorem jointStartProbability_eq_baseline_of_full_good_touching
    {N L Y x y : ℕ} {mask : Finset ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hY : 2 * L ≤ Y) (hmask : mask ⊆ dyadicBlock N)
    (hx : x ∈ fullGoodMask N L Y mask) (hy : y ∈ fullGoodMask N L Y mask)
    (hd : Nat.dist x y = L) :
    jointStartProbability N L x y = (1 : ℚ) / (2 : ℚ) ^ (2 * L) := by
  have hxb := hmask (mem_fullGoodMask.mp hx).1
  have hyb := hmask (mem_fullGoodMask.mp hy).1
  have hr := twoStartRho_eq_zero_of_touching_good
    (two_le_of_mem_dyadicBlock hN hxb) (two_le_of_mem_dyadicBlock hN hyb) hL hY hd
    (show x + L ≤ dyadicCutoff N L ∧ y + L ≤ dyadicCutoff N L by
      have hxx := Finset.mem_Ico.mp hxb
      have hyy := Finset.mem_Ico.mp hyb
      unfold dyadicCutoff; constructor <;> omega)
    (fun i => not_defective_of_mem_fullGoodMask hmask hx
      (mem_startTreeSupport.mpr (Or.inr ⟨i.val,i.isLt,rfl⟩)))
    (fun i => not_defective_of_mem_fullGoodMask hmask hy
      (mem_startTreeSupport.mpr (Or.inr ⟨i.val,i.isLt,rfl⟩)))
  have ha := abs_jointStartProbability_sub_baseline_le N L x y hL
  have hz : jointDefectWeight N L (x,y) = 0 := by simp [jointDefectWeight,jointRho,hr]
  rw [hz] at ha
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using ha))

end
end PaperC.V282.GoodTouchingProbability
