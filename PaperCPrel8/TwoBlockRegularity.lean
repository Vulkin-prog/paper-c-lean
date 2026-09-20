import PaperCPrel8.RoughPairHosts
import PaperCPrel8.RoughKernelRegularity

/-! # Failure of private pivots for two good supports forces a one-target rough host -/
namespace PaperC.Prel8.TwoBlockRegularity
open Finset RoughPairHosts RoughKernelRegularity LargeOddKernel
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem failure_pair_hosted {n Q Y : ℕ} (J : Fin 2 → ℕ) (hY : Q<Y)
    (hgrid : ∀ i, J i∈Icc 1 n)
    (hk : ∀ i, ∀ a : Fin (Q+1), 1<largeOddKernel Y (J i+a.val))
    (hbad : ¬Regular Q Y J) :
    (J 0,J 1)∈hostedPairs n Q Y ∨ (J 1,J 0)∈hostedPairs n Q Y := by
  obtain ⟨i,a,ha⟩ := failure_hosted Q Y J hY hbad
  fin_cases i
  · apply Or.inl
    refine mem_filter.mpr ⟨mem_product.mpr ⟨hgrid 0,hgrid 1⟩,a,hk 0 a,?_⟩
    intro p hp
    obtain ⟨l,hl,b,hb⟩ := ha p hp
    have he : l=1 := by fin_cases l <;> simp_all
    subst l
    exact ⟨b,hb⟩
  · apply Or.inr
    refine mem_filter.mpr ⟨mem_product.mpr ⟨hgrid 1,hgrid 0⟩,a,hk 1 a,?_⟩
    intro p hp
    obtain ⟨l,hl,b,hb⟩ := ha p hp
    have he : l=0 := by fin_cases l <;> simp_all
    subst l
    exact ⟨b,hb⟩

def badPairs (G : Finset ℕ) (Q Y : ℕ) : Finset (ℕ×ℕ) :=
  (G×ˢG).filter (fun z ↦ ¬Regular Q Y ![z.1,z.2])

/-- Both possible host orientations cost only a factor two. -/
theorem bad_pairs_count {n Q Y : ℕ} (G : Finset ℕ) (hG : G⊆Icc 1 n) (hY : Q<Y)
    (hk : ∀ j∈G, ∀ a : Fin (Q+1), 1<largeOddKernel Y (j+a.val)) :
    (badPairs G Q Y).card≤2*(hostedPairs n Q Y).card := by
  have hs : badPairs G Q Y⊆hostedPairs n Q Y∪(hostedPairs n Q Y).image Prod.swap := by
    intro z hz
    obtain ⟨hg,hb⟩ := mem_filter.mp hz
    obtain ⟨hx,hy⟩ := mem_product.mp hg
    have hj : ∀ i : Fin 2, (![z.1,z.2] i)∈Icc 1 n := by intro i; fin_cases i <;> simp [hG hx,hG hy]
    have hh : ∀ i : Fin 2, ∀ a : Fin (Q+1), 1<largeOddKernel Y (![z.1,z.2] i+a.val) := by
      intro i a
      fin_cases i
      · exact hk z.1 hx a
      · exact hk z.2 hy a
    rcases failure_pair_hosted ![z.1,z.2] hY hj hh hb with h|h
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_image.mpr ⟨(z.2,z.1),h,by cases z; rfl⟩)
  have hh := (card_le_card hs).trans (card_union_le _ _)
  have hi := card_image_le (s:=hostedPairs n Q Y) (f:=Prod.swap)
  omega

end
end PaperC.Prel8.TwoBlockRegularity
