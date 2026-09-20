import PaperCPrel8.CumulantActivityLayers
import PaperCPrel8.AbsolutePairLedger
import PaperCPrel8.ArithmeticLowCategory

/-! # Identification of the categorical two-site layer with ordered actual covariances -/
namespace PaperC.Prel8.CategoricalPairBridge
open Finset CategoricalTransversals CumulantActivityLayers FiniteCumulantEnvelope
open CategoricalMomentExpansion ActualSignedPalm ActualSignedCovariance ArithmeticLowCategory
open ArratiaGoldsteinGordonInput IndependentThinning ConditionalStartProbability
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {ι α Ω : Type*} [Fintype ι] [Fintype α] [Fintype Ω] [DecidableEq ι] [DecidableEq α]

theorem pair_transversal {a b : ι×α} (h : a.1≠b.1) : Transversal {a,b} := by
  intro i x y hx hy
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with ha|hb <;> rcases hy with hc|hd
  · exact (Prod.mk.inj (ha.trans hc.symm)).2
  · exact False.elim (h (by rw [← ha,← hd]))
  · exact False.elim (h (by rw [← hc,← hb]))
  · exact (Prod.mk.inj (hb.trans hd.symm)).2

theorem transversal_pair_sites {a b : ι×α} (h : Transversal {a,b}) (hab : a≠b) : a.1≠b.1 := by
  intro he
  apply hab
  apply Prod.ext he
  have hh := h a.1 a.2 b.2 (by simp) (by simpa [he] using (mem_insert_of_mem a (mem_singleton_self b)))
  exact hh

/-- Each two-element transversal has the two ordered orientations, counted exactly once. -/
theorem transversal_pair_sum (F : Finset (ι×α) → ℝ) :
    (∑ S∈transversals.filter (fun S : Finset (ι×α) ↦ S.card=2), 2*F S)=
      ∑ a : ι×α, ∑ b : ι×α, if a.1=b.1 then 0 else F {a,b} := by
  let P := (univ : Finset ((ι×α)×(ι×α))).filter (fun z ↦ z.1.1≠z.2.1)
  let T := transversals.filter (fun S : Finset (ι×α) ↦ S.card=2)
  have hmaps : ∀ z∈P, ({z.1,z.2}:Finset (ι×α))∈T := by
    intro z hz
    have hne : z.1.1≠z.2.1 := (mem_filter.mp hz).2
    have hab : z.1≠z.2 := fun he ↦ hne (congrArg Prod.fst he)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),pair_transversal hne⟩,
      by simp [hab]⟩
  have hfiber (S : Finset (ι×α)) (hS : S∈T) :
      (∑ z∈P.filter (fun z ↦ ({z.1,z.2}:Finset (ι×α))=S), F {z.1,z.2})=2*F S := by
    have hs := (mem_filter.mp hS).2
    have ht := (mem_filter.mp (mem_filter.mp hS).1).2
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hs
    have hsite := transversal_pair_sites ht hab
    have he : P.filter (fun z ↦ ({z.1,z.2}:Finset (ι×α))={a,b})={(a,b),(b,a)} := by
      ext z
      simp only [P,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
      constructor
      · intro hz
        have ha : z.1=a ∨ z.1=b := by
          have hm : z.1∈({a,b}:Finset (ι×α)) := by rw [← hz.2]; simp
          simpa only [mem_insert,mem_singleton] using hm
        have hb : z.2=a ∨ z.2=b := by
          have hm : z.2∈({a,b}:Finset (ι×α)) := by rw [← hz.2]; simp
          simpa only [mem_insert,mem_singleton] using hm
        rcases ha with ha|ha <;> rcases hb with hb|hb
        · exact False.elim (hz.1 (by rw [ha,hb]))
        · exact Or.inl (Prod.ext ha hb)
        · exact Or.inr (Prod.ext ha hb)
        · exact False.elim (hz.1 (by rw [ha,hb]))
      · rintro (rfl|rfl)
        · exact ⟨hsite,rfl⟩
        · exact ⟨Ne.symm hsite,Finset.pair_comm _ _⟩
    rw [he]
    simp only [sum_insert (show (a,b)∉({(b,a)}:Finset _) by simp [hab]),sum_singleton]
    rw [Finset.pair_comm b a]
    ring
  have hh := sum_fiberwise_of_maps_to hmaps (fun z ↦ F {z.1,z.2})
  rw [show (∑ S∈T, ∑ z∈P.filter (fun z ↦ ({z.1,z.2}:Finset (ι×α))=S), F {z.1,z.2})=
      ∑ S∈T, 2*F S from sum_congr rfl hfiber] at hh
  rw [hh]
  simp only [P,sum_filter]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  by_cases he : a.1=b.1 <;> simp [he]

/-- The activity convention agrees exactly with the ordered covariance sum. -/
theorem arithmetic_pair_activity {C L E : ℕ} (hL : 1≤L) (G : Finset ℕ)
    (mu : FinitePMF (SampleSpace C)) :
    pairActivity mu (retainedCategory C L E G)=AbsolutePairLedger.activity mu L E G := by
  unfold pairActivity
  have hw : (∑ S∈transversals.filter (fun S : Finset (G×(Fin (E+1)×F₂)) ↦ S.card=2),
      (2:ℝ)^(S.card-1)*|jointCumulant mu (indicator (retainedCategory C L E G)) S|)=
      ∑ S∈transversals.filter (fun S : Finset (G×(Fin (E+1)×F₂)) ↦ S.card=2),
        2*|jointCumulant mu (indicator (retainedCategory C L E G)) S| := by
    apply sum_congr rfl
    intro S hS
    rw [(mem_filter.mp hS).2]
    norm_num
  rw [hw,transversal_pair_sum]
  have hcov (a b : G×(Fin (E+1)×F₂)) (hne : a.1≠b.1) :
      jointCumulant mu (indicator (retainedCategory C L E G)) {a,b}=covariance (L:=L) mu a b := by
    have hab : a≠b := fun he ↦ hne (congrArg Prod.fst he)
    rw [pair_cumulant (by simp [hab]),centered_pair_moment mu _ hab]
    have hi : indicator (retainedCategory C L E G)=fun a w ↦ (field C L E G w a:ℝ) :=
      funext (fun a ↦ funext (fun w ↦ indicator_eq hL G a w))
    rw [hi]
    rfl
  simp only [Fintype.sum_prod_type (α₁:=G) (α₂:=Fin (E+1)×F₂),AbsolutePairLedger.activity]
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  by_cases he : j=k
  · simp [he]
  · simp only [he,ite_false]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    rw [hcov (j,a) (k,b) he]

end
end PaperC.Prel8.CategoricalPairBridge
