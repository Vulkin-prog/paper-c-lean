import PaperCV282.MediumMultipleCounts

/-! # Uniform square losses for every fixed reciprocal cutoff

For B/K<p<=B the global square-incidence loss is at most 2*K^3.
No prime-by-prime loss is subtracted from the main incidence mass.
-/
namespace PaperC.V282.FixedMediumSquares

open Finset MediumMultipleCounts
open scoped BigOperators

noncomputable section

theorem card_le_of_separated {S : Finset ℕ} {a B K : ℕ} (hK : 0 < K) (hB : 0 < B)
    (hwindow : ∀ n ∈ S, a ≤ n ∧ n < a+B)
    (hsep : ∀ m ∈ S, ∀ n ∈ S, m<n → B<K*(n-m)) : S.card ≤ K := by
  have hmem : ∀ n ∈ S, K*(n-a)/B ∈ range K := by
    intro n hn
    have hw := hwindow n hn
    have hdiff : n-a<B := by omega
    rw [mem_range,Nat.div_lt_iff_lt_mul hB]
    exact Nat.mul_lt_mul_of_pos_left hdiff hK
  have hgap (m n : ℕ) (hm : m∈S) (hn : n∈S) (hlt : m<n)
      (heq : K*(m-a)/B=K*(n-a)/B) : False := by
    have hw := hwindow m hm
    have hw' := hwindow n hn
    have hd : n-a=(m-a)+(n-m) := by omega
    have hdm := Nat.mod_add_div (K*(m-a)) B
    have hdn := Nat.mod_add_div (K*(n-a)) B
    have hrm := Nat.mod_lt (K*(m-a)) hB
    have hrn := Nat.mod_lt (K*(n-a)) hB
    have hs := hsep m hm n hn hlt
    rw [← heq] at hdn
    have hprod : K*(n-a)=K*(m-a)+K*(n-m) := by rw [hd,Nat.mul_add]
    omega
  have hinj : Set.InjOn (fun n => K*(n-a)/B) (S : Set ℕ) := by
    intro m hm n hn heq
    rcases lt_trichotomy m n with h | h | h
    · exact (hgap m n hm hn h heq).elim
    · exact h
    · exact (hgap n m hn hm h heq.symm).elim
  simpa only [card_range] using card_le_card_of_injOn (fun n => K*(n-a)/B) hmem hinj

theorem square_multiple_separation {a B K p q : ℕ} (ha : 1≤a)
    (hp : B<K*p) (hpq : p<q) : B<K*(a*q^2-a*p^2) := by
  have hsq : (p+1)^2≤q^2 := Nat.pow_le_pow_left (by omega) 2
  have hle := Nat.pow_le_pow_left hpq.le 2
  have hsub := Nat.sub_add_cancel hle
  have hbase : p≤q^2-p^2 := by nlinarith
  have hmul : q^2-p^2≤a*(q^2-p^2) := Nat.le_mul_of_pos_left _ ha
  rw [Nat.mul_sub_left_distrib] at hmul
  exact hp.trans_le (Nat.mul_le_mul_left K (hbase.trans hmul))

theorem coefficient_card_le {S : Finset ℕ} {a lo B K : ℕ}
    (ha : 1≤a) (hB : 0<B) (hK : 0<K)
    (hmedium : ∀ p∈S, B<K*p)
    (hwindow : ∀ p∈S, lo≤a*p^2 ∧ a*p^2<lo+B) : S.card≤K := by
  have hinj : Set.InjOn (fun p => a*p^2) (S : Set ℕ) := by
    intro p hp q hq heq
    have hs : p^2=q^2 := Nat.eq_of_mul_eq_mul_left (by omega) heq
    nlinarith
  rw [← card_image_iff.mpr hinj]
  apply card_le_of_separated hK hB
  · intro n hn
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hn
    exact hwindow p hp
  · intro m hm n hn hmn
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hm
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hn
    have hpq : p<q := by
      by_contra h
      have hs := Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.le_of_not_gt h) 2)
      omega
    exact square_multiple_separation ha (hmedium p hp) hpq

theorem square_coefficient_le {B K n p a : ℕ} (hB : 0<B)
    (hp : B<K*p) (hn : n≤B^2+B) (heq : n=a*p^2) : a≤2*K^2 := by
  have hs : B^2<(K*p)^2 := Nat.pow_lt_pow_left hp (by omega)
  have hs' : B^2<K^2*p^2 := by nlinarith [hs]
  have hb : B^2+B≤2*B^2 := by nlinarith
  have hcap : n≤(2*K^2)*p^2 := by nlinarith
  have hpp : 0<p^2 := by
    have hppos : 0<p := by nlinarith
    positivity
  rw [heq] at hcap
  exact Nat.le_of_mul_le_mul_right hcap hpp

def squareIncidences (K lo B : ℕ) : Finset (ℕ×ℕ) :=
  ((Ico lo (lo+B)).product (Icc 1 B)).filter
    (fun z => 0<z.1 ∧ B<K*z.2 ∧ z.2^2∣z.1)

theorem squareIncidences_card_le {K lo B : ℕ} (hK : 0<K) (hB : 0<B)
    (htop : lo+B≤B^2+B+1) : (squareIncidences K lo B).card≤(2*K^2)*K := by
  let S := squareIncidences K lo B
  let coefficient (z : ℕ×ℕ) := z.1/z.2^2
  have heq (z) (hz : z∈S) : z.1=coefficient z*z.2^2 :=
    (Nat.div_mul_cancel (mem_filter.mp hz).2.2.2).symm
  have hcoeff (z) (hz : z∈S) : coefficient z ∈ Icc 1 (2*K^2) := by
    obtain ⟨hz',hpos,hm,hsq⟩ := mem_filter.mp hz
    have hw := mem_Ico.mp (mem_product.mp hz').1
    rw [mem_Icc]
    constructor
    · have hc := heq z hz
      by_contra h
      have hc0 : coefficient z=0 := by omega
      rw [hc0,zero_mul] at hc
      omega
    · exact square_coefficient_le hB hm (by omega) (heq z hz)
  have hfiber (a) (ha : a∈Icc 1 (2*K^2)) : (S.filter fun z => coefficient z=a).card≤K := by
    have hinj : Set.InjOn Prod.snd ((S.filter fun z => coefficient z=a) : Set (ℕ×ℕ)) := by
      intro z hz w hw hp
      obtain ⟨hzS,hza⟩ := mem_filter.mp hz
      obtain ⟨hwS,hwa⟩ := mem_filter.mp hw
      apply Prod.ext
      · rw [heq z hzS,heq w hwS,hza,hwa,hp]
      · exact hp
    rw [← card_image_iff.mpr hinj]
    apply coefficient_card_le (mem_Icc.mp ha).1 hB hK
    · intro p hp
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hp
      exact (mem_filter.mp (mem_filter.mp hz).1).2.2.1
    · intro p hp
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hp
      obtain ⟨hzS,hza⟩ := mem_filter.mp hz
      have hw := mem_Ico.mp (mem_product.mp (mem_filter.mp hzS).1).1
      have hc := heq z hzS
      rw [hza] at hc
      rw [← hc]
      exact hw
  calc
    _ = ∑ a∈Icc 1 (2*K^2), (S.filter fun z => coefficient z=a).card := card_eq_sum_card_fiberwise hcoeff
    _ ≤ ∑ _a∈Icc 1 (2*K^2), K := sum_le_sum hfiber
    _ = (2*K^2)*K := by simp

theorem floor_sum_le_odd_incidence_add {K lo B : ℕ} {P : Finset ℕ}
    (hK : 0<K) (hB : 0<B) (hlo : 0<lo) (htop : lo+B≤B^2+B+1)
    (hP : ∀ p∈P, p.Prime ∧ p≤B ∧ B<K*p) :
    ∑ p∈P, B/p ≤ (oddIncidences lo B P).card+(2*K^2)*K := by
  have hsub : divisibilityIncidences lo B P ⊆ oddIncidences lo B P ∪ squareIncidences K lo B := by
    intro z hz
    obtain ⟨hwP,hd⟩ := mem_filter.mp hz
    obtain ⟨hw,hp⟩ := mem_product.mp hwP
    by_cases ho : parityVec z.1 z.2≠0
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨hw,hp⟩,ho⟩)
    · have hpdata := hP z.2 hp
      have hn : 0<z.1 := hlo.trans_le (mem_Ico.mp hw).1
      exact mem_union_right _ (mem_filter.mpr ⟨mem_product.mpr ⟨hw,mem_Icc.mpr
        ⟨hpdata.1.pos,hpdata.2.1⟩⟩,hn,hpdata.2.2,
        square_dvd_of_divides_of_parity_zero hn hpdata.1 hd (not_ne_iff.mp ho)⟩)
  exact (floor_sum_le_incidence_card hlo (fun p hp => (hP p hp).1.pos)).trans
    ((card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (squareIncidences_card_le hK hB htop) _)))

end
end PaperC.V282.FixedMediumSquares
