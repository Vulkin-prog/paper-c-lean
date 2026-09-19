import PaperCV282.SignedExactMarks
import PaperCV282.PrescribedValues

/-! # The arithmetic one-negative-prime run witness used in G.9 -/
namespace PaperC.Prel8.PrimeRunWitness
open Finset ConditionalStartProbability V282.PrescribedValues V282.SignedExactMarks
open V282.ExactMarkedModel V282.WindowValues
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem endpoint_parity {q t : ℕ} (hq : q.Prime) (ht : 0<t) (hqt : ¬q∣t) :
    parityVec (t*q) q=1 := by
  simp [parityVec_apply,Nat.factorization_mul (by omega : t≠0) hq.ne_zero,
    Nat.factorization_eq_zero_of_not_dvd hqt,hq.factorization]

theorem interior_parity {q t a : ℕ} (ha : 0<a) (haq : a<q) :
    parityVec (t*q+a) q=0 := by
  have hn : ¬q∣t*q+a := by
    intro hd
    have ha' : q∣a := by simpa using Nat.dvd_sub hd (dvd_mul_left q t)
    exact (Nat.le_of_dvd ha ha').not_gt haq
  simp [parityVec_apply,Nat.factorization_eq_zero_of_not_dvd hn]

/-- The two endpoints are negative and all q-1 interior values are positive. -/
theorem certified_word {C q t : ℕ} (hq : q.Prime) (ht : 0<t)
    (hqt : ¬q∣t) (hqt' : ¬q∣t+1) (p : PrimeUpTo C) (hp : p.val.val=q) :
    ∀ a : Fin ((q-1)+0+2),
      valueBit (Pi.single p 1 : SampleSpace C) (t*q+a.val)=signedExactWord (q-1) 0 0 a := by
  intro a
  rw [valueBit_prime_basis,hp]
  have hq2 := hq.two_le
  by_cases ha0 : a.val=0
  · simpa [signedExactWord,ha0] using endpoint_parity hq ht hqt
  · by_cases haq : a.val=q
    · have hv : t*q+a.val=(t+1)*q := by rw [haq]; ring
      rw [hv,endpoint_parity hq (by omega) hqt']
      simp [signedExactWord,haq,show q-1+0+2=q+1 by omega]
    · have ha' := a.isLt
      have ha : 0<a.val := by omega
      have hal : a.val<q := by omega
      rw [interior_parity ha hal]
      simp only [signedExactWord]
      rw [if_neg (by omega)]

/-- The witness is an actual signed exact mark of excess zero, not only a base start. -/
theorem certified_mark {C q t : ℕ} (hq : q.Prime) (ht : 0<t)
    (hqt : ¬q∣t) (hqt' : ¬q∣t+1) (p : PrimeUpTo C) (hp : p.val.val=q) :
    SignedExactMark (valueBit (Pi.single p 1 : SampleSpace C)) (t*q+1) (q-1) 0 0 := by
  apply (signedExactMark_iff_occurs (by omega) (by have := hq.two_le; omega) 0).mpr
  intro a
  simpa only [vertex,Nat.add_sub_cancel] using certified_word hq ht hqt hqt' p hp a

def certifiedIndices (q T : ℕ) : Finset ℕ :=
  (Icc 1 T).filter (fun t ↦ ¬q∣t ∧ ¬q∣t+1)

theorem consecutive_divisibility_disjoint {q t : ℕ} (hq : 2≤q) : ¬(q∣t ∧ q∣t+1) := by
  rintro ⟨ht,ht'⟩
  have hq1 : q∣1 := by simpa using Nat.dvd_sub ht' ht
  have := Nat.le_of_dvd (by norm_num : 0<1) hq1
  omega

theorem multiples_count (q T : ℕ) : ((Icc 1 T).filter (fun t ↦ q∣t)).card=T/q := by
  have he : Icc 1 T=Ioc 0 T := by ext t; simp; omega
  rw [he,Nat.Ioc_filter_dvd_card_eq_div]

theorem shifted_multiples_count {q T : ℕ} (hq : 2≤q) :
    ((Icc 1 T).filter (fun t ↦ q∣t+1)).card=(T+1)/q := by
  have he : ((Icc 1 T).filter (fun t ↦ q∣t+1)).image (fun t ↦ t+1)=
      (Icc 1 (T+1)).filter (fun t ↦ q∣t) := by
    ext t
    constructor
    · rintro h
      obtain ⟨s,hs,rfl⟩ := mem_image.mp h
      obtain ⟨hs,hd⟩ := mem_filter.mp hs
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by have := mem_Icc.mp hs; omega⟩,hd⟩
    · intro h
      obtain ⟨ht,hd⟩ := mem_filter.mp h
      have ht' := mem_Icc.mp ht
      have hqt := Nat.le_of_dvd ht'.1 hd
      refine mem_image.mpr ⟨t-1,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩,by omega⟩
      simpa only [Nat.sub_add_cancel ht'.1] using hd
  rw [← multiples_count q (T+1),← he,card_image_of_injective _ (fun a b h ↦ Nat.add_right_cancel h)]

/-- The exact count in G.9, including the two endpoint exclusions. -/
theorem certified_count {q T : ℕ} (hq : 2≤q) :
    (certifiedIndices q T).card=T-T/q-(T+1)/q := by
  let A := (Icc 1 T).filter (fun t ↦ q∣t)
  let B := (Icc 1 T).filter (fun t ↦ q∣t+1)
  have hd : Disjoint A B := by
    apply disjoint_left.mpr
    intro t ha hb
    exact consecutive_divisibility_disjoint hq ⟨(mem_filter.mp ha).2,(mem_filter.mp hb).2⟩
  have he : certifiedIndices q T=(Icc 1 T)\(A∪B) := by
    ext t
    simp [certifiedIndices,A,B]
    tauto
  rw [he,card_sdiff_of_subset (union_subset (filter_subset _ _) (filter_subset _ _)),card_union_of_disjoint hd,
    Nat.card_Icc]
  change T-(((Icc 1 T).filter (fun t ↦ q∣t)).card+((Icc 1 T).filter (fun t ↦ q∣t+1)).card)=_
  rw [multiples_count,shifted_multiples_count hq]
  omega

end
end PaperC.Prel8.PrimeRunWitness
