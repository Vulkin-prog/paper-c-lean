import PaperCPrel8.PrimeRunWitness
import PaperC.Asymptotics.PrefixBoundaryProbability

/-! # Retention and the exact probability of the G.9 prime witness -/
namespace PaperC.Prel8.PrimeWitnessRetention
open Finset PrimeRunWitness ConditionalStartProbability ArratiaGoldsteinGordonInput
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def certifiedSites (q M : ℕ) : Finset ℕ :=
  (certifiedIndices q (M/q-1)).image (fun t ↦ t*q)

theorem certified_sites_count {q M : ℕ} (hq : 2≤q) :
    (certifiedSites q M).card=(M/q-1)-(M/q-1)/q-((M/q-1)+1)/q := by
  rw [certifiedSites,card_image_of_injective _ (fun a b h ↦ (Nat.mul_left_inj (by omega : q≠0)).mp h),certified_count hq]

theorem certified_interval {q M t : ℕ} (hq : 2≤q) (ht : t∈certifiedIndices q (M/q-1)) :
    0<t ∧ (t+1)*q≤M := by
  have ht' := mem_Icc.mp (mem_filter.mp ht).1
  refine ⟨ht'.1,?_⟩
  have hh : t+1≤M/q := by omega
  exact (Nat.mul_le_mul_right q hh).trans (Nat.div_mul_le_self M q)

theorem certified_sites_subset {q M : ℕ} (hq : 2≤q) : certifiedSites q M⊆Icc 1 M := by
  intro j hj
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hj
  obtain ⟨htp,he⟩ := certified_interval hq ht
  exact mem_Icc.mpr ⟨Nat.mul_pos htp (by omega),by nlinarith⟩

/-- Arbitrary omissions remove at most their own number of certified sites. -/
theorem retained_count {q M : ℕ} (hq : 2≤q) (G : Finset ℕ) :
    (certifiedSites q M).card-((Icc 1 M)\G).card≤(certifiedSites q M∩G).card := by
  have hs : certifiedSites q M\G⊆(Icc 1 M)\G := by
    intro j hj
    exact mem_sdiff.mpr ⟨certified_sites_subset hq (mem_sdiff.mp hj).1,(mem_sdiff.mp hj).2⟩
  have hc := card_le_card hs
  have he := card_sdiff_add_card_inter (certifiedSites q M) G
  omega

/-- Every retained certified boundary carries the low type (zero excess, positive sign). -/
theorem retained_mark {C q M : ℕ} (hq : q.Prime) (p : PrimeUpTo C) (hp : p.val.val=q)
    (G : Finset ℕ) (j : ℕ) (hj : j∈certifiedSites q M∩G) :
    V282.ExactMarkedModel.SignedExactMark (valueBit (Pi.single p 1 : SampleSpace C)) (j+1) (q-1) 0 0 := by
  obtain ⟨t,ht,rfl⟩ := mem_image.mp (mem_inter.mp hj).1
  have hh := mem_filter.mp ht
  exact certified_mark hq (mem_Icc.mp hh.1).1 hh.2.1 hh.2.2 p hp

/-- This is the original uniform cylinder event, of mass 2^(-pi(C)). -/
theorem witness_probability (C : ℕ) (p : PrimeUpTo C) :
    eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ w=Pi.single p 1)=
      1/(2:ℝ)^Nat.primeCounting C := by
  unfold eventProbability
  rw [sum_eq_single (Pi.single p 1)]
  · simp only [ite_true,FinitePMF.uniform_prob,SampleSpace,Fintype.card_fun,ZMod.card,Nat.cast_pow,Nat.cast_ofNat,
      PrefixBoundaryProbability.card_primeUpTo_eq_primeCounting,one_div]
  · intro w hw hn
    simp [hn]
  · simp

end
end PaperC.Prel8.PrimeWitnessRetention
