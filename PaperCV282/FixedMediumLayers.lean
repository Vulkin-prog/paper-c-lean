import PaperCV282.FixedMediumSquares
import PaperC.Arithmetic.PrimeCountBridge

/-! # The exact K-1 layer formula for every positive reciprocal cutoff -/
namespace PaperC.V282.FixedMediumLayers

open Finset DefectCounting PrimeCountBridge
open scoped BigOperators

noncomputable section

def mediumPrimes (K B : ℕ) : Finset ℕ := smallPrimesUpTo B \ smallPrimesUpTo (B/K)

theorem mem_mediumPrimes {K B p : ℕ} (hK : 0<K) :
    p∈mediumPrimes K B ↔ p.Prime ∧ p≤B ∧ B<K*p := by
  simp only [mediumPrimes,mem_sdiff,mem_smallPrimesUpTo]
  constructor
  · rintro ⟨⟨hp,hpB⟩,hn⟩
    have hnot : ¬p≤B/K := fun h => hn ⟨hp,h⟩
    have hd : B/K<p := by omega
    exact ⟨hp,hpB,by simpa only [mul_comm] using (Nat.div_lt_iff_lt_mul hK).mp hd⟩
  · rintro ⟨hp,hpB,hB⟩
    have hd : B/K<p := (Nat.div_lt_iff_lt_mul hK).mpr (by simpa only [mul_comm] using hB)
    exact ⟨⟨hp,hpB⟩,by omega⟩

theorem floor_lt_cutoff {K B p : ℕ} (hK : 0<K) (hp : p∈mediumPrimes K B) : B/p<K :=
  (Nat.div_lt_iff_lt_mul (mem_mediumPrimes hK |>.mp hp).1.pos).mpr
    (mem_mediumPrimes hK |>.mp hp).2.2

theorem floor_eq_layers {K B p : ℕ} (hK : 0<K) (hp : p∈mediumPrimes K B) :
    B/p=∑ j∈Icc 1 (K-1), if j≤B/p then 1 else 0 := by
  have hs := floor_lt_cutoff hK hp
  have hf : (Icc 1 (K-1)).filter (fun j => j≤B/p)=Icc 1 (B/p) := by
    ext j
    simp only [mem_filter,mem_Icc]
    omega
  rw [← sum_filter,hf]
  simp

theorem layer_primes_eq {K B j : ℕ} (hK : 0<K) (hj : j∈Icc 1 (K-1)) :
    (mediumPrimes K B).filter (fun p => j≤B/p)=
      smallPrimesUpTo (B/j) \ smallPrimesUpTo (B/K) := by
  have hjpos : 0<j := (mem_Icc.mp hj).1
  ext p
  simp only [mem_filter,mem_mediumPrimes hK,mem_sdiff,mem_smallPrimesUpTo]
  constructor
  · rintro ⟨⟨hp,hpB,hmed⟩,hjp⟩
    have hjp' := (Nat.le_div_iff_mul_le hp.pos).mp hjp
    have hpj := (Nat.le_div_iff_mul_le hjpos).mpr (by simpa only [mul_comm] using hjp')
    have hd : B/K<p := (Nat.div_lt_iff_lt_mul hK).mpr (by simpa only [mul_comm] using hmed)
    exact ⟨⟨hp,hpj⟩,by omega⟩
  · rintro ⟨⟨hp,hpj⟩,hn⟩
    have hpB : p≤B := hpj.trans (Nat.div_le_self B j)
    have hnot : ¬p≤B/K := fun h => hn ⟨hp,h⟩
    have hd : B/K<p := by omega
    have hmed : B<K*p := by simpa only [mul_comm] using (Nat.div_lt_iff_lt_mul hK).mp hd
    have hpj' := (Nat.le_div_iff_mul_le hjpos).mp hpj
    exact ⟨⟨hp,hpB,hmed⟩,(Nat.le_div_iff_mul_le hp.pos).mpr (by simpa only [mul_comm] using hpj')⟩

theorem layer_card {K B j : ℕ} (hK : 0<K) (hj : j∈Icc 1 (K-1)) :
    ((mediumPrimes K B).filter (fun p => j≤B/p)).card=
      PrimesUpTo.count (B/j)-PrimesUpTo.count (B/K) := by
  rw [layer_primes_eq hK hj,card_sdiff_of_subset]
  · rw [← count_eq_card_smallPrimesUpTo,← count_eq_card_smallPrimesUpTo]
  · intro p hp
    have hd : B/K≤B/j := Nat.div_le_div_left (by have := (mem_Icc.mp hj).2; omega) (mem_Icc.mp hj).1
    exact mem_smallPrimesUpTo.mpr ⟨(mem_smallPrimesUpTo.mp hp).1,(mem_smallPrimesUpTo.mp hp).2.trans hd⟩

theorem floor_sum_eq_prime_layers (K B : ℕ) (hK : 0<K) :
    ∑ p∈mediumPrimes K B, B/p=
      ∑ j∈Icc 1 (K-1), (PrimesUpTo.count (B/j)-PrimesUpTo.count (B/K)) := by
  calc
    _ = ∑ p∈mediumPrimes K B, ∑ j∈Icc 1 (K-1), if j≤B/p then 1 else 0 :=
      sum_congr rfl (fun p hp => floor_eq_layers hK hp)
    _ = ∑ j∈Icc 1 (K-1), ∑ p∈mediumPrimes K B, if j≤B/p then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter]
      simpa using layer_card (B := B) hK hj

end
end PaperC.V282.FixedMediumLayers
