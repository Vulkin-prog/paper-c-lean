import PaperCV282.MediumMultipleCounts
import PaperC.Arithmetic.PrimeCountBridge

/-! # Exact prime-count layers of the medium incidence sum

The layer-cake identity is finite and includes all floor and endpoint
conventions. PNT is used only in the subsequent asymptotic module.
-/

namespace PaperC.V282.MediumPrimeLayers

open Finset DefectCounting PrimeCountBridge MediumMultipleCounts
open scoped BigOperators

/-- The inclusive medium interval B/11 < p <= B. -/
def mediumPrimes (B : ℕ) : Finset ℕ :=
  smallPrimesUpTo B \ smallPrimesUpTo (B / 11)

theorem mem_mediumPrimes {B p : ℕ} :
    p ∈ mediumPrimes B ↔ p.Prime ∧ p ≤ B ∧ B < 11 * p := by
  simp only [mediumPrimes, mem_sdiff, mem_smallPrimesUpTo]
  constructor
  · rintro ⟨⟨hp,hpB⟩,hn⟩
    have hnot : ¬p ≤ B / 11 := fun h => hn ⟨hp,h⟩
    have hdiv : B / 11 < p := by omega
    exact ⟨hp,hpB,by simpa only [mul_comm] using (Nat.div_lt_iff_lt_mul (by decide : 0 < 11)).mp hdiv⟩
  · rintro ⟨hp,hpB,hB⟩
    have hdiv : B / 11 < p :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 11)).mpr (by simpa only [mul_comm] using hB)
    exact ⟨⟨hp,hpB⟩,by omega⟩

/-- No medium prime contributes more than ten multiples to the floor-sum. -/
theorem floor_lt_eleven {B p : ℕ} (hp : p ∈ mediumPrimes B) : B / p < 11 :=
  (Nat.div_lt_iff_lt_mul (mem_mediumPrimes.mp hp).1.pos).mpr (mem_mediumPrimes.mp hp).2.2

/-- The exact ten-layer decomposition of a medium prime's floor weight. -/
theorem floor_eq_layers {B p : ℕ} (hp : p ∈ mediumPrimes B) :
    B / p = ∑ j ∈ Icc 1 10, if j ≤ B / p then 1 else 0 := by
  have hsmall := floor_lt_eleven hp
  have hfilter : (Icc 1 10).filter (fun j => j ≤ B / p) = Icc 1 (B / p) := by
    ext j
    simp only [mem_filter, mem_Icc]
    omega
  rw [← sum_filter, hfilter]
  simp

/-- A fixed layer is precisely a difference of inclusive prime intervals. -/
theorem layer_primes_eq {B j : ℕ} (hj : j ∈ Icc 1 10) :
    (mediumPrimes B).filter (fun p => j ≤ B / p) =
      smallPrimesUpTo (B / j) \ smallPrimesUpTo (B / 11) := by
  have hjpos : 0 < j := (mem_Icc.mp hj).1
  ext p
  simp only [mem_filter, mem_mediumPrimes, mem_sdiff, mem_smallPrimesUpTo]
  constructor
  · rintro ⟨⟨hp,hpB,hmed⟩,hjp⟩
    have hjp' := (Nat.le_div_iff_mul_le hp.pos).mp hjp
    have hpj := (Nat.le_div_iff_mul_le hjpos).mpr (by simpa only [mul_comm] using hjp')
    have hdiv : B / 11 < p :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 11)).mpr (by simpa only [mul_comm] using hmed)
    exact ⟨⟨hp,hpj⟩,by omega⟩
  · rintro ⟨⟨hp,hpj⟩,hn⟩
    have hpB : p ≤ B := hpj.trans (Nat.div_le_self B j)
    have hnot : ¬p ≤ B / 11 := fun h => hn ⟨hp,h⟩
    have hdiv : B / 11 < p := by omega
    have hmed : B < 11 * p := by
      simpa only [mul_comm] using (Nat.div_lt_iff_lt_mul (by decide : 0 < 11)).mp hdiv
    have hpj' := (Nat.le_div_iff_mul_le hjpos).mp hpj
    exact ⟨⟨hp,hpB,hmed⟩,
      (Nat.le_div_iff_mul_le hp.pos).mpr (by simpa only [mul_comm] using hpj')⟩

/-- Counting a layer gives exactly pi(B/j)-pi(B/11). -/
theorem layer_card {B j : ℕ} (hj : j ∈ Icc 1 10) :
    ((mediumPrimes B).filter (fun p => j ≤ B / p)).card =
      PrimesUpTo.count (B / j) - PrimesUpTo.count (B / 11) := by
  rw [layer_primes_eq hj, card_sdiff_of_subset]
  · rw [← count_eq_card_smallPrimesUpTo, ← count_eq_card_smallPrimesUpTo]
  · intro p hp
    have hd : B / 11 ≤ B / j := Nat.div_le_div_left (by have := (mem_Icc.mp hj).2; omega)
      (mem_Icc.mp hj).1
    exact mem_smallPrimesUpTo.mpr ⟨(mem_smallPrimesUpTo.mp hp).1,
      (mem_smallPrimesUpTo.mp hp).2.trans hd⟩

/-- The exact floor-sum identity preceding companion equation (E.3). -/
theorem floor_sum_eq_prime_layers (B : ℕ) :
    ∑ p ∈ mediumPrimes B, B / p =
      ∑ j ∈ Icc 1 10, (PrimesUpTo.count (B / j) - PrimesUpTo.count (B / 11)) := by
  calc
    _ = ∑ p ∈ mediumPrimes B, ∑ j ∈ Icc 1 10, if j ≤ B / p then 1 else 0 :=
      sum_congr rfl (fun p hp => floor_eq_layers hp)
    _ = ∑ j ∈ Icc 1 10, ∑ p ∈ mediumPrimes B, if j ≤ B / p then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter]
      simpa using layer_card (B := B) hj

/-- Exact arithmetic lower bound for the odd incidence count in a quadratic window. -/
theorem prime_layers_le_odd_incidence_add {lo B : ℕ}
    (hlo : 0 < lo) (hB : 1332 ≤ B) (htop : lo + B ≤ B ^ 2 + B + 1) :
    ∑ j ∈ Icc 1 10, (PrimesUpTo.count (B / j) - PrimesUpTo.count (B / 11)) ≤
      (oddIncidences lo B (mediumPrimes B)).card + 854 := by
  rw [← floor_sum_eq_prime_layers]
  exact floor_sum_le_odd_incidence_add hlo hB htop (fun p hp => mem_mediumPrimes.mp hp)

end PaperC.V282.MediumPrimeLayers
