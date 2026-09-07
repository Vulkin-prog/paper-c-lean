import PaperCV282.MediumSquareExceptions
import PaperC.Arithmetic.ParityVector

/-! # Divisibility incidences and odd valuation incidences

Each prime contributes at least floor(B/p) multiples in every positive
window of B consecutive integers. The only multiples lost on reducing
valuation modulo two have square divisibility.
-/

namespace PaperC.V282.MediumMultipleCounts

open Finset MediumSquareExceptions
open scoped BigOperators

noncomputable section

/-- Multiples of p in the literal B-integer window. -/
def multiples (lo B p : ℕ) : Finset ℕ := (Ico lo (lo + B)).filter (p ∣ ·)

/-- A uniform lower count, independent of the position of the window. -/
theorem div_le_multiples_card {lo B p : ℕ} (hlo : 0 < lo) (hp : 0 < p) :
    B / p ≤ (multiples lo B p).card := by
  let f (j : ℕ) := ((lo - 1) / p + 1 + j) * p
  have hmem : ∀ j ∈ range (B / p), f j ∈ multiples lo B p := by
    intro j hj
    have hj' := mem_range.mp hj
    have hmod := Nat.mod_lt (lo - 1) hp
    have hd := Nat.mod_add_div (lo - 1) p
    have hb := Nat.div_mul_le_self B p
    have hjp : (j + 1) * p ≤ (B / p) * p := Nat.mul_le_mul_right p (by omega)
    have hlop : (lo - 1) / p * p ≤ lo - 1 := Nat.div_mul_le_self (lo - 1) p
    have hloeq : lo - 1 + 1 = lo := by omega
    have hfirst : lo ≤ ((lo - 1) / p + 1) * p := by nlinarith
    have hlow : lo ≤ f j := by dsimp [f]; nlinarith
    have hhigh : f j < lo + B := by dsimp [f]; nlinarith
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hlow,hhigh⟩, dvd_mul_left p _⟩
  have hinj : Set.InjOn f (↑(range (B / p)) : Set ℕ) := by
    intro i hi j hj heq
    dsimp [f] at heq
    have := Nat.eq_of_mul_eq_mul_right hp heq
    omega
  simpa only [card_range] using Finset.card_le_card_of_injOn f hmem hinj

/-- A divisible prime of even parity must divide to at least the second power. -/
theorem square_dvd_of_divides_of_parity_zero {n p : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hd : p ∣ n) (hz : parityVec n p = 0) : p ^ 2 ∣ n := by
  have hone := (hp.dvd_iff_one_le_factorization (by omega : n ≠ 0)).mp hd
  apply (hp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).mpr
  by_contra htwo
  have he : n.factorization p = 1 := by omega
  simp [parityVec_apply,he] at hz

/-- All divisibility incidences on a selected set of primes. -/
def divisibilityIncidences (lo B : ℕ) (P : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((Ico lo (lo + B)).product P).filter (fun z => z.2 ∣ z.1)

/-- The actual nonzero entries after reducing prime valuations modulo two. -/
def oddIncidences (lo B : ℕ) (P : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((Ico lo (lo + B)).product P).filter (fun z => parityVec z.1 z.2 ≠ 0)

/-- Double counting the ordinary incidences prime by prime. -/
theorem divisibilityIncidences_card (lo B : ℕ) (P : Finset ℕ) :
    (divisibilityIncidences lo B P).card = ∑ p ∈ P, (multiples lo B p).card := by
  classical
  have heq : divisibilityIncidences lo B P =
      P.biUnion (fun p => (multiples lo B p).image (fun n => (n,p))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hwP,hd⟩ := mem_filter.mp hz
      obtain ⟨hw,hp⟩ := mem_product.mp hwP
      exact mem_biUnion.mpr ⟨z.2,hp,mem_image.mpr
        ⟨z.1,mem_filter.mpr ⟨hw,hd⟩,rfl⟩⟩
    · intro hz
      obtain ⟨q,hq,hmq⟩ := mem_biUnion.mp hz
      obtain ⟨m,hm,hz⟩ := mem_image.mp hmq
      cases hz
      exact mem_filter.mpr ⟨mem_product.mpr ⟨(mem_filter.mp hm).1,hq⟩,
        (mem_filter.mp hm).2⟩
  rw [heq, card_biUnion]
  · apply sum_congr rfl
    intro p hp
    exact card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
  · intro p hp q hq hpq
    apply disjoint_left.mpr
    intro z hz hqz
    obtain ⟨n,hn,hnz⟩ := mem_image.mp hz
    obtain ⟨m,hm,hmz⟩ := mem_image.mp hqz
    exact hpq (by simpa using congrArg Prod.snd (hnz.trans hmz.symm))

/-- The ordinary floor-sum is a lower bound for the true incidence count. -/
theorem floor_sum_le_incidence_card {lo B : ℕ} {P : Finset ℕ}
    (hlo : 0 < lo) (hP : ∀ p ∈ P, 0 < p) :
    ∑ p ∈ P, B / p ≤ (divisibilityIncidences lo B P).card := by
  rw [divisibilityIncidences_card]
  exact sum_le_sum (fun p hp => div_le_multiples_card hlo (hP p hp))

/-- At most 854 entries are lost between divisibility and odd valuation. -/
theorem floor_sum_le_odd_incidence_add {lo B : ℕ} {P : Finset ℕ}
    (hlo : 0 < lo) (hB : 1332 ≤ B) (htop : lo + B ≤ B ^ 2 + B + 1)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < 11 * p) :
    ∑ p ∈ P, B / p ≤ (oddIncidences lo B P).card + 854 := by
  classical
  have hsub : divisibilityIncidences lo B P ⊆
      oddIncidences lo B P ∪ squareIncidences lo B := by
    intro z hz
    obtain ⟨hwP,hd⟩ := mem_filter.mp hz
    obtain ⟨hw,hp⟩ := mem_product.mp hwP
    by_cases hodd : parityVec z.1 z.2 ≠ 0
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨hw,hp⟩,hodd⟩)
    · have hpdata := hP z.2 hp
      have hn : 0 < z.1 := hlo.trans_le (mem_Ico.mp hw).1
      apply mem_union_right
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hw,mem_Icc.mpr ⟨hpdata.1.pos,hpdata.2.1⟩⟩,
        hn,hpdata.2.2,square_dvd_of_divides_of_parity_zero hn hpdata.1 hd (not_ne_iff.mp hodd)⟩
  calc
    _ ≤ (divisibilityIncidences lo B P).card :=
      floor_sum_le_incidence_card hlo (fun p hp => (hP p hp).1.pos)
    _ ≤ (oddIncidences lo B P ∪ squareIncidences lo B).card := card_le_card hsub
    _ ≤ (oddIncidences lo B P).card + (squareIncidences lo B).card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (squareIncidences_card_le hB htop) _

end
end PaperC.V282.MediumMultipleCounts
