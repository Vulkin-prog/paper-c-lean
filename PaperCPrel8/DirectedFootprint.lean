import PaperCPrel8.PrimeForcing
import PaperC.Arithmetic.IntervalCongruence

/-! # Finite directed change-set bounds

These are counts of possible changes under the specified prime forcing.
No independence or undirected dependency-graph property is asserted.
-/
namespace PaperC.Prel8.DirectedFootprint
open PaperC.Prel8.PrimeForcing PaperC.Prel8.OddPrimePivot
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- A translated divisibility class has at most `n/p+1` positive starts. -/
theorem card_divisible_offset (n b p : ℕ) (hp : 0 < p) :
    (((Finset.Icc 1 n).filter fun k => p ∣ k+b).card : ℝ) ≤ (n : ℝ)/p+1 := by
  let T := (Finset.Ico (b+1) (b+n+1)).filter fun x => x ≡ 0 [MOD p]
  have hi : ((Finset.Icc 1 n).filter fun k => p ∣ k+b).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun k => k+b)
    · intro k hk
      obtain ⟨hkr, hd⟩ := Finset.mem_filter.mp hk
      have hkr := Finset.mem_Icc.mp hkr
      dsimp only
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hd.modEq_zero_nat⟩
    · intro x hx y hy he
      dsimp only at he
      omega
  have hc := card_nat_Ico_modEq_cast_le_div_add_one (b+1) (b+n+1) 0 p hp (by omega)
  have hc' := (Rat.cast_le (K := ℝ)).mpr hc
  push_cast at hc'
  have hT : (T.card : ℝ) ≤ (n : ℝ)/p+1 := by
    convert hc' using 1
    ring
  exact (by exact_mod_cast hi : (_ : ℝ) ≤ T.card).trans hT

variable {M : ℕ} {ι : Type*} [Fintype ι]

/-- The directed footprint is covered by the individual divisibility classes. -/
theorem footprint_subset_cover (G : Finset ℕ) (n Q : ℕ) (q : ι → PrimeUpTo M)
    (hG : G ⊆ Finset.Icc 1 n) :
    directedFootprint G Q q ⊆ Finset.univ.biUnion
      (fun a : ι => Finset.univ.biUnion (fun b : Fin (Q+1) =>
        (Finset.Icc 1 n).filter fun k => (q a).val.val ∣ k+b.val)) := by
  classical
  intro k hk
  obtain ⟨hk, a, b, hd⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hG hk, hd⟩⟩⟩

/-- Exact finite pointwise footprint estimate of companion F.6. -/
theorem card_footprint_le (G : Finset ℕ) (n Q : ℕ) (q : ι → PrimeUpTo M)
    (hG : G ⊆ Finset.Icc 1 n) :
    ((directedFootprint G Q q).card : ℝ) ≤
      (Q+1 : ℝ) * ∑ a, ((n : ℝ)/(q a).val.val+1) := by
  classical
  calc
    _ ≤ ((Finset.univ.biUnion (fun a : ι => Finset.univ.biUnion (fun b : Fin (Q+1) =>
        (Finset.Icc 1 n).filter fun k => (q a).val.val ∣ k+b.val))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (footprint_subset_cover G n Q q hG)
    _ ≤ ∑ a : ι, ∑ b : Fin (Q+1),
        (((Finset.Icc 1 n).filter fun k => (q a).val.val ∣ k+b.val).card : ℝ) := by
      have hi : (Finset.univ.biUnion (fun a : ι => Finset.univ.biUnion (fun b : Fin (Q+1) =>
          (Finset.Icc 1 n).filter fun k => (q a).val.val ∣ k+b.val))).card ≤
          ∑ a : ι, ∑ b : Fin (Q+1), ((Finset.Icc 1 n).filter fun k => (q a).val.val ∣ k+b.val).card :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a _ => Finset.card_biUnion_le)
      exact_mod_cast hi
    _ ≤ ∑ a : ι, ∑ _b : Fin (Q+1), ((n : ℝ)/(q a).val.val+1) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact card_divisible_offset n b.val (q a).val.val (q a).property.pos
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      rw [Finset.mul_sum]

/-- Actual truncated reciprocal population; only positive integers are counted. -/
def reciprocalPivots (X Y : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 X).filter (fun m => Y < largestOddPrime m), (largestOddPrime m : ℝ)⁻¹

/-- At one fixed offset, translating the start is injective into the reciprocal population. -/
theorem reciprocal_at_offset_le (G : Finset ℕ) (n Q Y a : ℕ)
    (hG : G ⊆ Finset.Icc 1 n) (ha : a ≤ Q)
    (hY : ∀ j ∈ G, Y < largestOddPrime (j+a)) :
    (∑ j ∈ G, (largestOddPrime (j+a) : ℝ)⁻¹) ≤ reciprocalPivots (n+Q) Y := by
  classical
  let T := (Finset.Icc 1 (n+Q)).filter (fun m => Y < largestOddPrime m)
  have hs : G.image (fun j => j+a) ⊆ T := by
    intro m hm
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hm
    have hr := Finset.mem_Icc.mp (hG hj)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hY j hj⟩
  have he : ∑ j ∈ G, (largestOddPrime (j+a) : ℝ)⁻¹ =
      ∑ m ∈ G.image (fun j => j+a), (largestOddPrime m : ℝ)⁻¹ := by
    rw [Finset.sum_image]
    intro x hx y hy he
    dsimp only at he
    omega
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Summing over offsets costs only their number, without counting primes as distinct integers. -/
theorem reciprocal_double_sum_le (G : Finset ℕ) (n Q Y : ℕ)
    (hG : G ⊆ Finset.Icc 1 n)
    (hY : ∀ j ∈ G, ∀ a : Fin (Q+1), Y < largestOddPrime (j+a.val)) :
    (∑ j ∈ G, ∑ a : Fin (Q+1), (largestOddPrime (j+a.val) : ℝ)⁻¹) ≤
      (Q+1 : ℝ) * reciprocalPivots (n+Q) Y := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _a : Fin (Q+1), reciprocalPivots (n+Q) Y := by
      apply Finset.sum_le_sum
      intro a _
      exact reciprocal_at_offset_le G n Q Y a.val hG (by omega) (fun j hj => hY j hj a)
    _ = _ := by simp

/-- The finite total footprint in F.6, using the actual reciprocal pivot population. -/
theorem total_footprint_le (G : Finset ℕ) (n Q Y : ℕ)
    (q : ℕ → Fin (Q+1) → PrimeUpTo M) (hG : G ⊆ Finset.Icc 1 n)
    (hq : ∀ j ∈ G, ∀ a : Fin (Q+1), (q j a).val.val = largestOddPrime (j+a.val))
    (hY : ∀ j ∈ G, ∀ a : Fin (Q+1), Y < largestOddPrime (j+a.val)) :
    (∑ j ∈ G, ((directedFootprint G Q (q j)).card : ℝ)) ≤
      (n : ℝ)*(Q+1 : ℝ)^2*(1+reciprocalPivots (n+Q) Y) := by
  classical
  have hrec := reciprocal_double_sum_le G n Q Y hG hY
  have hcard : (G.card : ℝ) ≤ n := by
    have h := Finset.card_le_card hG
    have h' : G.card ≤ n := by simpa using h
    exact_mod_cast h'
  have he (j : ℕ) (hj : j ∈ G) :
      (∑ a : Fin (Q+1), ((n : ℝ)/(q j a).val.val+1)) =
      (n : ℝ)*(∑ a : Fin (Q+1), (largestOddPrime (j+a.val) : ℝ)⁻¹)+(Q+1 : ℝ) := by
    simp_rw [hq j hj, div_eq_mul_inv]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  calc
    _ ≤ ∑ j ∈ G, (Q+1 : ℝ)*
        ((n : ℝ)*(∑ a : Fin (Q+1), (largestOddPrime (j+a.val) : ℝ)⁻¹)+(Q+1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← he j hj]
      exact card_footprint_le G n Q (q j) hG
    _ = (Q+1 : ℝ)*((n : ℝ)*
        (∑ j ∈ G, ∑ a : Fin (Q+1), (largestOddPrime (j+a.val) : ℝ)⁻¹)+G.card*(Q+1 : ℝ)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [mul_add]
    _ ≤ (Q+1 : ℝ)*((n : ℝ)*((Q+1 : ℝ)*reciprocalPivots (n+Q) Y)+(n : ℝ)*(Q+1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = _ := by ring

end
end PaperC.Prel8.DirectedFootprint
