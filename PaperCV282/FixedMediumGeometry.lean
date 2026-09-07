import PaperCV282.FixedMediumSquares
import PaperCV282.MicroscopicPrivatePrimes

/-! # Actual medium-prime geometry at every fixed reciprocal cutoff

The explicit threshold depends only on K. Every matrix row, column and
private-row loss below is verified for the literal parity valuations in a
positive quadratic window, without an incidence or rank premise.
-/
namespace PaperC.V282.FixedMediumGeometry

open Matrix Finset SimpleIncidenceModel PolynomialZoneLargePrimes
open MediumPrimeGeometry MicroscopicPrivatePrimes

noncomputable section

theorem scaled_quadratic_le_cube {a B : ℕ} (hB : 2 * a + 1 ≤ B) :
    a * (B ^ 2 + B) ≤ B ^ 3 := by
  have hBB : B ≤ B ^ 2 := by nlinarith
  have h1 := Nat.mul_le_mul_right B (show 2 * a ≤ B by omega)
  have h2 := Nat.mul_le_mul_right B h1
  have h3 := Nat.mul_le_mul_left a hBB
  nlinarith

theorem pair_medium_product_gt {K B p q : ℕ}
    (hB : 2 * (K ^ 3 + K ^ 2) + 1 ≤ B)
    (hp : B < K * p) (hq : B < K * q) : B < p * q := by
  have hs := Nat.mul_lt_mul'' hp hq
  have hb := Nat.mul_le_mul_right B (show K ^ 2 ≤ B by omega)
  by_contra h
  have hm := Nat.mul_le_mul_left (K ^ 2) (Nat.le_of_not_gt h)
  nlinarith

theorem three_medium_product_gt {K B p q r : ℕ}
    (hB : 2 * (K ^ 3 + K ^ 2) + 1 ≤ B)
    (hp : B < K * p) (hq : B < K * q) (hr : B < K * r) :
    B ^ 2 + B < p * q * r := by
  have hs := Nat.mul_lt_mul'' (Nat.mul_lt_mul'' hp hq) hr
  have hb := scaled_quadratic_le_cube (a := K ^ 3) (by omega : 2 * K ^ 3 + 1 ≤ B)
  by_contra h
  have hm := Nat.mul_le_mul_left (K ^ 3) (Nat.le_of_not_gt h)
  nlinarith

theorem large_two_medium_product_gt {K B q p r : ℕ}
    (hB : 2 * (K ^ 3 + K ^ 2) + 1 ≤ B)
    (hq : B < q) (hp : B < K * p) (hr : B < K * r) :
    B ^ 2 + B < q * p * r := by
  have hs := Nat.mul_lt_mul'' (Nat.mul_lt_mul'' hq hp) hr
  have hb := scaled_quadratic_le_cube (a := K ^ 2) (by omega : 2 * K ^ 2 + 1 ≤ B)
  by_contra h
  have hm := Nat.mul_le_mul_left (K ^ 2) (Nat.le_of_not_gt h)
  nlinarith

theorem medium_row_weight_le_two {K lo B : ℕ} {P : Finset ℕ}
    (hlo : 0 < lo) (hB : 2 * (K ^ 3 + K ^ 2) + 1 ≤ B) (htop : lo + B ≤ B ^ 2 + B + 1)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < K * p) (i : Fin B) :
    (rowSupport (mediumMatrix lo B P) i).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨p,hp,q,hq,r,hr,hpq,hpr,hqr⟩ := Finset.two_lt_card.mp (by omega :
    2 < (rowSupport (mediumMatrix lo B P) i).card)
  have hp' := hP p.val p.property
  have hq' := hP q.val q.property
  have hr' := hP r.val r.property
  have hn : 0 < lo + i.val := by omega
  have hd := triple_primes_product_dvd hp'.1 hq'.1 hr'.1
    (fun h => hpq (Subtype.ext h)) (fun h => hpr (Subtype.ext h))
    (fun h => hqr (Subtype.ext h))
    (divides_of_parity_ne_zero ((mem_rowSupport (mediumMatrix lo B P) i p).mp hp))
    (divides_of_parity_ne_zero ((mem_rowSupport (mediumMatrix lo B P) i q).mp hq))
    (divides_of_parity_ne_zero ((mem_rowSupport (mediumMatrix lo B P) i r).mp hr))
  have hle := Nat.le_of_dvd hn hd
  have hgt := three_medium_product_gt hB hp'.2.2 hq'.2.2 hr'.2.2
  have hi := i.isLt
  omega

theorem medium_pair_unique_row {K lo B p q : ℕ} (hB : 2 * (K ^ 3 + K ^ 2) + 1 ≤ B)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpm : B < K * p) (hqm : B < K * q)
    (i j : Fin B) (hpi : p ∣ lo + i.val) (hqi : q ∣ lo + i.val)
    (hpj : p ∣ lo + j.val) (hqj : q ∣ lo + j.val) : i = j := by
  have hcop : p.Coprime q := (hp.coprime_iff_not_dvd).mpr (by
    intro hd
    exact hpq ((Nat.dvd_prime hq).mp hd |>.resolve_left hp.ne_one))
  apply Fin.ext
  exact unique_index_of_large_prime_dvd (B := B) (k := B) le_rfl
    (pair_medium_product_gt hB hpm hqm) i.isLt j.isLt
    (hcop.mul_dvd_of_dvd_of_dvd hpi hqi) (hcop.mul_dvd_of_dvd_of_dvd hpj hqj)

theorem medium_rows_simple {K lo B : ℕ} {P : Finset ℕ} (hB : 2 * (K ^ 3 + K ^ 2) + 1 ≤ B)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < K * p)
    (i j : Fin B) (hi : (rowSupport (mediumMatrix lo B P) i).card = 2)
    (hij : rowSupport (mediumMatrix lo B P) i = rowSupport (mediumMatrix lo B P) j) : i = j := by
  classical
  obtain ⟨p,q,hpq,hrow⟩ := Finset.card_eq_two.mp hi
  have hp := hP p.val p.property
  have hq := hP q.val q.property
  apply medium_pair_unique_row (lo := lo) hB hp.1 hq.1 (fun h => hpq (Subtype.ext h)) hp.2.2 hq.2.2
  · apply divides_of_parity_ne_zero
    exact (mem_rowSupport (mediumMatrix lo B P) i p).mp (by rw [hrow]; simp)
  · apply divides_of_parity_ne_zero
    exact (mem_rowSupport (mediumMatrix lo B P) i q).mp (by rw [hrow]; simp)
  · apply divides_of_parity_ne_zero
    exact (mem_rowSupport (mediumMatrix lo B P) j p).mp (by rw [← hij,hrow]; simp)
  · apply divides_of_parity_ne_zero
    exact (mem_rowSupport (mediumMatrix lo B P) j q).mp (by rw [← hij,hrow]; simp)

theorem medium_row_weight_le_one_of_large {K lo B q : ℕ} {P : Finset ℕ}
    (hlo : 0 < lo) (hB : 2 * (K ^ 3 + K ^ 2) + 1 ≤ B) (htop : lo + B ≤ B ^ 2 + B + 1)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < K * p)
    (hq : q.Prime) (hlarge : B < q) (i : Fin B) (hqi : q ∣ lo + i.val) :
    (rowSupport (mediumMatrix lo B P) i).card ≤ 1 := by
  classical
  by_contra h
  obtain ⟨p,hp,r,hr,hpr⟩ := Finset.one_lt_card.mp (by omega :
    1 < (rowSupport (mediumMatrix lo B P) i).card)
  have hp' := hP p.val p.property
  have hr' := hP r.val r.property
  have hd := triple_primes_product_dvd hq hp'.1 hr'.1
    (by omega) (by omega) (fun h => hpr (Subtype.ext h)) hqi
    (divides_of_parity_ne_zero ((mem_rowSupport (mediumMatrix lo B P) i p).mp hp))
    (divides_of_parity_ne_zero ((mem_rowSupport (mediumMatrix lo B P) i r).mp hr))
  have hle := Nat.le_of_dvd (show 0 < lo + i.val by omega) hd
  have hgt := large_two_medium_product_gt hB hlarge hp'.2.2 hr'.2.2
  have hi := i.isLt
  omega

theorem divisible_indices_card_le {K lo B p : ℕ} (hK : 0 < K) (hB : 0 < B)
    (hp : B < K * p) (S : Finset (Fin B))
    (hdiv : ∀ i ∈ S, p ∣ lo + i.val) : S.card ≤ K := by
  classical
  have hinj : Function.Injective (fun i : Fin B => i.val) := Fin.val_injective
  rw [← card_image_of_injective S hinj]
  apply FixedMediumSquares.card_le_of_separated (a := 0) hK hB
  · intro n hn
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
    exact ⟨Nat.zero_le _, by simp only [zero_add]; exact i.isLt⟩
  · intro m hm n hn hmn
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hm
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hn
    have hd : p ∣ j.val - i.val := by
      simpa only [Nat.add_sub_add_left] using Nat.dvd_sub (hdiv j hj) (hdiv i hi)
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hmn) hd
    exact hp.trans_le (Nat.mul_le_mul_left K hle)

theorem medium_column_weight_le {K lo B : ℕ} {P : Finset ℕ}
    (hK : 0 < K) (hB : 0 < B) (hP : ∀ p ∈ P, B < K * p) (p : P) :
    (columnSupport (mediumMatrix lo B P) p).card ≤ K := by
  apply divisible_indices_card_le hK hB (hP p.val p.property)
  intro i hi
  exact divides_of_parity_ne_zero ((mem_columnSupport (mediumMatrix lo B P) i p).mp hi)

theorem private_medium_row_weight_le_one {K lo B : ℕ} {P : Finset ℕ}
    (hlo : 0 < lo) (hB : 2 * (K ^ 3 + K ^ 2) + 1 ≤ B)
    (htop : lo + B ≤ B ^ 2 + B + 1)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < K * p)
    (i : Fin B) (hi : i ∈ privateRows lo B) :
    (rowSupport (mediumMatrix lo B P) i).card ≤ 1 := by
  obtain ⟨p,rfl⟩ := (mem_privateRows lo B i).mp hi
  have hp := prime_and_large_of_mem_largePrimeFactors p.property
  exact medium_row_weight_le_one_of_large hlo hB htop hP hp.1 hp.2 _ (privateIndex_dvd lo B p)

end
end PaperC.V282.FixedMediumGeometry
