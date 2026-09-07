import PaperCV282.PrivateIncidenceBudget
import PaperC.Arithmetic.PolynomialZoneLargePrimes

/-! # Arithmetic geometry of medium-prime incidences

All bounds concern literal parity valuations in a consecutive window. The
quadratic cap forbids three medium factors, repeated two-column supports,
and two medium factors on a row already carrying a large prime.
-/
namespace PaperC.V282.MediumPrimeGeometry

open Matrix Finset SimpleIncidenceModel PolynomialZoneLargePrimes

noncomputable section

def mediumMatrix (lo B : ℕ) (P : Finset ℕ) : Matrix (Fin B) P F₂ :=
  fun i p => parityVec (lo + i.val) p.val

theorem divides_of_parity_ne_zero {n p : ℕ} (h : parityVec n p ≠ 0) : p ∣ n := by
  by_contra hd
  have hz : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hd
  exact h (by simp [parityVec_apply,hz])

theorem pair_medium_product_gt {B p q : ℕ} (hB : 1332 ≤ B)
    (hp : B < 11 * p) (hq : B < 11 * q) : B < p * q := by
  have hs := Nat.mul_lt_mul'' hp hq
  have hb : 121 * B ≤ B ^ 2 := by nlinarith
  nlinarith

theorem three_medium_product_gt {B p q r : ℕ} (hB : 1332 ≤ B)
    (hp : B < 11 * p) (hq : B < 11 * q) (hr : B < 11 * r) :
    B ^ 2 + B < p * q * r := by
  have hs := Nat.mul_lt_mul'' (Nat.mul_lt_mul'' hp hq) hr
  have hbase : 1331 * (B ^ 2 + B) ≤ B ^ 3 := by
    have h1 : B * (B - 1331) ≥ 1332 := by
      have hd : 1 ≤ B - 1331 := by omega
      have := Nat.mul_le_mul_left B hd
      nlinarith
    have he : B - 1331 + 1331 = B := by omega
    nlinarith [Nat.mul_le_mul_left B h1]
  nlinarith

theorem large_two_medium_product_gt {B q p r : ℕ} (hB : 1332 ≤ B)
    (hq : B < q) (hp : B < 11 * p) (hr : B < 11 * r) :
    B ^ 2 + B < q * p * r := by
  have hs := Nat.mul_lt_mul'' (Nat.mul_lt_mul'' hq hp) hr
  have hb : 121 * (B ^ 2 + B) ≤ B ^ 3 := by
    have h1 : 122 * B ≤ B ^ 2 := by nlinarith
    have h2 := Nat.mul_le_mul_left B h1
    nlinarith
  nlinarith

theorem two_large_product_gt {B p q : ℕ} (hp : B < p) (hq : B < q) :
    B ^ 2 + B < p * q := by
  have h := Nat.mul_le_mul (show B + 1 ≤ p by omega) (show B + 1 ≤ q by omega)
  nlinarith

theorem triple_primes_product_dvd {n p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hdp : p ∣ n) (hdq : q ∣ n) (hdr : r ∣ n) : p * q * r ∣ n := by
  have h : ({p,q,r} : Finset ℕ).prod id ∣ n := by
    apply Finset.prod_primes_dvd n
    · intro a ha
      simp only [mem_insert,mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact hp.prime
      · exact hq.prime
      · exact hr.prime
    · intro a ha
      simp only [mem_insert,mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact hdp
      · exact hdq
      · exact hdr
  simpa [hpq,hpr,hqr,mul_assoc] using h

theorem medium_row_weight_le_two {lo B : ℕ} {P : Finset ℕ}
    (hlo : 0 < lo) (hB : 1332 ≤ B) (htop : lo + B ≤ B ^ 2 + B + 1)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < 11 * p) (i : Fin B) :
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

theorem medium_pair_unique_row {lo B p q : ℕ} (hB : 1332 ≤ B)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpm : B < 11 * p) (hqm : B < 11 * q)
    (i j : Fin B) (hpi : p ∣ lo + i.val) (hqi : q ∣ lo + i.val)
    (hpj : p ∣ lo + j.val) (hqj : q ∣ lo + j.val) : i = j := by
  have hcop : p.Coprime q := (hp.coprime_iff_not_dvd).mpr (by
    intro hd
    exact hpq ((Nat.dvd_prime hq).mp hd |>.resolve_left hp.ne_one))
  apply Fin.ext
  exact unique_index_of_large_prime_dvd (B := B) (k := B) le_rfl
    (pair_medium_product_gt hB hpm hqm) i.isLt j.isLt
    (hcop.mul_dvd_of_dvd_of_dvd hpi hqi) (hcop.mul_dvd_of_dvd_of_dvd hpj hqj)

theorem medium_rows_simple {lo B : ℕ} {P : Finset ℕ} (hB : 1332 ≤ B)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < 11 * p)
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

theorem divisible_indices_card_le_eleven {lo B p : ℕ} (hB : 0 < B)
    (hp : B < 11 * p) (S : Finset (Fin B))
    (hdiv : ∀ i ∈ S, p ∣ lo + i.val) : S.card ≤ 11 := by
  classical
  let f : {i // i ∈ S} → Fin 11 := fun i => ⟨11 * i.val.val / B, by
    rw [Nat.div_lt_iff_lt_mul hB]
    have hi := i.val.isLt
    omega⟩
  have hf : Function.Injective f := by
    intro i j heq
    have he : 11 * i.val.val / B = 11 * j.val.val / B := congrArg Fin.val heq
    have hmi := Nat.mod_lt (11 * i.val.val) hB
    have hmj := Nat.mod_lt (11 * j.val.val) hB
    have hdi := Nat.mod_add_div (11 * i.val.val) B
    have hdj := Nat.mod_add_div (11 * j.val.val) B
    rw [← he] at hdj
    have hcong : i.val.val ≡ j.val.val [MOD p] :=
      (Nat.ModEq.refl lo).add_left_cancel
        ((hdiv i.val i.property).modEq_zero_nat.trans (hdiv j.val j.property).modEq_zero_nat.symm)
    apply Subtype.ext
    apply Fin.ext
    apply hcong.eq_of_abs_lt
    rw [abs_lt]
    constructor <;> omega
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fin] using hcard

theorem medium_column_weight_le_eleven {lo B : ℕ} {P : Finset ℕ} (hB : 0 < B)
    (hP : ∀ p ∈ P, B < 11 * p) (p : P) :
    (columnSupport (mediumMatrix lo B P) p).card ≤ 11 := by
  apply divisible_indices_card_le_eleven hB (hP p.val p.property)
  intro i hi
  exact divides_of_parity_ne_zero ((mem_columnSupport (mediumMatrix lo B P) i p).mp hi)

theorem medium_row_weight_le_one_of_large {lo B q : ℕ} {P : Finset ℕ}
    (hlo : 0 < lo) (hB : 1332 ≤ B) (htop : lo + B ≤ B ^ 2 + B + 1)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < 11 * p)
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

end
end PaperC.V282.MediumPrimeGeometry
