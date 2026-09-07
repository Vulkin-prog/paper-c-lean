import PaperCV282.MediumPrimeGeometry
import PaperCV282.MicroscopicValuationMatrix

/-! # Actual private columns in the quadratic microscopic window

Every prime above the window length divides a unique value, to exponent
one. Distinct such primes have distinct value rows under the quadratic
cap. Thus their number is exactly the number of private coordinates.
-/
namespace PaperC.V282.MicroscopicPrivatePrimes

open Matrix Finset PolynomialZoneLargePrimes MediumPrimeGeometry
open PrivateIncidenceRank MicroscopicValuationMatrix WindowValues

noncomputable section

def privateIndex (lo B : ℕ) (p : largePrimeFactors B lo B) : Fin B :=
  ⟨Classical.choose (existsUnique_index_dvd_of_mem_largePrimeFactors le_rfl p.property).exists,
    (Classical.choose_spec (existsUnique_index_dvd_of_mem_largePrimeFactors le_rfl p.property).exists).1⟩

theorem privateIndex_dvd (lo B : ℕ) (p : largePrimeFactors B lo B) :
    p.val ∣ lo + (privateIndex lo B p).val :=
  (Classical.choose_spec (existsUnique_index_dvd_of_mem_largePrimeFactors le_rfl p.property).exists).2

theorem privateIndex_unique (lo B : ℕ) (p : largePrimeFactors B lo B)
    (i : Fin B) (hi : p.val ∣ lo + i.val) : i = privateIndex lo B p := by
  apply Fin.ext
  exact unique_index_of_large_prime_dvd le_rfl
    (prime_and_large_of_mem_largePrimeFactors p.property).2
    i.isLt (privateIndex lo B p).isLt hi (privateIndex_dvd lo B p)

theorem large_factorization_eq_one {lo B p : ℕ} (hlo : 0 < lo)
    (htop : lo + B ≤ B ^ 2 + B + 1) (hp : p.Prime) (hBp : B < p)
    (i : Fin B) (hd : p ∣ lo + i.val) : (lo + i.val).factorization p = 1 := by
  have hn : lo + i.val ≠ 0 := by omega
  have hone := (hp.dvd_iff_one_le_factorization hn).mp hd
  have hnot : ¬2 ≤ (lo + i.val).factorization p := by
    intro hh
    have hs := (hp.pow_dvd_iff_le_factorization hn).mpr hh
    have hle := Nat.le_of_dvd (show 0 < lo + i.val by omega) hs
    have hgt := two_large_product_gt hBp hBp
    have hi := i.isLt
    nlinarith
  omega

theorem privateIndex_injective {lo B : ℕ} (hlo : 0 < lo)
    (htop : lo + B ≤ B ^ 2 + B + 1) : Function.Injective (privateIndex lo B) := by
  intro p q heq
  apply Subtype.ext
  by_contra hpq
  have hp := prime_and_large_of_mem_largePrimeFactors p.property
  have hq := prime_and_large_of_mem_largePrimeFactors q.property
  have hcop : p.val.Coprime q.val := (hp.1.coprime_iff_not_dvd).mpr (by
    intro hd
    exact hpq ((Nat.dvd_prime hq.1).mp hd |>.resolve_left hp.1.ne_one))
  have hdq : q.val ∣ lo + (privateIndex lo B p).val := by
    rw [heq]
    exact privateIndex_dvd lo B q
  have hprod := hcop.mul_dvd_of_dvd_of_dvd (privateIndex_dvd lo B p) hdq
  have hle := Nat.le_of_dvd (show 0 < lo + (privateIndex lo B p).val by omega) hprod
  have hgt := two_large_product_gt hp.2 hq.2
  have hi := (privateIndex lo B p).isLt
  omega

def privateRows (lo B : ℕ) : Finset (Fin B) :=
  Finset.univ.image (privateIndex lo B)

theorem card_privateRows {lo B : ℕ} (hlo : 0 < lo)
    (htop : lo + B ≤ B ^ 2 + B + 1) :
    (privateRows lo B).card = (largePrimeFactors B lo B).card := by
  rw [privateRows, Finset.card_image_of_injective _ (privateIndex_injective hlo htop)]
  simp only [Finset.card_univ,Fintype.card_coe]

theorem mem_privateRows (lo B : ℕ) (i : Fin B) :
    i ∈ privateRows lo B ↔ ∃ p : largePrimeFactors B lo B, privateIndex lo B p = i := by
  simp [privateRows]

def privateColumn (M lo B : ℕ) (hlo : 0 < lo) (hcut : lo + B ≤ M + 1)
    (p : largePrimeFactors B lo B) : PrimeUpTo M :=
  ⟨⟨p.val, by
    have hp := Nat.le_of_dvd (show 0 < lo + (privateIndex lo B p).val by omega)
      (privateIndex_dvd lo B p)
    have hi := (privateIndex lo B p).isLt
    omega⟩, (prime_and_large_of_mem_largePrimeFactors p.property).1⟩

theorem private_column_pure {M lo B : ℕ} (hlo : 0 < lo)
    (htop : lo + B ≤ B ^ 2 + B + 1) (hcut : lo + B ≤ M + 1)
    (p : largePrimeFactors B lo B) :
    (valuationMatrix M (lo + 1) B).col (privateColumn M lo B hlo hcut p) =
      Pi.single (privateIndex lo B p) (1 : F₂) := by
  funext i
  have hp := prime_and_large_of_mem_largePrimeFactors p.property
  by_cases hi : i = privateIndex lo B p
  · subst i
    have he := large_factorization_eq_one hlo htop hp.1 hp.2 _ (privateIndex_dvd lo B p)
    simp [valuationMatrix,vertex,privateColumn,parityVec_apply,he]
  · have hnd : ¬p.val ∣ lo + i.val := fun hd => hi (privateIndex_unique lo B p i hd)
    have hz := Nat.factorization_eq_zero_of_not_dvd hnd
    simp [valuationMatrix,vertex,privateColumn,parityVec_apply,hz,hi]

theorem private_coordinate_mem_range {M lo B : ℕ} (hlo : 0 < lo)
    (htop : lo + B ≤ B ^ 2 + B + 1) (hcut : lo + B ≤ M + 1)
    (i : Fin B) (hi : i ∈ privateRows lo B) :
    Pi.single i (1 : F₂) ∈ LinearMap.range (valuationMatrix M (lo + 1) B).mulVecLin := by
  obtain ⟨p,rfl⟩ := (mem_privateRows lo B i).mp hi
  exact private_column_mem_range _ _ _ (private_column_pure hlo htop hcut p)

theorem private_medium_row_weight_le_one {lo B : ℕ} {P : Finset ℕ}
    (hlo : 0 < lo) (hB : 1332 ≤ B) (htop : lo + B ≤ B ^ 2 + B + 1)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < 11 * p)
    (i : Fin B) (hi : i ∈ privateRows lo B) :
    (SimpleIncidenceModel.rowSupport (mediumMatrix lo B P) i).card ≤ 1 := by
  obtain ⟨p,rfl⟩ := (mem_privateRows lo B i).mp hi
  have hp := prime_and_large_of_mem_largePrimeFactors p.property
  exact medium_row_weight_le_one_of_large hlo hB htop hP hp.1 hp.2 _ (privateIndex_dvd lo B p)

end
end PaperC.V282.MicroscopicPrivatePrimes
