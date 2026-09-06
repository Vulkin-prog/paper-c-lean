import PaperCV282.MicroscopicPrivatePrimes
import PaperCV282.MediumPrimeLayers

/-! # The finite microscopic rank bound from real prime incidences

Both inputs to the rank inequality are literal arithmetic counts: large
prime divisors of the consecutive product and odd medium-prime incidences.
All matrix hypotheses are proved from positivity and the quadratic window.
-/
namespace PaperC.V282.MicroscopicIncidenceRank

open Matrix Finset SimpleIncidenceModel PrivateIncidenceBudget
open MediumPrimeGeometry MicroscopicPrivatePrimes MicroscopicValuationMatrix
open MediumMultipleCounts MediumPrimeLayers PolynomialZoneLargePrimes WindowValues

noncomputable section

theorem incidenceMass_mediumMatrix (lo B : ℕ) (P : Finset ℕ) :
    incidenceMass (mediumMatrix lo B P) = (oddIncidences lo B P).card := by
  classical
  let S := (Finset.univ.product Finset.univ).filter
    (fun z : Fin B × P => mediumMatrix lo B P z.1 z.2 ≠ 0)
  have hs : incidenceMass (mediumMatrix lo B P) = S.card := by
    simp only [incidenceMass,rowSupport,S,Finset.card_filter,Finset.product_eq_sprod,Finset.sum_product]
  rw [hs]
  apply Finset.card_bij (fun z _ => (lo + z.1.val,z.2.val))
  · intro z hz
    have hz' : mediumMatrix lo B P z.1 z.2 ≠ 0 := (Finset.mem_filter.mp hz).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by have := z.1.isLt; omega⟩,
      z.2.property⟩,hz'⟩
  · intro z hz w hw hzw
    apply Prod.ext
    · apply Fin.ext
      have := congrArg Prod.fst hzw
      omega
    · apply Subtype.ext
      exact congrArg Prod.snd hzw
  · rintro ⟨n,p⟩ hz
    obtain ⟨hnp,hodd⟩ := Finset.mem_filter.mp hz
    obtain ⟨hn,hp⟩ := Finset.mem_product.mp hnp
    obtain ⟨hlo,htop⟩ := Finset.mem_Ico.mp hn
    let i : Fin B := ⟨n - lo, by omega⟩
    refine ⟨(i,⟨p,hp⟩),?_,?_⟩
    · simp only [S,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_univ,true_and]
      change parityVec (lo + (n - lo)) p ≠ 0
      simpa only [Nat.add_sub_of_le hlo] using hodd
    · apply Prod.ext
      · dsimp [i]
        omega
      · rfl

def mediumColumn (M B : ℕ) (P : Finset ℕ) (hBM : B ≤ M)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < 11 * p) (p : P) : PrimeUpTo M :=
  ⟨⟨p.val, Nat.lt_succ_of_le ((hP p.val p.property).2.1.trans hBM)⟩,
    (hP p.val p.property).1⟩

theorem mediumMatrix_eq_submatrix (M lo B : ℕ) (P : Finset ℕ) (hBM : B ≤ M)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < 11 * p) :
    mediumMatrix lo B P = (valuationMatrix M (lo + 1) B).submatrix id (mediumColumn M B P hBM hP) := by
  ext i p
  simp [mediumMatrix,valuationMatrix,vertex,mediumColumn,Matrix.submatrix]

/-- Exact positive-part quotient bound, with every row and column hypothesis discharged. -/
theorem microscopic_rank_private_incidence {M lo B : ℕ} (P : Finset ℕ)
    (hlo : 0 < lo) (hB : 1332 ≤ B) (htop : lo + B ≤ B ^ 2 + B + 1)
    (hcut : lo + B ≤ M + 1)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < 11 * p) :
    ((largePrimeFactors B lo B).card : ℝ) +
      ((oddIncidences lo B P).card - (largePrimeFactors B lo B).card : ℕ) / 12 ≤
        ((valuationMatrix M (lo + 1) B).rank : ℝ) := by
  have hBM : B ≤ M := by omega
  have h := private_incidence_rank_twelfth (valuationMatrix M (lo + 1) B) (privateRows lo B)
    (mediumColumn M B P hBM hP)
    (private_coordinate_mem_range hlo htop hcut)
  rw [← mediumMatrix_eq_submatrix M lo B P hBM hP] at h
  specialize h (medium_row_weight_le_two hlo hB htop hP)
    (medium_column_weight_le_eleven (by omega) (fun p hp => (hP p hp).2.2))
    (medium_rows_simple hB hP) (private_medium_row_weight_le_one hlo hB htop hP)
  rw [card_privateRows hlo htop,incidenceMass_mediumMatrix] at h
  exact h

/-- The convenient linear form keeps both prime counts, even when E is smaller than t. -/
theorem microscopic_rank_linear_budget {M lo B : ℕ} (P : Finset ℕ)
    (hlo : 0 < lo) (hB : 1332 ≤ B) (htop : lo + B ≤ B ^ 2 + B + 1)
    (hcut : lo + B ≤ M + 1)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < 11 * p) :
    11 * ((largePrimeFactors B lo B).card : ℝ) + ((oddIncidences lo B P).card : ℝ) ≤
      12 * ((valuationMatrix M (lo + 1) B).rank : ℝ) := by
  have h := microscopic_rank_private_incidence P hlo hB htop hcut hP
  have hn : (oddIncidences lo B P).card ≤ (largePrimeFactors B lo B).card +
      ((oddIncidences lo B P).card - (largePrimeFactors B lo B).card) := by omega
  have hr : ((oddIncidences lo B P).card : ℝ) ≤ ((largePrimeFactors B lo B).card : ℝ) +
      ((oddIncidences lo B P).card - (largePrimeFactors B lo B).card : ℕ) := by exact_mod_cast hn
  nlinarith

/-- The paper's complete medium-prime interval, not an abstract incidence hypothesis. -/
theorem microscopic_rank_medium_primes {M lo B : ℕ}
    (hlo : 0 < lo) (hB : 1332 ≤ B) (htop : lo + B ≤ B ^ 2 + B + 1)
    (hcut : lo + B ≤ M + 1) :
    11 * ((largePrimeFactors B lo B).card : ℝ) +
      ((oddIncidences lo B (mediumPrimes B)).card : ℝ) ≤
        12 * ((valuationMatrix M (lo + 1) B).rank : ℝ) :=
  microscopic_rank_linear_budget (mediumPrimes B) hlo hB htop hcut (fun _ hp => mem_mediumPrimes.mp hp)

end
end PaperC.V282.MicroscopicIncidenceRank
