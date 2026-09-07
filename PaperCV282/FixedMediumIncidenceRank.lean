import PaperCV282.FixedMediumGeometry
import PaperCV282.FixedMediumLayers
import PaperCV282.MicroscopicIncidenceRank

/-! # The literal finite first inequality of companion E.4

For every fixed K, all matrix hypotheses are discharged on the actual
medium-prime interval. The positive part retains exactly the loss of at
most one incidence per private row, and the start matrix loses at most
one further constant direction. No asymptotic or literature premise is used.
-/
namespace PaperC.V282.FixedMediumIncidenceRank

open Matrix Finset SimpleIncidenceModel PrivateIncidenceBudget
open MediumPrimeGeometry MicroscopicPrivatePrimes MicroscopicValuationMatrix
open MediumMultipleCounts PolynomialZoneLargePrimes WindowValues

noncomputable section

def mediumColumn (M B : ℕ) (P : Finset ℕ) (hBM : B ≤ M)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B) (p : P) : PrimeUpTo M :=
  ⟨⟨p.val, Nat.lt_succ_of_le ((hP p.val p.property).2.trans hBM)⟩,
    (hP p.val p.property).1⟩

theorem mediumMatrix_eq_submatrix (M lo B : ℕ) (P : Finset ℕ) (hBM : B ≤ M)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B) :
    mediumMatrix lo B P = (valuationMatrix M (lo + 1) B).submatrix id
      (mediumColumn M B P hBM hP) := by
  ext i p
  simp [mediumMatrix,valuationMatrix,vertex,mediumColumn,Matrix.submatrix]

theorem value_rank_private_incidence {K M lo B : ℕ} (P : Finset ℕ)
    (hK : 0 < K) (hlo : 0 < lo) (hB : 2 * (K ^ 3 + K ^ 2) + 1 ≤ B)
    (htop : lo + B ≤ B ^ 2 + B + 1) (hcut : lo + B ≤ M + 1)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ B ∧ B < K * p) :
    ((largePrimeFactors B lo B).card : ℝ) +
      ((oddIncidences lo B P).card - (largePrimeFactors B lo B).card : ℕ) / (K + 1 : ℝ) ≤
        ((valuationMatrix M (lo + 1) B).rank : ℝ) := by
  have hBM : B ≤ M := by omega
  have hP' : ∀ p ∈ P, p.Prime ∧ p ≤ B := fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩
  have h := private_incidence_rank_real (valuationMatrix M (lo + 1) B) (privateRows lo B)
    (mediumColumn M B P hBM hP') K (private_coordinate_mem_range hlo htop hcut)
  rw [← mediumMatrix_eq_submatrix M lo B P hBM hP'] at h
  specialize h (FixedMediumGeometry.medium_row_weight_le_two hlo hB htop hP)
    (FixedMediumGeometry.medium_column_weight_le hK (by omega) (fun p hp => (hP p hp).2.2))
    (FixedMediumGeometry.medium_rows_simple hB hP)
    (FixedMediumGeometry.private_medium_row_weight_le_one hlo hB htop hP)
  rw [card_privateRows hlo htop,MicroscopicIncidenceRank.incidenceMass_mediumMatrix] at h
  exact h

theorem nat_sub_cast_eq_positive_part (E t : ℕ) :
    ((E - t : ℕ) : ℝ) = max ((E : ℝ) - t) 0 := by
  by_cases h : t ≤ E
  · rw [Nat.cast_sub h, max_eq_left]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have h' : E ≤ t := by omega
    rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero, max_eq_right]
    exact sub_nonpos.mpr (by exact_mod_cast h')

/-- Exact private-rank plus positive-part incidence inequality for every fixed K. -/
theorem equation_E_four_intermediate_values {K M lo B : ℕ}
    (hK : 2 ≤ K) (hlo : 0 < lo) (hB : 2 * (K ^ 3 + K ^ 2) + 1 ≤ B)
    (htop : lo + B ≤ B ^ 2 + B + 1) (hcut : lo + B ≤ M + 1) :
    ((largePrimeFactors B lo B).card : ℝ) +
      max (((oddIncidences lo B (FixedMediumLayers.mediumPrimes K B)).card : ℝ) -
        (largePrimeFactors B lo B).card) 0 / (K + 1 : ℝ) ≤
      ((valuationMatrix M (lo + 1) B).rank : ℝ) := by
  have h := value_rank_private_incidence (FixedMediumLayers.mediumPrimes K B)
    (by omega : 0 < K) hlo hB htop hcut
    (fun p hp => (FixedMediumLayers.mem_mediumPrimes (by omega : 0 < K)).mp hp)
  rwa [nat_sub_cast_eq_positive_part] at h

/-- The first printed inequality of E.4 for the actual start matrix,
including the final loss of one constant direction. The threshold precedes
both the window position and the ambient prime cylinder. -/
theorem equation_E_four_intermediate_start {K M lo B : ℕ}
    (hK : 2 ≤ K) (hlo : 0 < lo) (hB : 2 * (K ^ 3 + K ^ 2) + 1 ≤ B)
    (htop : lo + B ≤ B ^ 2 + B + 1) (hcut : lo + B ≤ M + 1) :
    ((largePrimeFactors B lo B).card : ℝ) +
      max (((oddIncidences lo B (FixedMediumLayers.mediumPrimes K B)).card : ℝ) -
        (largePrimeFactors B lo B).card) 0 / (K + 1 : ℝ) - 1 ≤
      ((startMatrix M (lo + 1) (B - 1)).rank : ℝ) := by
  have hv := equation_E_four_intermediate_values hK hlo hB htop hcut
  have hs := valuation_rank_le_start_rank_add_one (M := M) (x := lo + 1) (L := B - 1)
    (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ B)] at hs
  have hsR : ((valuationMatrix M (lo + 1) B).rank : ℝ) ≤
      ((startMatrix M (lo + 1) (B - 1)).rank : ℝ) + 1 := by exact_mod_cast hs
  linarith

end
end PaperC.V282.FixedMediumIncidenceRank
