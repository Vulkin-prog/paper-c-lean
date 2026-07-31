import PaperC.Combinatorics.CanonicalResidualAmbientCertificate
import PaperC.Combinatorics.CertificateLemmaSevenOne
import PaperC.Arithmetic.ResidualVertexPrimeCellCount
import PaperC.Analysis.ExponentialSeriesMajorant

set_option maxHeartbeats 1800000

/-!
# Effective fixed-channel certificate mass

This file combines the ambient canonical certificates with Lemmas 7.1 and
7.2.  It first identifies the one-dimensional local cell weight of the
ambient family with `residualPrimeMass`, then derives the explicit
fixed-certificate-size estimate with base

`3584 (L+1) / log₂(L+1)`.
-/

namespace PaperC
namespace CanonicalResidualComponents

open scoped BigOperators
open ResidualChannelLemmaSevenTwo

noncomputable section

/--
The local one-dimensional weight of the vertex-cell ambient family is
exactly the residual prime mass from Lemma 7.2.
-/
theorem sum_canonicalResidualAmbientCells_card_div_eq_residualPrimeMass
    (L a b : ℕ) (h : ℤ) :
    (∑ p : CanonicalResidualAmbientPrime L a b,
        ((canonicalResidualAmbientCells L a b h p).card : ℚ) /
          (canonicalResidualAmbientPrimeModulus p : ℚ)) =
      residualPrimeMass L a b h := by
  classical
  unfold residualPrimeMass
  conv_rhs => rw [← Finset.sum_attach]
  rw [Finset.univ_eq_attach]
  apply Finset.sum_congr rfl
  intro p _hp
  simp only [canonicalResidualAmbientCells,
    canonicalResidualAmbientPrimeModulus]
  rw [residualVertexPrimeCells_card_eq_residualPrimeCells_card]

/--
Effective fixed-size one-dimensional certificate-mass estimate for an active
nontrivial channel.  The constant is `4 * 896`, because Lemma 7.1 is applied
with certificate weight `u=4`.
-/
theorem canonicalResidualAmbient_admissibleCertificateSolutionMass_le
    {L a b N r : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hqTwo : 2 ≤ Nat.max a b)
    (hB : 4 ≤ L + 1)
    (hm : 2 ≤ (channelCells L a b h).card) :
    CRT.admissibleCertificateSolutionMass
        (Finset.univ :
          Finset (CanonicalResidualAmbientCell L a b h))
        r
        canonicalResidualAmbientLeftResidue
        canonicalResidualAmbientCellModulus
        N (2 * N) N 4 ≤
      (((2 * N : ℕ) : ℚ) *
        (((3584 : ℚ) * (L + 1 : ℚ) /
            (Nat.log 2 (L + 1) : ℚ)) ^ r /
          (r.factorial : ℚ))) := by
  have hlemma :=
    CRT.labeledCell_admissibleCertificateSolutionMass_le
      (canonicalResidualAmbientCells L a b h) r
      canonicalResidualAmbientLeftResidue
      canonicalResidualAmbientPrimeModulus
      canonicalResidualAmbientPrimeModulus_prime
      N (2 * N) 1 N
      (by omega) (by omega)
      4 (by norm_num)
  rw [sum_canonicalResidualAmbientCells_card_div_eq_residualPrimeMass]
    at hlemma
  have hlocal :
      CRT.admissibleCertificateSolutionMass
          (Finset.univ :
            Finset (CanonicalResidualAmbientCell L a b h))
          r
          canonicalResidualAmbientLeftResidue
          canonicalResidualAmbientCellModulus
          N (2 * N) N 4 ≤
        (((2 * N : ℕ) : ℚ) *
          (((4 : ℚ) * residualPrimeMass L a b h) ^ r /
            (r.factorial : ℚ))) := by
    simpa [canonicalResidualAmbientCellModulus] using hlemma
  have hmass :=
    ResidualChannelLemmaSevenTwo.residualPrimeMass_le
      ha hb hab hqTwo hB hm
  have hmassNonneg : 0 ≤ residualPrimeMass L a b h := by
    unfold residualPrimeMass
    apply Finset.sum_nonneg
    intro p hp
    apply div_nonneg
    · positivity
    · have hpPrime := (mem_residualPrimeRange.mp hp).1
      exact_mod_cast hpPrime.pos.le
  have hbase :
      (4 : ℚ) * residualPrimeMass L a b h ≤
        (3584 : ℚ) * (L + 1 : ℚ) /
          (Nat.log 2 (L + 1) : ℚ) := by
    calc
      (4 : ℚ) * residualPrimeMass L a b h ≤
          4 * (896 * (L + 1 : ℚ) /
            (Nat.log 2 (L + 1) : ℚ)) :=
        mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ = (3584 : ℚ) * (L + 1 : ℚ) /
          (Nat.log 2 (L + 1) : ℚ) := by ring
  have hpow :
      ((4 : ℚ) * residualPrimeMass L a b h) ^ r ≤
        ((3584 : ℚ) * (L + 1 : ℚ) /
          (Nat.log 2 (L + 1) : ℚ)) ^ r :=
    pow_le_pow_left₀
      (mul_nonneg (by norm_num) hmassNonneg) hbase r
  exact hlocal.trans
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hpow (by positivity))
      (by positivity))

/-- Sum of the preceding estimate over all certificate sizes `r < R`. -/
theorem sum_canonicalResidualAmbient_admissibleCertificateSolutionMass_le
    {L a b N R : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hqTwo : 2 ≤ Nat.max a b)
    (hB : 4 ≤ L + 1)
    (hm : 2 ≤ (channelCells L a b h).card) :
    (∑ r ∈ Finset.range R,
        CRT.admissibleCertificateSolutionMass
          (Finset.univ :
            Finset (CanonicalResidualAmbientCell L a b h))
          r
          canonicalResidualAmbientLeftResidue
          canonicalResidualAmbientCellModulus
          N (2 * N) N 4) ≤
      (((2 * N : ℕ) : ℚ) *
        ∑ r ∈ Finset.range R,
          ((3584 : ℚ) * (L + 1 : ℚ) /
              (Nat.log 2 (L + 1) : ℚ)) ^ r /
            (r.factorial : ℚ)) := by
  calc
    (∑ r ∈ Finset.range R,
        CRT.admissibleCertificateSolutionMass
          (Finset.univ :
            Finset (CanonicalResidualAmbientCell L a b h))
          r
          canonicalResidualAmbientLeftResidue
          canonicalResidualAmbientCellModulus
          N (2 * N) N 4) ≤
        ∑ r ∈ Finset.range R,
          (((2 * N : ℕ) : ℚ) *
            (((3584 : ℚ) * (L + 1 : ℚ) /
                (Nat.log 2 (L + 1) : ℚ)) ^ r /
              (r.factorial : ℚ))) := by
      apply Finset.sum_le_sum
      intro r _hr
      exact
        canonicalResidualAmbient_admissibleCertificateSolutionMass_le
          ha hb hab hqTwo hB hm
    _ = (((2 * N : ℕ) : ℚ) *
        ∑ r ∈ Finset.range R,
          ((3584 : ℚ) * (L + 1 : ℚ) /
              (Nat.log 2 (L + 1) : ℚ)) ^ r /
            (r.factorial : ℚ)) := by
      rw [Finset.mul_sum]

/--
Real-exponential form of the finite fixed-channel mass bound.
-/
theorem sum_canonicalResidualAmbient_admissibleCertificateSolutionMass_cast_le_exp
    {L a b N R : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hqTwo : 2 ≤ Nat.max a b)
    (hB : 4 ≤ L + 1)
    (hm : 2 ≤ (channelCells L a b h).card) :
    ((∑ r ∈ Finset.range R,
        CRT.admissibleCertificateSolutionMass
          (Finset.univ :
            Finset (CanonicalResidualAmbientCell L a b h))
          r
          canonicalResidualAmbientLeftResidue
          canonicalResidualAmbientCellModulus
          N (2 * N) N 4 : ℚ) : ℝ) ≤
      ((((2 * N : ℕ) : ℚ) : ℝ) *
        Real.exp
          (((3584 : ℚ) * (L + 1 : ℚ) /
            (Nat.log 2 (L + 1) : ℚ) : ℚ) : ℝ)) := by
  let base : ℚ :=
    (3584 : ℚ) * (L + 1 : ℚ) /
      (Nat.log 2 (L + 1) : ℚ)
  have hfinite :=
    sum_canonicalResidualAmbient_admissibleCertificateSolutionMass_le
      (N := N) (R := R) ha hb hab hqTwo hB hm
  have hfiniteCast :
      ((∑ r ∈ Finset.range R,
          CRT.admissibleCertificateSolutionMass
            (Finset.univ :
              Finset (CanonicalResidualAmbientCell L a b h))
            r
            canonicalResidualAmbientLeftResidue
            canonicalResidualAmbientCellModulus
            N (2 * N) N 4 : ℚ) : ℝ) ≤
        ((((2 * N : ℕ) : ℚ) *
          ∑ r ∈ Finset.range R,
            base ^ r / (r.factorial : ℚ) : ℚ) : ℝ) := by
    dsimp [base]
    exact_mod_cast hfinite
  have hbase : 0 ≤ base := by
    dsimp [base]
    apply div_nonneg
    · positivity
    · exact_mod_cast Nat.zero_le (Nat.log 2 (L + 1))
  calc
    ((∑ r ∈ Finset.range R,
        CRT.admissibleCertificateSolutionMass
          (Finset.univ :
            Finset (CanonicalResidualAmbientCell L a b h))
          r
          canonicalResidualAmbientLeftResidue
          canonicalResidualAmbientCellModulus
          N (2 * N) N 4 : ℚ) : ℝ) ≤
        ((((2 * N : ℕ) : ℚ) : ℝ) *
          (((∑ r ∈ Finset.range R,
              base ^ r / (r.factorial : ℚ) : ℚ)) : ℝ)) := by
      simpa using hfiniteCast
    _ ≤ ((((2 * N : ℕ) : ℚ) : ℝ) *
          Real.exp (base : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact ratCast_sum_range_pow_div_factorial_le_exp
          base hbase R
      · positivity
    _ = ((((2 * N : ℕ) : ℚ) : ℝ) *
        Real.exp
          (((3584 : ℚ) * (L + 1 : ℚ) /
            (Nat.log 2 (L + 1) : ℚ) : ℚ) : ℝ)) := by
      rfl

end

end CanonicalResidualComponents
end PaperC
