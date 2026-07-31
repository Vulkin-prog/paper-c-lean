import PaperC.Combinatorics.CertificateLemmaSevenOne
import PaperC.Combinatorics.CertificatePopulationCover
import PaperC.Combinatorics.ResidualMasses
import PaperC.Combinatorics.SigmaZeroAmbientCertificate

set_option maxHeartbeats 1800000

/-!
# The fixed-size `σ = 0`, `P# ≤ N` population cover

This module applies the pair-independent ambient certificate to an actual
population of dyadic pairs.  For each fixed residual component count `r`, it
filters the `σ = 0`, small-product pairs, assigns to each pair its canonical
ambient certificate, and invokes the membership-dependent two-dimensional
cover.  The result is then composed directly with the bounded-cell form of
Lemma 7.1.
-/

namespace PaperC
namespace PropositionSevenThreeSigmaZeroCover

open CanonicalResidualComponents
open RationalMassFinite
open ResidualComponentCounts
open SigmaZeroAmbientCertificate
open scoped BigOperators

noncomputable section

/-- The subtype-level fixed-size `σ=0`, `P#≤N` population. -/
noncomputable def sigmaZeroSmallProductSubtypePairs
    (N A L r : ℕ) (hN : 2 ≤ N) :
    Finset (ResidualMasses.SeparatedDyadicPair N L) := by
  classical
  exact Finset.univ.filter fun pair ↦
    ResidualMasses.pairSigma A pair = 0 ∧
      CanonicalResidualPrimeProductAtMost
        (A := A) (L := L)
        (show 1 ≤ pair.1.1 by
          have hx := (ResidualMasses.pair_coordinates_two_le hN pair).1
          omega)
        (show 1 ≤ pair.1.2 by
          have hy := (ResidualMasses.pair_coordinates_two_le hN pair).2
          omega)
        N ∧
      canonicalResidualComponentCount
        A pair.1.1 pair.1.2 L = r

/-- The same population as a finset of actual ordered pairs. -/
noncomputable def sigmaZeroSmallProductPairs
    (N A L r : ℕ) (hN : 2 ≤ N) :
    Finset (ℕ × ℕ) :=
  (sigmaZeroSmallProductSubtypePairs N A L r hN).image Subtype.val

theorem mem_sigmaZeroSmallProductSubtypePairs
    {N A L r : ℕ} {hN : 2 ≤ N}
    {pair : ResidualMasses.SeparatedDyadicPair N L} :
    pair ∈ sigmaZeroSmallProductSubtypePairs N A L r hN ↔
      ResidualMasses.pairSigma A pair = 0 ∧
        CanonicalResidualPrimeProductAtMost
          (A := A) (L := L)
          (show 1 ≤ pair.1.1 by
            have hx := (ResidualMasses.pair_coordinates_two_le hN pair).1
            omega)
          (show 1 ≤ pair.1.2 by
            have hy := (ResidualMasses.pair_coordinates_two_le hN pair).2
            omega)
          N ∧
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L = r := by
  simp [sigmaZeroSmallProductSubtypePairs]

/-- Every value in the population is a separated dyadic pair. -/
theorem mem_sigmaZeroSmallProductPairs_separated
    {N A L r : ℕ} {hN : 2 ≤ N}
    {pair : ℕ × ℕ}
    (hpair : pair ∈ sigmaZeroSmallProductPairs N A L r hN) :
    pair ∈ separatedDyadicPairs N L := by
  rw [sigmaZeroSmallProductPairs, Finset.mem_image] at hpair
  obtain ⟨z, _hz, rfl⟩ := hpair
  exact z.2

/-- Every value in the fixed-size population has component count `r`. -/
theorem mem_sigmaZeroSmallProductPairs_componentCount
    {N A L r : ℕ} {hN : 2 ≤ N}
    {pair : ℕ × ℕ}
    (hpair : pair ∈ sigmaZeroSmallProductPairs N A L r hN) :
    canonicalResidualComponentCount A pair.1 pair.2 L = r := by
  rw [sigmaZeroSmallProductPairs, Finset.mem_image] at hpair
  obtain ⟨z, hz, rfl⟩ := hpair
  exact (mem_sigmaZeroSmallProductSubtypePairs.mp hz).2.2

/-- Every value in the population lies in the small-product branch. -/
theorem mem_sigmaZeroSmallProductPairs_smallProduct
    {N A L r : ℕ} {hN : 2 ≤ N}
    {pair : ℕ × ℕ}
    (hpair : pair ∈ sigmaZeroSmallProductPairs N A L r hN) :
    CanonicalResidualPrimeProductAtMost
      (A := A) (L := L)
      (pair_left_one_le hN
        (mem_sigmaZeroSmallProductPairs_separated hpair))
      (pair_right_one_le hN
        (mem_sigmaZeroSmallProductPairs_separated hpair))
      N := by
  rw [sigmaZeroSmallProductPairs, Finset.mem_image] at hpair
  obtain ⟨z, hz, rfl⟩ := hpair
  have hzData := mem_sigmaZeroSmallProductSubtypePairs.mp hz
  simpa only using hzData.2.1

/--
Assign to each population member its ambient certificate, transported along
the equality `c#=r`.
-/
noncomputable def sigmaZeroAmbientAssignment
    {N A L r : ℕ} (hN : 2 ≤ N)
    (pair : ℕ × ℕ)
    (hpair : pair ∈ sigmaZeroSmallProductPairs N A L r hN) :
    CRT.UnorderedCertificate
      (Finset.univ : Finset (AmbientLabeledCell N L)) r := by
  have hsep := mem_sigmaZeroSmallProductPairs_separated hpair
  have hr := mem_sigmaZeroSmallProductPairs_componentCount hpair
  rw [← hr]
  exact ambientCertificate (A := A) hN hsep

/--
The dependent ambient assignment is admissible for every population member.
-/
theorem sigmaZeroAmbientAssignment_admissible
    {N A L r : ℕ} (hN : 2 ≤ N)
    (pair : ℕ × ℕ)
    (hpair : pair ∈ sigmaZeroSmallProductPairs N A L r hN) :
    CRT.CertificateAdmissible ambientModulus N
      (sigmaZeroAmbientAssignment hN pair hpair) := by
  have hsep := mem_sigmaZeroSmallProductPairs_separated hpair
  have hr := mem_sigmaZeroSmallProductPairs_componentCount hpair
  have hsmall := mem_sigmaZeroSmallProductPairs_smallProduct hpair
  subst r
  simpa [sigmaZeroAmbientAssignment] using
    (ambientCertificate_admissible_iff hN hsep).2 hsmall

/-- Every pair is contained in the solution rectangle of its assignment. -/
theorem sigmaZeroAmbientAssignment_solution
    {N A L r : ℕ} (hN : 2 ≤ N)
    (pair : ℕ × ℕ)
    (hpair : pair ∈ sigmaZeroSmallProductPairs N A L r hN) :
    pair ∈
      CRT.certificatePairSolutions
        ambientLeftResidue ambientRightResidue ambientModulus
        N (2 * N) N (2 * N)
        (sigmaZeroAmbientAssignment hN pair hpair) := by
  have hsep := mem_sigmaZeroSmallProductPairs_separated hpair
  have hr := mem_sigmaZeroSmallProductPairs_componentCount hpair
  subst r
  simpa [sigmaZeroAmbientAssignment,
    CRT.certificatePairSolutions] using
    pair_mem_ambientCertificateSolutions
      (A := A) hN hsep
      (mem_separatedDyadicPairs.mp hsep).1
      (mem_separatedDyadicPairs.mp hsep).2.1

/-- The exact dependent population-cover lower bound at fixed `r`. -/
theorem four_pow_mul_card_le_ambientPairSolutionMass
    {N A L r : ℕ} (hN : 2 ≤ N) :
    (4 : ℚ) ^ r *
        ((sigmaZeroSmallProductPairs N A L r hN).card : ℚ) ≤
      CRT.admissibleCertificatePairSolutionMass
        (Finset.univ : Finset (AmbientLabeledCell N L)) r
        ambientLeftResidue ambientRightResidue ambientModulus
        N (2 * N) N (2 * N) N 4 := by
  exact
    CRT.pow_mul_card_population_le_admissibleCertificatePairSolutionMass'
      (sigmaZeroSmallProductPairs N A L r hN)
      (sigmaZeroAmbientAssignment hN)
      ambientLeftResidue ambientRightResidue ambientModulus
      N (2 * N) N (2 * N) N 4 (by norm_num)
      (sigmaZeroAmbientAssignment_admissible hN)
      (sigmaZeroAmbientAssignment_solution hN)

/--
Lemma 7.1 specialized to the fixed ambient cell family.  Keeping the
manuscript's unnormalized `((1+1)N)²` factor here avoids asking `simp` to
normalize the whole certificate-mass expression.
-/
theorem ambientPairSolutionMass_le
    {N L r : ℕ} :
    CRT.admissibleCertificatePairSolutionMass
        (Finset.univ : Finset (AmbientLabeledCell N L)) r
        ambientLeftResidue ambientRightResidue ambientModulus
        N (2 * N) N (2 * N) N 4 ≤
      ((((1 + 1) * N : ℕ) : ℚ) ^ 2) *
        (((4 : ℚ) * ((L + 1) ^ 2 : ℕ) *
            ∑ p : AmbientPrime N L,
              1 / (ambientPrimeModulus p : ℚ) ^ 2) ^ r /
          r.factorial) := by
  change
    CRT.admissibleCertificatePairSolutionMass
        (Finset.univ : Finset (AmbientLabeledCell N L)) r
        ambientLeftResidue ambientRightResidue
        (CRT.labeledCellModulus (ambientCells N L) ambientPrimeModulus)
        N (2 * N) N (2 * N) N 4 ≤ _
  exact
    CRT.labeledCell_admissibleCertificatePairSolutionMass_le
      (ambientCells N L) r
      ambientLeftResidue ambientRightResidue
      ambientPrimeModulus ((L + 1) ^ 2)
      (fun p ↦ (mem_ambientPrimes.mp p.2).1)
      (fun p ↦ by simp only [card_ambientCells, le_refl])
      N (2 * N) N (2 * N) 1 N
      (by omega) (by omega) (by omega) (by omega)
      4 (by norm_num)

/--
Fixed-size `σ=0` cover followed by the two-dimensional bound of Lemma 7.1.
-/
theorem four_pow_mul_card_sigmaZeroSmallProductPairs_le
    {N A L r : ℕ} (hN : 2 ≤ N) :
    (4 : ℚ) ^ r *
        ((sigmaZeroSmallProductPairs N A L r hN).card : ℚ) ≤
      (((2 * N : ℕ) : ℚ) ^ 2) *
        (((4 : ℚ) * ((L + 1) ^ 2 : ℕ) *
            ∑ p : AmbientPrime N L,
              1 / (ambientPrimeModulus p : ℚ) ^ 2) ^ r /
          r.factorial) := by
  refine
    (four_pow_mul_card_le_ambientPairSolutionMass
      (A := A) (L := L) (r := r) hN).trans ?_
  simpa only [one_add_one_eq_two] using
    (ambientPairSolutionMass_le (N := N) (L := L) (r := r))

/-- The finite-size sum of the specialized ambient Lemma 7.1 bounds. -/
theorem sum_ambientPairSolutionMass_le
    {N L R : ℕ} :
    (∑ r ∈ Finset.range R,
        CRT.admissibleCertificatePairSolutionMass
          (Finset.univ : Finset (AmbientLabeledCell N L)) r
          ambientLeftResidue ambientRightResidue ambientModulus
          N (2 * N) N (2 * N) N 4) ≤
      ((((1 + 1) * N : ℕ) : ℚ) ^ 2) *
        ∑ r ∈ Finset.range R,
          (((4 : ℚ) * ((L + 1) ^ 2 : ℕ) *
              ∑ p : AmbientPrime N L,
                1 / (ambientPrimeModulus p : ℚ) ^ 2) ^ r /
            r.factorial) := by
  change
    (∑ r ∈ Finset.range R,
        CRT.admissibleCertificatePairSolutionMass
          (Finset.univ : Finset (AmbientLabeledCell N L)) r
          ambientLeftResidue ambientRightResidue
          (CRT.labeledCellModulus (ambientCells N L) ambientPrimeModulus)
          N (2 * N) N (2 * N) N 4) ≤ _
  exact
    CRT.sum_labeledCell_admissibleCertificatePairSolutionMass_le
      (ambientCells N L) R
      ambientLeftResidue ambientRightResidue
      ambientPrimeModulus ((L + 1) ^ 2)
      (fun p ↦ (mem_ambientPrimes.mp p.2).1)
      (fun p ↦ by simp only [card_ambientCells, le_refl])
      N (2 * N) N (2 * N) 1 N
      (by omega) (by omega) (by omega) (by omega)
      4 (by norm_num)

/--
Summed fixed-size cover over the full vertex-budget range `r < L+2`.
-/
theorem sum_four_pow_mul_card_sigmaZeroSmallProductPairs_le
    {N A L : ℕ} (hN : 2 ≤ N) :
    (∑ r ∈ Finset.range (L + 2),
        (4 : ℚ) ^ r *
          ((sigmaZeroSmallProductPairs N A L r hN).card : ℚ)) ≤
      (((2 * N : ℕ) : ℚ) ^ 2) *
        ∑ r ∈ Finset.range (L + 2),
          (((4 : ℚ) * ((L + 1) ^ 2 : ℕ) *
              ∑ p : AmbientPrime N L,
                1 / (ambientPrimeModulus p : ℚ) ^ 2) ^ r /
            r.factorial) := by
  calc
    (∑ r ∈ Finset.range (L + 2),
        (4 : ℚ) ^ r *
          ((sigmaZeroSmallProductPairs N A L r hN).card : ℚ)) ≤
        ∑ r ∈ Finset.range (L + 2),
          CRT.admissibleCertificatePairSolutionMass
            (Finset.univ : Finset (AmbientLabeledCell N L)) r
            ambientLeftResidue ambientRightResidue ambientModulus
            N (2 * N) N (2 * N) N 4 := by
      apply Finset.sum_le_sum
      intro r _hr
      exact
        four_pow_mul_card_le_ambientPairSolutionMass
          (A := A) (L := L) hN
    _ ≤
        (((2 * N : ℕ) : ℚ) ^ 2) *
          ∑ r ∈ Finset.range (L + 2),
            (((4 : ℚ) * ((L + 1) ^ 2 : ℕ) *
                ∑ p : AmbientPrime N L,
                  1 / (ambientPrimeModulus p : ℚ) ^ 2) ^ r /
              r.factorial) := by
      simpa only [one_add_one_eq_two] using
        (sum_ambientPairSolutionMass_le
          (N := N) (L := L) (R := L + 2))

end

end PropositionSevenThreeSigmaZeroCover
end PaperC
