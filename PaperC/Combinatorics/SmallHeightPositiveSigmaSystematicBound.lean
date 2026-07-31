import PaperC.Combinatorics.SmallHeightTauEnvelope

/-!
# The systematic positive-sigma bound in the small-height sector

This module isolates the finite systematic part of Proposition 7.4.  On the
positive-`σ` branch,

`4^σ ≤ 2 (4^σ - 1)`,

and the latter weights form a subsum of the full base-four rational mass.
The residual factor is then bounded pointwise by the finite small-height
envelope for `τ`.
-/

namespace PaperC
namespace SmallHeightPositiveSigmaSystematicBound

open Affine
open RationalMassFinite
open ResidualMasses
open SmallHeightLargeProductPairs
open SmallHeightResidualComponentEnvelope
open SmallHeightTauEnvelope

noncomputable section

/--
The systematic base-four mass of any finite family of separated-pair
subtypes is bounded by the full rational mass after replacing `4^σ` by
`4^σ - 1`.
-/
theorem sum_four_pow_pairSigma_sub_one_le_rationalMass
    {N A L : ℕ}
    (population : Finset (SeparatedDyadicPair N L)) :
    (∑ pair ∈ population,
        (4 ^ pairSigma A pair - 1)) ≤
      rationalMass N A L 4 := by
  classical
  let values : Finset (ℕ × ℕ) :=
    population.image Subtype.val
  have hvalues :
      values ⊆ separatedDyadicPairs N L := by
    intro pair hpair
    dsimp only [values] at hpair
    rw [Finset.mem_image] at hpair
    obtain ⟨z, _hz, rfl⟩ := hpair
    exact z.2
  have hsumImage :
      (∑ pair ∈ values,
          (4 ^ canonicalPairSigma A L pair.1 pair.2 - 1)) =
        ∑ pair ∈ population,
          (4 ^ pairSigma A pair - 1) := by
    unfold values
    rw [Finset.sum_image]
    · rfl
    · intro pair _hpair other _hother hval
      exact Subtype.val_injective hval
  calc
    (∑ pair ∈ population,
        (4 ^ pairSigma A pair - 1)) =
        ∑ pair ∈ values,
          (4 ^ canonicalPairSigma A L pair.1 pair.2 - 1) :=
      hsumImage.symm
    _ ≤
        ∑ pair ∈ separatedDyadicPairs N L,
          (4 ^ canonicalPairSigma A L pair.1 pair.2 - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hvalues
      intro pair _hpair _hnot
      exact Nat.zero_le _
    _ = rationalMass N A L 4 := by
      rfl

/-- For a positive exponent, `4^σ` is at most twice `4^σ - 1`. -/
theorem four_pow_le_two_mul_four_pow_sub_one
    {σ : ℕ} (hσ : 0 < σ) :
    4 ^ σ ≤ 2 * (4 ^ σ - 1) := by
  have hpow :
      4 ^ 1 ≤ 4 ^ σ :=
    Nat.pow_le_pow_right (by norm_num) hσ
  norm_num at hpow
  omega

/--
The systematic fourth-power sum on the positive branch is at most twice the
full base-four rational mass.
-/
theorem sum_four_pow_pairSigma_positive_le_two_mul_rationalMass
    {N A L : ℕ} (hN : 2 ≤ N) :
    (∑ pair ∈
        positiveSigmaSmallHeightLargeProductPairs N A L hN,
        4 ^ pairSigma A pair) ≤
      2 * rationalMass N A L 4 := by
  calc
    (∑ pair ∈
        positiveSigmaSmallHeightLargeProductPairs N A L hN,
        4 ^ pairSigma A pair) ≤
        ∑ pair ∈
          positiveSigmaSmallHeightLargeProductPairs N A L hN,
          2 * (4 ^ pairSigma A pair - 1) := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact
        four_pow_le_two_mul_four_pow_sub_one
          (mem_positiveSigmaSmallHeightLargeProductPairs.mp hpair).2
    _ =
        2 *
          ∑ pair ∈
            positiveSigmaSmallHeightLargeProductPairs N A L hN,
            (4 ^ pairSigma A pair - 1) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * rationalMass N A L 4 :=
      Nat.mul_le_mul_left 2
        (sum_four_pow_pairSigma_sub_one_le_rationalMass
          (positiveSigmaSmallHeightLargeProductPairs N A L hN))

/--
For a small-height pair, its quadratic residual weight is bounded by the
uniform residual envelope times its systematic fourth-power weight.
-/
theorem quadraticResidualWeight_le_tauEnvelope_mul_four_pow_pairSigma_of_mem
    {N A L : ℕ} {hN : 2 ≤ N}
    (hB : 8 ≤ L + 1)
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ smallHeightLargeProductPairs N A L hN) :
    quadraticResidualWeight A hN pair ≤
      4 ^ smallHeightTauEnvelope A N L *
        4 ^ pairSigma A pair := by
  have htau :
      4 ^ pairTau A hN pair ≤
        4 ^ smallHeightTauEnvelope A N L :=
    four_pow_pairTau_le_four_pow_smallHeightTauEnvelope_of_mem
      hB hpair
  unfold quadraticResidualWeight
  calc
    4 ^ pairSigma A pair *
          (4 ^ pairTau A hN pair - 1) ≤
        4 ^ pairSigma A pair *
          4 ^ pairTau A hN pair :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤
        4 ^ pairSigma A pair *
          4 ^ smallHeightTauEnvelope A N L :=
      Nat.mul_le_mul_left _ htau
    _ =
        4 ^ smallHeightTauEnvelope A N L *
          4 ^ pairSigma A pair := by
      rw [Nat.mul_comm]

/--
Before invoking the rational-mass estimate, the positive-`σ` quadratic mass
is the small-height residual factor times its systematic fourth-power sum.
-/
theorem positiveSigmaQuadraticResidualMass_le_tauEnvelope_mul_systematicSum
    {N A L : ℕ} (hN : 2 ≤ N)
    (hB : 8 ≤ L + 1) :
    positiveSigmaSmallHeightLargeProductQuadraticResidualMass
        N A L hN ≤
      4 ^ smallHeightTauEnvelope A N L *
        ∑ pair ∈
          positiveSigmaSmallHeightLargeProductPairs N A L hN,
          4 ^ pairSigma A pair := by
  unfold positiveSigmaSmallHeightLargeProductQuadraticResidualMass
  unfold quadraticResidualMass
  calc
    (∑ pair ∈
        positiveSigmaSmallHeightLargeProductPairs N A L hN,
        quadraticResidualWeight A hN pair) ≤
        ∑ pair ∈
          positiveSigmaSmallHeightLargeProductPairs N A L hN,
          4 ^ smallHeightTauEnvelope A N L *
            4 ^ pairSigma A pair := by
      apply Finset.sum_le_sum
      intro pair hpair
      apply
        quadraticResidualWeight_le_tauEnvelope_mul_four_pow_pairSigma_of_mem
          hB
      exact
        (mem_activeSmallHeightLargeProductPairs.mp
          (mem_positiveSigmaSmallHeightLargeProductPairs.mp hpair).1).1
    _ =
        4 ^ smallHeightTauEnvelope A N L *
          ∑ pair ∈
            positiveSigmaSmallHeightLargeProductPairs N A L hN,
            4 ^ pairSigma A pair := by
      rw [Finset.mul_sum]

/--
Finite positive-`σ` conclusion:

`Q_pos ≤ 2 · 4^smallHeightTauEnvelope · rationalMass(N,A,L,4)`.
-/
theorem positiveSigmaQuadraticResidualMass_le_two_mul_tauEnvelope_mul_rationalMass
    {N A L : ℕ} (hN : 2 ≤ N)
    (hB : 8 ≤ L + 1) :
    positiveSigmaSmallHeightLargeProductQuadraticResidualMass
        N A L hN ≤
      2 * 4 ^ smallHeightTauEnvelope A N L *
        rationalMass N A L 4 := by
  have hsystematic :=
    sum_four_pow_pairSigma_positive_le_two_mul_rationalMass
      (A := A) (L := L) hN
  calc
    positiveSigmaSmallHeightLargeProductQuadraticResidualMass
          N A L hN ≤
        4 ^ smallHeightTauEnvelope A N L *
          ∑ pair ∈
            positiveSigmaSmallHeightLargeProductPairs N A L hN,
            4 ^ pairSigma A pair :=
      positiveSigmaQuadraticResidualMass_le_tauEnvelope_mul_systematicSum
        hN hB
    _ ≤
        4 ^ smallHeightTauEnvelope A N L *
          (2 * rationalMass N A L 4) :=
      Nat.mul_le_mul_left _ hsystematic
    _ =
        2 * 4 ^ smallHeightTauEnvelope A N L *
          rationalMass N A L 4 := by
      ring

end

end SmallHeightPositiveSigmaSystematicBound
end PaperC
