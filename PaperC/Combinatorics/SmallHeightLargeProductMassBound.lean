import PaperC.Combinatorics.SmallHeightTauEnvelope

set_option maxHeartbeats 1800000

/-!
# Finite mass bounds for the small-height large-product sector

This module isolates the finite combinatorial part of Proposition 7.4.
The remaining analytic task is deliberately exposed through one exact
finite envelope:

`4 ^ max(D# + c#)`.

On the positive-`σ` branch, the quadratic residual mass is bounded by this
envelope times the base-four rational mass of Proposition 5.4 (up to the
harmless absolute factor `2`).  On the active `σ=0` branch, it is bounded by
the same envelope times the relational-host cardinality.

No small-height estimate for `c#` is assumed here.  Proving that the displayed
envelope is `N^(o_C(1))` is the separate prime-counting step of Proposition
7.4.
-/

namespace PaperC
namespace SmallHeightLargeProductMassBound

open scoped BigOperators
open Affine
open CanonicalResidualComponents
open RationalMassFinite
open ResidualComponentCounts
open ResidualMasses
open SmallHeightLargeProductPairs
open SmallHeightTauEnvelope

noncomputable section

/-! ## The exact finite `D# + c#` envelope -/

/--
Largest value of `D# + c#` on the full small-height, large-product
population.  The empty-population value is zero.
-/
noncomputable def maxSmallHeightLargeProductCoreExponent
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  (smallHeightLargeProductPairs N A L hN).sup fun pair ↦
    canonicalCorrectedDefectCount
        A pair.1.1 pair.1.2 L +
      canonicalResidualComponentCount
        A pair.1.1 pair.1.2 L

/-- The corresponding exact multiplicative factor `4 ^ max(D# + c#)`. -/
noncomputable def smallHeightLargeProductCoreFactor
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  4 ^ maxSmallHeightLargeProductCoreExponent N A L hN

/-- Every member of the sector is bounded by the finite core maximum. -/
theorem canonicalCoreExponent_le_max
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ smallHeightLargeProductPairs N A L hN) :
    canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L ≤
      maxSmallHeightLargeProductCoreExponent N A L hN := by
  unfold maxSmallHeightLargeProductCoreExponent
  exact
    Finset.le_sup
      (f := fun pair ↦
        canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L +
          canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L)
      hpair

/-- Equation (6.3), followed by passage to the finite sector maximum. -/
theorem pairTau_le_maxSmallHeightLargeProductCoreExponent
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ smallHeightLargeProductPairs N A L hN) :
    pairTau A hN pair ≤
      maxSmallHeightLargeProductCoreExponent N A L hN :=
  (pairTau_le_canonicalCorrected_add_residual
      (A := A) hN pair).trans
    (canonicalCoreExponent_le_max hpair)

/--
Pointwise extraction of the complete finite core factor:

`4^σ (4^τ - 1) ≤ 4^max(D#+c#) · 4^σ`.
-/
theorem quadraticResidualWeight_le_coreFactor_mul_four_pow_sigma
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ smallHeightLargeProductPairs N A L hN) :
    quadraticResidualWeight A hN pair ≤
      smallHeightLargeProductCoreFactor N A L hN *
        4 ^ pairSigma A pair := by
  have htau :
      pairTau A hN pair ≤
        maxSmallHeightLargeProductCoreExponent N A L hN :=
    pairTau_le_maxSmallHeightLargeProductCoreExponent hpair
  unfold quadraticResidualWeight
  unfold smallHeightLargeProductCoreFactor
  calc
    4 ^ pairSigma A pair *
          (4 ^ pairTau A hN pair - 1) ≤
        4 ^ pairSigma A pair *
          4 ^ pairTau A hN pair :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤
        4 ^ pairSigma A pair *
          4 ^ maxSmallHeightLargeProductCoreExponent N A L hN :=
      Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by norm_num) htau)
    _ =
        4 ^ maxSmallHeightLargeProductCoreExponent N A L hN *
          4 ^ pairSigma A pair := by
      rw [Nat.mul_comm]

/--
Uniform version of the pointwise weight extraction, using the independent
small-height envelopes for `D#` and `c#`.
-/
theorem quadraticResidualWeight_le_uniformCoreFactor_mul_four_pow_sigma
    {N A L : ℕ} {hN : 2 ≤ N}
    (hB : 8 ≤ L + 1)
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ smallHeightLargeProductPairs N A L hN) :
    quadraticResidualWeight A hN pair ≤
      4 ^ smallHeightTauEnvelope A N L *
        4 ^ pairSigma A pair := by
  have htau :
      pairTau A hN pair ≤ smallHeightTauEnvelope A N L :=
    pairTau_le_smallHeightTauEnvelope_of_mem hB hpair
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
      Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by norm_num) htau)
    _ =
        4 ^ smallHeightTauEnvelope A N L *
          4 ^ pairSigma A pair := by
      rw [Nat.mul_comm]

/-! ## Comparison with the systematic rational mass -/

/--
For every finite family of separated-pair subtypes, its systematic
base-four mass is bounded by the full rational mass of Proposition 5.4.
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

/-- For `σ>0`, `4^σ` is at most twice `4^σ-1`. -/
theorem four_pow_le_two_mul_four_pow_sub_one
    {σ : ℕ} (hσ : 0 < σ) :
    4 ^ σ ≤ 2 * (4 ^ σ - 1) := by
  have hpow :
      4 ^ 1 ≤ 4 ^ σ :=
    Nat.pow_le_pow_right (by norm_num) hσ
  norm_num at hpow
  omega

/--
The systematic `4^σ` sum on the positive branch is controlled by twice the
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

/-! ## The positive-`σ` quadratic branch -/

/--
Finite positive-`σ` estimate:

`Q_pos ≤ 2 · 4^max(D#+c#) · rationalMass(N,A,L,4)`.

Proposition 5.4 supplies the `N^(5/3+o_C(1))` estimate for the last factor.
-/
theorem positiveSigmaQuadraticResidualMass_le
    {N A L : ℕ} (hN : 2 ≤ N) :
    positiveSigmaSmallHeightLargeProductQuadraticResidualMass
        N A L hN ≤
      2 * smallHeightLargeProductCoreFactor N A L hN *
        rationalMass N A L 4 := by
  let population :=
    positiveSigmaSmallHeightLargeProductPairs N A L hN
  let factor :=
    smallHeightLargeProductCoreFactor N A L hN
  have hpopulation :
      ∀ pair ∈ population,
        pair ∈ smallHeightLargeProductPairs N A L hN := by
    intro pair hpair
    have hpositive :=
      mem_positiveSigmaSmallHeightLargeProductPairs.mp hpair
    exact
      (mem_activeSmallHeightLargeProductPairs.mp hpositive.1).1
  have hsystematic :
      (∑ pair ∈ population, 4 ^ pairSigma A pair) ≤
        2 * rationalMass N A L 4 := by
    simpa only [population] using
      sum_four_pow_pairSigma_positive_le_two_mul_rationalMass
        (A := A) hN
  unfold positiveSigmaSmallHeightLargeProductQuadraticResidualMass
  unfold quadraticResidualMass
  calc
    (∑ pair ∈ population,
        quadraticResidualWeight A hN pair) ≤
        ∑ pair ∈ population,
          factor * 4 ^ pairSigma A pair := by
      apply Finset.sum_le_sum
      intro pair hpair
      simpa only [factor] using
        quadraticResidualWeight_le_coreFactor_mul_four_pow_sigma
          (hpopulation pair hpair)
    _ =
        factor *
          ∑ pair ∈ population, 4 ^ pairSigma A pair := by
      rw [Finset.mul_sum]
    _ ≤ factor * (2 * rationalMass N A L 4) :=
      Nat.mul_le_mul_left factor hsystematic
    _ =
        2 * smallHeightLargeProductCoreFactor N A L hN *
          rationalMass N A L 4 := by
      dsimp only [factor]
      ring

/--
Uniform positive-`σ` estimate, with the finite small-height envelope exposed:

`Q_pos ≤ 2 · 4^(D_max+c_max) · rationalMass(N,A,L,4)`.
-/
theorem positiveSigmaQuadraticResidualMass_le_uniform
    {N A L : ℕ} (hN : 2 ≤ N)
    (hB : 8 ≤ L + 1) :
    positiveSigmaSmallHeightLargeProductQuadraticResidualMass
        N A L hN ≤
      2 * 4 ^ smallHeightTauEnvelope A N L *
        rationalMass N A L 4 := by
  let population :=
    positiveSigmaSmallHeightLargeProductPairs N A L hN
  let factor :=
    4 ^ smallHeightTauEnvelope A N L
  have hpopulation :
      ∀ pair ∈ population,
        pair ∈ smallHeightLargeProductPairs N A L hN := by
    intro pair hpair
    have hpositive :=
      mem_positiveSigmaSmallHeightLargeProductPairs.mp hpair
    exact
      (mem_activeSmallHeightLargeProductPairs.mp hpositive.1).1
  have hsystematic :
      (∑ pair ∈ population, 4 ^ pairSigma A pair) ≤
        2 * rationalMass N A L 4 := by
    simpa only [population] using
      sum_four_pow_pairSigma_positive_le_two_mul_rationalMass
        (A := A) hN
  unfold positiveSigmaSmallHeightLargeProductQuadraticResidualMass
  unfold quadraticResidualMass
  calc
    (∑ pair ∈ population,
        quadraticResidualWeight A hN pair) ≤
        ∑ pair ∈ population,
          factor * 4 ^ pairSigma A pair := by
      apply Finset.sum_le_sum
      intro pair hpair
      simpa only [factor] using
        quadraticResidualWeight_le_uniformCoreFactor_mul_four_pow_sigma
          hB (hpopulation pair hpair)
    _ =
        factor *
          ∑ pair ∈ population, 4 ^ pairSigma A pair := by
      rw [Finset.mul_sum]
    _ ≤ factor * (2 * rationalMass N A L 4) :=
      Nat.mul_le_mul_left factor hsystematic
    _ =
        2 * 4 ^ smallHeightTauEnvelope A N L *
          rationalMass N A L 4 := by
      dsimp only [factor]
      ring

/-! ## The active `σ=0` quadratic branch -/

/--
Finite exceptional-branch estimate:

`Q_zero ≤ 4^max(D#+c#) · #relationalHosts`.
-/
theorem sigmaZeroQuadraticResidualMass_le
    {N A L : ℕ} (hN : 2 ≤ N) :
    sigmaZeroSmallHeightLargeProductQuadraticResidualMass
        N A L hN ≤
      smallHeightLargeProductCoreFactor N A L hN *
        (RelationalHosts.relationalHosts N L).card := by
  let population :=
    sigmaZeroSmallHeightLargeProductPairs N A L hN
  let factor :=
    smallHeightLargeProductCoreFactor N A L hN
  have hpopulation :
      ∀ pair ∈ population,
        pair ∈ smallHeightLargeProductPairs N A L hN := by
    intro pair hpair
    have hzero :=
      mem_sigmaZeroSmallHeightLargeProductPairs.mp hpair
    exact
      (mem_activeSmallHeightLargeProductPairs.mp hzero.1).1
  unfold sigmaZeroSmallHeightLargeProductQuadraticResidualMass
  unfold quadraticResidualMass
  calc
    (∑ pair ∈ population,
        quadraticResidualWeight A hN pair) ≤
        ∑ _pair ∈ population, factor := by
      apply Finset.sum_le_sum
      intro pair hpair
      have hpoint :=
        quadraticResidualWeight_le_coreFactor_mul_four_pow_sigma
          (hpopulation pair hpair)
      have hsigma :
          pairSigma A pair = 0 :=
        (mem_sigmaZeroSmallHeightLargeProductPairs.mp hpair).2
      simpa only [factor, hsigma, pow_zero, Nat.mul_one] using hpoint
    _ = population.card * factor := by
      simp
    _ ≤
        (RelationalHosts.relationalHosts N L).card * factor :=
      Nat.mul_le_mul_right factor
        (by
          simpa only [population] using
            card_sigmaZeroSmallHeightLargeProductPairs_le_relationalHosts
              (A := A) hN)
    _ =
        smallHeightLargeProductCoreFactor N A L hN *
          (RelationalHosts.relationalHosts N L).card := by
      dsimp only [factor]
      rw [Nat.mul_comm]

/--
Uniform active `σ=0` estimate, with the finite small-height envelope exposed:

`Q_zero ≤ 4^(D_max+c_max) · #relationalHosts`.
-/
theorem sigmaZeroQuadraticResidualMass_le_uniform
    {N A L : ℕ} (hN : 2 ≤ N)
    (hB : 8 ≤ L + 1) :
    sigmaZeroSmallHeightLargeProductQuadraticResidualMass
        N A L hN ≤
      4 ^ smallHeightTauEnvelope A N L *
        (RelationalHosts.relationalHosts N L).card := by
  let population :=
    sigmaZeroSmallHeightLargeProductPairs N A L hN
  let factor :=
    4 ^ smallHeightTauEnvelope A N L
  have hpopulation :
      ∀ pair ∈ population,
        pair ∈ smallHeightLargeProductPairs N A L hN := by
    intro pair hpair
    have hzero :=
      mem_sigmaZeroSmallHeightLargeProductPairs.mp hpair
    exact
      (mem_activeSmallHeightLargeProductPairs.mp hzero.1).1
  unfold sigmaZeroSmallHeightLargeProductQuadraticResidualMass
  unfold quadraticResidualMass
  calc
    (∑ pair ∈ population,
        quadraticResidualWeight A hN pair) ≤
        ∑ _pair ∈ population, factor := by
      apply Finset.sum_le_sum
      intro pair hpair
      have hpoint :=
        quadraticResidualWeight_le_uniformCoreFactor_mul_four_pow_sigma
          hB (hpopulation pair hpair)
      have hsigma :
          pairSigma A pair = 0 :=
        (mem_sigmaZeroSmallHeightLargeProductPairs.mp hpair).2
      simpa only [factor, hsigma, pow_zero, Nat.mul_one] using hpoint
    _ = population.card * factor := by
      simp
    _ ≤
        (RelationalHosts.relationalHosts N L).card * factor :=
      Nat.mul_le_mul_right factor
        (by
          simpa only [population] using
            card_sigmaZeroSmallHeightLargeProductPairs_le_relationalHosts
              (A := A) hN)
    _ =
        4 ^ smallHeightTauEnvelope A N L *
          (RelationalHosts.relationalHosts N L).card := by
      dsimp only [factor]
      rw [Nat.mul_comm]

/-! ## Combined finite quadratic estimate -/

/--
The complete Proposition 7.4 population is bounded by the sum of its
systematic and exceptional finite envelopes.
-/
theorem smallHeightLargeProductQuadraticResidualMass_le
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallHeightLargeProductQuadraticResidualMass N A L hN ≤
      smallHeightLargeProductCoreFactor N A L hN *
          (RelationalHosts.relationalHosts N L).card +
        2 * smallHeightLargeProductCoreFactor N A L hN *
          rationalMass N A L 4 := by
  rw [smallHeightLargeProductQuadraticResidualMass_eq_branches hN]
  exact Nat.add_le_add
    (sigmaZeroQuadraticResidualMass_le (A := A) hN)
    (positiveSigmaQuadraticResidualMass_le (A := A) hN)

/--
Uniform complete finite quadratic estimate for Proposition 7.4.

The factor `4 ^ smallHeightTauEnvelope` splits exactly into the corrected
defect and residual-component factors by
`four_pow_smallHeightTauEnvelope_eq`.
-/
theorem smallHeightLargeProductQuadraticResidualMass_le_uniform
    {N A L : ℕ} (hN : 2 ≤ N)
    (hB : 8 ≤ L + 1) :
    smallHeightLargeProductQuadraticResidualMass N A L hN ≤
      4 ^ smallHeightTauEnvelope A N L *
          (RelationalHosts.relationalHosts N L).card +
        2 * 4 ^ smallHeightTauEnvelope A N L *
          rationalMass N A L 4 := by
  rw [smallHeightLargeProductQuadraticResidualMass_eq_branches hN]
  exact Nat.add_le_add
    (sigmaZeroQuadraticResidualMass_le_uniform (A := A) hN hB)
    (positiveSigmaQuadraticResidualMass_le_uniform (A := A) hN hB)

/-! ## Finite interpolation for the linear mass -/

/-- The complete active sector viewed as ordinary ordered pairs. -/
noncomputable def activeSmallHeightLargeProductPairValues
    (N A L : ℕ) (hN : 2 ≤ N) : Finset (ℕ × ℕ) :=
  (activeSmallHeightLargeProductPairs N A L hN).image Subtype.val

theorem card_activeSmallHeightLargeProductPairValues
    (N A L : ℕ) (hN : 2 ≤ N) :
    (activeSmallHeightLargeProductPairValues N A L hN).card =
      (activeSmallHeightLargeProductPairs N A L hN).card := by
  unfold activeSmallHeightLargeProductPairValues
  exact Finset.card_image_of_injective
    (activeSmallHeightLargeProductPairs N A L hN)
    Subtype.val_injective

/-- Every active pair, regardless of `σ`, is a relational host. -/
theorem pair_mem_relationalHosts_of_mem_active
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ activeSmallHeightLargeProductPairs N A L hN) :
    pair.1 ∈ RelationalHosts.relationalHosts N L := by
  have hactive :=
    mem_activeSmallHeightLargeProductPairs.mp hpair
  have hsep := mem_separatedDyadicPairs.mp pair.2
  rw [RelationalHosts.mem_relationalHosts]
  refine ⟨hsep.1, hsep.2.1, hsep.2.2, ?_⟩
  have hrho :=
    pairRho_eq_pairSigma_add_pairTau
      (A := A) hN pair
  unfold pairRho at hrho
  calc
    0 < pairSigma A pair + pairTau A hN pair := by
      omega
    _ =
        relationRho
          (twoStartSystem
            (dyadicCutoff N L) pair.1.1 pair.1.2 L) :=
      hrho.symm

theorem activeSmallHeightLargeProductPairValues_subset_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSmallHeightLargeProductPairValues N A L hN ⊆
      RelationalHosts.relationalHosts N L := by
  intro pair hpair
  rw [activeSmallHeightLargeProductPairValues,
    Finset.mem_image] at hpair
  obtain ⟨z, hz, rfl⟩ := hpair
  exact pair_mem_relationalHosts_of_mem_active hz

theorem card_activeSmallHeightLargeProductPairs_le_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    (activeSmallHeightLargeProductPairs N A L hN).card ≤
      (RelationalHosts.relationalHosts N L).card := by
  rw [← card_activeSmallHeightLargeProductPairValues N A L hN]
  exact Finset.card_le_card
    (activeSmallHeightLargeProductPairValues_subset_relationalHosts
      (A := A) hN)

/--
Equation (6.6) for the full small-height, large-product sector.

Together with the finite quadratic estimate above, Proposition 5.4, and the
relational-host bound, this is the exact input for the exponent `19/12`.
-/
theorem smallHeightLargeProductLinearResidualMass_cast_le
    {N A L : ℕ} (hN : 2 ≤ N) :
    (smallHeightLargeProductLinearResidualMass N A L hN : ℝ) ≤
      Real.sqrt
          ((RelationalHosts.relationalHosts N L).card : ℝ) *
        Real.sqrt
          (smallHeightLargeProductQuadraticResidualMass
            N A L hN : ℝ) := by
  have hinterp :=
    linearResidualMass_cast_le_sqrt_card_mul_sqrt_quadratic
      (A := A) hN
      (activeSmallHeightLargeProductPairs N A L hN)
  have hcard :
      ((activeSmallHeightLargeProductPairs N A L hN).card : ℝ) ≤
        ((RelationalHosts.relationalHosts N L).card : ℝ) := by
    exact_mod_cast
      card_activeSmallHeightLargeProductPairs_le_relationalHosts
        (A := A) hN
  rw [smallHeightLargeProductLinearResidualMass_eq_active hN]
  rw [smallHeightLargeProductQuadraticResidualMass_eq_active hN]
  unfold activeSmallHeightLargeProductLinearResidualMass
  unfold activeSmallHeightLargeProductQuadraticResidualMass
  exact hinterp.trans
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt hcard)
      (Real.sqrt_nonneg _))

end

end SmallHeightLargeProductMassBound
end PaperC
