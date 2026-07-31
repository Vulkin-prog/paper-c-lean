import PaperC.Asymptotics.PropositionSixteenOneCore

set_option maxHeartbeats 1800000

/-!
# The dyadic endpoint of the bounded-ratio mass

The bounded-ratio interval of Proposition 16.1 is parametrized by its
integral right endpoint `M`.  At `M = 2 * N` its block, cutoff, separated
pair population, relation exponent, and homogeneous weight are
definitionally the corresponding dyadic objects of Proposition 11.2.

This file records that specialization as a public transport theorem.  The
only apparent mismatch is at `N < 2`: Proposition 11.2 defines its
proof-independent real mass to be zero there, whereas `R2κ` is an
unconditional finite sum.  The latter sum is also zero, since `[N,2N)` has
at most one element for `N = 0,1`.
-/

namespace PaperC
namespace DyadicKappaTransport

open RationalMassFinite
open ResidualMasses

noncomputable section

/-! ## Definitional endpoint identifications -/

@[simp]
theorem boundedRatioBlock_two_mul
    (N : ℕ) :
    PropositionSixteenOne.boundedRatioBlock N (2 * N) =
      dyadicBlock N := by
  rfl

@[simp]
theorem boundedRatioCutoff_two_mul
    (N L : ℕ) :
    PropositionSixteenOne.boundedRatioCutoff (2 * N) L =
      dyadicCutoff N L := by
  rfl

@[simp]
theorem separatedBoundedRatioPairs_two_mul
    (N L : ℕ) :
    PropositionSixteenOne.separatedBoundedRatioPairs N (2 * N) L =
      separatedDyadicPairs N L := by
  rfl

theorem separatedBoundedRatioPair_two_mul
    (N L : ℕ) :
    PropositionSixteenOne.SeparatedBoundedRatioPair N (2 * N) L =
      SeparatedDyadicPair N L := by
  rfl

@[simp]
theorem pairRho_two_mul
    {N L : ℕ}
    (pair :
      PropositionSixteenOne.SeparatedBoundedRatioPair
        N (2 * N) L) :
    PropositionSixteenOne.pairRho pair =
      ResidualMasses.pairRho pair := by
  rfl

@[simp]
theorem homogeneousWeight_two_mul
    {N L : ℕ}
    (pair :
      PropositionSixteenOne.SeparatedBoundedRatioPair
        N (2 * N) L) :
    PropositionSixteenOne.homogeneousWeight pair =
      PropositionElevenTwo.homogeneousWeight pair := by
  rfl

@[simp]
theorem homogeneousMassNat_two_mul
    {N L : ℕ} (hN : 2 ≤ N) :
    PropositionSixteenOne.homogeneousMassNat N (2 * N) L =
      PropositionElevenTwo.homogeneousMassNat
        (L := L) hN := by
  rfl

/-! ## The harmless range `N < 2` -/

/--
At the dyadic endpoint the bounded-ratio separated population is empty
below the threshold used in Proposition 11.2.
-/
theorem separatedBoundedRatioPairs_two_mul_eq_empty_of_not_two_le
    {N L : ℕ} (hN : ¬ 2 ≤ N) :
    PropositionSixteenOne.separatedBoundedRatioPairs
        N (2 * N) L =
      ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro pair hpair
  have hp :=
    PropositionSixteenOne.mem_separatedBoundedRatioPairs.mp hpair
  have hx :=
    PropositionSixteenOne.mem_boundedRatioBlock.mp hp.1
  have hy :=
    PropositionSixteenOne.mem_boundedRatioBlock.mp hp.2.1
  have hNsmall : N = 0 ∨ N = 1 := by omega
  rcases hNsmall with rfl | rfl
  · omega
  · have hxone : pair.1 = 1 := by omega
    have hyone : pair.2 = 1 := by omega
    simpa [hxone, hyone] using hp.2.2

/--
Although `R2κ` itself has no small-`N` convention, its dyadic specialization
vanishes below `N = 2`.
-/
theorem R2κ_two_mul_eq_zero_of_not_two_le
    {N L : ℕ} (hN : ¬ 2 ≤ N) :
    PropositionSixteenOne.R2κ N (2 * N) L = 0 := by
  rw [PropositionSixteenOne.R2κ_eq_filtered_sum,
    separatedBoundedRatioPairs_two_mul_eq_empty_of_not_two_le hN]
  simp

/-! ## Public mass transport -/

/--
The Proposition 11.2 homogeneous mass is exactly the `κ = 2` endpoint of
the Proposition 16.1 bounded-ratio mass, for every `N`.

For `2 ≤ N` this is definitional after unfolding the proof-independent
wrapper.  For `N < 2` both sides vanish by the preceding finite-population
lemma.
-/
theorem homogeneousMass_eq_R2κ_two_mul
    (A N L : ℕ) :
    PropositionElevenTwo.homogeneousMass A N L =
      PropositionSixteenOne.R2κ N (2 * N) L := by
  by_cases hN : 2 ≤ N
  · simp only [PropositionElevenTwo.homogeneousMass, dif_pos hN,
      PropositionSixteenOne.R2κ]
    exact_mod_cast (homogeneousMassNat_two_mul hN).symm
  · rw [PropositionElevenTwo.homogeneousMass]
    simp only [dif_neg hN]
    exact (R2κ_two_mul_eq_zero_of_not_two_le hN).symm

end

end DyadicKappaTransport
end PaperC
