import PaperCV282.MacroscopicGeometry
import PaperCV282.TwoWindowSquareHosts
import PaperC.Asymptotics.PropositionSixteenOneCore

/-!
# Exact finite masses for the macroscopic relation profile

Both masses use the article's ordered separated pairs in
`[ceil(M^δ), M)` and the adequate prime cutoff `M + L`. The start mass
is exactly the historical interval mass, whose finite rational/residual
decomposition is available without a bound on the endpoint ratio.
The full-value mass satisfies the finite comparison (3.24).

No asymptotic profile is assumed or asserted in this file.
-/

namespace PaperC.V282.MacroscopicRelationProfile

open Affine MacroscopicGeometry TwoWindowParity TwoWindowSquareHosts
open scoped BigOperators

noncomputable section

/-- The natural weighted start-relation mass on the macroscopic pair mask. -/
def macroscopicStartMassNat (M L : ℕ) (δ : ℝ) : ℕ :=
  ∑ xy ∈ separatedPairs (macroscopicStarts M δ) L,
    (2 ^ relationRho (twoStartSystem (M + L) xy.1 xy.2 L) - 1)

/-- The natural full-value relation mass, on the identical mask and cutoff. -/
def macroscopicValueMassNat (M L : ℕ) (δ : ℝ) : ℕ :=
  ∑ xy ∈ separatedPairs (macroscopicStarts M δ) L,
    (2 ^ relationRho (twoValueSystem (M + L) xy.1 xy.2 L) - 1)

/-- The interval representation agrees exactly, even for empty populations. -/
theorem macroscopicSeparatedPairs_eq_boundedRatioPairs (M L : ℕ) (δ : ℝ) :
    separatedPairs (macroscopicStarts M δ) L =
      PropositionSixteenOne.separatedBoundedRatioPairs ⌈(M : ℝ) ^ δ⌉₊ M L := rfl

/-- Exact identification with the retained real interval mass. No ratio,
length or positivity hypothesis is needed for this equality of definitions. -/
theorem macroscopicStartMassNat_cast_eq_R2kappa (M L : ℕ) (δ : ℝ) :
    (macroscopicStartMassNat M L δ : ℝ) =
      PropositionSixteenOne.R2κ ⌈(M : ℝ) ^ δ⌉₊ M L := by
  simp only [macroscopicStartMassNat, Nat.cast_sum,
    PropositionSixteenOne.R2κ_eq_filtered_sum,
    macroscopicSeparatedPairs_eq_boundedRatioPairs,
    PropositionSixteenOne.boundedRatioCutoff]
  rfl

/-- The exact rational/residual decomposition transfers to the macroscopic
interval for every coding parameter `A`, including the article's `A = 3`. -/
theorem macroscopicStartMassNat_cast_eq_systematic_add_residual
    (A : ℕ) {M L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) :
    (macroscopicStartMassNat M L δ : ℝ) =
      PropositionSixteenOne.systematicMass A ⌈(M : ℝ) ^ δ⌉₊ M L +
        PropositionSixteenOne.residualMass A ⌈(M : ℝ) ^ δ⌉₊ M L := by
  rw [macroscopicStartMassNat_cast_eq_R2kappa]
  exact PropositionSixteenOne.R2κ_eq_systematic_add_residual
    (two_le_macroscopic_lowerEndpoint hM hδ)

/-- Equation (3.24) on the literal macroscopic mask. Positivity and cutoff
adequacy hold without a logarithmic-band or endpoint-ratio assumption. -/
theorem macroscopicValueMassNat_le_four_start_add_hosts
    {M L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) :
    macroscopicValueMassNat M L δ ≤
      4 * macroscopicStartMassNat M L δ +
        3 * (squareProductHosts L (separatedPairs (macroscopicStarts M δ) L)).card := by
  apply finite_equation_three_twenty_four_square_hosts
  · intro x hx
    exact (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hM hδ hx)).1
  · intro x hx
    have hxM := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hM hδ hx)).2
    omega

end
end PaperC.V282.MacroscopicRelationProfile
