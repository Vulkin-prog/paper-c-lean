import PaperCV282.MacroscopicSmallHeightTau
import PaperCV282.ResidualSectorMass
import PaperCV282.RationalProfile

/-!
# The actual positive small-channel residual sector

Sector two uses the upper-endpoint prime-product test and the positive
small-height test from the eight-sector partition. Its genuine residual
weight is `2^sigma * (2^tau - 1)`. Positivity of sigma bounds `2^sigma`
by twice `2^sigma - 1`, so the uniform residual factor can be summed
against the already proved rational mass in base two.

This proves the sector-two profile on the exact macroscopic interval;
no critical run-length window or assumed sector estimate is used.
-/

namespace PaperC.V282.MacroscopicSmallHeightSector

open PropositionSixteenOne ResidualSectorPartition ResidualSectorMass
open MacroscopicGeometry MacroscopicShallowSigma MacroscopicSmallHeightTau
open RationalHeightMass RationalProfile LogarithmicWordPowers
open scoped BigOperators

noncomputable section

/-- The partition's second test is exactly the positive small-height predicate. -/
theorem smallPositiveChannel_iff {N M A L : ℕ}
    (pair : SeparatedBoundedRatioPair N M L) :
    smallPositiveChannel A pair ↔
      hasSmallPositiveCanonicalHeight A L pair.1.1 pair.1.2 := by
  simp only [smallPositiveChannel, hasSmallPositiveCanonicalHeight, pairSigma,
    Nat.cast_add, Nat.cast_one]

/-- Positive systematic dimension lets the rational weight pay for its binary factor. -/
theorem two_pow_le_two_mul_weight {n : ℕ} (hn : 0 < n) :
    2 ^ n ≤ 2 * (2 ^ n - 1) := by
  have htwo : 2 ≤ 2 ^ n := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  omega

/-- Any positive-sigma population with a bounded residual binary factor
is controlled by the actual interval systematic mass. -/
theorem sum_residualWeight_le_two_factor_systematic
    {N M A L : ℕ} (hN : 2 ≤ N)
    (s : Finset (SeparatedBoundedRatioPair N M L)) {F : ℝ} (hF : 0 ≤ F)
    (hsigma : ∀ pair ∈ s, 0 < pairSigma A pair)
    (htau : ∀ pair ∈ s, (2 : ℝ) ^ pairTau A hN pair ≤ F) :
    ((∑ pair ∈ s, residualWeight A hN pair : ℕ) : ℝ) ≤
      2 * F * (systematicMassNat (N := N) (M := M) (L := L) A : ℝ) := by
  have hpoint : ∀ pair ∈ s, (residualWeight A hN pair : ℝ) ≤
      2 * F * (systematicWeight A pair : ℝ) := by
    intro pair hpair
    have hsig : 2 ^ pairSigma A pair ≤ 2 * systematicWeight A pair :=
      two_pow_le_two_mul_weight (hsigma pair hpair)
    have hnat : residualWeight A hN pair ≤
        (2 * systematicWeight A pair) * 2 ^ pairTau A hN pair := by
      unfold residualWeight
      exact Nat.mul_le_mul hsig (Nat.sub_le _ _)
    have hreal : (residualWeight A hN pair : ℝ) ≤
        (2 * (systematicWeight A pair : ℝ)) * (2 : ℝ) ^ pairTau A hN pair := by
      exact_mod_cast hnat
    calc
      _ ≤ (2 * (systematicWeight A pair : ℝ)) * (2 : ℝ) ^ pairTau A hN pair := hreal
      _ ≤ (2 * (systematicWeight A pair : ℝ)) * F :=
        mul_le_mul_of_nonneg_left (htau pair hpair) (by positivity)
      _ = 2 * F * (systematicWeight A pair : ℝ) := by ring
  have hsubset : (∑ pair ∈ s, systematicWeight A pair) ≤
      systematicMassNat (N := N) (M := M) (L := L) A :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ s)
  have hsubsetReal : (∑ pair ∈ s, (systematicWeight A pair : ℝ)) ≤
      (systematicMassNat (N := N) (M := M) (L := L) A : ℝ) := by
    exact_mod_cast hsubset
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ pair ∈ s, 2 * F * (systematicWeight A pair : ℝ) := Finset.sum_le_sum hpoint
    _ = 2 * F * ∑ pair ∈ s, (systematicWeight A pair : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsubsetReal (by positivity)

/-- The exact sector-two natural mass satisfies the preceding finite comparison. -/
theorem sector_two_massNat_le_two_factor_systematic
    {N M A L : ℕ} (hN : 2 ≤ N) {F : ℝ} (hF : 0 ≤ F)
    (htau : ∀ pair ∈ sectorPairs N M A L hN 1,
      (2 : ℝ) ^ pairTau A hN pair ≤ F) :
    (sectorMassNat (M := M) (L := L) A hN 1 : ℝ) ≤
      2 * F * (systematicMassNat (N := N) (M := M) (L := L) A : ℝ) := by
  apply sum_residualWeight_le_two_factor_systematic hN _ hF
  · intro pair hpair
    exact ((sectorOf_eq_two_iff.mp (mem_sectorPairs.mp hpair)).2).1
  · exact htau

/-- The full rational profile of manuscript sector two, with all fixed
parameters before a common threshold and with the true residual mass.
The estimate is uniform in `A >= 1`, and includes the paper's `A = 3`. -/
theorem sector_two_mass_le_rational_profile_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ, 1 ≤ A →
      sectorMass A 1 ⌈(M : ℝ) ^ delta⌉₊ M L ≤
        (M : ℝ) ^ epsilon *
          ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
            (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))) := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  have hthird : 0 < epsilon / 3 := by positivity
  obtain ⟨Mtau, htau⟩ := two_pow_pairTau_le_rpow_eventually
    betaMin betaMax delta (epsilon / 3) hbetaMin hbeta hdelta hthird
  obtain ⟨Mrational, hrational⟩ := height_masses_uniform_profiles
    betaMax hbetaMax.le (epsilon / 3) hthird
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax hbetaMax.le 2 0 (epsilon / 3) hthird
  refine ⟨max Mtau (max Mrational (max Mconstant 2)), ?_⟩
  intro M hM L hlower hupper A hA
  have hMtau : Mtau ≤ M := (le_max_left _ _).trans hM
  have hrest : max Mrational (max Mconstant 2) ≤ M := (le_max_right _ _).trans hM
  have hMrational : Mrational ≤ M := (le_max_left _ _).trans hrest
  have htail : max Mconstant 2 ≤ M := (le_max_right _ _).trans hrest
  have hMconstant : Mconstant ≤ M := (le_max_left _ _).trans htail
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans htail
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊ := two_le_macroscopic_lowerEndpoint hMtwo hdelta
  have hfactor : (2 : ℝ) ≤ (M : ℝ) ^ (epsilon / 3) := by
    have h := hconstant M hMconstant L (by simpa only [Nat.cast_add, Nat.cast_one] using hupper)
    simpa using h
  have hfinite : (sectorMassNat (M := M) (L := L) A hN 1 : ℝ) ≤
      2 * (M : ℝ) ^ (epsilon / 3) *
        (systematicMassNat (N := ⌈(M : ℝ) ^ delta⌉₊) (M := M) (L := L) A : ℝ) := by
    apply sector_two_massNat_le_two_factor_systematic hN (by positivity)
    intro pair hpair
    apply htau M hMtau L hlower hupper A hN pair
    exact (smallPositiveChannel_iff pair).mp
      (sectorOf_eq_two_iff.mp (mem_sectorPairs.mp hpair)).2
  obtain ⟨hheightTwo, hheightThree⟩ := hrational M hMrational L
    (by simpa only [Nat.cast_add, Nat.cast_one] using hupper) ⌈(M : ℝ) ^ delta⌉₊ A hA
  have hsystematic :
      (systematicMassNat (N := ⌈(M : ℝ) ^ delta⌉₊) (M := M) (L := L) A : ℝ) ≤
        (M : ℝ) ^ (epsilon / 3) *
          ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
            (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))) := by
    rw [systematicMassNat_eq_boundedRationalMass, boundedRationalMass_eq_height_masses, Nat.cast_add]
    calc
      _ ≤ (M : ℝ) ^ (epsilon / 3) *
          ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ))) +
          (M : ℝ) ^ (epsilon / 3) *
          ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))) :=
        add_le_add hheightTwo hheightThree
      _ = _ := by ring
  rw [sectorMass, dif_pos hN]
  refine hfinite.trans ?_
  calc
    _ ≤ 2 * (M : ℝ) ^ (epsilon / 3) *
        ((M : ℝ) ^ (epsilon / 3) *
          ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
            (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ)))) :=
      mul_le_mul_of_nonneg_left hsystematic (by positivity)
    _ ≤ (M : ℝ) ^ (epsilon / 3) * (M : ℝ) ^ (epsilon / 3) *
        ((M : ℝ) ^ (epsilon / 3) *
          ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
            (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ)))) := by
      gcongr
    _ = (M : ℝ) ^ epsilon *
        ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
          (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))) := by
      rw [← mul_assoc, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
      congr 2
      ring

end
end PaperC.V282.MacroscopicSmallHeightSector
