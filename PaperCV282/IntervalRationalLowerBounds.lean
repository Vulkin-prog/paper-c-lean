import PaperCV282.RationalFamilyMass
import PaperCV282.MacroscopicRelationProfile
import PaperCV282.MacroscopicCanonicalCode

/-!
# The explicit lower bounds (3.22) and (3.23)

The finite parameter intervals produce the actual ordered separated
families in the dyadic and macroscopic masks. The real versions use
explicit constants in place of the manuscript's bounded rounding error.
-/

namespace PaperC.V282.IntervalRationalLowerBounds

open Affine HostRankMass RationalFamilyMass TwoWindowParity
open MacroscopicGeometry MacroscopicRelationProfile
open scoped BigOperators

noncomputable section

/-- The parameters of `(t,2t)` in the macroscopic interval. -/
def halfParameters (M : ℕ) (delta : ℝ) : Finset ℕ :=
  Finset.Ico ⌈(M : ℝ) ^ delta⌉₊ ((M + 1) / 2)

/-- Exact natural count of the macroscopic parameters. -/
theorem card_halfParameters (M : ℕ) (delta : ℝ) :
    (halfParameters M delta).card = (M + 1) / 2 - ⌈(M : ℝ) ^ delta⌉₊ := by
  simp [halfParameters]

/-- Both orientations really belong to the separated macroscopic mask. -/
theorem half_family_subset_macroscopic {M L : ℕ} {delta : ℝ}
    (hL : L < ⌈(M : ℝ) ^ delta⌉₊) :
    orientedPairs 1 2 (halfParameters M delta) ⊆
      separatedPairs (macroscopicStarts M delta) L := by
  intro xy hxy
  rcases (mem_orientedPairs 1 2 (halfParameters M delta) xy).mp hxy with
    ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  all_goals
    simp only [halfParameters, Finset.mem_Ico] at ht
    simp only [one_mul, mem_separatedPairs, mem_macroscopicStarts, Nat.dist]
    omega

/-- Finite equation (3.23) with an exact nonnegative integer coefficient. -/
theorem macroscopicStartMassNat_lower_bound {M L : ℕ} {delta : ℝ}
    (hM : 2 ≤ M) (hdelta : 0 < delta) (hL : L < ⌈(M : ℝ) ^ delta⌉₊) :
    2 * ((M + 1) / 2 - ⌈(M : ℝ) ^ delta⌉₊) *
      (2 ^ ((L + 1) / 2 - 1) - 1) ≤ macroscopicStartMassNat M L delta := by
  have hf := half_family_lower_bound (M + L) L (halfParameters M delta)
    (separatedPairs (macroscopicStarts M delta) L) (by
      intro t ht
      exact (two_le_macroscopic_lowerEndpoint hM hdelta).trans (Finset.mem_Ico.mp ht).1)
    (half_family_subset_macroscopic hL)
  simpa only [card_halfParameters, relationWeightMass, macroscopicStartMassNat] using hf

/-- The macroscopic coefficient differs from `M-2*M^delta` by at most a fixed
downward rounding error; the bound is valid even if the interval is empty. -/
theorem macroscopic_coefficient_lower_bound (M : ℕ) (delta : ℝ) :
    (M : ℝ) - 2 * (M : ℝ) ^ delta - 2 ≤
      ((2 * ((M + 1) / 2 - ⌈(M : ℝ) ^ delta⌉₊) : ℕ) : ℝ) := by
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ M) delta)
  have harith : M ≤ 2 * ((M + 1) / 2 - ⌈(M : ℝ) ^ delta⌉₊) +
      2 * ⌈(M : ℝ) ^ delta⌉₊ := by omega
  have hcast : (M : ℝ) ≤ (2 * ((M + 1) / 2 - ⌈(M : ℝ) ^ delta⌉₊) : ℕ) +
      2 * (⌈(M : ℝ) ^ delta⌉₊ : ℝ) := by exact_mod_cast harith
  linarith

/-- Equation (3.23) with the explicit error `-2` replacing `O(1)`. -/
theorem equation_three_twenty_three_finite {M L : ℕ} {delta : ℝ}
    (hM : 2 ≤ M) (hdelta : 0 < delta) (hL : L < ⌈(M : ℝ) ^ delta⌉₊) :
    ((M : ℝ) - 2 * (M : ℝ) ^ delta - 2) *
      ((2 ^ ((L + 1) / 2 - 1) - 1 : ℕ) : ℝ) ≤
        (macroscopicStartMassNat M L delta : ℝ) := by
  have hfinite : ((2 * ((M + 1) / 2 - ⌈(M : ℝ) ^ delta⌉₊) : ℕ) : ℝ) *
      ((2 ^ ((L + 1) / 2 - 1) - 1 : ℕ) : ℝ) ≤
        (macroscopicStartMassNat M L delta : ℝ) := by
    exact_mod_cast macroscopicStartMassNat_lower_bound hM hdelta hL
  exact (mul_le_mul_of_nonneg_right (macroscopic_coefficient_lower_bound M delta)
    (by positivity)).trans hfinite

/-- The parameters `ceil(N/2) <= t < ceil(2N/3)` of the dyadic family `(2t,3t)`. -/
def thirdParameters (N : ℕ) : Finset ℕ :=
  Finset.Ico ((N + 1) / 2) ((2 * N + 2) / 3)

/-- Exact natural count of the dyadic parameters. -/
theorem card_thirdParameters (N : ℕ) :
    (thirdParameters N).card = (2 * N + 2) / 3 - (N + 1) / 2 := by
  simp [thirdParameters]

/-- Both dyadic orientations satisfy the genuine window separation condition. -/
theorem third_family_subset_dyadic {N L : ℕ} (hNL : 2 * (L + 1) ≤ N) :
    orientedPairs 2 3 (thirdParameters N) ⊆ separatedPairs (dyadicBlock N) L := by
  intro xy hxy
  rcases (mem_orientedPairs 2 3 (thirdParameters N) xy).mp hxy with
    ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  all_goals
    simp only [thirdParameters, Finset.mem_Ico] at ht
    simp only [mem_separatedPairs, dyadicBlock, Finset.mem_Ico, Nat.dist]
    omega

/-- Finite equation (3.22) with an exact integer coefficient. -/
theorem dyadic_relationWeightMass_lower_bound {N L : ℕ} (hNL : 2 * (L + 1) ≤ N) :
    2 * ((2 * N + 2) / 3 - (N + 1) / 2) *
      (2 ^ ((L + 2) / 3 - 1) - 1) ≤
        relationWeightMass (2 * N + L) L (separatedPairs (dyadicBlock N) L) := by
  have hf := third_family_lower_bound (2 * N + L) L (thirdParameters N)
    (separatedPairs (dyadicBlock N) L) (by
      intro t ht
      simp only [thirdParameters, Finset.mem_Ico] at ht
      omega) (third_family_subset_dyadic hNL)
  simpa only [card_thirdParameters] using hf

/-- The dyadic pair coefficient is at least `N/3-1`. -/
theorem dyadic_coefficient_lower_bound (N : ℕ) :
    (N : ℝ) / 3 - 1 ≤ ((2 * ((2 * N + 2) / 3 - (N + 1) / 2) : ℕ) : ℝ) := by
  have hnat : N ≤ 3 * (2 * ((2 * N + 2) / 3 - (N + 1) / 2)) + 3 := by omega
  have hcast : (N : ℝ) ≤ 3 * (2 * ((2 * N + 2) / 3 - (N + 1) / 2) : ℕ) + 3 := by
    exact_mod_cast hnat
  linarith

/-- Equation (3.22) on the historical real interval mass, with error `-1`. -/
theorem equation_three_twenty_two_finite {N L : ℕ} (hNL : 2 * (L + 1) ≤ N) :
    ((N : ℝ) / 3 - 1) * ((2 ^ ((L + 2) / 3 - 1) - 1 : ℕ) : ℝ) ≤
      PropositionSixteenOne.R2κ N (2 * N) L := by
  have hfinite : ((2 * ((2 * N + 2) / 3 - (N + 1) / 2) : ℕ) : ℝ) *
      ((2 ^ ((L + 2) / 3 - 1) - 1 : ℕ) : ℝ) ≤
      (relationWeightMass (2 * N + L) L (separatedPairs (dyadicBlock N) L) : ℝ) := by
    exact_mod_cast dyadic_relationWeightMass_lower_bound hNL
  have heq : (relationWeightMass (2 * N + L) L (separatedPairs (dyadicBlock N) L) : ℝ) =
      PropositionSixteenOne.R2κ N (2 * N) L := by
    simp only [relationWeightMass, Nat.cast_sum, PropositionSixteenOne.R2κ_eq_filtered_sum,
      PropositionSixteenOne.boundedRatioCutoff]
    rfl
  rw [heq] at hfinite
  exact (mul_le_mul_of_nonneg_right (dyadic_coefficient_lower_bound N) (by positivity)).trans hfinite

/-- Equation (3.23), uniformly in all logarithmic lengths, with the threshold
chosen before `M` and `L`; the macroscopic exponent is fixed. -/
theorem equation_three_twenty_three_eventually
    (C delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ C * Real.log M →
      ((M : ℝ) - 2 * (M : ℝ) ^ delta - 2) *
        ((2 ^ ((L + 1) / 2 - 1) - 1 : ℕ) : ℝ) ≤
          (macroscopicStartMassNat M L delta : ℝ) := by
  obtain ⟨Mpower, hpower⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    C delta hC hdelta 1 (by omega)
  refine ⟨max Mpower 2, ?_⟩
  intro M hM L hL
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hM
  have hp := hpower M ((le_max_left _ _).trans hM) (L + 1) (by simpa using hL)
  have hceil := Nat.le_ceil ((M : ℝ) ^ delta)
  have hstart : L < ⌈(M : ℝ) ^ delta⌉₊ := by
    simp only [pow_one, Nat.cast_add, Nat.cast_one] at hp
    have : (L : ℝ) < (⌈(M : ℝ) ^ delta⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  exact equation_three_twenty_three_finite hMtwo hdelta hstart

/-- Equation (3.22), uniformly in all logarithmic dyadic lengths, with error `-1`. -/
theorem equation_three_twenty_two_eventually (C : ℝ) (hC : 0 ≤ C) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ C * Real.log N →
      ((N : ℝ) / 3 - 1) * ((2 ^ ((L + 2) / 3 - 1) - 1 : ℕ) : ℝ) ≤
        PropositionSixteenOne.R2κ N (2 * N) L := by
  obtain ⟨Npower, hpower⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    (2 * C) 1 (by positivity) (by norm_num) 1 (by omega)
  refine ⟨Npower, ?_⟩
  intro N hN L hL
  have hp := hpower N hN (2 * (L + 1)) (by
    push_cast
    nlinarith)
  have hsep : 2 * (L + 1) ≤ N := by
    simp only [pow_one, Real.rpow_one, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one] at hp
    have : (2 : ℝ) * (L + 1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  exact equation_three_twenty_two_finite hsep

end
end PaperC.V282.IntervalRationalLowerBounds
