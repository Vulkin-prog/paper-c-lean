import PaperCV282.HostRankMass
import PaperCV282.MacroscopicRelationProfile

/-!
# Literal real ceilings for finite two-window relation masses

The ceiling is a real parameter, as in Section 3.8, and may vary with
the ambient scale. Finite comparison and support statements are uniform
in that parameter. No terminal population estimate is assumed here.
-/

namespace PaperC.V282.CappedRelationMass

open Affine TwoWindowParity TwoWindowSquareHosts FullHostComparison
open HostRankMass MacroscopicGeometry MacroscopicRelationProfile
open scoped BigOperators

noncomputable section

/-- Capped start-relation mass on an arbitrary finite ordered pair mask. -/
def cappedStartMass (K L : ℕ) (T : ℝ) (s : Finset (ℕ × ℕ)) : ℝ :=
  ∑ xy ∈ s, min T ((2 ^ relationRho (twoStartSystem K xy.1 xy.2 L) - 1 : ℕ) : ℝ)

/-- Capped full-value mass, with the identical real ceiling and pair mask. -/
def cappedValueMass (K L : ℕ) (T : ℝ) (s : Finset (ℕ × ℕ)) : ℝ :=
  ∑ xy ∈ s, min T ((2 ^ relationRho (twoValueSystem K xy.1 xy.2 L) - 1 : ℕ) : ℝ)

/-- The rational summand may be left uncapped in the canonical decomposition. -/
theorem min_add_le_left_add_min {a b T : ℝ} (ha : 0 ≤ a) :
    min T (a + b) ≤ a + min T b := by
  by_cases hb : b ≤ T
  · rw [min_eq_right hb]
    exact min_le_right _ _
  · rw [min_eq_left (le_of_not_ge hb)]
    exact (min_le_left _ _).trans (by linarith)

/-- A common factor at least one can be taken outside any nonnegative ceiling. -/
theorem min_mul_le_mul_min {E Q T : ℝ} (hE : 1 ≤ E) (hT : 0 ≤ T) :
    min T (E * Q) ≤ E * min T Q := by
  by_cases hQT : Q ≤ T
  · rw [min_eq_right hQT]
    exact min_le_right _ _
  · rw [min_eq_left (le_of_not_ge hQT)]
    exact (min_le_left _ _).trans (by nlinarith)

/-- The fixed affine correction survives capping with the same ceiling. -/
theorem min_four_mul_add_three_le {a T : ℝ} (hT : 0 ≤ T) :
    min T (4 * a + 3) ≤ 4 * min T a + 3 := by
  by_cases haT : a ≤ T
  · rw [min_eq_right haT]
    exact min_le_right _ _
  · rw [min_eq_left (le_of_not_ge haT)]
    exact (min_le_left _ _).trans (by linarith)

theorem cappedStartMass_nonneg (K L : ℕ) {T : ℝ} (hT : 0 ≤ T) (s : Finset (ℕ × ℕ)) :
    0 ≤ cappedStartMass K L T s := by
  apply Finset.sum_nonneg
  intro xy _
  exact le_min hT (Nat.cast_nonneg _)

theorem cappedValueMass_nonneg (K L : ℕ) {T : ℝ} (hT : 0 ≤ T) (s : Finset (ℕ × ℕ)) :
    0 ≤ cappedValueMass K L T s := by
  apply Finset.sum_nonneg
  intro xy _
  exact le_min hT (Nat.cast_nonneg _)

/-- Increasing the ceiling increases the exact capped start mass. -/
theorem cappedStartMass_mono_cap (K L : ℕ) {S T : ℝ} (hST : S ≤ T) (s : Finset (ℕ × ℕ)) :
    cappedStartMass K L S s ≤ cappedStartMass K L T s := by
  exact Finset.sum_le_sum fun _ _ => min_le_min_right _ hST

/-- Increasing the ceiling increases the exact capped full-value mass. -/
theorem cappedValueMass_mono_cap (K L : ℕ) {S T : ℝ} (hST : S ≤ T) (s : Finset (ℕ × ℕ)) :
    cappedValueMass K L S s ≤ cappedValueMass K L T s := by
  exact Finset.sum_le_sum fun _ _ => min_le_min_right _ hST

/-- Restriction of the pair mask preserves the capped start upper bounds. -/
theorem cappedStartMass_mono_mask (K L : ℕ) {T : ℝ} (hT : 0 ≤ T)
    {s t : Finset (ℕ × ℕ)} (hst : s ⊆ t) :
    cappedStartMass K L T s ≤ cappedStartMass K L T t := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ => le_min hT (Nat.cast_nonneg _))

/-- Restriction of the pair mask also preserves the full-value upper bounds. -/
theorem cappedValueMass_mono_mask (K L : ℕ) {T : ℝ} (hT : 0 ≤ T)
    {s t : Finset (ℕ × ℕ)} (hst : s ⊆ t) :
    cappedValueMass K L T s ≤ cappedValueMass K L T t := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ => le_min hT (Nat.cast_nonneg _))

/-- The capped start mass is below the exact uncapped natural mass. -/
theorem cappedStartMass_le_relationWeightMass (K L : ℕ) (T : ℝ) (s : Finset (ℕ × ℕ)) :
    cappedStartMass K L T s ≤ (relationWeightMass K L s : ℝ) := by
  unfold relationWeightMass
  rw [Nat.cast_sum]
  exact Finset.sum_le_sum fun _ _ => min_le_right _ _

/-- Zero-nullity pairs contribute nothing under a nonnegative ceiling. -/
theorem cappedStartMass_eq_sum_hosts (K L : ℕ) {T : ℝ} (hT : 0 ≤ T) (s : Finset (ℕ × ℕ)) :
    cappedStartMass K L T s =
      ∑ xy ∈ startRelationHosts K L s,
        min T ((2 ^ relationRho (twoStartSystem K xy.1 xy.2 L) - 1 : ℕ) : ℝ) := by
  classical
  unfold cappedStartMass startRelationHosts
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro xy _
  split_ifs with h
  · rfl
  · simp only [ne_eq, not_not] at h
    simp [h, min_eq_right hT]

/-- The ceiling times the sparse host count bounds the entire capped mass. -/
theorem cappedStartMass_le_cap_mul_hosts (K L : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (s : Finset (ℕ × ℕ)) :
    cappedStartMass K L T s ≤ T * ((startRelationHosts K L s).card : ℝ) := by
  rw [cappedStartMass_eq_sum_hosts K L hT]
  calc
    _ ≤ ∑ _xy ∈ startRelationHosts K L s, T := Finset.sum_le_sum fun _ _ => min_le_left _ _
    _ = _ := by simp [mul_comm]

/-- Literal capped comparison at a pair of windows, including zero hosts. -/
theorem capped_value_weight_le_four_start_add_host (K x y L : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    min T ((2 ^ relationRho (twoValueSystem K x y L) - 1 : ℕ) : ℝ) ≤
      4 * min T ((2 ^ relationRho (twoStartSystem K x y L) - 1 : ℕ) : ℝ) +
        3 * (if relationRho (twoValueSystem K x y L) ≠ 0 then (1 : ℝ) else 0) := by
  classical
  by_cases hzero : relationRho (twoValueSystem K x y L) = 0
  · simp only [hzero, pow_zero, Nat.sub_self, Nat.cast_zero, ne_eq, not_true_eq_false,
      if_false, mul_zero, add_zero, min_eq_right hT]
    exact mul_nonneg (by norm_num) (le_min hT (Nat.cast_nonneg _))
  · have hraw := value_weight_le_four_start_weight_add_host K x y L
    rw [if_pos hzero] at hraw
    have hraw' : ((2 ^ relationRho (twoValueSystem K x y L) - 1 : ℕ) : ℝ) ≤
        4 * ((2 ^ relationRho (twoStartSystem K x y L) - 1 : ℕ) : ℝ) + 3 := by
      exact_mod_cast hraw
    rw [if_pos hzero, mul_one]
    exact (min_le_min_left T hraw').trans (min_four_mul_add_three_le hT)

/-- The summed host indicator is the exact cardinal, in real arithmetic. -/
theorem sum_value_host_indicator (K L : ℕ) (s : Finset (ℕ × ℕ)) :
    (∑ xy ∈ s, if relationRho (twoValueSystem K xy.1 xy.2 L) ≠ 0 then (1 : ℝ) else 0) =
      ((valueRelationalHosts K L s).card : ℝ) := by
  classical
  simp [valueRelationalHosts, Finset.card_filter, Nat.cast_sum]

/-- Prescribing the signs costs at most four capped start masses and three full hosts. -/
theorem cappedValueMass_le_four_start_add_hosts (K L : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (s : Finset (ℕ × ℕ)) :
    cappedValueMass K L T s ≤ 4 * cappedStartMass K L T s +
      3 * ((valueRelationalHosts K L s).card : ℝ) := by
  classical
  calc
    _ ≤ ∑ xy ∈ s,
        (4 * min T ((2 ^ relationRho (twoStartSystem K xy.1 xy.2 L) - 1 : ℕ) : ℝ) +
          3 * (if relationRho (twoValueSystem K xy.1 xy.2 L) ≠ 0 then (1 : ℝ) else 0)) :=
      Finset.sum_le_sum fun xy _ => capped_value_weight_le_four_start_add_host K xy.1 xy.2 L hT
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_value_host_indicator]; rfl

/-- The capped comparison uses the arithmetic square-product hosts on an adequate positive mask. -/
theorem cappedValueMass_le_four_start_add_square_hosts
    (K L : ℕ) {T : ℝ} (hT : 0 ≤ T) (s : Finset (ℕ × ℕ))
    (hpos : ∀ xy ∈ s, 2 ≤ xy.1 ∧ 2 ≤ xy.2)
    (hcut : ∀ xy ∈ s, xy.1 + L ≤ K + 1 ∧ xy.2 + L ≤ K + 1) :
    cappedValueMass K L T s ≤ 4 * cappedStartMass K L T s +
      3 * ((squareProductHosts L s).card : ℝ) := by
  rw [← valueRelationalHosts_eq_squareProductHosts K L s hpos hcut]
  exact cappedValueMass_le_four_start_add_hosts K L hT s

end
end PaperC.V282.CappedRelationMass
