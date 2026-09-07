import PaperCV282.ShiftedKernelPairCount

/-!
# Shifted small-kernel energy in the actual start windows

For starts in `[X,2X)`, the values `x-1+i` lie in `[X-1,2X+L)`.
Three dyadic value slices based at `floor(X/2)` cover this enlarged
interval. The uniform pair count transports to each slice, and exact
window double counting gives the explicit factor `(L+1)^2`.
-/

namespace PaperC.V282.MacroscopicKernelEnergy

open KernelWindowEnergy ShiftedKernelPairCount LogarithmicWordPowers MacroscopicCanonicalCode
open scoped BigOperators

noncomputable section

/-- Three adjacent dyadic value slices cover the actual enlarged window interval. -/
theorem shiftedKernelValues_subset_three_slices
    (B T h X L : ℕ) (hX : 6 ≤ X) (hL : L ≤ X) :
    shiftedKernelValues B T (X - 1) (2 * X + L) h ⊆
      shiftedKernelValues B T (X / 2) (2 * (X / 2)) h ∪
        shiftedKernelValues B T (2 * (X / 2)) (2 * (2 * (X / 2))) h ∪
        shiftedKernelValues B T (4 * (X / 2)) (2 * (4 * (X / 2))) h := by
  intro n hn
  obtain ⟨hnrange, hk⟩ := Finset.mem_filter.mp hn
  have hnrange' := Finset.mem_Ico.mp hnrange
  by_cases hnfirst : n < 2 * (X / 2)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hnfirst⟩, hk⟩))
  by_cases hnsecond : n < 4 * (X / 2)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hk⟩))
  · exact Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hk⟩)

/-- Counting the three-slice cover retains every boundary occurrence. -/
theorem card_shiftedKernelValues_le_three_slices
    (B T h X L : ℕ) (hX : 6 ≤ X) (hL : L ≤ X) :
    (shiftedKernelValues B T (X - 1) (2 * X + L) h).card ≤
      (shiftedKernelValues B T (X / 2) (2 * (X / 2)) h).card +
        (shiftedKernelValues B T (2 * (X / 2)) (2 * (2 * (X / 2))) h).card +
        (shiftedKernelValues B T (4 * (X / 2)) (2 * (4 * (X / 2))) h).card := by
  have hc := (Finset.card_le_card
    (shiftedKernelValues_subset_three_slices B T h X L hX hL)).trans (Finset.card_union_le _ _)
  have hu := Finset.card_union_le
    (s := shiftedKernelValues B T (X / 2) (2 * (X / 2)) h)
    (t := shiftedKernelValues B T (2 * (X / 2)) (2 * (2 * (X / 2))) h)
  omega

/-- Both the logarithmic band and the square-root cap transport to nearby value slices. -/
theorem kernel_parameters_on_nearby_slice
    {X Z L T : ℕ} {C D : ℝ} (hX : 0 < X) (hZ : 3 ≤ Z) (hXZ : X ≤ 3 * Z)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hL : (L + 1 : ℝ) ≤ C * Real.log X)
    (hT : (T : ℝ) ≤ D * Real.sqrt ((X : ℝ) * (L + 1))) :
    (L + 1 : ℝ) ≤ (2 * C) * Real.log Z ∧
      (T : ℝ) ≤ (2 * D) * Real.sqrt ((Z : ℝ) * (L + 1)) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hZreal : (3 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hXZreal : (X : ℝ) ≤ 3 * Z := by exact_mod_cast hXZ
  have hlog : Real.log X ≤ 2 * Real.log Z := by
    have hbound : (X : ℝ) ≤ (Z : ℝ) ^ 2 := by nlinarith
    have hh := Real.log_le_log hXpos hbound
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hsqrt : Real.sqrt ((X : ℝ) * (L + 1)) ≤ 2 * Real.sqrt ((Z : ℝ) * (L + 1)) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hXZreal (by positivity : (0 : ℝ) ≤ L + 1)]
  constructor
  · exact hL.trans ((mul_le_mul_of_nonneg_left hlog hC).trans_eq (by ring))
  · exact hT.trans ((mul_le_mul_of_nonneg_left hsqrt hD).trans_eq (by ring))

/-- The complete shifted-pair count on the enlarged actual value interval. -/
theorem card_enlarged_shiftedKernelValues_le_two_thirds_eventually
    (C D epsilon : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ C * Real.log X → ∀ T h : ℕ,
      0 < h → h ≤ L + 1 →
      (T : ℝ) ≤ D * Real.sqrt ((X : ℝ) * (L + 1)) →
      ((shiftedKernelValues (L + 1) T (X - 1) (2 * X + L) h).card : ℝ) ≤
        (X : ℝ) ^ (2 / (3 : ℝ) + epsilon) := by
  let eta : ℝ := min (epsilon / 2) (1 / 6)
  have heta : 0 < eta := lt_min (by positivity) (by norm_num)
  have hetaE : eta ≤ epsilon / 2 := min_le_left _ _
  have hetaSixth : eta ≤ 1 / 6 := min_le_right _ _
  obtain ⟨Xpair, hpair⟩ := card_shiftedKernelValues_le_two_thirds_eventually
    (2 * C) (2 * D) eta (by positivity) (by positivity) heta
  obtain ⟨Xconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    C hC 6 0 (epsilon / 2) (by positivity)
  obtain ⟨Xlength, hlength⟩ := logarithmic_power_lt_rpow_eventually C 1 hC (by norm_num) 1 (by omega)
  refine ⟨max (2 * Xpair + 2) (max Xconstant (max Xlength 6)), ?_⟩
  intro X hX L hL T h hh hhB hT
  have hXsix : 6 ≤ X := by omega
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlen := hlength X (by omega) (L + 1) (by simpa using hL)
  have hLX : L ≤ X := by
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hlen
    exact_mod_cast (show (L : ℝ) ≤ X by linarith)
  have hsix : (6 : ℝ) ≤ (X : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant X (by omega) L (by simpa using hL)
  have hlocal : ∀ Z : ℕ, X / 2 ≤ Z → Z ≤ 2 * X →
      ((shiftedKernelValues (L + 1) T Z (2 * Z) h).card : ℝ) ≤
        2 * (X : ℝ) ^ (2 / (3 : ℝ) + eta) := by
    intro Z hZmin hZmax
    have hZthree : 3 ≤ Z := by omega
    have hXZ : X ≤ 3 * Z := by omega
    obtain ⟨hLZ, hTZ⟩ := kernel_parameters_on_nearby_slice (by omega : 0 < X) hZthree hXZ hC hD hL hT
    have hc := hpair Z (by omega) L hLZ T h hh hhB hTZ
    have hpowTwo : (2 : ℝ) ^ (2 / (3 : ℝ) + eta) ≤ 2 := by
      calc
        _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := Real.rpow_one _
    calc
      _ ≤ _ := hc
      _ ≤ (2 * X : ℝ) ^ (2 / (3 : ℝ) + eta) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hZmax) (by positivity)
      _ = (2 : ℝ) ^ (2 / (3 : ℝ) + eta) * (X : ℝ) ^ (2 / (3 : ℝ) + eta) :=
        Real.mul_rpow (by positivity) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hpowTwo (by positivity)
  have hfirst := hlocal (X / 2) le_rfl (by omega)
  have hsecond := hlocal (2 * (X / 2)) (by omega) (by omega)
  have hthird := hlocal (4 * (X / 2)) (by omega) (by omega)
  have hnat := card_shiftedKernelValues_le_three_slices (L + 1) T h X L hXsix hLX
  have hfinite : ((shiftedKernelValues (L + 1) T (X - 1) (2 * X + L) h).card : ℝ) ≤
      6 * (X : ℝ) ^ (2 / (3 : ℝ) + eta) := by
    have hreal : ((shiftedKernelValues (L + 1) T (X - 1) (2 * X + L) h).card : ℝ) ≤
        ((shiftedKernelValues (L + 1) T (X / 2) (2 * (X / 2)) h).card : ℝ) +
          ((shiftedKernelValues (L + 1) T (2 * (X / 2)) (2 * (2 * (X / 2))) h).card : ℝ) +
          ((shiftedKernelValues (L + 1) T (4 * (X / 2)) (2 * (4 * (X / 2))) h).card : ℝ) := by
      exact_mod_cast hnat
    linarith
  calc
    _ ≤ _ := hfinite
    _ ≤ (X : ℝ) ^ (epsilon / 2) * (X : ℝ) ^ (2 / (3 : ℝ) + eta) :=
      mul_le_mul_of_nonneg_right hsix (by positivity)
    _ = (X : ℝ) ^ (epsilon / 2 + (2 / (3 : ℝ) + eta)) := (Real.rpow_add hXpos _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hXone (by linarith)

/-- Lemma 3.24 with its literal binomial energy and explicit square of the window length. -/
theorem lemma_three_twenty_four
    (C D epsilon : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ C * Real.log X → ∀ T : ℕ,
      (T : ℝ) ≤ D * Real.sqrt ((X : ℝ) * (L + 1)) →
      (windowEnergy (L + 1) T L (Finset.Ico X (2 * X)) : ℝ) ≤
        (X : ℝ) ^ (2 / (3 : ℝ) + epsilon) * (L + 1 : ℝ) ^ 2 := by
  obtain ⟨Xpair, hpair⟩ := card_enlarged_shiftedKernelValues_le_two_thirds_eventually
    C D epsilon hC hD hepsilon
  refine ⟨max Xpair 1, ?_⟩
  intro X hX L hL T hT
  have hfinite := dyadic_windowEnergy_le_length_mul_sum_shifted (L + 1) T L X (by omega)
  have hcast : (windowEnergy (L + 1) T L (Finset.Ico X (2 * X)) : ℝ) ≤
      (L + 1 : ℝ) * ∑ h ∈ Finset.Icc 1 L,
        ((shiftedKernelValues (L + 1) T (X - 1) (2 * X + L) h).card : ℝ) := by exact_mod_cast hfinite
  have hsum : (∑ h ∈ Finset.Icc 1 L,
      ((shiftedKernelValues (L + 1) T (X - 1) (2 * X + L) h).card : ℝ)) ≤
        (L : ℝ) * (X : ℝ) ^ (2 / (3 : ℝ) + epsilon) := by
    calc
      _ ≤ ∑ _h ∈ Finset.Icc 1 L, (X : ℝ) ^ (2 / (3 : ℝ) + epsilon) := by
        apply Finset.sum_le_sum
        intro h hh
        have hh' := Finset.mem_Icc.mp hh
        exact hpair X (by omega) L hL T h (by omega) (by omega) hT
      _ = _ := by simp [Nat.card_Icc]
  calc
    _ ≤ _ := hcast
    _ ≤ (L + 1 : ℝ) * ((L : ℝ) * (X : ℝ) ^ (2 / (3 : ℝ) + epsilon)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := by
      have hpower : (0 : ℝ) ≤ (X : ℝ) ^ (2 / (3 : ℝ) + epsilon) := by positivity
      nlinarith

end
end PaperC.V282.MacroscopicKernelEnergy
