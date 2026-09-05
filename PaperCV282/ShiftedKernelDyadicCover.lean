import PaperCV282.ShiftedKernelBoxAsymptotics
import PaperCV282.DivisorSubpolynomial

/-!
# Exhaustive dyadic coverage above the cube-root kernel cutoff

Dyadic ranges are based at the ceiling of the real cube root. This
preserves the exact lower bound required by the box estimate, including
kernels close to the cutoff. The finite cover is counted with multiplicity
only as an upper bound; no disjointness of the image is assumed.
-/

namespace PaperC.V282.ShiftedKernelDyadicCover

open LargeOddKernel ShiftedKernelRangeCount ShiftedKernelBoxAsymptotics
open scoped BigOperators

noncomputable section

/-- The integer base of the first high-kernel range. -/
def kernelRangeBase (X : ℕ) : ℕ := ⌈(X : ℝ) ^ (1 / (3 : ℝ))⌉₊

/-- Only scales whose lower endpoint can occur below the requested kernel cap. -/
def kernelScales (X T : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 (3 * X) + 1)).filter fun j => 2 ^ j * kernelRangeBase X ≤ T

/-- Both canonical kernels lie above the integer cube-root threshold and below the cap. -/
def highShiftedKernelValues (B T X h : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter fun n =>
    (kernelRangeBase X ≤ largeOddKernel B n ∧ largeOddKernel B n ≤ T) ∧
      (kernelRangeBase X ≤ largeOddKernel B (n + h) ∧ largeOddKernel B (n + h) ≤ T)

/-- Integer dyadic intervals starting at any positive base cover every larger integer. -/
theorem exists_scaled_dyadic_range {R n Z : ℕ} (hR : 0 < R) (hRn : R ≤ n) (hnZ : n ≤ Z) :
    ∃ j < Nat.log 2 Z + 1, 2 ^ j * R ≤ n ∧ n < 2 * (2 ^ j * R) := by
  let j := Nat.log 2 (n / R)
  have hdiv : 0 < n / R := Nat.div_pos hRn hR
  have hlo : 2 ^ j ≤ n / R := Nat.pow_log_le_self 2 (by omega)
  have hhi : n / R < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) _
  have hl : 2 ^ j * R ≤ n := (Nat.le_div_iff_mul_le hR).mp hlo
  have hu : n < 2 ^ (j + 1) * R := (Nat.div_lt_iff_lt_mul hR).mp hhi
  have hj : j ≤ Nat.log 2 Z := Nat.log_mono_right ((Nat.div_le_self n R).trans hnZ)
  refine ⟨j, by omega, hl, ?_⟩
  simpa only [pow_succ] using hu.trans_le (by nlinarith : 2 ^ j * 2 * R ≤ 2 * (2 ^ j * R))

/-- Every high pair enters a genuine pair of admissible dyadic kernel boxes. -/
theorem highShiftedKernelValues_subset_ranges
    {B T X h : ℕ} (hX : 0 < X) (hhX : h ≤ X) :
    highShiftedKernelValues B T X h ⊆
      (kernelScales X T).biUnion fun i => (kernelScales X T).biUnion fun j =>
        shiftedKernelRangeValues B h X (2 ^ i * kernelRangeBase X) (2 ^ j * kernelRangeBase X) := by
  intro n hn
  obtain ⟨hn, hr, hs⟩ := Finset.mem_filter.mp hn
  have hnX := Finset.mem_Ico.mp hn
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hbase : 0 < kernelRangeBase X := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hXreal _)
  have hnr : largeOddKernel B n ≤ 3 * X := (largeOddKernel_le (B := B) (by omega : 0 < n)).trans (by omega)
  have hns : largeOddKernel B (n + h) ≤ 3 * X := (largeOddKernel_le (B := B) (by omega : 0 < n + h)).trans (by omega)
  obtain ⟨i, hi, hir, hirt⟩ := exists_scaled_dyadic_range hbase hr.1 hnr
  obtain ⟨j, hj, hjs, hjst⟩ := exists_scaled_dyadic_range hbase hs.1 hns
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hir.trans hr.2⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hjs.trans hs.2⟩, ?_⟩
  exact mem_shiftedKernelRangeValues.mpr ⟨hnX, ⟨hir, hirt⟩, ⟨hjs, hjst⟩⟩


/-- The number of pairs of scales is subpolynomial, uniformly in the cap. -/
theorem card_kernelScales_sq_le_rpow_eventually
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ T : ℕ,
      ((kernelScales X T).card : ℝ) ^ 2 ≤ (X : ℝ) ^ epsilon := by
  let C : ℝ := 2 / Real.log 2 + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨Xpoly, hpoly⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    C hC 1 2 epsilon hepsilon
  refine ⟨max Xpoly (max (⌈Real.exp 1⌉₊ + 1) 3), ?_⟩
  intro X hX T
  have hXthree : 3 ≤ X := by omega
  have hexp : Real.exp 1 ≤ (X : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈Real.exp 1⌉₊ ≤ X by omega))
  have hlogOne : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have hlog := DivisorSubpolynomial.binary_log_le_polynomial_log
    (by omega : 0 < 3 * X) (by nlinarith : 3 * X ≤ X ^ 2)
  have hceiling : ((Nat.log 2 (3 * X) + 1 : ℕ) : ℝ) ≤ C * Real.log X := by
    dsimp [C]
    push_cast
    norm_num at hlog
    nlinarith
  have hp := hpoly X (by omega) (Nat.log 2 (3 * X)) hceiling
  rw [abs_of_nonneg (by positivity)] at hp
  have hc : ((kernelScales X T).card : ℝ) ≤ (Nat.log 2 (3 * X) + 1 : ℝ) := by
    have hn := Finset.card_filter_le (Finset.range (Nat.log 2 (3 * X) + 1))
      (fun j => 2 ^ j * kernelRangeBase X ≤ T)
    simp only [Finset.card_range] at hn
    exact_mod_cast hn
  exact (pow_le_pow_left₀ (by positivity) hc 2).trans (by simpa using hp)

/-- The complete high-kernel population after both dyadic scale sums. -/
theorem card_highShiftedKernelValues_le_two_thirds_eventually
    (C D epsilon : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ C * Real.log X → ∀ T h : ℕ,
      0 < h → h ≤ L + 1 →
      (T : ℝ) ≤ D * Real.sqrt ((X : ℝ) * (L + 1)) →
      ((highShiftedKernelValues (L + 1) T X h).card : ℝ) ≤
        (X : ℝ) ^ (2 / (3 : ℝ) + epsilon) := by
  obtain ⟨Xbox, hbox⟩ := card_shiftedKernelRangeValues_le_two_thirds_eventually
    C D (epsilon / 2) hC hD (by positivity)
  obtain ⟨Xscales, hscales⟩ := card_kernelScales_sq_le_rpow_eventually
    (epsilon / 2) (by positivity)
  obtain ⟨Xlength, hlength⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    C 1 hC (by norm_num) 1 (by omega)
  refine ⟨max Xbox (max Xscales (max Xlength 1)), ?_⟩
  intro X hX L hL T h hh hhB hT
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hl := hlength X (by omega) (L + 1) (by simpa using hL)
  have hhX : h ≤ X := by
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hl
    have hhreal : (h : ℝ) ≤ L + 1 := by exact_mod_cast hhB
    exact_mod_cast (show (h : ℝ) ≤ X by linarith)
  have hscale : ∀ i ∈ kernelScales X T,
      (X : ℝ) ^ (1 / (3 : ℝ)) ≤ (2 ^ i * kernelRangeBase X : ℕ) ∧
      ((2 ^ i * kernelRangeBase X : ℕ) : ℝ) ≤ D * Real.sqrt ((X : ℝ) * (L + 1)) := by
    intro i hi
    have htwo : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
    constructor
    · exact (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_mul_of_pos_left (kernelRangeBase X) (by omega : 0 < 2 ^ i)))
    · have hnat := (Finset.mem_filter.mp hi).2
      exact (by exact_mod_cast hnat : ((2 ^ i * kernelRangeBase X : ℕ) : ℝ) ≤ T).trans hT
  have hlocal : ∀ i ∈ kernelScales X T, ∀ j ∈ kernelScales X T,
      ((shiftedKernelRangeValues (L + 1) h X (2 ^ i * kernelRangeBase X)
        (2 ^ j * kernelRangeBase X)).card : ℝ) ≤ (X : ℝ) ^ (2 / (3 : ℝ) + epsilon / 2) := by
    intro i hi j hj
    exact hbox X (by omega) L hL h _ _ hh hhB
      (hscale i hi).1 (hscale j hj).1 (hscale i hi).2 (hscale j hj).2
  have hcover : (highShiftedKernelValues (L + 1) T X h).card ≤
      ∑ i ∈ kernelScales X T, ∑ j ∈ kernelScales X T,
        (shiftedKernelRangeValues (L + 1) h X (2 ^ i * kernelRangeBase X)
          (2 ^ j * kernelRangeBase X)).card := by
    refine (Finset.card_le_card (highShiftedKernelValues_subset_ranges (by omega) hhX)).trans ?_
    exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => Finset.card_biUnion_le)
  have hbound : ((highShiftedKernelValues (L + 1) T X h).card : ℝ) ≤
      ((kernelScales X T).card : ℝ) ^ 2 * (X : ℝ) ^ (2 / (3 : ℝ) + epsilon / 2) := by
    have hc : ((highShiftedKernelValues (L + 1) T X h).card : ℝ) ≤
      ∑ i ∈ kernelScales X T, ∑ j ∈ kernelScales X T,
        ((shiftedKernelRangeValues (L + 1) h X (2 ^ i * kernelRangeBase X)
          (2 ^ j * kernelRangeBase X)).card : ℝ) := by exact_mod_cast hcover
    refine hc.trans ?_
    calc
      _ ≤ ∑ _i ∈ kernelScales X T, ∑ _j ∈ kernelScales X T,
          (X : ℝ) ^ (2 / (3 : ℝ) + epsilon / 2) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum (hlocal i hi)
      _ = _ := by simp [pow_two, mul_assoc]
  calc
    _ ≤ _ := hbound
    _ ≤ (X : ℝ) ^ (epsilon / 2) * (X : ℝ) ^ (2 / (3 : ℝ) + epsilon / 2) :=
      mul_le_mul_of_nonneg_right (hscales X (by omega) T) (by positivity)
    _ = _ := by rw [← Real.rpow_add hXpos]; congr 1; ring

end
end PaperC.V282.ShiftedKernelDyadicCover
