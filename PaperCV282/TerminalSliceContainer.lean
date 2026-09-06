import PaperCV282.KernelWindowEnergy
import PaperCV282.SmallKernelAnchors
import PaperC.Affine.RationalChannelCode

/-!
# The actual first-start container on a terminal slice

A first start is retained exactly when its complete window contains a value
whose large odd kernel is at most the chosen cap. All boundary values enter
the finite container up to 3X, and each value belongs to at most B windows.
The kernel cap is quantified after the uniform threshold.
-/

namespace PaperC.V282.TerminalSliceContainer

open Affine RationalChannelCode LargeOddKernel TerminalKernelCount KernelWindowEnergy
open SizeTwoHostAsymptotics MacroscopicCanonicalCode
open scoped BigOperators

noncomputable section

/-- First starts in the actual dyadic slice with at least one small-kernel window value. -/
def smallKernelFirstStarts (X L T : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter fun x => (smallKernelOffsets (L + 1) T L x).Nonempty

theorem mem_smallKernelFirstStarts {X L T x : ℕ} :
    x ∈ smallKernelFirstStarts X L T ↔ (X ≤ x ∧ x < 2 * X) ∧
      ∃ i : ℕ, i < L + 1 ∧ largeOddKernel (L + 1) (x - 1 + i) ≤ T := by
  simp [smallKernelFirstStarts, smallKernelOffsets, Finset.Nonempty]

/-- The retained complete-start labels and the incidence offsets are identical. -/
theorem startCompleteVertexLabel_eq_shift {x L : ℕ} (hx : 1 ≤ x) (i : Fin (L + 1)) :
    startCompleteVertexLabel x L i = x - 1 + i.val := by
  unfold startCompleteVertexLabel
  split <;> omega

/-- An actual small-kernel graph label places its start in the exact container. -/
theorem mem_smallKernelFirstStarts_of_label {X L T x : ℕ} (hX : 1 ≤ X)
    (hx : x ∈ Finset.Ico X (2 * X)) (i : Fin (L + 1))
    (hi : largeOddKernel (L + 1) (startCompleteVertexLabel x L i) ≤ T) :
    x ∈ smallKernelFirstStarts X L T := by
  have hxrange := Finset.mem_Ico.mp hx
  exact mem_smallKernelFirstStarts.mpr ⟨hxrange, i.val, i.isLt,
    by simpa only [startCompleteVertexLabel_eq_shift (hX.trans hxrange.1) i] using hi⟩

/-- The finite value cover includes the left boundary `x-1` and every right offset. -/
theorem smallKernelFirstStarts_subset_value_cover {X L T : ℕ} (hX : 2 ≤ X) (hL : L ≤ X) :
    smallKernelFirstStarts X L T ⊆ (Finset.range (L + 1)).biUnion fun i =>
      (boundedLargeKernelValues (L + 1) T (3 * X)).image fun n => n + 1 - i := by
  intro x hx
  obtain ⟨hxrange, i, hi, hk⟩ := mem_smallKernelFirstStarts.mp hx
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_range.mpr hi, Finset.mem_image.mpr ?_⟩
  exact ⟨x - 1 + i, mem_boundedLargeKernelValues.mpr ⟨by omega, by omega, hk⟩, by omega⟩

/-- Each possible small-kernel value costs at most one full window length. -/
theorem card_smallKernelFirstStarts_le {X L T : ℕ} (hX : 2 ≤ X) (hL : L ≤ X) :
    (smallKernelFirstStarts X L T).card ≤
      (L + 1) * (boundedLargeKernelValues (L + 1) T (3 * X)).card := by
  refine (Finset.card_le_card (smallKernelFirstStarts_subset_value_cover hX hL)).trans ?_
  calc
    _ ≤ ∑ _i ∈ Finset.range (L + 1), (boundedLargeKernelValues (L + 1) T (3 * X)).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
    _ = _ := by simp

/-- The square-root kernel cutoff gives its literal three-quarter-power value envelope. -/
theorem card_kernelValues_le_three_quarters_envelope
    {X B T : ℕ} {D : ℝ} (hX : 0 < X) (hB : 1 ≤ B) (hD : 0 ≤ D)
    (hT : (T : ℝ) ≤ D * Real.sqrt ((X : ℝ) * B)) :
    ((boundedLargeKernelValues B T (3 * X)).card : ℝ) ≤
      (4 * Real.sqrt D * B * Real.exp (2 * Real.sqrt B)) * (X : ℝ) ^ (3 / (4 : ℝ)) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hs : Real.sqrt (3 * X : ℝ) ≤ 2 * Real.sqrt X := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hXpos.le]
    nlinarith
  have hsB : Real.sqrt (Real.sqrt B) ≤ (B : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hh : Real.sqrt B ≤ (B : ℝ) := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    nlinarith
  have hsX : Real.sqrt (Real.sqrt X) = (X : ℝ) ^ (1 / (4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le]
    norm_num
  have ht : Real.sqrt T ≤ Real.sqrt D * (X : ℝ) ^ (1 / (4 : ℝ)) * B := by
    calc
      _ ≤ Real.sqrt (D * Real.sqrt ((X : ℝ) * B)) := Real.sqrt_le_sqrt hT
      _ = Real.sqrt D * (Real.sqrt (Real.sqrt X) * Real.sqrt (Real.sqrt B)) := by
        rw [Real.sqrt_mul hD, Real.sqrt_mul hXpos.le, Real.sqrt_mul (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt D * ((X : ℝ) ^ (1 / (4 : ℝ)) * B) := by rw [hsX]; gcongr
      _ = _ := by ring
  have hpower : Real.sqrt X * (X : ℝ) ^ (1 / (4 : ℝ)) = (X : ℝ) ^ (3 / (4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hXpos]
    norm_num
  calc
    _ ≤ 2 * Real.sqrt (3 * X : ℕ) * Real.sqrt T * Real.exp (2 * Real.sqrt B) :=
      card_boundedLargeKernelValues_cast_le_exp B T (3 * X)
    _ ≤ 2 * (2 * Real.sqrt X) * (Real.sqrt D * (X : ℝ) ^ (1 / (4 : ℝ)) * B) *
        Real.exp (2 * Real.sqrt B) := by push_cast; gcongr
    _ = (4 * Real.sqrt D * B * Real.exp (2 * Real.sqrt B)) *
        (Real.sqrt X * (X : ℝ) ^ (1 / (4 : ℝ))) := by ring
    _ = _ := by rw [hpower]

/-- The complete first-start container of Lemma 3.23, uniformly before the natural kernel cap. -/
theorem card_smallKernelFirstStarts_le_three_quarters_eventually
    (C D epsilon : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ C * Real.log X → ∀ T : ℕ,
      (T : ℝ) ≤ D * Real.sqrt ((X : ℝ) * (L + 1)) →
      ((smallKernelFirstStarts X L T).card : ℝ) ≤ (X : ℝ) ^ (3 / (4 : ℝ) + epsilon) := by
  obtain ⟨Xfactor, hfactor⟩ := polynomial_euler_le_rpow_eventually C (4 * Real.sqrt D) epsilon hC hepsilon
  obtain ⟨Xlength, hlength⟩ := logarithmic_power_lt_rpow_eventually C 1 hC (by norm_num) 1 (by omega)
  refine ⟨max Xfactor (max Xlength 2), ?_⟩
  intro X hX L hupper T hT
  have hXtwo : 2 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlen := hlength X (by omega) (L + 1) (by simpa using hupper)
  have hL : L ≤ X := by
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hlen
    exact_mod_cast (show (L : ℝ) ≤ X by linarith)
  have hB : (1 : ℝ) ≤ L + 1 := by have := Nat.cast_nonneg (α := ℝ) L; linarith
  have hf := hfactor X (by omega) L (by simpa using hupper)
  rw [abs_of_nonneg (by positivity)] at hf
  have hpow : (L + 1 : ℝ) ^ 2 ≤ (L + 1 : ℝ) ^ 5 := pow_le_pow_right₀ hB (by omega)
  have hexp : Real.exp (2 * Real.sqrt (L + 1 : ℝ)) ≤ Real.exp (4 * Real.sqrt (L + 1 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sqrt_nonneg (L + 1 : ℝ)]
  have hsmall : 4 * Real.sqrt D * (L + 1 : ℝ) ^ 2 * Real.exp (2 * Real.sqrt (L + 1 : ℝ)) ≤
      (X : ℝ) ^ epsilon := by
    refine le_trans ?_ hf
    gcongr
  have hkernel := card_kernelValues_le_three_quarters_envelope
    (by omega : 0 < X) (by omega : 1 ≤ L + 1) hD (by simpa using hT)
  have hcount : ((smallKernelFirstStarts X L T).card : ℝ) ≤
      (L + 1 : ℝ) * ((boundedLargeKernelValues (L + 1) T (3 * X)).card : ℝ) := by
    exact_mod_cast card_smallKernelFirstStarts_le (T := T) hXtwo hL
  calc
    _ ≤ _ := hcount
    _ ≤ (L + 1 : ℝ) * ((4 * Real.sqrt D * (L + 1 : ℝ) * Real.exp (2 * Real.sqrt (L + 1 : ℝ))) *
        (X : ℝ) ^ (3 / (4 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Nat.cast_add, Nat.cast_one] using hkernel
    _ = (4 * Real.sqrt D * (L + 1 : ℝ) ^ 2 * Real.exp (2 * Real.sqrt (L + 1 : ℝ))) *
        (X : ℝ) ^ (3 / (4 : ℝ)) := by ring
    _ ≤ (X : ℝ) ^ epsilon * (X : ℝ) ^ (3 / (4 : ℝ)) := mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := by rw [← Real.rpow_add hXpos]; congr 1; ring

/-- The integer determinant cap fits the common analytic square-root band. -/
theorem nat_sqrt_terminal_cap_le (X B : ℕ) :
    (Nat.sqrt (6 * X * B) : ℝ) ≤ Real.sqrt 6 * Real.sqrt ((X : ℝ) * B) := by
  calc
    _ ≤ Real.sqrt ((6 * X * B : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    _ = _ := by push_cast; rw [mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]

/-- The exact natural cap supplied by the terminal determinant bound. -/
theorem card_determinantCapFirstStarts_le_three_quarters_eventually
    (C epsilon : ℝ) (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ C * Real.log X →
      ((smallKernelFirstStarts X L (Nat.sqrt (6 * X * (L + 1)))).card : ℝ) ≤
        (X : ℝ) ^ (3 / (4 : ℝ) + epsilon) := by
  obtain ⟨Xzero, hcount⟩ := card_smallKernelFirstStarts_le_three_quarters_eventually
    C (Real.sqrt 6) epsilon hC (by positivity) hepsilon
  refine ⟨Xzero, ?_⟩
  intro X hX L hL
  exact hcount X hX L hL _ (by simpa only [Nat.cast_add, Nat.cast_one] using nat_sqrt_terminal_cap_le X (L + 1))

end
end PaperC.V282.TerminalSliceContainer
