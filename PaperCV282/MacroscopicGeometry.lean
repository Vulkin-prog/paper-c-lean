import PaperCV282.TwoWindowParity
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The macroscopic start interval

The article uses the integer starts in `[ceil(M^δ), M)`. For `M ≥ 2`
and `δ > 0`, its lower endpoint is at least two, so a natural interval
represents exactly those positive integer starts. The real-threshold
membership theorem makes the ceiling convention explicit.

No assumption `δ < 1` is needed for this geometry: an empty interval is
allowed. The separation predicate is the existing one for the complete
length-`L + 1` vertex windows.
-/

namespace PaperC.V282.MacroscopicGeometry

open TwoWindowParity

noncomputable section

/-- The article's macroscopic interval, represented by natural starts. -/
def macroscopicStarts (M : ℕ) (δ : ℝ) : Finset ℕ :=
  Finset.Ico ⌈(M : ℝ) ^ δ⌉₊ M

/-- Membership uses the inclusive ceiling and the exclusive upper endpoint. -/
@[simp]
theorem mem_macroscopicStarts (M : ℕ) (δ : ℝ) (x : ℕ) :
    x ∈ macroscopicStarts M δ ↔ ⌈(M : ℝ) ^ δ⌉₊ ≤ x ∧ x < M := by
  simp [macroscopicStarts]

/-- The natural ceiling gives exactly the displayed real lower threshold. -/
theorem mem_macroscopicStarts_iff_real (M : ℕ) (δ : ℝ) (x : ℕ) :
    x ∈ macroscopicStarts M δ ↔ (M : ℝ) ^ δ ≤ (x : ℝ) ∧ x < M := by
  simp [macroscopicStarts, Nat.ceil_le]

/-- Positive macroscopic exponents put the first possible start above one. -/
theorem two_le_macroscopic_lowerEndpoint {M : ℕ} {δ : ℝ}
    (hM : 2 ≤ M) (hδ : 0 < δ) :
    2 ≤ ⌈(M : ℝ) ^ δ⌉₊ := by
  have hpow : (1 : ℝ) < (M : ℝ) ^ δ :=
    Real.one_lt_rpow (by exact_mod_cast (show 1 < M by omega)) hδ
  have hceil : 1 < ⌈(M : ℝ) ^ δ⌉₊ :=
    Nat.lt_ceil.mpr (by simpa only [Nat.cast_one] using hpow)
  omega

/-- Every macroscopic start lies in the global positive interval. -/
theorem macroscopicStarts_subset_Icc {M : ℕ} {δ : ℝ}
    (hM : 2 ≤ M) (hδ : 0 < δ) :
    macroscopicStarts M δ ⊆ Finset.Icc 2 M := by
  intro x hx
  obtain ⟨hlower, hupper⟩ := (mem_macroscopicStarts M δ x).mp hx
  exact Finset.mem_Icc.mpr
    ⟨(two_le_macroscopic_lowerEndpoint hM hδ).trans hlower, hupper.le⟩

/-- Separated macroscopic pairs are contained in the same global square. -/
theorem separatedPairs_macroscopicStarts_subset_Icc_product
    {M : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) (L : ℕ) :
    separatedPairs (macroscopicStarts M δ) L ⊆
      Finset.Icc 2 M ×ˢ Finset.Icc 2 M := by
  intro xy hxy
  have hpair := (mem_separatedPairs (macroscopicStarts M δ) L xy.1 xy.2).mp hxy
  exact Finset.mem_product.mpr
    ⟨macroscopicStarts_subset_Icc hM hδ hpair.1,
      macroscopicStarts_subset_Icc hM hδ hpair.2.1⟩

end
end PaperC.V282.MacroscopicGeometry
