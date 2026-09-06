import PaperC.Arithmetic.BalasubramanianShoreyMaximum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Source-shaped square-product exclusion

Shorey, RIMS Kokyuroku 886 (1994), pp.55--56, equation (15) and
the subsequent square case. The coefficient is smooth, with no size bound.
The proposition is an explicit literature argument, never an axiom.
-/
namespace PaperC.V282.PostQuadraticLiterature

open Filter BalasubramanianShoreyInput
open scoped Topology

noncomputable section

/-- The square case recorded by Shorey, with the source's zero-based shifts.
The threshold precedes the height, coefficient, square root and shifts. -/
def ShoreySquareProductStatement : Prop :=
  ∃ theta : ℝ, ∀ epsilon : ℝ, 0 < epsilon →
    ∃ Kzero : ℕ, ∀ k ≥ Kzero, ∀ z b y : ℕ, ∀ offsets : Finset ℕ,
      2 ≤ offsets.card → offsets ⊆ Finset.range k →
      0 < b → 0 < y → IsSmoothAt k b →
      (∏ d ∈ offsets, (z + d)) = b * y ^ 2 →
      Real.exp (1 - theta + epsilon) *
        ((k : ℝ) * Real.log k / Real.log (Real.log k)) < z →
      (offsets.card : ℝ) < mu k theta

/-- Every fixed multiple of the source height is eventually below k². -/
theorem square_exceeds_source_height_eventually (theta : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      Real.exp (2 - theta) *
        ((k : ℝ) * Real.log k / Real.log (Real.log k)) < (k : ℝ) ^ 2 := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun k : ℕ => Real.exp (2 - theta) * (Real.log k / k))
      atTop (𝓝 0) := by
    simpa using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul (Real.exp (2 - theta))
  filter_upwards [hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (Real.tendsto_log_atTop.comp hlog).eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 2] with k hr hk htwo
  have hkp : 0 < (k : ℝ) := by positivity
  have hl : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast htwo)
  have hh : Real.exp (2 - theta) * Real.log k < (k : ℝ) := by
    have := (div_lt_iff₀ hkp).mp (show
      Real.exp (2 - theta) * Real.log k / k < 1 by simpa [mul_div_assoc] using hr)
    simpa using this
  calc
    _ ≤ Real.exp (2 - theta) * ((k : ℝ) * Real.log k) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact div_le_self (by positivity) hk
    _ < (k : ℝ) ^ 2 := by nlinarith

/-- Moving the source shifts by one preserves the actual integer product. -/
theorem shifted_product_eq {k m : ℕ} {offsets : Finset ℕ}
    (h : offsets ⊆ Finset.Icc 1 k) :
    (∏ d ∈ offsets.image (fun d => d - 1), (m + 1 + d)) =
      ∏ d ∈ offsets, (m + d) := by
  classical
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro d hd
    have := (Finset.mem_Icc.mp (h hd)).1
    omega
  · intro a ha b hb hab
    change a - 1 = b - 1 at hab
    have := (Finset.mem_Icc.mp (h ha)).1
    have := (Finset.mem_Icc.mp (h hb)).1
    omega

/-- The published square case implies the retained product interface.
No defective-window or probability conclusion is imported. -/
theorem balasubramanianShorey_of_square_product
    (hShorey : ShoreySquareProductStatement) : BalasubramanianShoreyStatement := by
  classical
  obtain ⟨theta, hs⟩ := hShorey
  obtain ⟨Kzero, hKzero⟩ := hs 1 (by norm_num)
  obtain ⟨Kh, hKh⟩ := eventually_atTop.mp (square_exceeds_source_height_eventually theta)
  refine ⟨theta, max Kzero Kh, ?_⟩
  intro k m offsets b y _hk hm hdense hprod
  by_contra hlarge
  have hK : Kzero ≤ k := by omega
  have hH : Kh ≤ k := by omega
  obtain ⟨htwo, _hcard, hoffsets, hb, hy, heq, hsmooth⟩ := hprod
  have hinj : Set.InjOn (fun d : ℕ => d - 1) offsets := by
    intro a ha b hb hab
    change a - 1 = b - 1 at hab
    have := (Finset.mem_Icc.mp (hoffsets ha)).1
    have := (Finset.mem_Icc.mp (hoffsets hb)).1
    omega
  have hcard : (offsets.image (fun d => d - 1)).card = offsets.card :=
    Finset.card_image_of_injOn hinj
  have hrange : offsets.image (fun d => d - 1) ⊆ Finset.range k := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    have := Finset.mem_Icc.mp (hoffsets ha)
    exact Finset.mem_range.mpr (by omega)
  have hheight : Real.exp (1 - theta + 1) *
      ((k : ℝ) * Real.log k / Real.log (Real.log k)) < (m + 1 : ℕ) := by
    have hh := hKh k hH
    have hmreal : (k : ℝ) ^ 2 < m := by exact_mod_cast hm
    have he : 1 - theta + 1 = 2 - theta := by ring
    rw [he]
    push_cast
    linarith
  have ht := hKzero k hK (m + 1) b y (offsets.image (fun d => d - 1))
    (by simpa only [hcard] using htwo) hrange hb hy hsmooth
    ((shifted_product_eq hoffsets).trans heq) hheight
  rw [hcard] at ht
  exact (not_lt_of_ge hdense) ht

end
end PaperC.V282.PostQuadraticLiterature
