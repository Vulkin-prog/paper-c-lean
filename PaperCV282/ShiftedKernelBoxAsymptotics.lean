import PaperCV282.ShiftedKernelRangeCount
import PaperCV282.SizeTwoHostAsymptotics

/-!
# The two-thirds bound in each shifted-kernel box

The lower kernel cutoff is `X^(1/3)` and the upper cutoff is a fixed
multiple of `sqrt(X*B)`. Their affine count is `X^(2/3)` times a polynomial
in `B` and the smooth Euler product squared. The logarithmic upper band
absorbs both losses uniformly before the shift and both kernel ranges.
This module does not sum the boxes or count their incidences in windows.
-/

namespace PaperC.V282.ShiftedKernelBoxAsymptotics

open DefectCounting ShiftedKernelRangeCount TerminalKernelCount
open SizeTwoHostAsymptotics MacroscopicCanonicalCode
open scoped BigOperators

noncomputable section

/-- Algebraic form of the finite shifted-pair estimate in a single kernel box. -/
theorem card_shiftedKernelRangeValues_le_sqrt_product
    (B h X R S : ℕ) (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    (hR : 0 < R) (hS : 0 < S) :
    ((shiftedKernelRangeValues B h X R S).card : ℝ) ≤
      12 * (∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹)) ^ 2 *
        ((X : ℝ) / Real.sqrt ((R : ℝ) * S) +
          2 * h * Real.sqrt ((R : ℝ) * S)) := by
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  have hz : 0 < Real.sqrt ((R : ℝ) * S) := Real.sqrt_pos.mpr (mul_pos hRreal hSreal)
  have hprod : Real.sqrt ((3 * X : ℝ) / R) * Real.sqrt ((3 * X : ℝ) / S) =
      (3 * X : ℝ) / Real.sqrt ((R : ℝ) * S) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show ((3 * X : ℝ) / R) * ((3 * X : ℝ) / S) =
      (3 * X : ℝ) ^ 2 / ((R : ℝ) * S) by ring]
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  have hsquare := Real.sq_sqrt (mul_nonneg hRreal.le hSreal.le)
  refine (card_shiftedKernelRangeValues_le_sqrt_fibres B h X R S hX hh hhX hR hS).trans_eq ?_
  rw [show 4 * Real.sqrt ((3 * X : ℝ) / R) * Real.sqrt ((3 * X : ℝ) / S) =
    4 * (Real.sqrt ((3 * X : ℝ) / R) * Real.sqrt ((3 * X : ℝ) / S)) by ring, hprod]
  calc
    _ = 12 * (∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹)) ^ 2 *
        ((X : ℝ) / Real.sqrt ((R : ℝ) * S) +
          2 * h * ((R : ℝ) * S) / Real.sqrt ((R : ℝ) * S)) := by
      field_simp
      ring
    _ = _ := by
      have hdiv : ((R : ℝ) * S) / Real.sqrt ((R : ℝ) * S) = Real.sqrt ((R : ℝ) * S) := by
        apply (div_eq_iff hz.ne').mpr
        simpa only [pow_two] using hsquare.symm
      rw [mul_div_assoc, hdiv]

/-- The elementary two-thirds comparison for two kernel ranges. -/
theorem sqrt_product_profile_le_two_thirds
    {X B R S h D : ℝ} (hX : 1 ≤ X) (hB : 1 ≤ B)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hhB : h ≤ B) (hD : 0 ≤ D)
    (hRlower : X ^ (1 / (3 : ℝ)) ≤ R) (hSlower : X ^ (1 / (3 : ℝ)) ≤ S)
    (hRupper : R ≤ D * Real.sqrt (X * B)) (hSupper : S ≤ D * Real.sqrt (X * B)) :
    X / Real.sqrt (R * S) + 2 * h * Real.sqrt (R * S) ≤
      (1 + 2 * D) * B ^ 2 * X ^ (2 / (3 : ℝ)) := by
  have hXpos : 0 < X := by linarith
  have hBpos : 0 < B := by linarith
  have hlow : X ^ (1 / (3 : ℝ)) ≤ Real.sqrt (R * S) := by
    have hmul := mul_le_mul hRlower hSlower (by positivity) hR
    have hs := Real.sqrt_le_sqrt hmul
    simpa only [← pow_two, Real.sqrt_sq (Real.rpow_nonneg hXpos.le _)] using hs
  have hzpos : 0 < Real.sqrt (R * S) := (Real.rpow_pos_of_pos hXpos _).trans_le hlow
  have hupp : Real.sqrt (R * S) ≤ D * Real.sqrt (X * B) := by
    have hmul := mul_le_mul hRupper hSupper hS (by positivity : 0 ≤ D * Real.sqrt (X * B))
    have hs := Real.sqrt_le_sqrt hmul
    simpa only [← pow_two, Real.sqrt_sq (by positivity : 0 ≤ D * Real.sqrt (X * B))] using hs
  have hrootX : Real.sqrt X ≤ X ^ (2 / (3 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hrootB : Real.sqrt B ≤ B := by
    exact (Real.sqrt_le_iff).mpr ⟨hBpos.le, by nlinarith⟩
  have hupp' : Real.sqrt (R * S) ≤ D * X ^ (2 / (3 : ℝ)) * B := by
    refine hupp.trans ?_
    rw [Real.sqrt_mul hXpos.le]
    calc
      _ ≤ D * (X ^ (2 / (3 : ℝ)) * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hrootX hrootB (by positivity) (by positivity)) hD
      _ = _ := by ring
  have hfirst : X / Real.sqrt (R * S) ≤ X ^ (2 / (3 : ℝ)) := by
    apply (div_le_iff₀ hzpos).mpr
    calc
      X = X ^ (2 / (3 : ℝ)) * X ^ (1 / (3 : ℝ)) := by
        rw [← Real.rpow_add hXpos, show (2 / (3 : ℝ)) + 1 / 3 = 1 by ring, Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  have hsecond : h * Real.sqrt (R * S) ≤ D * B ^ 2 * X ^ (2 / (3 : ℝ)) := by
    have hp := mul_le_mul hhB hupp' (by positivity : 0 ≤ Real.sqrt (R * S)) hBpos.le
    exact hp.trans_eq (by ring)
  have hBsq : 1 ≤ B ^ 2 := one_le_pow₀ hB
  nlinarith [mul_le_mul_of_nonneg_right hBsq (Real.rpow_nonneg hXpos.le (2 / (3 : ℝ)))]

/-- Every box in the terminal kernel range obeys a finite two-thirds/Euler envelope. -/
theorem card_shiftedKernelRangeValues_le_two_thirds_envelope
    (B h X R S : ℕ) (D : ℝ) (hX : 1 ≤ X) (hB : 1 ≤ B)
    (hh : 0 < h) (hhB : h ≤ B) (hhX : h ≤ X) (hD : 0 ≤ D)
    (hRlower : (X : ℝ) ^ (1 / (3 : ℝ)) ≤ R)
    (hSlower : (X : ℝ) ^ (1 / (3 : ℝ)) ≤ S)
    (hRupper : (R : ℝ) ≤ D * Real.sqrt ((X : ℝ) * B))
    (hSupper : (S : ℝ) ≤ D * Real.sqrt ((X : ℝ) * B)) :
    ((shiftedKernelRangeValues B h X R S).card : ℝ) ≤
      (12 * (1 + 2 * D) * (B : ℝ) ^ 5 * Real.exp (4 * Real.sqrt B)) *
        (X : ℝ) ^ (2 / (3 : ℝ)) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hR : 0 < R := by exact_mod_cast (Real.rpow_pos_of_pos hXpos (1 / (3 : ℝ))).trans_le hRlower
  have hS : 0 < S := by exact_mod_cast (Real.rpow_pos_of_pos hXpos (1 / (3 : ℝ))).trans_le hSlower
  have hprofile := sqrt_product_profile_le_two_thirds (h := (h : ℝ))
    (by exact_mod_cast hX) (by exact_mod_cast hB) (by positivity) (by positivity)
    (by exact_mod_cast hhB) hD hRlower hSlower hRupper hSupper
  have hW : 0 ≤ ∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹) := by positivity
  have hEuler : (∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹)) ^ 2 ≤
      Real.exp (4 * Real.sqrt B) := by
    have he := prod_smallPrimesUpTo_one_add_inv_sqrt_le B
    calc
      _ ≤ (Real.exp (2 * Real.sqrt B)) ^ 2 := pow_le_pow_left₀ hW he 2
      _ = _ := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hBpow : (B : ℝ) ^ 2 ≤ (B : ℝ) ^ 5 :=
    pow_le_pow_right₀ (by exact_mod_cast hB) (by omega)
  calc
    _ ≤ 12 * (∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹)) ^ 2 *
        ((X : ℝ) / Real.sqrt ((R : ℝ) * S) + 2 * h * Real.sqrt ((R : ℝ) * S)) :=
      card_shiftedKernelRangeValues_le_sqrt_product B h X R S (by omega) hh hhX hR hS
    _ ≤ 12 * Real.exp (4 * Real.sqrt B) *
        ((1 + 2 * D) * (B : ℝ) ^ 5 * (X : ℝ) ^ (2 / (3 : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hEuler (by norm_num)
      · exact hprofile.trans (by gcongr)
      · positivity
      · positivity
    _ = _ := by ring

/-- Uniform two-thirds bound in each individual dyadic kernel box.
The common threshold precedes the shift and both independently chosen ranges. -/
theorem card_shiftedKernelRangeValues_le_two_thirds_eventually
    (C D epsilon : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ C * Real.log X →
      ∀ h R S : ℕ, 0 < h → h ≤ L + 1 →
      (X : ℝ) ^ (1 / (3 : ℝ)) ≤ R →
      (X : ℝ) ^ (1 / (3 : ℝ)) ≤ S →
      (R : ℝ) ≤ D * Real.sqrt ((X : ℝ) * (L + 1)) →
      (S : ℝ) ≤ D * Real.sqrt ((X : ℝ) * (L + 1)) →
      ((shiftedKernelRangeValues (L + 1) h X R S).card : ℝ) ≤
        (X : ℝ) ^ (2 / (3 : ℝ) + epsilon) := by
  obtain ⟨Xfactor, hfactor⟩ := polynomial_euler_le_rpow_eventually C
    (12 * (1 + 2 * D)) epsilon hC hepsilon
  obtain ⟨Xlength, hlength⟩ := logarithmic_power_lt_rpow_eventually
    C 1 hC (by norm_num) 1 (by omega)
  refine ⟨max Xfactor (max Xlength 1), ?_⟩
  intro X hX L hL h R S hh hhB hRlower hSlower hRupper hSupper
  have hXone : 1 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlen := hlength X (by omega) (L + 1) (by simpa using hL)
  have hhX : h ≤ X := by
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hlen
    have hhreal : (h : ℝ) ≤ L + 1 := by exact_mod_cast hhB
    exact_mod_cast (show (h : ℝ) ≤ X by linarith)
  have hfinite := card_shiftedKernelRangeValues_le_two_thirds_envelope
    (L + 1) h X R S D hXone (by omega) hh hhB hhX hD
    hRlower hSlower (by simpa using hRupper) (by simpa using hSupper)
  have hf := hfactor X (by omega) L (by simpa using hL)
  rw [abs_of_nonneg (by positivity)] at hf
  calc
    _ ≤ _ := hfinite
    _ ≤ (X : ℝ) ^ epsilon * (X : ℝ) ^ (2 / (3 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Nat.cast_add, Nat.cast_one] using hf
    _ = _ := by rw [← Real.rpow_add hXpos]; congr 1; ring

end
end PaperC.V282.ShiftedKernelBoxAsymptotics
