import PaperC.Arithmetic.IntervalCongruence
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# The affine fibres in shifted small-kernel energy

For fixed quotients `q,q'`, pairs of kernels solve `q*r+h=q'*s`.
Projection to `r` is injective and lies in one congruence class modulo
`q'/gcd(q',q)`. This gives the finite box count underlying Lemma 3.24.
The coefficients need not be coprime and no kernel estimate is assumed.
-/

namespace PaperC.V282.ShiftedKernelBoxCount

noncomputable section

/-- All natural solutions of one shifted affine equation in a rectangular box. -/
def boxSolutions (q q' h a b c d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico a b ×ˢ Finset.Ico c d).filter fun rs => q * rs.1 + h = q' * rs.2

theorem mem_boxSolutions {q q' h a b c d : ℕ} {rs : ℕ × ℕ} :
    rs ∈ boxSolutions q q' h a b c d ↔
      (a ≤ rs.1 ∧ rs.1 < b) ∧ (c ≤ rs.2 ∧ rs.2 < d) ∧
        q * rs.1 + h = q' * rs.2 := by
  simp [boxSolutions, and_assoc]

/-- Solubility forces the exact gcd obstruction, with no coprimality assumption. -/
theorem gcd_dvd_shift_of_solution {q q' h r s : ℕ}
    (heq : q * r + h = q' * s) : q'.gcd q ∣ h := by
  have hleft : q'.gcd q ∣ q * r := dvd_mul_of_dvd_left (Nat.gcd_dvd_right q' q) r
  have hright : q'.gcd q ∣ q * r + h := by
    rw [heq]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left q' q) s
  exact (Nat.dvd_add_iff_right hleft).mpr hright

/-- The second coefficient determines the second coordinate from the first. -/
theorem fst_injOn_boxSolutions {q q' h a b c d : ℕ} (hq' : 0 < q') :
    Set.InjOn Prod.fst (↑(boxSolutions q q' h a b c d) : Set (ℕ × ℕ)) := by
  intro rs hrs uv huv heq
  apply Prod.ext heq
  have hrsEq := (mem_boxSolutions.mp hrs).2.2
  have huvEq := (mem_boxSolutions.mp huv).2.2
  exact Nat.eq_of_mul_eq_mul_left hq' (by rw [← hrsEq, ← huvEq, heq])

/-- Any two first coordinates agree modulo the primitive first-coordinate step. -/
theorem first_coordinates_modEq {q q' h r s r' s' : ℕ} (hq' : 0 < q')
    (heq : q * r + h = q' * s) (heq' : q * r' + h = q' * s') :
    r ≡ r' [MOD q' / q'.gcd q] := by
  apply Nat.ModEq.cancel_left_div_gcd hq'
  apply Nat.ModEq.add_right_cancel' h
  rw [heq, heq']
  exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right q' s) |>.trans
    (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right q' s')).symm

/-- The primitive step is positive whenever the second coefficient is positive. -/
theorem primitive_step_pos {q q' : ℕ} (hq' : 0 < q') :
    0 < q' / q'.gcd q := by
  exact Nat.div_pos (Nat.gcd_le_left q hq') (Nat.gcd_pos_of_pos_left q hq')

/-- Uniform interval count in terms of the exact primitive step. -/
theorem card_boxSolutions_le_primitive_step
    (q q' h a b c d : ℕ) (hq' : 0 < q') (hab : a ≤ b) :
    ((boxSolutions q q' h a b c d).card : ℝ) ≤
      ((b : ℝ) - a) / (q' / q'.gcd q : ℕ) + 1 := by
  classical
  by_cases hempty : boxSolutions q q' h a b c d = ∅
  · rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hdiff : (0 : ℝ) ≤ b - a := sub_nonneg.mpr (by exact_mod_cast hab)
    positivity
  · obtain ⟨rs, hrs⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have himage : (boxSolutions q q' h a b c d).image Prod.fst ⊆
        (Finset.Ico a b).filter fun r => r ≡ rs.1 [MOD q' / q'.gcd q] := by
      intro r hr
      obtain ⟨uv, huv, rfl⟩ := Finset.mem_image.mp hr
      have hu := mem_boxSolutions.mp huv
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hu.1,
        first_coordinates_modEq hq' hu.2.2 (mem_boxSolutions.mp hrs).2.2⟩
    have hcard : (boxSolutions q q' h a b c d).card ≤
        ((Finset.Ico a b).filter fun r => r ≡ rs.1 [MOD q' / q'.gcd q]).card := by
      rw [← Finset.card_image_of_injOn (fst_injOn_boxSolutions hq')]
      exact Finset.card_le_card himage
    have hcount := card_nat_Ico_modEq_cast_le_div_add_one
      a b rs.1 (q' / q'.gcd q) (primitive_step_pos hq') hab
    have hcountReal :
        (((Finset.Ico a b).filter fun r => r ≡ rs.1 [MOD q' / q'.gcd q]).card : ℝ) ≤
          ((b : ℝ) - a) / (q' / q'.gcd q : ℕ) + 1 := by
      have hcast := (Rat.cast_le (K := ℝ)).mpr hcount
      push_cast at hcast
      exact hcast
    have hcardReal : ((boxSolutions q q' h a b c d).card : ℝ) ≤
        (((Finset.Ico a b).filter fun r => r ≡ rs.1 [MOD q' / q'.gcd q]).card : ℝ) := by
      exact_mod_cast hcard
    exact hcardReal.trans hcountReal

/-- Real arithmetic form of the primitive-step count. -/
theorem card_boxSolutions_le_gcd
    (q q' h a b c d : ℕ) (hq' : 0 < q') (hab : a ≤ b) :
    ((boxSolutions q q' h a b c d).card : ℝ) ≤
      1 + ((b : ℝ) - a) * (q'.gcd q : ℝ) / q' := by
  have hcount := card_boxSolutions_le_primitive_step q q' h a b c d hq' hab
  have hqReal : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
  have hgReal : (q'.gcd q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left q hq').ne'
  rw [Nat.cast_div (Nat.gcd_dvd_left q' q) hgReal] at hcount
  convert hcount using 1
  field_simp
  ring

/-- A positive shift pays for the gcd, uniformly over both kernel ranges. -/
theorem card_boxSolutions_le_shift
    (q q' h a b c d : ℕ) (hq' : 0 < q') (hh : 0 < h) (hab : a ≤ b) :
    ((boxSolutions q q' h a b c d).card : ℝ) ≤
      1 + ((b : ℝ) - a) * h / q' := by
  by_cases hempty : boxSolutions q q' h a b c d = ∅
  · rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hdiff : (0 : ℝ) ≤ b - a := sub_nonneg.mpr (by exact_mod_cast hab)
    positivity
  · obtain ⟨rs, hrs⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hg : q'.gcd q ≤ h := Nat.le_of_dvd hh
      (gcd_dvd_shift_of_solution (mem_boxSolutions.mp hrs).2.2)
    refine (card_boxSolutions_le_gcd q q' h a b c d hq' hab).trans ?_
    apply add_le_add_right
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hg)
        (sub_nonneg.mpr (by exact_mod_cast hab))) (Nat.cast_nonneg q')

/-- The dyadic-range fibre estimate used in shifted kernel energy. -/
theorem card_dyadic_boxSolutions_le
    (q q' h R S X : ℕ) (hq' : 0 < q') (hh : 0 < h) (hX : 0 < X)
    (hscale : X ≤ 2 * q' * S) :
    ((boxSolutions q q' h R (2 * R) S (2 * S)).card : ℝ) ≤
      1 + 2 * R * S * h / X := by
  have hbase := card_boxSolutions_le_shift q q' h R (2 * R) S (2 * S) hq' hh (by omega)
  have hqReal : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hXReal : (0 : ℝ) < X := by exact_mod_cast hX
  have hscaleReal : (X : ℝ) ≤ 2 * q' * S := by exact_mod_cast hscale
  refine hbase.trans ?_
  push_cast
  rw [add_le_add_iff_left, div_le_div_iff₀ hqReal hXReal]
  nlinarith [mul_le_mul_of_nonneg_left hscaleReal (by positivity : (0 : ℝ) ≤ R * h)]

end
end PaperC.V282.ShiftedKernelBoxCount
