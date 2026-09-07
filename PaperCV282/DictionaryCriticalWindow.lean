import PaperCV282.DictionaryProfileNormalization
import PaperC.Probability.CriticalRunWindow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Literal critical windows for growing dictionaries

The manuscript centers B at log_2(N*m), rather than log_2 N.
The threshold below is uniform before both the word length and m.
-/

namespace PaperC.V282.DictionaryCriticalWindow

open Filter Topology CriticalRunWindow DictionaryProfileNormalization

noncomputable section

/-- The exact intensity has a logarithmic exponential representation. -/
theorem dictionary_intensity_eq_exp {N m : ℝ} (hN : 0 < N) (hm : 0 < m) (B : ℕ) :
    N * m / (2 : ℝ) ^ B = Real.exp (Real.log (N * m) - (B : ℝ) * Real.log 2) := by
  rw [Real.exp_sub,Real.exp_log (mul_pos hN hm),Real.exp_nat_mul,Real.exp_log (by norm_num)]

/-- Both fixed intensity bounds follow directly from the printed absolute-value window. -/
theorem dictionary_intensity_bounds {N m C : ℝ} {B : ℕ}
    (hN : 0 < N) (hm : 0 < m)
    (hwindow : |(B : ℝ) - Real.log (N * m) / Real.log 2| ≤ C) :
    Real.exp (-C * Real.log 2) ≤ N * m / (2 : ℝ) ^ B ∧
      N * m / (2 : ℝ) ^ B ≤ Real.exp (C * Real.log 2) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨hl,hu⟩ := abs_le.mp hwindow
  have hl' : (B : ℝ) - C ≤ Real.log (N * m) / Real.log 2 := by linarith
  have hu' : Real.log (N * m) / Real.log 2 ≤ (B : ℝ) + C := by linarith
  have hlo := (le_div_iff₀ hlog).mp hl'
  have hhi := (div_le_iff₀ hlog).mp hu'
  rw [dictionary_intensity_eq_exp hN hm]
  exact ⟨Real.exp_le_exp.mpr (by nlinarith),Real.exp_le_exp.mpr (by nlinarith)⟩

/-- The full growing-dictionary critical window lies in a single fixed logarithmic band. -/
theorem dictionary_critical_log_band_eventually (C : ℝ) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ m : ℝ, 1 ≤ m →
      m ≤ (N : ℝ) ^ (1 / (2 : ℝ)) → ∀ B : ℕ,
      |(B : ℝ) - Real.log ((N : ℝ) * m) / Real.log 2| ≤ C →
      lowerConstant * Real.log N ≤ B ∧ (B : ℝ) ≤ upperConstant * Real.log N := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nzero,hzero⟩ := eventually_atTop.1
    (hnatlog.eventually (eventually_ge_atTop (max (2 * C * Real.log 2) 1)))
  refine ⟨max Nzero 1, ?_⟩
  intro N hN m hm hmN B hwindow
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmpos : 0 < m := by linarith
  have hlogN := hzero N (by omega)
  have hmLog : 0 ≤ Real.log m := Real.log_nonneg hm
  have hmLogUpper := Real.log_le_log hmpos hmN
  rw [Real.log_rpow hn] at hmLogUpper
  have hnm : Real.log ((N : ℝ) * m) = Real.log N + Real.log m := Real.log_mul hn.ne' hmpos.ne'
  obtain ⟨hl,hu⟩ := abs_le.mp hwindow
  rw [hnm] at hl hu
  have hblo : (Real.log N + Real.log m) / Real.log 2 - C ≤ (B : ℝ) := by linarith
  have hbhi : (B : ℝ) ≤ (Real.log N + Real.log m) / Real.log 2 + C := by linarith
  have hClog : 2 * C * Real.log 2 ≤ Real.log N := (le_max_left _ _).trans hlogN
  constructor
  · unfold lowerConstant
    have hlow : Real.log N / (2 * Real.log 2) ≤
        (Real.log N + Real.log m) / Real.log 2 - C := by
      apply (le_sub_iff_add_le).mpr
      apply (le_div_iff₀ hlog).mpr
      have hc : Real.log N / (2 * Real.log 2) * Real.log 2 = Real.log N / 2 := by field_simp
      nlinarith
    calc
      _ = Real.log N / (2 * Real.log 2) := by ring
      _ ≤ _ := hlow.trans hblo
  · unfold upperConstant
    have hhigh : (Real.log N + Real.log m) / Real.log 2 + C ≤
        2 * Real.log N / Real.log 2 := by
      apply (le_sub_iff_add_le).mp
      apply (div_le_iff₀ hlog).mpr
      have hc : (2 * Real.log N / Real.log 2 - C) * Real.log 2 =
          2 * Real.log N - C * Real.log 2 := by field_simp
      nlinarith
    calc
      _ ≤ 2 * Real.log N / Real.log 2 := hbhi.trans hhigh
      _ = _ := by ring

/-- Under bounded intensity, the dictionary polynomial costs at most a constant times m^(2/3). -/
theorem dictionary_profile_le_card_power {lambda m K : ℝ}
    (hlambda : 0 ≤ lambda) (hK : lambda ≤ K) (hm : 1 ≤ m) :
    dictionaryPolynomialProfile lambda m ≤
      (K + K ^ (11 / (6 : ℝ)) + K ^ (4 / (3 : ℝ))) * m ^ (2 / (3 : ℝ)) := by
  have hKzero : 0 ≤ K := hlambda.trans hK
  have hmzero : 0 ≤ m := by linarith
  have hmone : 1 ≤ m ^ (2 / (3 : ℝ)) := Real.one_le_rpow hm (by norm_num)
  have hmexp : m ^ (1 / (6 : ℝ)) ≤ m ^ (2 / (3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  have hfirst : lambda ≤ K * m ^ (2 / (3 : ℝ)) :=
    hK.trans (le_mul_of_one_le_right hKzero hmone)
  have hsecond : lambda ^ (11 / (6 : ℝ)) * m ^ (1 / (6 : ℝ)) ≤
      K ^ (11 / (6 : ℝ)) * m ^ (2 / (3 : ℝ)) := by
    exact mul_le_mul (Real.rpow_le_rpow hlambda hK (by norm_num)) hmexp
      (Real.rpow_nonneg hmzero _) (Real.rpow_nonneg hKzero _)
  have hthird := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hlambda hK (by norm_num : (0 : ℝ) ≤ 4 / 3))
    (Real.rpow_nonneg hmzero (2 / 3))
  unfold dictionaryPolynomialProfile
  nlinarith

/-- Choosing epsilon=eta/6 gives the printed N^(-eta/2) polynomial error. -/
theorem dictionary_polynomial_error_critical {N lambda m K eta : ℝ}
    (hN : 0 < N) (hlambda : 0 ≤ lambda) (hK : lambda ≤ K) (hm : 1 ≤ m)
    (hcard : m ≤ N ^ (1 / 2 - eta)) :
    N ^ (-(1 / (3 : ℝ)) + eta / 6) * dictionaryPolynomialProfile lambda m ≤
      (K + K ^ (11 / (6 : ℝ)) + K ^ (4 / (3 : ℝ))) * N ^ (-(eta / 2)) := by
  have hcoef : 0 ≤ K + K ^ (11 / (6 : ℝ)) + K ^ (4 / (3 : ℝ)) := by
    have : 0 ≤ K := hlambda.trans hK
    positivity
  have hcardpow := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ m) hcard
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_mul hN.le] at hcardpow
  calc
    _ ≤ N ^ (-(1 / (3 : ℝ)) + eta / 6) *
        ((K + K ^ (11 / (6 : ℝ)) + K ^ (4 / (3 : ℝ))) * N ^ ((1 / 2 - eta) * (2 / 3))) := by
      exact mul_le_mul_of_nonneg_left
        ((dictionary_profile_le_card_power hlambda hK hm).trans
          (mul_le_mul_of_nonneg_left hcardpow hcoef)) (Real.rpow_nonneg hN.le _)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hN]
      congr 2
      ring

end
end PaperC.V282.DictionaryCriticalWindow
