import PaperCV282.ProfileMonomials
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact normalization of the capped dictionary profile

The dictionary probability at one site is a, its cardinality is m and
its total intensity is N*a. The normalization retains m explicitly;
no bounded-cardinality or bounded-intensity assumption is used here.
-/

namespace PaperC.V282.DictionaryProfileNormalization

open ProfileMonomials

noncomputable section

/-- The three contributions printed in the dictionary bound (5.2). -/
def dictionaryPolynomialProfile (lambda m : ℝ) : ℝ :=
  lambda + lambda ^ (11 / (6 : ℝ)) * m ^ (1 / (6 : ℝ)) +
    lambda ^ (4 / (3 : ℝ)) * m ^ (2 / (3 : ℝ))

theorem dictionaryPolynomialProfile_nonneg {lambda m : ℝ}
    (hlambda : 0 ≤ lambda) (hm : 0 ≤ m) :
    0 ≤ dictionaryPolynomialProfile lambda m := by
  unfold dictionaryPolynomialProfile
  positivity

/-- General exponent identity behind both uncapped monomials. -/
theorem dictionary_monomial_identity {N a m : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hm : 0 ≤ m) (u v : ℝ) :
    a ^ 2 * (N ^ u * (m / a) ^ v) =
      N ^ (u - 2 + v) * (N * a) ^ (2 - v) * m ^ v := by
  rw [Real.div_rpow hm ha.le, Real.mul_rpow hN.le ha.le]
  have hNprod : N ^ (u - 2 + v) * N ^ (2 - v) = N ^ u := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have haquot : a ^ (2 - v) = a ^ 2 / a ^ v := by
    rw [Real.rpow_sub ha]
    norm_num
  rw [haquot]
  calc
    _ = (N ^ u * (a ^ 2 / a ^ v)) * m ^ v := by ring
    _ = _ := by rw [← hNprod]; ring

/-- Capping by the marginal leaves a single power of the total intensity. -/
theorem dictionary_terminal_identity {N a : ℝ} (hN : 0 < N) (ha : 0 < a) :
    a ^ 2 * (N ^ (2 / (3 : ℝ)) * (1 / a)) = N ^ (-(1 / (3 : ℝ))) * (N * a) := by
  have hpow : N ^ (-(1 / (3 : ℝ))) * N = N ^ (2 / (3 : ℝ)) := by
    conv_lhs => rhs; rw [← Real.rpow_one N]
    rw [← Real.rpow_add hN]
    norm_num
  calc
    _ = N ^ (2 / (3 : ℝ)) * a := by field_simp
    _ = (N ^ (-(1 / (3 : ℝ))) * N) * a := by rw [hpow]
    _ = _ := by ring

/-- The actual marginal cap gives exactly the printed scale and cardinality exponents. -/
theorem normalized_cappedProfile_le {N a m Q : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hm : 0 ≤ m) (hQ : Q = m / a) :
    a ^ 2 * cappedProfile N Q (1 / a) ≤
      N ^ (-(1 / (3 : ℝ))) * dictionaryPolynomialProfile (N * a) m := by
  have hone := dictionary_monomial_identity hN ha hm (3 / 2) (1 / 6)
  have htwo := dictionary_monomial_identity hN ha hm 1 (2 / 3)
  norm_num at hone htwo
  have hterm := mul_le_mul_of_nonneg_left (min_le_left (1 / a) Q)
    (show 0 ≤ a ^ 2 * N ^ (2 / (3 : ℝ)) by positivity)
  have htermId := dictionary_terminal_identity hN ha
  unfold cappedProfile dictionaryPolynomialProfile
  rw [hQ] at *
  nlinarith

/-- A diagonal error is already below the second dictionary profile monomial. -/
theorem dictionary_diagonal_le {N a m : ℝ}
    (hN : 0 < N) (ha : 0 < a) (ham : a ≤ m) :
    a ^ 2 * N ≤ N ^ (-(1 / (3 : ℝ))) *
      ((N * a) ^ (4 / (3 : ℝ)) * m ^ (2 / (3 : ℝ))) := by
  have hm : 0 < m := ha.trans_le ham
  have hpow : 1 ≤ (m / a) ^ (2 / (3 : ℝ)) :=
    Real.one_le_rpow (by exact (one_le_div ha).mpr ham) (by norm_num)
  have hh := dictionary_monomial_identity hN ha hm.le 1 (2 / 3)
  norm_num at hh
  calc
    _ ≤ a ^ 2 * (N * (m / a) ^ (2 / (3 : ℝ))) := by
      simpa only [mul_one, mul_assoc] using
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (sq_nonneg a) hN.le)
    _ = _ := by rw [hh]; ring

end
end PaperC.V282.DictionaryProfileNormalization
