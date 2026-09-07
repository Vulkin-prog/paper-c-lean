import PaperCV282.ProfileMonomials
import PaperCV282.LogarithmicWordPowers
import PaperC.Probability.CriticalRunWindow

/-!
# Normalizing the genuine relation profile at critical run lengths

The word space has size twice the reciprocal start probability. Keeping
that factor two gives an exact identity for the normalized coarse profile.
Only an upper bound on the actual intensity is needed in the inequality.
-/

namespace PaperC.V282.CriticalProfileNormalization

open ProfileMonomials LogarithmicWordPowers

noncomputable section

/-- Exact critical normalization with the full word size equal to twice the run size. -/
theorem coarseProfile_div_square_eq {N p : ℝ} (hN : 0 < N) (hp : 0 < p) :
    coarseProfile N (2 * p) / p ^ 2 =
      N ^ (-(1 / (3 : ℝ))) * ((N / p) ^ 2 + 2 * (N / p)) := by
  have hfirst : N ^ (5 / (3 : ℝ)) = N ^ (-(1 / (3 : ℝ))) * N ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN]
    congr 1
    norm_num
  have hsecond : N ^ (2 / (3 : ℝ)) = N ^ (-(1 / (3 : ℝ))) * N := by
    calc
      _ = N ^ (-(1 / (3 : ℝ)) + 1) := by congr 1; norm_num
      _ = N ^ (-(1 / (3 : ℝ))) * N ^ (1 : ℝ) := Real.rpow_add hN _ _
      _ = _ := by rw [Real.rpow_one]
  unfold coarseProfile
  rw [hfirst, hsecond]
  field_simp

/-- Bounded intensity gives the explicit one-third saving in the two-window profile. -/
theorem coarseProfile_div_square_le {N p K : ℝ}
    (hN : 0 < N) (hp : 0 < p) (hbalance : N / p ≤ K) :
    coarseProfile N (2 * p) / p ^ 2 ≤
      (K ^ 2 + 2 * K) * N ^ (-(1 / (3 : ℝ))) := by
  rw [coarseProfile_div_square_eq hN hp]
  have hmean : 0 ≤ N / p := by positivity
  have hsq := pow_le_pow_left₀ hmean hbalance 2
  calc
    _ ≤ N ^ (-(1 / (3 : ℝ))) * (K ^ 2 + 2 * K) := by gcongr
    _ = _ := by ring

/-- The exact word-size specialization, including the last factor of two. -/
theorem coarseProfile_div_runSquare_le {N L : ℕ} {K : ℝ}
    (hN : 0 < N) (hbalance : (N : ℝ) / (2 : ℝ) ^ L ≤ K) :
    coarseProfile N ((2 : ℝ) ^ (L + 1)) / (2 : ℝ) ^ (2 * L) ≤
      (K ^ 2 + 2 * K) * (N : ℝ) ^ (-(1 / (3 : ℝ))) := by
  have hh := coarseProfile_div_square_le (by exact_mod_cast hN : (0 : ℝ) < N)
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ L) hbalance
  simpa only [pow_succ, show 2 * L = L * 2 by omega, pow_mul, mul_comm] using hh

/-- Any fixed coefficient is absorbed uniformly before the critical length is chosen. -/
theorem constant_le_rpow_in_criticalWindow_eventually
    (C a epsilon : ℝ) (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      CriticalRunWindow.InRunLengthWindow C N L → a ≤ (N : ℝ) ^ epsilon := by
  obtain ⟨Nwindow, hwindow⟩ := CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    CriticalRunWindow.upperConstant
    (CriticalRunWindow.lowerConstant_pos.trans CriticalRunWindow.lowerConstant_lt_upperConstant).le
    a 0 epsilon hepsilon
  refine ⟨max Nwindow Nconstant, ?_⟩
  intro N hN L hL
  have hw := hwindow N (by omega) L hL
  exact (le_abs_self a).trans (by
    simpa using hconstant N (by omega) L hw.1.2.2.2)

end
end PaperC.V282.CriticalProfileNormalization
