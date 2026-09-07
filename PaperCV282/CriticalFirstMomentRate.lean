import PaperCV282.CriticalProfileNormalization

/-!
# Real-exponent form of the critical first-moment error

The retained reciprocal-power result is converted to the explicit
inequality required by the quantitative second-moment calculation.
The loss is arbitrary and the threshold precedes the run length.
-/

namespace PaperC.V282.CriticalFirstMomentRate

noncomputable section

/-- Converting a uniform negative half-power estimate to any positive real exponent loss. -/
theorem negativeHalfPower_le_rpow_eventually
    {admissible : ℕ → ℕ → Prop} {f : ℕ → ℕ → ℝ}
    (hf : UniformNegativeHalfPowerSubpolynomialOn admissible f)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, admissible N L →
      |f N L| ≤ (N : ℝ) ^ (-(1 / (2 : ℝ)) + epsilon) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / epsilon)
  have hkpos : 0 < k := by
    have hh : (0 : ℝ) < k := (one_div_pos.mpr hepsilon).trans hk
    exact_mod_cast hh
  have hkE : 1 < (k : ℝ) * epsilon := by
    have hh := (div_lt_iff₀ hepsilon).mp hk
    nlinarith
  obtain ⟨Nbase, hbase⟩ := hf k hkpos
  refine ⟨max Nbase 1, ?_⟩
  intro N hN L hL
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpower := hbase N (by omega) L hL
  have hnormalized : (N : ℝ) * |f N L| ≤ (N : ℝ) ^ (1 / (2 : ℝ) + epsilon) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega : 2 * k ≠ 0)).mp
    calc
      _ = |(N : ℝ) * f N L| ^ (2 * k) := by rw [abs_mul, abs_of_pos hNpos]
      _ ≤ (N : ℝ) ^ (k + 1) := hpower
      _ = (N : ℝ) ^ ((k : ℝ) + 1) := by norm_cast
      _ ≤ (N : ℝ) ^ ((1 / (2 : ℝ) + epsilon) * (2 * k : ℕ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hNone
        push_cast
        nlinarith
      _ = _ := Real.rpow_mul_natCast hNpos.le _ _
  have hidentity : (N : ℝ) * (N : ℝ) ^ (-(1 / (2 : ℝ)) + epsilon) =
      (N : ℝ) ^ (1 / (2 : ℝ) + epsilon) := by
    calc
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 / (2 : ℝ)) + epsilon) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ (1 + (-(1 / (2 : ℝ)) + epsilon)) := (Real.rpow_add hNpos _ _).symm
      _ = _ := by congr 1; ring
  nlinarith [hnormalized.trans_eq hidentity.symm]

/-- The first line of Corollary 4.4 for the exact finite-cylinder expectation. -/
theorem critical_first_moment_le_eventually (C epsilon : ℝ)
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      CriticalRunWindow.InRunLengthWindow C N L →
      |(dyadicExpectation N L : ℝ) - (N : ℝ) / (2 : ℝ) ^ L| ≤
        (N : ℝ) ^ (-(1 / (2 : ℝ)) + epsilon) :=
  negativeHalfPower_le_rpow_eventually
    (CriticalRunWindow.firstMoment_error_uniformNegativeHalfPower hC) epsilon hepsilon

end
end PaperC.V282.CriticalFirstMomentRate
