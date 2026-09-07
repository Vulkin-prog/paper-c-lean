import PaperCV282.HardRelativeMargin

/-! # Information margins for the true relative bulk error

The event information is the only quantity multiplied into the established
bulk kernel estimate. No limiting probability or comparison is an input.
-/
namespace PaperC.V282.AffineCrossoverBudget

open Filter Topology SaddleParameters SaddleScales AggregateInformationBudget
open SaddleRateConvergence

noncomputable section

/-- The quantitative relative error after hard conditioning. -/
def relativeError (M : ℕ) (c : ℝ) : ℝ :=
  67 * (Real.exp (-(c / 2) * saddleNu 1 (Real.log M)) + (M : ℝ) ^ (-(1 / 6 : ℝ)))

theorem relativeError_nonneg (M : ℕ) (c : ℝ) : 0 ≤ relativeError M c := by
  unfold relativeError
  positivity

theorem relativeError_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun M : ℕ => relativeError M c) atTop (𝓝 0) := by
  have he := margin_exponential_nat_tendsto_zero 1 c 0 (by norm_num) (by linarith)
  have hp := polynomial_error_nat_tendsto_zero (1 / 6) (by norm_num)
  simpa only [relativeError, sub_zero, show -(1 / 3 : ℝ) + 1 / 6 = -(1 / 6 : ℝ) by ring,
    add_zero, mul_zero] using (he.add hp).const_mul 67

/-- Every positive power absorbs the information factor below the saddle. -/
theorem information_power_eventually (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ I : ℝ,
      I ≤ saddleCutoff 1 (Real.log M) → Real.exp I ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨Mzero, hzero⟩ := eventually_atTop.mp
    (exp_saddle_le_power_eventually 1 epsilon hepsilon)
  exact ⟨Mzero,fun M hM I hI => (Real.exp_le_exp.mpr hI).trans
    (by simpa only [one_mul] using hzero M hM)⟩

/-- The budget implies I≤V uniformly, before I is chosen. -/
theorem information_le_saddle_eventually {c : ℝ} (hc : 0 < c) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ I : ℝ,
      I ≤ saddleCutoff 1 (Real.log M) - c * saddleNu 1 (Real.log M) →
      I ≤ saddleCutoff 1 (Real.log M) := by
  have hnu := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨Mzero,hzero⟩ := eventually_atTop.mp (hnu.eventually (eventually_ge_atTop (0 : ℝ)))
  refine ⟨Mzero,fun M hM I hI => hI.trans ?_⟩
  exact sub_le_self _ (mul_nonneg hc.le (hzero M hM))

/-- The fixed epsilon=1/12 and eta=c/2 leave an explicit vanishing margin. -/
theorem weighted_bulk_error_eventually {c : ℝ} (hc : 0 < c) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ I : ℝ,
      I ≤ saddleCutoff 1 (Real.log M) - c * saddleNu 1 (Real.log M) →
      67 * Real.exp I *
        (Real.exp (-saddleCutoff 1 (Real.log M) + (c / 2) * saddleNu 1 (Real.log M)) +
          (M : ℝ) ^ (-(1 / 3 : ℝ) + 1 / 12)) ≤ relativeError M c := by
  obtain ⟨Np,hp⟩ := information_power_eventually (1/12) (by norm_num)
  obtain ⟨Ni,hi⟩ := information_le_saddle_eventually hc
  refine ⟨max Np (max Ni 1),?_⟩
  intro M hM I hI
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0<M by omega)
  have hexp : Real.exp I *
      Real.exp (-saddleCutoff 1 (Real.log M) + (c / 2) * saddleNu 1 (Real.log M)) ≤
      Real.exp (-(c / 2) * saddleNu 1 (Real.log M)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpoly : Real.exp I * (M : ℝ) ^ (-(1/3 : ℝ)+1/12) ≤ (M : ℝ)^(-(1/6 : ℝ)) := by
    calc
      _ ≤ (M : ℝ)^(1/12 : ℝ) * (M : ℝ)^(-(1/3 : ℝ)+1/12) :=
        mul_le_mul_of_nonneg_right (hp M (by omega) I (hi M (by omega) I hI))
          (Real.rpow_nonneg hMpos.le _)
      _ = _ := by rw [← Real.rpow_add hMpos]; congr 1; ring
  unfold relativeError
  nlinarith only [hexp,hpoly]

end
end PaperC.V282.AffineCrossoverBudget
