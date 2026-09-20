import PaperCPrel8.MicroscopicRetainedTheorem
import PaperCPrel8.MicroscopicBadPivotCount
import PaperCV282.MacroTransportInformation

/-! # Uniform rates for the true microscopic discarded events -/
namespace PaperC.Prel8.MicroscopicDiscardRates
open PaperC.Prel8.MicroscopicActualGeometry PaperC.Prel8.MicroscopicPaperBudget
open PaperC.Prel8.MicroscopicProfileBudget PaperC.Prel8.MicroscopicInformationCutoff
open PaperC.Prel8.MicroscopicBadPivotCount
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.SaddlePoissonScales
open PaperC.V282.AggregateCutoffRemainder PaperC.V282.MacroTransportInformation
open Filter Topology
noncomputable section

/-- The second scale is positive and eventually smaller than the hard saddle. -/
theorem nu_le_saddle_eventually :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, 0 ≤ saddleNu 1 (Real.log M) ∧
      saddleNu 1 (Real.log M) ≤ saddleCutoff 1 (Real.log M) := by
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hn := (tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).comp hlog
  have hr := (tendsto_saddleCutoff_div_nu (by norm_num : (0:ℝ)<1)).comp hlog
  obtain ⟨Mn,hnu⟩ := eventually_atTop.mp (hn.eventually (eventually_gt_atTop (0:ℝ)))
  obtain ⟨Mr,hquot⟩ := eventually_atTop.mp (hr.eventually (eventually_ge_atTop (1:ℝ)))
  refine ⟨max Mn Mr, ?_⟩
  intro M hM
  have hp : 0 < saddleNu 1 (Real.log M) := hnu M (by omega)
  exact ⟨hp.le, by simpa only [one_mul] using (le_div_iff₀ hp).mp (hquot M (by omega))⟩

/-- Information-weighted microscopic remainders are smaller than every fixed second-scale exponential. -/
theorem deep_budget_rate (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ I : ℝ, I ≤ saddleCutoff 1 (Real.log M) →
      Real.exp I*Real.exp (-d*(Real.log M/Real.log (Real.log M))) ≤
        Real.exp (-c*saddleNu 1 (Real.log M)) := by
  obtain ⟨Md,hdp⟩ := saddle_le_deep_scale_eventually 1 (1+c) d (by norm_num) hd
  obtain ⟨Mn,hn⟩ := nu_le_saddle_eventually
  refine ⟨max Md Mn, ?_⟩
  intro M hM I hI
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := hdp M (by omega)
  have hv := (hn M (by omega)).2
  nlinarith

/-- Rounding the square-root cutoff preserves the expected factor two. -/
theorem rounded_sqrt_ratio (M : ℕ) (hM : 1 ≤ M) :
    (⌈Real.sqrt M⌉₊:ℝ)/(M:ℝ) ≤ 2*(M:ℝ)^(-(1/(2:ℝ))) := by
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0<M by omega)
  have hs : 1 ≤ Real.sqrt (M:ℝ) := by
    exact Real.le_sqrt_of_sq_le (by exact_mod_cast hM)
  have hc := (Nat.ceil_lt_add_one (Real.sqrt_nonneg (M:ℝ))).le
  have he : Real.sqrt (M:ℝ)/(M:ℝ)=(M:ℝ)^(-(1/(2:ℝ))) := by
    rw [Real.sqrt_eq_rpow]
    have h := Real.rpow_sub hm (1/2) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  calc
    _ ≤ (2*Real.sqrt (M:ℝ))/(M:ℝ) := div_le_div_of_nonneg_right (by linarith) hm.le
    _ = _ := by rw [mul_div_assoc,he]

/-- The true shallow-prefix deletion has a uniform power saving after conditioning. -/
theorem shallow_budget_rate (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ I lambda : ℝ, 0 < lambda →
      I+Real.log lambda ≤ saddleCutoff 1 (Real.log M) →
      Real.exp I*lambda*((⌈Real.sqrt M⌉₊:ℝ)/(M:ℝ)) ≤ (M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  obtain ⟨Mp,hp⟩ := eventually_atTop.mp
    (constant_exp_saddle_le_power_eventually 2 1 (1/6+epsilon) (by norm_num) (by linarith))
  refine ⟨max Mp 1, ?_⟩
  intro M hM I lambda hl hb
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0<M by omega)
  have he : Real.exp I*lambda ≤ Real.exp (saddleCutoff 1 (Real.log M)) := by
    simpa only [Real.exp_add,Real.exp_log hl] using Real.exp_le_exp.mpr hb
  have hs := rounded_sqrt_ratio M (by omega)
  have hp' := hp M (by omega)
  simp only [one_mul] at hp'
  calc
    _ ≤ Real.exp (saddleCutoff 1 (Real.log M))*(2*(M:ℝ)^(-(1/(2:ℝ)))) := by gcongr
    _ = (2*Real.exp (saddleCutoff 1 (Real.log M)))*(M:ℝ)^(-(1/(2:ℝ))) := by ring
    _ ≤ (M:ℝ)^(1/6+epsilon)*(M:ℝ)^(-(1/(2:ℝ))) := by gcongr
    _ = _ := by rw [← Real.rpow_add hm]; congr 1; ring

end
end PaperC.Prel8.MicroscopicDiscardRates
