import PaperCPrel8.DyadicRestriction

/-! # One-factor dyadic information budget at the larger prefix

The bounded change of intensity and monotonicity of the saddle suffice. No
implicit derivative or assumption about the final process comparison is used.
-/
namespace PaperC.Prel8.DyadicBudget
open Filter Topology
open PaperC.Prel8.SaddleScaleMonotonicity PaperC.Prel8.MicroscopicPaperBudget
open PaperC.Prel8.MicroscopicActualGeometry
open PaperC.V282.AllStartSoftPoisson PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
noncomputable section

/-- The dyadic and larger-prefix rates differ by a bounded factor, with exact natural subtraction. -/
theorem enlarged_intensity {N L : ℕ} (hL : L ≤ N) :
    (fullRate N L:ℝ) ≤ siteRate (4*N) L ∧ siteRate (4*N) L ≤ 4*(fullRate N L:ℝ) := by
  rw [fullRate_coe]
  unfold siteRate
  constructor
  · exact div_le_div_of_nonneg_right (by exact_mod_cast (show N ≤ 4*N-L by omega)) (by positivity)
  · have hc : ((4*N-L:ℕ):ℝ) ≤ 4*(N:ℝ) := by exact_mod_cast Nat.sub_le (4*N) L
    calc
      _ ≤ (4*(N:ℝ))/(2:ℝ)^L := div_le_div_of_nonneg_right hc (by positivity)
      _ = _ := by ring

/-- All hard scale comparisons needed for the dyadic transfer hold together. -/
theorem hard_dilation_eventually :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero,
      primeCutoff N ≤ primeCutoff (4*N) ∧
      saddleNu 1 (Real.log N) ≤ saddleNu 1 (Real.log (4*N:ℕ)) := by
  have hl : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nzero,h⟩ := eventually_atTop.mp (hl.eventually (eventually_ge_atTop (saddleThreshold 1)))
  refine ⟨max 1 Nzero, ?_⟩
  intro N hN
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hlog : Real.log N ≤ Real.log (4*N:ℕ) := Real.log_le_log hn (by push_cast; linarith)
  have hc := cutoff_mono (by norm_num : (0:ℝ)<1) (h N (by omega)) hlog
  exact ⟨Nat.floor_le_floor (Real.exp_le_exp.mpr hc),nu_mono (by norm_num) (h N (by omega)) hlog⟩

/-- The literal one-factor dyadic budget transfers with any strict loss of margin. -/
theorem dyadic_budget_eventually (c a : ℝ) (ha : 0 < a) (hac : a < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, L ≤ N → ∀ I : ℝ,
      1 ≤ (fullRate N L:ℝ) →
      I+Real.log (fullRate N L:ℝ) ≤ saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      1 ≤ siteRate (4*N) L ∧
      I+Real.log (siteRate (4*N) L) ≤
        saddleCutoff 1 (Real.log (4*N:ℕ))-a*saddleNu 1 (Real.log (4*N:ℕ)) := by
  have hl : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hd := shifted_information_margin (Real.log 4) (Real.log 4) c a
    (Real.log_nonneg (by norm_num)) ha hac
  obtain ⟨Nzero,h⟩ := eventually_atTop.mp (hl.eventually hd)
  refine ⟨max 1 Nzero, ?_⟩
  intro N hN L hL I hr hb
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hs := enlarged_intensity hL
  have hp : 0 < (fullRate N L:ℝ) := by linarith
  have hlog := Real.log_le_log (hp.trans_le hs.1) hs.2
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hp.ne'] at hlog
  have hh := h N (by omega)
  have he : Real.log (4*N:ℕ)=Real.log N+Real.log 4 := by
    rw [Nat.cast_mul,Real.log_mul (by norm_num) hn.ne']
    norm_num
    ring
  rw [he]
  exact ⟨hr.trans hs.1,by linarith⟩

/-- A logarithmic band at N remains a fixed band at 4N, and all dyadic starts fit. -/
theorem enlarged_band_eventually (betaMin betaMax : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin*Real.log N ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log N →
      L ≤ N ∧ (betaMin/2)*Real.log (4*N:ℕ) ≤ (L+1:ℝ) ∧
      (L+1:ℝ) ≤ betaMax*Real.log (4*N:ℕ) := by
  obtain ⟨Nl,hl⟩ := logarithmic_length_quarter betaMax (hmin.trans hband)
  have hh : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nh,hlog⟩ := eventually_atTop.mp (hh.eventually (eventually_ge_atTop (Real.log 4)))
  refine ⟨max 1 (max Nl Nh), ?_⟩
  intro N hN L hlo hhi
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have he : Real.log (4*N:ℕ)=Real.log N+Real.log 4 := by
    rw [Nat.cast_mul,Real.log_mul (by norm_num) hn.ne']
    norm_num
    ring
  have hL := hl N (by omega) L hhi
  have hlogN := hlog N (by omega)
  rw [he]
  have hfour : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  exact ⟨by omega,by nlinarith,by nlinarith⟩

end
end PaperC.Prel8.DyadicBudget
