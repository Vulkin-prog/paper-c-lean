import PaperCPrel8.OddPrimePivot
import PaperCV282.SaddleCutoffAdmissibility

/-! # Uniform Rankin counting with a free population ceiling

For a reference height log M, the positive Rankin tilt only improves when
counting up to X ≥ M. This covers the actual enlarged marked support without
replacing log X by log M inside an unspecified asymptotic remainder.
-/
namespace PaperC.Prel8.PivotRankinUniform
open PaperC.Prel8.OddPrimePivot
open PaperC.V282.PrimeEulerPNT PaperC.V282.PrimeEulerRankin
open PaperC.V282.PrimeEulerFreeScales PaperC.V282.PrimeEulerFreeCutoff
open PaperC.V282.SaddleParameters PaperC.V282.SaddleBranch
open PaperC.V282.ExponentialIntegral PaperC.V282.SaddleCutoffAdmissibility
open PaperC.V282.SaddleScales
open Set Filter Topology
noncomputable section

/-- Actual pivot count in a uniform free band, valid for every enlarged population. -/
theorem enlarged_population_rankin (hPNT : PrimeNumberTheoremRemainder)
    (c C epsilon : ℝ) (hc : 0<c) (hC : 0<C) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ X ≥ M, ∀ w : ℝ,
      c*Real.sqrt (Real.log M*Real.log (Real.log M)) ≤ w →
      w ≤ C*Real.sqrt (Real.log M*Real.log (Real.log M)) →
      ((pivotValues X ⌊Real.exp w⌋₊).card : ℝ)/X ≤
        Real.exp (-saddleCost (Real.log M/w)+epsilon*(Real.log M/w)) := by
  obtain ⟨Hband,hband⟩ := sqrt_log_band_eventually_in_power_band c C hc hC
  obtain ⟨Hdomain,hdomain⟩ := power_band_eventually_rankin_domain
  obtain ⟨Heuler,heuler⟩ := euler_errors_power_band_of_pnt hPNT epsilon hepsilon
  have hnatlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Mzero,hzero⟩ := eventually_atTop.mp
    (hnatlog.eventually (eventually_ge_atTop (max Hband (max Hdomain Heuler))))
  refine ⟨max Mzero 1, ?_⟩
  intro M hM X hMX w hlo hhi
  have hH := hzero M (by omega)
  obtain ⟨hpLo,hpHi⟩ := hband (Real.log M) (by order) w hlo hhi
  obtain ⟨_,hw,_,_,htilt,hhalf⟩ := hdomain (Real.log M) (by order) w hpLo hpHi
  have he := (heuler (Real.log M) (by order) w hpLo hpHi).2
  have hcut : 1 ≤ ⌊Real.exp w⌋₊ := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp hw.le)
  rw [pivotValues_eq_defectiveValues hcut]
  have hfinite := normalized_defectiveValues_le_exp_logSum (by omega : 0<X) ⌊Real.exp w⌋₊ hhalf
  have hlogs : Real.log M ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast (show 0<M by omega)) (by exact_mod_cast hMX)
  have htiltlog := mul_le_mul_of_nonneg_left hlogs htilt.le
  have hmain : freeCutoffTilt (Real.log M) w*Real.log M =
      (Real.log M/w)*upperSaddleBranch (Real.log M/w) := by unfold freeCutoffTilt; ring
  apply hfinite.trans
  apply Real.exp_le_exp.mpr
  unfold saddleCost
  linarith [le_abs_self (rankinLogSum ⌊Real.exp w⌋₊ (freeCutoffTilt (Real.log M) w)-
    exponentialIntegral (upperSaddleBranch (Real.log M/w)))]

/-- Uniform counting on the full shell band around the actual hard cutoff. -/
theorem hard_band_count (hPNT : PrimeNumberTheoremRemainder) (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ X ≥ M, ∀ w : ℝ,
      saddleCutoff 1 (Real.log M) ≤ w → w ≤ 4*saddleCutoff 1 (Real.log M) →
      ((pivotValues X ⌊Real.exp w⌋₊).card : ℝ) ≤
        X*Real.exp (-saddleCost (Real.log M/w)+epsilon*saddleNu 1 (Real.log M)) := by
  obtain ⟨c,C,hc,hC,Hband,hband⟩ := saddleCutoff_sqrt_log_band_eventually (by norm_num : (0 : ℝ)<1)
  obtain ⟨Mcount,hcount⟩ := enlarged_population_rankin hPNT c (4*C) epsilon hc (by positivity) hepsilon
  have hnatlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ M : ℕ in atTop, ∀ X ≥ M, ∀ w : ℝ,
      saddleCutoff 1 (Real.log M) ≤ w → w ≤ 4*saddleCutoff 1 (Real.log M) →
      ((pivotValues X ⌊Real.exp w⌋₊).card : ℝ) ≤
        X*Real.exp (-saddleCost (Real.log M/w)+epsilon*saddleNu 1 (Real.log M)) := by
    filter_upwards [eventually_ge_atTop (max Mcount 2),
      hnatlog.eventually (eventually_ge_atTop (max Hband (saddleThreshold 1)))] with M hM hH
    intro X hMX w hwlo hwhi
    obtain ⟨hVlo,hVhi⟩ := hband (Real.log M) (by order)
    have h := hcount M (by omega) X hMX w (hVlo.trans hwlo) (by nlinarith)
    have hX : (0 : ℝ)<X := by exact_mod_cast (show 0<X by omega)
    have hV := saddleCutoff_pos (by norm_num : (0 : ℝ)<1) (by order : saddleThreshold 1 ≤ Real.log M)
    have hlog : 0≤Real.log M := Real.log_nonneg (by exact_mod_cast (show 1≤M by omega))
    have hnu : Real.log M/w ≤ saddleNu 1 (Real.log M) :=
      div_le_div_of_nonneg_left hlog hV hwlo
    have hexp : Real.exp (-saddleCost (Real.log M/w)+epsilon*(Real.log M/w)) ≤
        Real.exp (-saddleCost (Real.log M/w)+epsilon*saddleNu 1 (Real.log M)) :=
      Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_left hnu hepsilon.le))
    have hcard := (div_le_iff₀ hX).mp h
    calc
      _ ≤ Real.exp (-saddleCost (Real.log M/w)+epsilon*(Real.log M/w))*X := hcard
      _ ≤ Real.exp (-saddleCost (Real.log M/w)+epsilon*saddleNu 1 (Real.log M))*X :=
        mul_le_mul_of_nonneg_right hexp hX.le
      _ = _ := mul_comm _ _
  exact eventually_atTop.mp hevent

end
end PaperC.Prel8.PivotRankinUniform
