import PaperCPrel8.RoughKernelReciprocal
import PaperCPrel8.PivotRankinUniform

/-! # Uniform saddle estimate for rough-kernel counts

The Euler prefactor is controlled at the reference height, uniformly in the
larger population ceiling and the numerical kernel threshold. The original
PNT remainder is the only analytic input to these statements.
-/
namespace PaperC.Prel8.RoughKernelSaddle
open TerminalKernelCount V282.DefectiveRankinCount
open PaperC.V282.PrimeEulerPNT PaperC.V282.PrimeEulerRankin
open PaperC.V282.PrimeEulerFreeScales PaperC.V282.PrimeEulerFreeCutoff
open PaperC.V282.SaddleParameters PaperC.V282.SaddleBranch
open PaperC.V282.ExponentialIntegral PaperC.V282.SaddleCutoffAdmissibility
open PaperC.V282.SaddleScales
open Set Filter Topology
noncomputable section

/-- The variable-cutoff Euler prefactor, including the admissible tilt domain. -/
theorem enlarged_prefactor (hPNT : PrimeNumberTheoremRemainder)
    (c C epsilon : ℝ) (hc : 0<c) (hC : 0<C) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ X ≥ M, ∀ w : ℝ,
      c*Real.sqrt (Real.log M*Real.log (Real.log M)) ≤ w →
      w ≤ C*Real.sqrt (Real.log M*Real.log (Real.log M)) →
      0 < freeCutoffTilt (Real.log M) w ∧ freeCutoffTilt (Real.log M) w ≤ 1/2 ∧
      (X : ℝ) ^ (-freeCutoffTilt (Real.log M) w) *
        rankinEulerProduct ⌊Real.exp w⌋₊ (freeCutoffTilt (Real.log M) w) ≤
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
  refine ⟨htilt, hhalf, ?_⟩
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  rw [rankinEulerProduct_eq_exp, Real.rpow_def_of_pos hXpos, ← Real.exp_add]
  have hlogs : Real.log M ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast (show 0<M by omega)) (by exact_mod_cast hMX)
  have htiltlog := mul_le_mul_of_nonneg_left hlogs htilt.le
  have hmain : freeCutoffTilt (Real.log M) w*Real.log M =
      (Real.log M/w)*upperSaddleBranch (Real.log M/w) := by unfold freeCutoffTilt; ring
  apply Real.exp_le_exp.mpr
  unfold saddleCost
  linarith [le_abs_self (rankinLogSum ⌊Real.exp w⌋₊ (freeCutoffTilt (Real.log M) w)-
    exponentialIntegral (upperSaddleBranch (Real.log M/w)))]

/-- Uniform small-kernel count in the free cutoff band, for every threshold T. -/
theorem enlarged_count (hPNT : PrimeNumberTheoremRemainder)
    (c C epsilon : ℝ) (hc : 0<c) (hC : 0<C) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ X ≥ M, ∀ w : ℝ,
      c*Real.sqrt (Real.log M*Real.log (Real.log M)) ≤ w →
      w ≤ C*Real.sqrt (Real.log M*Real.log (Real.log M)) → ∀ T : ℕ,
      ((boundedLargeKernelValues ⌊Real.exp w⌋₊ T X).card : ℝ)/X ≤
        Real.exp (-saddleCost (Real.log M/w)+epsilon*(Real.log M/w)) *
          (1 + (T : ℝ) ^ freeCutoffTilt (Real.log M) w / freeCutoffTilt (Real.log M) w) := by
  obtain ⟨Mzero, h⟩ := enlarged_prefactor hPNT c C epsilon hc hC hepsilon
  refine ⟨max Mzero 1, ?_⟩
  intro M hM X hMX w hlo hhi T
  obtain ⟨ht, hh, hp⟩ := h M (by omega) X hMX w hlo hhi
  apply (RoughKernelRankin.normalized_count_le ⌊Real.exp w⌋₊ T X (by omega) ht hh).trans
  exact mul_le_mul_of_nonneg_right hp (by positivity)

/-- At the actual hard cutoff, the exponent is -V+epsilon*nu. -/
theorem hard_count (hPNT : PrimeNumberTheoremRemainder)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ X ≥ M, ∀ T : ℕ,
      ((boundedLargeKernelValues ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ T X).card : ℝ)/X ≤
        Real.exp (-saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) *
          (1 + (T : ℝ) ^ freeCutoffTilt (Real.log M) (saddleCutoff 1 (Real.log M)) /
            freeCutoffTilt (Real.log M) (saddleCutoff 1 (Real.log M))) := by
  obtain ⟨c,C,hc,hC,Hband,hband⟩ := saddleCutoff_sqrt_log_band_eventually (by norm_num : (0 : ℝ)<1)
  obtain ⟨Mc,hcount⟩ := enlarged_count hPNT c C epsilon hc hC hepsilon
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Mh,hh⟩ := eventually_atTop.mp
    (hl.eventually (eventually_ge_atTop (max Hband (saddleThreshold 1))))
  refine ⟨max Mc Mh, ?_⟩
  intro M hM X hMX T
  have hH := hh M (by omega)
  obtain ⟨hlo,hhi⟩ := hband (Real.log M) (by order)
  have h := hcount M (by omega) X hMX _ hlo hhi T
  have he := saddleCutoff_equation (by norm_num : (0 : ℝ) < 1)
    (by order : saddleThreshold 1 ≤ Real.log M)
  simp only [one_mul] at he
  simpa only [saddleNu, ← he] using h

end
end PaperC.Prel8.RoughKernelSaddle
