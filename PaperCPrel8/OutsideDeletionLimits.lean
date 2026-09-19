import PaperCPrel8.OutsideDeletion
import PaperCV282.SaddleRateConvergence

/-! # Both named ordinary deletion costs vanish under the original paper budget -/
namespace PaperC.Prel8.OutsideDeletionLimits
open Filter Topology OutsideDeletion StrongerDeletionTheorem
open MicroscopicActualGeometry MicroscopicProfileBudget MicroscopicPaperBudget MicroscopicConditionalSpatial
open MicroscopicDeletedTarget MicroscopicDiscardTheorem ConditionalStartProbability
open InfiniteRademacher MeasureTheory V282.AllStartSoftPoisson
open V282.SaddleParameters V282.SaddleScales V282.SaddleRateConvergence V282.PrimeEulerPNT
open V282.RareConditioningRates
open V282.LaishramUniformInput V282.PostQuadraticLiterature
noncomputable section
local instance : MeasurableSpace F₂ := ⊤

/-- The actual target intensity delta_G, including original and additional deletion. -/
theorem target_tendsto (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax theta c : ℝ) (hmin : 0<betaMin) (hband : betaMin<betaMax)
    (htheta : 0≤theta) (htc : theta<c) (L : ℕ → ℕ) (I : ℕ → ℝ)
    (hregime : ∀ᶠ M : ℕ in atTop, betaMin*Real.log M≤(L M+1:ℝ) ∧
      (L M+1:ℝ)≤betaMax*Real.log M ∧ 0≤I M ∧ 1≤siteRate M (L M) ∧
      I M+Real.log (siteRate M (L M))≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) :
    Tendsto (fun M ↦ targetCost M (L M) (I M) theta) atTop (𝓝 0) := by
  obtain ⟨M0,hmain⟩ := deleted_target_rate_eventually hPNT betaMin betaMax c (c/2) (1/6)
    hmin hband (by linarith) (by linarith) (by norm_num)
  have he := margin_exponential_nat_tendsto_zero 1 c 0 (by norm_num) (by linarith)
  have hp := polynomial_error_nat_tendsto_zero (1/6) (by norm_num)
  have ha := paper_added_mass_tendsto hPNT betaMin betaMax theta c hmin hband htheta htc L I hregime
  have hh : Tendsto (fun M : ℕ ↦ Real.exp (-(c/2)*saddleNu 1 (Real.log M))+
      (M:ℝ)^(-(1/(3:ℝ))+1/6)+(1/(2:ℝ)^(L M))*((added M (L M) (I M) theta).card:ℝ)) atTop (𝓝 0) := by
    simpa only [sub_zero,add_zero] using (he.add hp).add ha
  apply squeeze_zero' (Eventually.of_forall (fun M ↦ by unfold targetCost; positivity)) _ hh
  filter_upwards [hregime,eventually_ge_atTop M0] with M h hm
  exact (targetCost_le M (L M) (I M) theta).trans
    (add_le_add_left (hmain M hm (L M) (I M) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) _)

/-- The actual conditional source probability d_A, with the original small-prime event. -/
theorem source_tendsto
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax theta c : ℝ) (hmin : 0<betaMin) (hband : betaMin<betaMax)
    (htheta : 0≤theta) (htc : theta<c) (L : ℕ → ℕ) (I : ℕ → ℝ)
    (A : ∀ M, SmallSample (sourceCylinder M (L M) (I M)) (primeCutoff M) → Prop)
    (hA : ∀ M, 0 < infiniteRademacherMeasure.real
      (traceEvent (sourceCylinder M (L M) (I M)) (primeCutoff M) (A M)))
    (hinfo : ∀ M, I M=eventInformation
      (traceEvent (sourceCylinder M (L M) (I M)) (primeCutoff M) (A M)))
    (hregime : ∀ᶠ M : ℕ in atTop, betaMin*Real.log M≤(L M+1:ℝ) ∧
      (L M+1:ℝ)≤betaMax*Real.log M ∧ 0≤I M ∧ 1≤siteRate M (L M) ∧
      I M+Real.log (siteRate M (L M))≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) :
    Tendsto (fun M ↦ sourceCost M (L M) (I M) theta (A M)) atTop (𝓝 0) := by
  obtain ⟨M0,hmain⟩ := deleted_probability_eventually hLS hShorey hPNT hNR
    betaMin betaMax c (c/2) (1/6) hmin hband (by linarith) (by linarith) (by norm_num)
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hmin hband (by linarith)
  have he := (margin_exponential_nat_tendsto_zero 1 c 0 (by norm_num) (by linarith)).const_mul 3
  have hp := polynomial_error_nat_tendsto_zero (1/6) (by norm_num)
  have ha := (paper_added_mass_tendsto hPNT betaMin betaMax theta c hmin hband htheta htc L I hregime).const_mul 2
  have hh : Tendsto (fun M : ℕ ↦ 3*Real.exp (-(c/2)*saddleNu 1 (Real.log M))+
      (M:ℝ)^(-(1/(3:ℝ))+1/6)+2*((1/(2:ℝ)^(L M))*((added M (L M) (I M) theta).card:ℝ))) atTop (𝓝 0) := by
    simpa only [sub_zero,add_zero,mul_zero] using (he.add hp).add ha
  apply squeeze_zero' (Eventually.of_forall (fun M ↦ ENNReal.toReal_nonneg)) _ hh
  filter_upwards [hregime,eventually_ge_atTop M0,eventually_ge_atTop Mg] with M h hm hmg
  have hc := hmain M hm (L M) h.1 h.2.1 _ (hA M) h.2.2.2.1 (by rw [← hinfo]; exact h.2.2.2.2)
  rw [← hinfo] at hc
  exact (sourceCost_le M (L M) (I M) theta
    (hg M hmg (L M) (I M) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) (A M) (hA M)).trans
      (add_le_add_left hc _)
end
end PaperC.Prel8.OutsideDeletionLimits
