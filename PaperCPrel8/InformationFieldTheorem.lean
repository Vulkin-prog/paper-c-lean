import PaperCPrel8.InformationFieldBudget

/-! # The full signed field at the actual information-adapted cutoff -/
namespace PaperC.Prel8.InformationFieldTheorem
open Filter Topology MeasureTheory
open PaperC.InfiniteRademacher PaperC.InfiniteCylinderTransfer
open PaperC.V282.SpatialMarkedEventComparison PaperC.V282.SpatialMarkedMovableBudget
open PaperC.V282.ExactMarkedMovableRates PaperC.V282.MovableMarkedBudget
open PaperC.V282.RareConditioningRates PaperC.V282.AllStartSoftPoisson
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.SaddleCutoffAdmissibility
open PaperC.V282.PrimeEulerPNT PaperC.V282.ProcessAGGInput
open PaperC.Prel8.InformationSaddleBudget PaperC.Prel8.InformationFieldBudget
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤

/-- Uniform comparison with all sites, signs and unbounded excesses retained.
The auxiliary truncation is the already certified larger deterministic one;
it is removed from both laws before this conclusion. -/
theorem information_field_in_band (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c c' epsilon : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon) (heps : epsilon < 1/3) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin*Real.log N ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log N →
      1 ≤ (fullRate N L:ℝ) → ∀ A : Set InfiniteSample,
      0 < infiniteRademacherMeasure.real A →
      eventInformation A ≤ saddleCutoff 1 (Real.log N) →
      MeasurableSet[MeasurableSpace.comap
        (restrictToFinite ⌊Real.exp (informationCutoff (Real.log N) (eventInformation A))⌋₊) inferInstance] A →
      Real.log (fullRate N L:ℝ) ≤ informationBudget (Real.log N) (eventInformation A)-
        c*(Real.log N/informationCutoff (Real.log N) (eventInformation A)) →
      spatialEventDistance N L A ≤
        67*Real.exp (-c'*(Real.log N/informationCutoff (Real.log N) (eventInformation A)))+
        64*(N:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  obtain ⟨lo,hi1,hlo,hhi1,H1,h1⟩ := saddleCutoff_sqrt_log_band_eventually (by norm_num : (0:ℝ)<1)
  obtain ⟨lo2,hi,hlo2,hhi,H2,h2⟩ := saddleCutoff_sqrt_log_band_eventually (by norm_num : (0:ℝ)<2)
  obtain ⟨Nf,hf⟩ := spatial_event_free_band hAGG hPNT lo hi betaMin (2*betaMax) (epsilon/2) (c-c')
    hlo hhi hbetaMin (by linarith) (by positivity) (by linarith)
  obtain ⟨Ne,he⟩ := movable_mark_band_eventually betaMax (hbetaMin.trans hbeta)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nz,hz⟩ := eventually_atTop.1
    ((hlog.eventually (eventually_ge_atTop (max H1 (max H2 (max (saddleThreshold 1) (saddleThreshold 2)))))).and
      ((polynomial_absorption epsilon hepsilon).and (tail_absorption c' hc')))
  refine ⟨max 2 (max Nf (max Ne Nz)),?_⟩
  intro N hN L hLlo hLhi hlambda A hpos hIV hA hbudget
  have hdata := hz N (by omega)
  have hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ Real.log N := by exact le_trans (le_max_right _ _) ((le_max_right _ _).trans hdata.1)
  have hI := eventInformation_nonneg A hpos
  let I := eventInformation A
  let w := informationCutoff (Real.log N) I
  let nu := Real.log N/w
  let lambda : ℝ := fullRate N L
  have hs := cutoff_spec hH hI hIV
  have hw : 0 < w := cutoff_pos hH hI hIV
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le ((le_max_left _ _).trans hH)
  have hnu : 0 ≤ nu := div_nonneg hHp.le hw.le
  have hwlo : lo*Real.sqrt (Real.log N*Real.log (Real.log N)) ≤ w :=
    (h1 _ ((le_max_left _ _).trans hdata.1)).1.trans hs.1.1
  have hwhi : w ≤ hi*Real.sqrt (Real.log N*Real.log (Real.log N)) :=
    hs.1.2.trans (h2 _ ((le_max_left _ _).trans ((le_max_right _ _).trans hdata.1))).2
  have hraw := hf N (by omega) w hwlo hwhi L (movableMarkCutoff N) hLlo
    (he N (by omega) L hLhi) A hA hpos
  have hproducts := exponential_products hI hlambda hnu hc' hcc hs.2 hbudget
  have hpoly := hdata.2.1
  have hwexp : Real.exp w ≤ Real.exp (saddleCutoff 2 (Real.log N)) := Real.exp_le_exp.mpr hs.1.2
  have hpolyprod := mul_le_mul_of_nonneg_right hproducts.2.2.1
    (Real.rpow_nonneg (Nat.cast_nonneg N) (-(1/(3:ℝ))+epsilon/2))
  have hpolyw := mul_le_mul_of_nonneg_right hwexp
    (Real.rpow_nonneg (Nat.cast_nonneg N) (-(1/(3:ℝ))+epsilon/2))
  have hfree : Real.exp I*freeMarkedRate N L w (epsilon/2) (c-c') ≤
      64*Real.exp (-c'*nu)+64*(N:ℝ)^(-(1/(3:ℝ))+epsilon) := by
    unfold freeMarkedRate
    change Real.exp I*(32*(lambda*Real.exp (-saddleCost nu+(c-c')*nu)+
      lambda^2*Real.exp (-w+(c-c')*nu)+lambda*(1+lambda)*(N:ℝ)^(-(1/(3:ℝ))+epsilon/2))) ≤ _
    nlinarith [hproducts.1,hproducts.2.1]
  let tail : ℝ := lambda/(2:ℝ)^(movableMarkCutoff N+1)
  have ht0 : 0 ≤ tail := by dsimp [tail,lambda]; positivity
  have heI : 1 ≤ Real.exp I := Real.one_le_exp_iff.mpr hI
  have htt := mul_le_mul (hproducts.2.2.2.trans hwexp) (movableMarkCutoff_geometric_tail N)
    (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^(movableMarkCutoff N+1)) (Real.exp_nonneg _)
  have ht : Real.exp I*tail ≤ Real.exp (-2*saddleCutoff 2 (Real.log N)) := by
    have heq : Real.exp (saddleCutoff 2 (Real.log N))*Real.exp (-3*saddleCutoff 2 (Real.log N)) =
        Real.exp (-2*saddleCutoff 2 (Real.log N)) := by rw [← Real.exp_add]; congr 1; ring
    rw [heq] at htt
    simpa only [tail,mul_one_div,mul_div_assoc] using htt
  have hsmall := ht.trans (hdata.2.2 I hI hIV)
  have htail : tail ≤ Real.exp I*tail := le_mul_of_one_le_left ht0 heI
  have hone : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N:ℝ)^(-(1/(2:ℝ))+epsilon/2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hone (by linarith)
  rw [div_eq_mul_inv,← exp_eventInformation A hpos] at hraw
  have htailpow := mul_le_mul_of_nonneg_left hpow (mul_nonneg (Real.exp_nonneg I) ht0)
  change spatialEventDistance N L A ≤ 67*Real.exp (-c'*nu)+64*(N:ℝ)^(-(1/(3:ℝ))+epsilon)
  change spatialEventDistance N L A ≤
    (freeMarkedRate N L w (epsilon/2) (c-c')+tail*(1+(N:ℝ)^(-(1/(2:ℝ))+epsilon/2)))*Real.exp I+tail at hraw
  nlinarith

end
end PaperC.Prel8.InformationFieldTheorem
