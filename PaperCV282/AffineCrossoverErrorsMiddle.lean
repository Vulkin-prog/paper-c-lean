import PaperCV282.AffineCrossoverErrorsInterior
import PaperCV282.PostQuadraticDecay

/-! # The actual middle event with its information factor and two-source normalization -/
namespace PaperC.V282.AffineCrossoverErrorsMiddle

open Filter Topology MeasureTheory InfiniteRademacher AllStartSoftPoisson
open DeepStartEvents PostQuadraticLiterature PostQuadraticDecay BalasubramanianShoreyInput
open PrimeEulerPNT RarePrefixEvents CrossoverMarkedTarget CrossoverRareScale BulkPopulation
open AffineCrossoverBudget AffineCrossoverErrorsScales SaddleParameters SaddleScales BulkMarkedConvergence

noncomputable section

/-- Quantitative conditioning of the actual middle event, before taking either limit. -/
theorem weighted_middle_bound_eventually
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax delta : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hdelta : 0<delta) (hdeltaOne : delta<1) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      ∀ I : ℝ, I≤saddleCutoff 1 (Real.log M) →
      Real.exp I*infiniteRademacherMeasure.real (middleEvent M L delta)/
        ((borderRate L : ℝ)+(fullRate M L : ℝ)) ≤
        (M : ℝ)^(-((1-delta)/2)) + Real.exp (-((L : ℝ)/Real.log L)) := by
  obtain ⟨theta,K,hK,Md,hd⟩ := equation_seven_eight betaMin betaMax hbetaMin hbeta hShorey hPNT hNR
  obtain ⟨Le,he⟩ := eventually_atTop.mp
    (exceptional_relative_to_border_le_eventually hPNT theta K 2 hK (by norm_num))
  obtain ⟨Ms,hs⟩ := information_le_length_scale_eventually betaMin betaMax hbetaMin hbeta
  obtain ⟨Mp,hp⟩ := information_power_eventually ((1-delta)/2) (by linarith)
  obtain ⟨Ma,ha⟩ := CriticalWeightedDefect.admissible_eventually hbetaMin hbeta
  obtain ⟨Mh,hh⟩ := CriticalWeightedDefect.height_tends_to_infinity (c₂ := betaMax) hbetaMin (Le+1)
  refine ⟨max Md (max Ms (max Mp (max Ma (max Mh 1)))),?_⟩
  intro M hM L hlo hhi I hI
  have hL := hh M (by omega) (L+1) (ha M (by omega) (L+1)
    ⟨hbetaMin,hbeta,by simpa using hlo,by simpa using hhi⟩)
  have hMpos : 0<(M : ℝ) := by exact_mod_cast (show 0<M by omega)
  have hb : 0<(borderRate L : ℝ) := by exact_mod_cast borderRate_pos L
  have hlambda : 0<(fullRate M L : ℝ) := by rw [fullRate_coe];positivity
  let E : ℝ := Real.exp (K*((L : ℝ)/Real.log L))*(2 : ℝ)^(-gap (L+1) theta)
  have hE : 0≤E := by dsimp [E];positivity
  have hraw : infiniteRademacherMeasure.real (middleEvent M L delta)≤(M : ℝ)^delta/(2 : ℝ)^L+E :=
    hd M (by omega) L (by simpa using hlo) (by simpa using hhi) delta hdelta hdeltaOne
  have hsplit : infiniteRademacherMeasure.real (middleEvent M L delta)/
      ((borderRate L : ℝ)+(fullRate M L : ℝ)) ≤ (M : ℝ)^(delta-1)+E/(borderRate L : ℝ) := by
    calc
      _ ≤ ((M : ℝ)^delta/(2 : ℝ)^L+E)/((borderRate L : ℝ)+(fullRate M L : ℝ)) :=
        div_le_div_of_nonneg_right hraw (by positivity)
      _ = ((M : ℝ)^delta/(2 : ℝ)^L)/((borderRate L : ℝ)+(fullRate M L : ℝ))+
          E/((borderRate L : ℝ)+(fullRate M L : ℝ)) := add_div _ _ _
      _ ≤ ((M : ℝ)^delta/(2 : ℝ)^L)/(fullRate M L : ℝ)+E/(borderRate L : ℝ) := by
        exact add_le_add (div_le_div_of_nonneg_left (by positivity) hlambda (by linarith))
          (div_le_div_of_nonneg_left hE hb (by linarith))
      _ = _ := by
        congr 1
        rw [fullRate_coe,Real.rpow_sub hMpos,Real.rpow_one]
        field_simp
  have hpower : Real.exp I*(M : ℝ)^(delta-1)≤(M : ℝ)^(-((1-delta)/2)) := by
    calc
      _ ≤ (M : ℝ)^((1-delta)/2)*(M : ℝ)^(delta-1) :=
        mul_le_mul_of_nonneg_right (hp M (by omega) I hI) (Real.rpow_nonneg hMpos.le _)
      _ = _ := by rw [← Real.rpow_add hMpos];congr 1;ring
  have hexception : Real.exp I*(E/(borderRate L : ℝ))≤Real.exp (-((L : ℝ)/Real.log L)) := by
    have het : E/(borderRate L : ℝ)≤Real.exp (-2*((L : ℝ)/Real.log L)) := by
      simpa only [E,borderRate_coe] using he L (by omega)
    apply (mul_le_mul_of_nonneg_left het (Real.exp_nonneg I)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hscale := hs M (by omega) L hlo hhi I hI
    linarith
  have hweighted := mul_le_mul_of_nonneg_left hsplit (Real.exp_nonneg I)
  rw [← mul_div_assoc] at hweighted
  nlinarith only [hweighted,hpower,hexception]

/-- The weighted middle probability is negligible relative to border plus ambient mean. -/
theorem weighted_middle_full_scale_tendsto_zero
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (I : ℕ→ℝ) (hI : ∀ᶠ n in atTop,I n≤saddleCutoff 1 (Real.log (sizes n))) :
    Tendsto (fun n => Real.exp (I n)*infiniteRademacherMeasure.real (middleEvent (sizes n) (lengths n) delta)/
      ((borderRate (lengths n) : ℝ)+(fullRate (sizes n) (lengths n) : ℝ))) atTop (𝓝 0) := by
  obtain ⟨Mzero,hzero⟩ := weighted_middle_bound_eventually hShorey hPNT hNR (1/2) (beta+1) delta
    (by norm_num) (by linarith) hdelta hdeltaOne
  have hp := (tendsto_rpow_neg_atTop (by linarith : 0<(1-delta)/2)).comp
    (tendsto_natCast_atTop_atTop.comp hsizes)
  have he := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (nat_div_log_tendsto_atTop.comp hlengths))
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_
    (by simpa only [Function.comp_def,add_zero] using hp.add he)
  filter_upwards [hupper,hrare.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),hsizes.eventually (eventually_ge_atTop (max Mzero 1)),hI]
    with n hu hr hl hn hin
  have hband := rare_window_band (by omega) hl hbeta hu hr.le
  exact hzero (sizes n) (by omega) (lengths n) hband.1 hband.2 (I n) hin

/-- The denominator is now the true contained bulk population, without any phase assumption. -/
theorem weighted_middle_rare_scale_tendsto_zero
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (I : ℕ→ℝ) (hI : ∀ᶠ n in atTop,I n≤saddleCutoff 1 (Real.log (sizes n))) :
    Tendsto (fun n => Real.exp (I n)*infiniteRademacherMeasure.real (middleEvent (sizes n) (lengths n) delta)/
      rareScale (sizes n) (lengths n) delta) atTop (𝓝 0) := by
  apply relative_zero_of_half_le (Eventually.of_forall fun _ => by positivity)
    (Eventually.of_forall fun n => add_pos_of_pos_of_nonneg
      (by exact_mod_cast borderRate_pos (lengths n)) (by positivity)) ?_
    (weighted_middle_full_scale_tendsto_zero hShorey hPNT hNR sizes lengths hsizes hlengths
      beta delta hbeta hdelta hdeltaOne hupper hrare I hI)
  have hr := bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1))
  filter_upwards [hr.eventually (lt_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
    hsizes.eventually (eventually_ge_atTop 1)] with n hn hs
  have hp : 0<(fullRate (sizes n) (lengths n) : ℝ) := by
    rw [fullRate_coe]
    have hsn : 0<(sizes n : ℝ) := by exact_mod_cast (show 0<sizes n by omega)
    positivity
  have hb := (lt_div_iff₀ hp).mp hn
  have ha : 0≤(borderRate (lengths n) : ℝ) := by positivity
  rw [rareScale,totalRate_bulk_eq]
  linarith

end
end PaperC.V282.AffineCrossoverErrorsMiddle
