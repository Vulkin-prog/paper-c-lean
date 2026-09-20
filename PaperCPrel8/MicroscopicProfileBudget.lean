import PaperCPrel8.MicroscopicValueProfile
import PaperCPrel8.MicroscopicInformationCutoff

/-! # Arithmetic relation profile at the actual information cutoff

The shifted band and exponential inflation are discharged uniformly from the
base logarithmic band and information budget. No arbitrary excess cutoff remains.
-/
namespace PaperC.Prel8.MicroscopicProfileBudget
open PaperC.Prel8.MicroscopicValueProfile PaperC.Prel8.MicroscopicInformationCutoff
open PaperC.Prel8.MicroscopicRelationExcess PaperC.Prel8.MicroscopicGoodField
open PaperC.V282.SaddleParameters PaperC.V282.AllStartSoftPoisson
noncomputable section

/-- The paper's cutoff uses the actual ambient start intensity. -/
def paperExcess (M L : ℕ) (I : ℝ) : ℕ :=
  excessCutoff I (saddleCutoff 1 (Real.log M)) (fullRate M L)

/-- The normalized relation cost has the usual power saving at the literal varying cutoff. -/
theorem actual_cutoff_profile_bound
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n L Y C : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ (fullRate M L:ℝ) →
      I+Real.log (fullRate M L:ℝ) ≤ saddleCutoff 1 (Real.log M) →
      n+1 ≤ M → M+(L+paperExcess M L I+1) ≤ C →
      (1/(2:ℝ)^L)^2 * separatedExcess C L (paperExcess M L I)
        (goodSites M n L (paperExcess M L I) Y) ≤
        (M:ℝ)^(-(1/(3:ℝ))+epsilon)*((fullRate M L:ℝ)^2+2*(fullRate M L:ℝ)) := by
  obtain ⟨Mp,hp⟩ := normalized_separatedExcess_good_le_eventually betaMin (betaMax+1)
    (epsilon/2) hbetaMin (by linarith) (by positivity)
  obtain ⟨Mb,hb⟩ := shifted_band_eventually betaMin betaMax 1 (by norm_num)
  obtain ⟨Mc,hc⟩ := cutoff_profile_subpolynomial (epsilon/2) (by positivity)
  refine ⟨max 1 (max Mp (max Mb Mc)), ?_⟩
  intro M hM n L Y C I hlo hhi hI hlam hbudget hn hC
  obtain ⟨hslo,hshi⟩ := hb M (by omega) L I (fullRate M L) hlo hhi hI hlam hbudget
  have hp' := hp M (by omega) n L (paperExcess M L I) Y C hslo hshi hn hC
  have hc' := hc M (by omega) I (fullRate M L) hI hlam hbudget
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  calc
    _ ≤ _ := hp'
    _ ≤ (M:ℝ)^(epsilon/2)*(M:ℝ)^(-(1/(3:ℝ))+epsilon/2)*
        ((fullRate M L:ℝ)^2+2*(fullRate M L:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hc' (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hm]
      congr 2
      ring

/-- Information and intensity together control the entire quadratic rate factor. -/
theorem conditional_rate_factor_le {I V lambda : ℝ} (hI : 0 ≤ I) (hlambda : 1 ≤ lambda)
    (hbudget : I+Real.log lambda ≤ V) :
    Real.exp I*(lambda^2+2*lambda) ≤ 3*Real.exp (2*V) := by
  have hlam : 0 < lambda := by linarith
  have hprod : Real.exp I*lambda ≤ Real.exp V := by
    simpa only [Real.exp_add,Real.exp_log hlam] using Real.exp_le_exp.mpr hbudget
  have hsmall : lambda ≤ Real.exp V := by
    have he := Real.one_le_exp hI
    nlinarith
  have hquad := mul_le_mul hprod hsmall hlam.le (Real.exp_pos V).le
  rw [show 2*V=V+V by ring,Real.exp_add]
  have hm := mul_le_mul_of_nonneg_left (show lambda ≤ lambda^2 by nlinarith) (Real.exp_pos I).le
  nlinarith

/-- Even after conditioning, the actual cutoff's relation contribution has a uniform power saving. -/
theorem conditional_actual_profile_bound
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n L Y C : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ (fullRate M L:ℝ) →
      I+Real.log (fullRate M L:ℝ) ≤ saddleCutoff 1 (Real.log M) →
      n+1 ≤ M → M+(L+paperExcess M L I+1) ≤ C →
      Real.exp I*((1/(2:ℝ)^L)^2 * separatedExcess C L (paperExcess M L I)
        (goodSites M n L (paperExcess M L I) Y)) ≤ (M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  obtain ⟨Mp,hp⟩ := actual_cutoff_profile_bound betaMin betaMax (epsilon/2) hbetaMin hbeta (by positivity)
  obtain ⟨Mc,hc⟩ := Filter.eventually_atTop.mp
    (PaperC.V282.AggregateCutoffRemainder.constant_exp_saddle_le_power_eventually
      3 2 (epsilon/2) (by norm_num) (by positivity))
  refine ⟨max 1 (max Mp Mc), ?_⟩
  intro M hM n L Y C I hlo hhi hI hlam hb hn hC
  have hp' := hp M (by omega) n L Y C I hlo hhi hI hlam hb hn hC
  have hf := conditional_rate_factor_le hI hlam hb
  have hs := hf.trans (hc M (by omega))
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  calc
    _ ≤ Real.exp I*((M:ℝ)^(-(1/(3:ℝ))+epsilon/2)*
        ((fullRate M L:ℝ)^2+2*(fullRate M L:ℝ))) :=
      mul_le_mul_of_nonneg_left hp' (Real.exp_pos I).le
    _ = (M:ℝ)^(-(1/(3:ℝ))+epsilon/2)*
        (Real.exp I*((fullRate M L:ℝ)^2+2*(fullRate M L:ℝ))) := by ring
    _ ≤ (M:ℝ)^(-(1/(3:ℝ))+epsilon/2)*(M:ℝ)^(epsilon/2) := by gcongr
    _ = _ := by rw [← Real.rpow_add hm]; congr 1; ring

end
end PaperC.Prel8.MicroscopicProfileBudget
