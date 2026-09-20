import PaperCPrel8.RoughKernelDeletionLimits
import PaperCPrel8.SignedGoodReplacement
import PaperCPrel8.MicroscopicActualGeometry

/-! # Appendix G.1 at the paper's literal information cutoff and original conditioning

All geometric premises are discharged by the paper's length and information
budget. The retained and replaced laws use the genuine arithmetic signed
field and the original small-prime event, with no conditioning amplification.
-/
namespace PaperC.Prel8.StrongerDeletionTheorem
open RoughKernelThreshold RoughKernelDeletion RoughKernelGoodSet RoughKernelDeletionLimits
open MicroscopicActualGeometry MicroscopicPaperBudget MicroscopicProfileBudget MicroscopicGoodField
open ActualSignedPalm SignedGoodReplacement FiniteFieldReplacement
open ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
open V282.SaddleParameters V282.SaddleScales V282.PrimeEulerPNT V282.FiniteFieldTotalVariation
open Set Filter Topology
noncomputable section

def originalGood (M L : ℕ) (I : ℝ) : Finset ℕ :=
  goodSites M (M-L) L (paperExcess M L I) (primeCutoff M)
def strongerGood (M L : ℕ) (I theta : ℝ) : Finset ℕ :=
  paperGood M (M-L) L (paperExcess M L I) (primeCutoff M) ⌊threshold theta (Real.log M)⌋₊
def added (M L : ℕ) (I theta : ℝ) : Finset ℕ := originalGood M L I \ strongerGood M L I theta

/-- Uniform source-facing mass and total count bounds, at the paper's actual E_* and Y. -/
theorem paper_counts (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax theta c : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax)
    (htheta : 0 ≤ theta) (htc : theta < c) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      (1/(2:ℝ)^L) * ((added M L I theta).card : ℝ) ≤
        Real.exp (-((c-theta)/2)*saddleNu 1 (Real.log M)) ∧
      (((Finset.Icc 1 (M-L)) \ strongerGood M L I theta).card : ℝ) ≤
        (⌈Real.sqrt M⌉₊ : ℝ) + M * Real.exp
          (-saddleCutoff 1 (Real.log M)+(theta+1)*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hmin hband (by linarith)
  obtain ⟨Ma,ha⟩ := added_mass_bound hPNT (betaMax+1) theta c (by linarith) htheta htc
  obtain ⟨Mt,ht⟩ := total_count hPNT (betaMax+1) theta 1 (by linarith) htheta (by norm_num)
  refine ⟨max Mg (max Ma Mt), ?_⟩
  intro M hM L I hlo hhi hI hlambda hbudget
  have hgeo := hg M (by omega) L I hlo hhi hI hlambda hbudget
  have hQ : ((L+paperExcess M L I+1:ℕ):ℝ) ≤ (betaMax+1)*Real.log M := by
    have := hgeo.shifted_upper
    push_cast
    linarith
  have hmass : (1/(2:ℝ)^L) * ((M-L:ℕ):ℝ) ≤
      Real.exp (saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) := by
    have he : (1/(2:ℝ)^L) * ((M-L:ℕ):ℝ) = siteRate M L := by unfold siteRate; ring
    rw [he]
    rw [← Real.exp_log (show 0 < siteRate M L by linarith)]
    exact Real.exp_le_exp.mpr (by linarith)
  constructor
  · exact ha M (by omega) (M-L) (L+paperExcess M L I+1) hgeo.population hgeo.support_short hQ
      (originalGood M L I) (goodSites_subset _ _ _ _ _) _ (by positivity) hmass
  · have h := ht M (by omega) (M-L) L (paperExcess M L I) hgeo.population hgeo.support_short
      (by exact_mod_cast hQ)
    apply h.trans
    apply add_le_add (le_refl _)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le M L) (Real.exp_pos _).le

/-- The precise theta+epsilon exponent, uniform before the paper parameters are chosen. -/
theorem paper_added_count (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax theta c epsilon : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax)
    (htheta : 0 ≤ theta) (hc : 0 < c) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      ((added M L I theta).card : ℝ) ≤ ((M-L:ℕ):ℝ) * Real.exp
        (-saddleCutoff 1 (Real.log M)+(theta+epsilon)*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hmin hband hc
  obtain ⟨Ma,ha⟩ := RoughKernelStrongCount.added_count hPNT (betaMax+1) theta epsilon
    (by linarith) htheta hepsilon
  refine ⟨max Mg Ma, ?_⟩
  intro M hM L I hlo hhi hI hlambda hbudget
  have hgeo := hg M (by omega) L I hlo hhi hI hlambda hbudget
  have hQ : ((L+paperExcess M L I+1:ℕ):ℝ) ≤ (betaMax+1)*Real.log M := by
    have := hgeo.shifted_upper
    push_cast
    linarith
  exact ha M (by omega) (M-L) (L+paperExcess M L I+1) hgeo.population hgeo.support_short hQ
    (originalGood M L I) (goodSites_subset _ _ _ _ _)

/-- Actual independent replacement of all additionally deleted low signed coordinates. -/
theorem paper_replacement (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax theta c : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax)
    (htheta : 0 ≤ theta) (htc : theta < c) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      ∀ A : SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop,
      ∀ hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
        (fun w ↦ A (restrictSmall _ _ w)),
      massTotalVariation
        (finiteFieldLaw (sourceLaw A hA) (field (sourceCylinder M L I) L (paperExcess M L I) (originalGood M L I)))
        (replacementLaw (sourceLaw A hA) (field (sourceCylinder M L I) L (paperExcess M L I) (originalGood M L I))
          (kept (originalGood M L I) (strongerGood M L I theta) (paperExcess M L I))
          (fill (originalGood M L I) (strongerGood M L I theta) L (paperExcess M L I))) ≤
        2 * Real.exp (-((c-theta)/2)*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hmin hband (by linarith)
  obtain ⟨Mc,hc⟩ := paper_counts hPNT betaMin betaMax theta c hmin hband htheta htc
  refine ⟨max Mg Mc, ?_⟩
  intro M hM L I hlo hhi hI hlambda hbudget A hA
  have hgeom := actual_goodGeometry (hg M (by omega) L I hlo hhi hI hlambda hbudget)
  have hp := replacement_cost hgeom (strongerGood M L I theta) A hA
  have hm := (hc M (by omega) L I hlo hhi hI hlambda hbudget).1
  change (1/(2:ℝ)^L) * (((originalGood M L I) \ strongerGood M L I theta).card : ℝ) ≤ _ at hm
  apply hp.trans
  change 2 * (1/(2:ℝ)^L) * (((originalGood M L I) \ strongerGood M L I theta).card : ℝ) ≤ _
  nlinarith

/-- The uniform bound for additional replacement vanishes. -/
theorem replacement_rate_tendsto (theta c : ℝ) (htc : theta < c) :
    Tendsto (fun M : ℕ ↦ 2 * Real.exp (-((c-theta)/2)*saddleNu 1 (Real.log M))) atTop (𝓝 0) := by
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he := Real.tendsto_exp_atBot.comp
    (((tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).comp hl).const_mul_atTop_of_neg
      (show -((c-theta)/2) < 0 by linarith))
  simpa only [mul_zero,Function.comp_def] using he.const_mul 2

/-- The actual additionally deleted mass vanishes at the paper's E_* and original good set. -/
theorem paper_added_mass_tendsto (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax theta c : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax)
    (htheta : 0 ≤ theta) (htc : theta < c) (L : ℕ → ℕ) (I : ℕ → ℝ)
    (hregime : ∀ᶠ M : ℕ in atTop, betaMin*Real.log M ≤ (L M+1:ℝ) ∧
      (L M+1:ℝ) ≤ betaMax*Real.log M ∧ 0 ≤ I M ∧ 1 ≤ siteRate M (L M) ∧
      I M+Real.log (siteRate M (L M)) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) :
    Tendsto (fun M ↦ (1/(2:ℝ)^(L M)) * ((added M (L M) (I M) theta).card : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Mc,hc⟩ := paper_counts hPNT betaMin betaMax theta c hmin hband htheta htc
  have he := (replacement_rate_tendsto theta c htc).div_const 2
  have he' : Tendsto (fun M : ℕ ↦ Real.exp (-((c-theta)/2)*saddleNu 1 (Real.log M))) atTop (𝓝 0) := by
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0),zero_div] using he
  apply squeeze_zero' _ _ he'
  · exact Filter.Eventually.of_forall (fun M ↦ by positivity)
  · filter_upwards [hregime,eventually_ge_atTop Mc] with M h hm
    exact (hc M hm (L M) (I M) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).1

/-- The full omitted fraction is o(M/log M) under only the paper's regime. -/
theorem paper_density_tendsto (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax theta c : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax)
    (htheta : 0 ≤ theta) (hc : 0 < c) (L : ℕ → ℕ) (I : ℕ → ℝ)
    (hregime : ∀ᶠ M : ℕ in atTop, betaMin*Real.log M ≤ (L M+1:ℝ) ∧
      (L M+1:ℝ) ≤ betaMax*Real.log M ∧ 0 ≤ I M ∧ 1 ≤ siteRate M (L M) ∧
      I M+Real.log (siteRate M (L M)) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) :
    Tendsto (fun M ↦ (((Finset.Icc 1 (M-L M)) \ strongerGood M (L M) (I M) theta).card : ℝ) /
      (M:ℝ) * Real.log M) atTop (𝓝 0) := by
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hmin hband hc
  apply total_density_tendsto hPNT (betaMax+1) theta (by linarith) htheta
    (fun M ↦ M-L M) L (fun M ↦ paperExcess M (L M) (I M))
  filter_upwards [hregime,eventually_ge_atTop Mg] with M h hm
  have hgeo := hg M hm (L M) (I M) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  refine ⟨Nat.sub_le _ _,hgeo.population,hgeo.support_short,?_⟩
  have := hgeo.shifted_upper
  linarith

end
end PaperC.Prel8.StrongerDeletionTheorem
