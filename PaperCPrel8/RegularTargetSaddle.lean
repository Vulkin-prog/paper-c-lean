import PaperCPrel8.RegularTargetCloud
import PaperCPrel8.RegularCloudCutoff
import PaperCPrel8.StrongerDeletionTheorem

/-! # The complete same-grid regular target at the literal paper parameters

All CRT cutoff side conditions are discharged by the logarithmic length band
and the paper information budget. The deleted-site and high-mark costs remain
explicit here, so they can be combined with their separate arithmetic bounds.
-/
namespace PaperC.Prel8.RegularTargetSaddle
open MeasureTheory ProbabilityTheory Finset
open V282.BulkMarkedTypes V282.BulkMarkedTarget V282.FiniteStartMaskAverages
open V282.SaddleParameters V282.SaddleScales
open MicroscopicActualGeometry MicroscopicPaperBudget MicroscopicProfileBudget
open StrongerDeletionTheorem RegularTargetCloud RegularCloudCutoff RoughKernelThreshold
open RoughKernelDeletion RoughKernelGoodSet
open Filter Topology
open scoped NNReal
noncomputable section

/-- The target's actual grid intensity equals Lambda from the paper. -/
theorem target_rate_eq (M L : ℕ) :
    (maskRate L (Icc 1 (M-L)):ℝ)=siteRate M L := by
  simp [maskRate,siteRate,Nat.card_Icc]
  rfl

/-- The intrinsic regular configurations at the paper's actual cutoffs. -/
def paperRegular (M L : ℕ) (I theta : ℝ) : SpatialMarkedConfig (Icc 1 (M-L)) → Prop :=
  RegularConfiguration (Icc 1 (M-L)) (L+paperExcess M L I+1) (primeCutoff M)
    ⌈2*siteRate M L⌉₊ (paperExcess M L I) (strongerGood M L I theta)

/-- Full signed/excess G.3 target bound with the CRT cost absorbed, at the
literal paper parameters. No analytic/arithmetic literature premise is used
for this probabilistic assembly; the excluded-site cardinality stays visible. -/
theorem paper_target_bound (betaMin betaMax c theta : ℝ)
    (hmin : 0<betaMin) (hband : betaMin<betaMax) (hc : 0<c) (htheta : 0<theta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M≤(L+1:ℝ) → (L+1:ℝ)≤betaMax*Real.log M →
      0≤I → 1≤siteRate M L →
      I+Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      (spatialTargetMeasure (Icc 1 (M-L)) L).real {z | ¬paperRegular M L I theta z} ≤
        siteRate M L*(((Icc 1 (M-L)) \ strongerGood M L I theta).card:ℝ)/(M-L:ℕ)+
        Real.exp (-c*theta*saddleNu 1 (Real.log M)^2/(4*saddleParameter 1 (Real.log M)))+
        Real.exp (-((2*Real.log 2-1)*siteRate M L))+
        siteRate M L/(2:ℝ)^(paperExcess M L I+1) := by
  have hB : 0<betaMax+1 := by linarith
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hmin hband hc
  have hlog : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Mc,hcut⟩ := eventually_atTop.mp (hlog.eventually (cutoff_gap_eventually c (betaMax+1) hc hB))
  obtain ⟨Ma,habs⟩ := eventually_atTop.mp (hlog.eventually (cloud_cost_eventually c theta (betaMax+1) hc htheta hB))
  refine ⟨max Mg (max Mc Ma),?_⟩
  intro M hM L I hlo hhi hI hr hbudget
  have hgeo := hg M (by omega) L I hlo hhi hI hr hbudget
  have hn : 0<M-L := by
    by_contra h
    have he : M-L=0 := by omega
    simp [siteRate,he] at hr
    linarith
  have hbudget' : Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) := by linarith
  have hQ : ((L+paperExcess M L I+1:ℕ)+1:ℝ)≤(betaMax+1)*Real.log M := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hgeo.shifted_upper
  have hcut' := (hcut M (by omega) (siteRate M L) _ hr hQ hbudget').1
  have habs' := habs M (by omega) (siteRate M L) _ hr hQ hbudget'
  have hK : 1≤⌈2*siteRate M L⌉₊ := by exact_mod_cast (ceil_twice_le _ hr).1
  have hQY : L+paperExcess M L I+1<primeCutoff M := by have := hgeo.strong_prime; omega
  have hT : 0<threshold theta (Real.log M) := Real.exp_pos _
  have h := target_failure_le (M-L) L (L+paperExcess M L I+1) (primeCutoff M)
    ⌈2*siteRate M L⌉₊ (paperExcess M L I) hn hK hgeo.support_short hQY
    (strongerGood M L I theta) (threshold theta (Real.log M)) hT
    (by rw [target_rate_eq]; exact Nat.le_ceil _) hcut'
    (fun j hj a ↦ ((mem_strongGood_floor _ _ _ _ _ hT.le).mp hj).2 a |>.le)
  simp only [target_rate_eq] at h
  change (spatialTargetMeasure (Icc 1 (M-L)) L).real
    {z | ¬RegularConfiguration (Icc 1 (M-L)) (L+paperExcess M L I+1) (primeCutoff M)
      ⌈2*siteRate M L⌉₊ (paperExcess M L I) (strongerGood M L I theta) z} ≤ _
  exact h.trans (add_le_add (add_le_add (add_le_add (le_refl _) habs') (le_refl _)) (le_refl _))

end
end PaperC.Prel8.RegularTargetSaddle
