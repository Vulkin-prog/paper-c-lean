import PaperCPrel8.RegularTargetSaddle
import PaperCPrel8.MicroscopicDeletedTarget
import PaperCPrel8.MicroscopicSpatialRates
import PaperCV282.SaddleRateConvergence

/-! # Complete regular-target error and its vanishing under the paper regime -/
namespace PaperC.Prel8.RegularTargetCompletion
open MeasureTheory ProbabilityTheory Finset Filter Topology
open RegularTargetSaddle RegularTargetCloud StrongerDeletionTheorem
open MicroscopicActualGeometry MicroscopicPaperBudget MicroscopicProfileBudget
open MicroscopicDiscardRates MicroscopicSpatialRates RoughKernelGoodSet
open V282.SaddleParameters V282.SaddleScales V282.PrimeEulerPNT V282.AllStartSoftPoisson
open V282.BulkMarkedTarget V282.AggregateCutoffRemainder
noncomputable section

/-- Uniform total omissions with an arbitrary positive second-scale slack. -/
theorem omitted_count_eventually (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c theta eta : ℝ) (hmin : 0<betaMin) (hband : betaMin<betaMax)
    (hc : 0<c) (htheta : 0≤theta) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M≤(L+1:ℝ) → (L+1:ℝ)≤betaMax*Real.log M →
      0≤I → 1≤siteRate M L →
      I+Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      (((Icc 1 (M-L)) \ strongerGood M L I theta).card:ℝ) ≤
        (⌈Real.sqrt M⌉₊:ℝ)+(M-L:ℕ)*Real.exp
          (-saddleCutoff 1 (Real.log M)+(theta+eta)*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hmin hband hc
  obtain ⟨Mt,ht⟩ := total_count hPNT (betaMax+1) theta eta (by linarith) htheta heta
  refine ⟨max Mg Mt,?_⟩
  intro M hM L I hlo hhi hI hr hb
  have g := hg M (by omega) L I hlo hhi hI hr hb
  exact ht M (by omega) (M-L) L (paperExcess M L I) g.population g.support_short
    (by have := g.shifted_upper; linarith)

/-- The first two displayed G.3 terms bound the exact target deleted-site intensity. -/
theorem omitted_rate_eventually (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c theta eta : ℝ) (hmin : 0<betaMin) (hband : betaMin<betaMax)
    (hc : 0<c) (htheta : 0≤theta) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M≤(L+1:ℝ) → (L+1:ℝ)≤betaMax*Real.log M →
      0≤I → 1≤siteRate M L →
      I+Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      siteRate M L*(((Icc 1 (M-L)) \ strongerGood M L I theta).card:ℝ)/(M-L:ℕ) ≤
        4*siteRate M L*(M:ℝ)^(-(1/(2:ℝ)))+siteRate M L*Real.exp
          (-saddleCutoff 1 (Real.log M)+(theta+eta)*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mc,hcount⟩ := omitted_count_eventually hPNT betaMin betaMax c theta eta hmin hband hc htheta heta
  obtain ⟨Ml,hl⟩ := logarithmic_length_quarter betaMax (by linarith)
  refine ⟨max 1 (max Mc Ml),?_⟩
  intro M hM L I hlo hhi hI hr hb
  have hm : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hn : 0<M-L := by
    by_contra h; have he : M-L=0 := by omega
    have : (1:ℝ)≤0 := by simpa [siteRate,he] using hr
    linarith
  have hnR : (M-L:ℕ)≠(0:ℝ) := by exact_mod_cast hn.ne'
  have hcard := hcount M (by omega) L I hlo hhi hI hr hb
  have hp := div_le_div_of_nonneg_right hcard (by positivity : 0≤(2:ℝ)^L)
  have hlambda := (siteRate_comparison M L (by have := hl M (by omega) L hhi; omega)).2
  have hs := mul_le_mul_of_nonneg_left (rounded_sqrt_ratio M (by omega)) (show 0≤(fullRate M L:ℝ) by positivity)
  have hs2 := mul_le_mul_of_nonneg_right hlambda (show 0≤2*(M:ℝ)^(-(1/(2:ℝ))) by positivity)
  have he : (⌈Real.sqrt M⌉₊:ℝ)/(2:ℝ)^L = (fullRate M L:ℝ)*((⌈Real.sqrt M⌉₊:ℝ)/M) := by
    rw [fullRate_coe]; field_simp
  have hx : siteRate M L*(((Icc 1 (M-L)) \ strongerGood M L I theta).card:ℝ)/(M-L:ℕ) =
      (((Icc 1 (M-L)) \ strongerGood M L I theta).card:ℝ)/(2:ℝ)^L := by
    unfold siteRate; field_simp
  rw [hx]
  rw [add_div] at hp
  rw [he] at hp
  have he2 (x : ℝ) : (M-L:ℕ)*x/(2:ℝ)^L=siteRate M L*x := by unfold siteRate; ring
  rw [he2] at hp
  nlinarith only [hp,hs,hs2]

/-- Complete displayed regular-cloud bound, with arbitrary eta>0 replacing the
paper's o(nu) in its usual uniform second-scale formulation. -/
theorem target_error_eventually (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c theta eta : ℝ) (hmin : 0<betaMin) (hband : betaMin<betaMax)
    (hc : 0<c) (htheta : 0<theta) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M≤(L+1:ℝ) → (L+1:ℝ)≤betaMax*Real.log M →
      0≤I → 1≤siteRate M L →
      I+Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      (spatialTargetMeasure (Icc 1 (M-L)) L).real {z | ¬paperRegular M L I theta z} ≤
        4*siteRate M L*(M:ℝ)^(-(1/(2:ℝ)))+
        siteRate M L*Real.exp (-saddleCutoff 1 (Real.log M)+(theta+eta)*saddleNu 1 (Real.log M))+
        Real.exp (-c*theta*saddleNu 1 (Real.log M)^2/(4*saddleParameter 1 (Real.log M)))+
        Real.exp (-((2*Real.log 2-1)*siteRate M L))+
        siteRate M L/(2:ℝ)^(paperExcess M L I+1) := by
  obtain ⟨Mt,ht⟩ := paper_target_bound betaMin betaMax c theta hmin hband hc htheta
  obtain ⟨Mo,ho⟩ := omitted_rate_eventually hPNT betaMin betaMax c theta eta hmin hband hc htheta.le heta
  refine ⟨max Mt Mo,?_⟩
  intro M hM L I hlo hhi hI hr hb
  exact (ht M (by omega) L I hlo hhi hI hr hb).trans
    (add_le_add (add_le_add (add_le_add (ho M (by omega) L I hlo hhi hI hr hb) (le_refl _)) (le_refl _)) (le_refl _))

/-- The first displayed cost is uniformly dominated by M^(-1/4) under the budget. -/
theorem shallow_rate_eventually (c : ℝ) (hc : 0<c) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ rate I : ℝ,
      0<rate → 0≤I → I+Real.log rate≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      4*rate*(M:ℝ)^(-(1/(2:ℝ)))≤(M:ℝ)^(-(1/(4:ℝ))) := by
  obtain ⟨Mp,hp⟩ := eventually_atTop.mp
    (constant_exp_saddle_le_power_eventually 4 1 (1/4) (by norm_num) (by norm_num))
  obtain ⟨Mn,hn⟩ := nu_le_saddle_eventually
  refine ⟨max 1 (max Mp Mn),?_⟩
  intro M hM rate I hr hI hb
  have hm : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hn0 := (hn M (by omega)).1
  have hrV : rate≤Real.exp (saddleCutoff 1 (Real.log M)) := by
    rw [← Real.exp_log hr]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hp' := hp M (by omega)
  simp only [one_mul] at hp'
  calc
    _ ≤ (4*Real.exp (saddleCutoff 1 (Real.log M)))*(M:ℝ)^(-(1/(2:ℝ))) := by gcongr
    _ ≤ (M:ℝ)^(1/(4:ℝ))*(M:ℝ)^(-(1/(2:ℝ))) := by gcongr
    _ = _ := by rw [← Real.rpow_add hm]; congr 1; ring

/-- A uniform numerical majorant in which every term has a separate vanishing proof. -/
theorem target_vanishing_bound (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c theta : ℝ) (hmin : 0<betaMin) (hband : betaMin<betaMax)
    (htheta : 0<theta) (htc : theta<c) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M≤(L+1:ℝ) → (L+1:ℝ)≤betaMax*Real.log M →
      0≤I → 1≤siteRate M L →
      I+Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      (spatialTargetMeasure (Icc 1 (M-L)) L).real {z | ¬paperRegular M L I theta z} ≤
        (M:ℝ)^(-(1/(4:ℝ)))+
        Real.exp (-((c-theta)/2)*saddleNu 1 (Real.log M))+
        Real.exp (-c*theta*saddleNu 1 (Real.log M)^2/(4*saddleParameter 1 (Real.log M)))+
        Real.exp (-((2*Real.log 2-1)*siteRate M L))+
        Real.exp (-c*saddleNu 1 (Real.log M)) := by
  have hc : 0<c := htheta.trans htc
  obtain ⟨Mt,ht⟩ := target_error_eventually hPNT betaMin betaMax c theta ((c-theta)/2)
    hmin hband hc htheta (by linarith)
  obtain ⟨Ms,hs⟩ := shallow_rate_eventually c hc
  obtain ⟨Me,he⟩ := target_tail_eventually c hc
  refine ⟨max Mt (max Ms Me),?_⟩
  intro M hM L I hlo hhi hI hr hb
  have hmain := ht M (by omega) L I hlo hhi hI hr hb
  have hshallow := hs M (by omega) (siteRate M L) I (by linarith) hI hb
  have htail := he M (by omega) L I hI (Icc 1 (M-L)) (by simp [Nat.card_Icc])
  rw [target_rate_eq] at htail
  have hbudget : siteRate M L≤Real.exp (saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) := by
    rw [← Real.exp_log (show 0<siteRate M L by linarith)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hkernel := mul_le_mul_of_nonneg_right hbudget
    (Real.exp_pos (-saddleCutoff 1 (Real.log M)+(theta+(c-theta)/2)*saddleNu 1 (Real.log M))).le
  rw [← Real.exp_add] at hkernel
  have heq : saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)+
      (-saddleCutoff 1 (Real.log M)+(theta+(c-theta)/2)*saddleNu 1 (Real.log M)) =
      -((c-theta)/2)*saddleNu 1 (Real.log M) := by ring
  rw [heq] at hkernel
  exact hmain.trans (add_le_add (add_le_add (add_le_add (add_le_add hshallow hkernel) (le_refl _)) (le_refl _)) htail)

/-- G.3: the actual complete target exceptional probability tends to zero,
with precisely the growing-intensity assumption inherited from Appendix F. -/
theorem target_failure_tendsto (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c theta : ℝ) (hmin : 0<betaMin) (hband : betaMin<betaMax)
    (htheta : 0<theta) (htc : theta<c) (L : ℕ → ℕ) (I : ℕ → ℝ)
    (hrate : Tendsto (fun M ↦ siteRate M (L M)) atTop atTop)
    (hregime : ∀ᶠ M : ℕ in atTop, betaMin*Real.log M≤(L M+1:ℝ) ∧
      (L M+1:ℝ)≤betaMax*Real.log M ∧ 0≤I M ∧ 1≤siteRate M (L M) ∧
      I M+Real.log (siteRate M (L M))≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) :
    Tendsto (fun M ↦ (spatialTargetMeasure (Icc 1 (M-L M)) (L M)).real
      {z | ¬paperRegular M (L M) (I M) theta z}) atTop (𝓝 0) := by
  have hc : 0<c := htheta.trans htc
  have hlog : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnu := (tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).comp hlog
  have hp : Tendsto (fun M : ℕ ↦ (M:ℝ)^(-(1/(4:ℝ)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop
  have he := Real.tendsto_exp_atBot.comp (hnu.const_mul_atTop_of_neg (show -((c-theta)/2)<0 by linarith))
  have hg := (RegularCloudSaddle.regularity_error_tendsto c theta hc htheta).comp hlog
  have ht := Real.tendsto_exp_atBot.comp (hrate.const_mul_atTop_of_neg
    (show -(2*Real.log 2-1)<0 by linarith [Real.log_two_gt_d9]))
  have hm := Real.tendsto_exp_atBot.comp (hnu.const_mul_atTop_of_neg (show -c<0 by linarith))
  have hsum := (((hp.add he).add hg).add ht).add hm
  simp only [add_zero,Function.comp_def] at hsum
  obtain ⟨Mt,hbound⟩ := target_vanishing_bound hPNT betaMin betaMax c theta hmin hband htheta htc
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ ENNReal.toReal_nonneg)) _ hsum
  filter_upwards [hregime,eventually_ge_atTop Mt] with M h hM
  simpa only [Measure.real,neg_mul] using hbound M hM (L M) (I M) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

end
end PaperC.Prel8.RegularTargetCompletion
