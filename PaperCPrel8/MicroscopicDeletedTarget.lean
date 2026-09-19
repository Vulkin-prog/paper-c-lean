import PaperCPrel8.MicroscopicSiteRestoration

/-! # The Poisson intensity of the discarded actual sites -/
namespace PaperC.Prel8.MicroscopicDeletedTarget
open PaperC.Prel8.MicroscopicActualGeometry PaperC.Prel8.MicroscopicPaperBudget
open PaperC.Prel8.MicroscopicProfileBudget PaperC.Prel8.MicroscopicDiscardRates
open PaperC.Prel8.MicroscopicBadPivotCount PaperC.Prel8.MicroscopicDeletedSites
open PaperC.V282.AllStartSoftPoisson PaperC.V282.FiniteStartMaskAverages
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.PrimeEulerPNT
noncomputable section

/-- The unconditional target deletion cost has the required uniform rate. -/
theorem deleted_target_rate_eventually (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c c' epsilon : ℝ) (hbetaMin : 0 < betaMin) (hband : betaMin < betaMax)
    (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      (maskRate L (deletedStarts M (M-L) L (paperExcess M L I) (primeCutoff M)):ℝ) ≤
        Real.exp (-c'*saddleNu 1 (Real.log M))+(M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  let d := (c+c')/2
  let eta := (c-c')/2
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hbeta : 0 < betaMax := hbetaMin.trans hband
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hbetaMin hband (by linarith)
  obtain ⟨Mb,hb⟩ := paper_to_ambient_budget_eventually betaMax c d hbeta (by dsimp [d]; linarith)
  obtain ⟨Md,hd⟩ := badPivotSites_hard_bound hPNT (betaMax+1) eta (by linarith) heta
  obtain ⟨Ms,hs⟩ := shallow_budget_rate epsilon hepsilon
  refine ⟨max 1 (max Mg (max Mb (max Md Ms))), ?_⟩
  intro M hM L I hlo hhi hI hr hbudget
  have g := hg M (by omega) L I hlo hhi hI hr hbudget
  have hambient := (hb M (by omega) L I hhi hr hbudget).2
  have hlambda : 0 < (fullRate M L:ℝ) := by have := g.ambient_rate; linarith
  have hbadcard := hd M (by omega) (M-L) L (paperExcess M L I)
    g.population g.support_short (by have := g.shifted_upper; linarith)
  have hs' := hs M (by omega) I (fullRate M L) hlambda g.ambient_budget
  have hp : Real.exp I*(fullRate M L:ℝ) ≤ Real.exp (saddleCutoff 1 (Real.log M)-d*saddleNu 1 (Real.log M)) := by
    simpa only [Real.exp_add,Real.exp_log hlambda] using Real.exp_le_exp.mpr hambient
  have hbad : Real.exp I*(fullRate M L:ℝ)*
      Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) ≤
        Real.exp (-c'*saddleNu 1 (Real.log M)) := by
    apply (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add]
    congr 1
    dsimp [d,eta]
    ring
  have hsite : ((M-L:ℕ):ℝ)/(2:ℝ)^L ≤ (fullRate M L:ℝ) := by
    rw [fullRate_coe]
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le M L) (by positivity)
  have hbad' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsite (Real.exp_pos I).le)
    (Real.exp_pos (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M))).le
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0<M by omega)
  have hshallow : Real.exp I*((⌈Real.sqrt M⌉₊:ℝ)/(2:ℝ)^L) ≤ (M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
    convert hs' using 1
    rw [fullRate_coe]
    field_simp
  have hc : ((deletedStarts M (M-L) L (paperExcess M L I) (primeCutoff M)).card:ℝ) ≤
      (⌈Real.sqrt M⌉₊:ℝ)+((M-L:ℕ):ℝ)*Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) := by
    rw [deletedStarts_card]
    have h := deleted_card_le M (M-L) L (paperExcess M L I) (primeCutoff M)
    have hh : ((deletedSites M (M-L) L (paperExcess M L I) (primeCutoff M)).card:ℝ) ≤
        (⌈Real.sqrt M⌉₊:ℝ)+(badPivotSites (M-L) L (paperExcess M L I) (primeCutoff M)).card := by exact_mod_cast h
    exact hh.trans (add_le_add_right hbadcard _)
  have hei : 1 ≤ Real.exp I := Real.one_le_exp_iff.mpr hI
  change ((deletedStarts M (M-L) L (paperExcess M L I) (primeCutoff M)).card:ℝ)/(2:ℝ)^L ≤ _
  calc
    _ ≤ ((⌈Real.sqrt M⌉₊:ℝ)+((M-L:ℕ):ℝ)*Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)))/(2:ℝ)^L :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ ≤ Real.exp I*((⌈Real.sqrt M⌉₊:ℝ)+((M-L:ℕ):ℝ)*Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)))/(2:ℝ)^L := by
      gcongr
      exact le_mul_of_one_le_left (by positivity) hei
    _ = Real.exp I*((⌈Real.sqrt M⌉₊:ℝ)/(2:ℝ)^L)+Real.exp I*(((M-L:ℕ):ℝ)/(2:ℝ)^L)*Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) := by ring
    _ ≤ _ := by linarith only [hshallow,hbad'.trans hbad]

end
end PaperC.Prel8.MicroscopicDeletedTarget
