import PaperCPrel8.MicroscopicPaperBudget
import PaperCPrel8.MicroscopicGoodField

/-! # Actual microscopic geometry under the paper's information budget -/
namespace PaperC.Prel8.MicroscopicActualGeometry
open PaperC.Prel8.MicroscopicPaperBudget PaperC.Prel8.MicroscopicProfileBudget
open PaperC.Prel8.MicroscopicInformationCutoff PaperC.Prel8.MicroscopicGoodField
open PaperC.Prel8.ActualSignedPalm
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.V282.AllStartSoftPoisson PaperC.V282.SaddleCutoffAdmissibility
open Filter Topology
noncomputable section

def primeCutoff (M : ℕ) : ℕ := ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊
def sourceCylinder (M L : ℕ) (I : ℝ) : ℕ := 2*M+(L+paperExcess M L I+2)

/-- Every finite side condition used by the retained-field, count and profile bounds. -/
structure GeometryFacts (M L : ℕ) (I betaMin betaMax : ℝ) : Prop where
  length_pos : 1 ≤ L
  interior_end : M-L+1 ≤ M
  ambient_rate : 1 ≤ (fullRate M L:ℝ)
  ambient_budget : I+Real.log (fullRate M L:ℝ) ≤ saddleCutoff 1 (Real.log M)
  shifted_lower : betaMin*Real.log M ≤ (L+paperExcess M L I+2:ℝ)
  shifted_upper : (L+paperExcess M L I+2:ℝ) ≤ (betaMax+1)*Real.log M
  support_short : L+paperExcess M L I+1 ≤ M-L
  population : M ≤ 2*((M-L)+(L+paperExcess M L I+1))
  strong_prime : 2*(L+paperExcess M L I+2) ≤ primeCutoff M
  prime_in_cylinder : primeCutoff M ≤ sourceCylinder M L I
  profile_cylinder : M+(L+paperExcess M L I+1) ≤ sourceCylinder M L I

/-- The true cutoff has adequate length, private primes and an adequate common cylinder. -/
theorem actual_geometry_eventually (betaMin betaMax c : ℝ)
    (hbetaMin : 0 < betaMin) (hband : betaMin < betaMax) (hc : 0 < c) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      GeometryFacts M L I betaMin betaMax := by
  have hbeta : 0 < betaMax := hbetaMin.trans hband
  obtain ⟨Mb,hb⟩ := paper_to_ambient_unmargined betaMax c hbeta hc
  obtain ⟨Ms,hs⟩ := shifted_band_eventually betaMin betaMax 1 (by norm_num)
  obtain ⟨Ml,hl⟩ := logarithmic_length_quarter betaMax hbeta
  obtain ⟨Mq,hq⟩ := logarithmic_length_quarter (betaMax+2) (by linarith)
  obtain ⟨My,hy⟩ := saddleCutoff_nat_admissible_eventually 1 (betaMax+2) (by norm_num) (by linarith)
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Mh,hh⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop (max 1 (2/betaMin))))
  refine ⟨max Mb (max Ms (max Ml (max Mq (max My Mh)))), ?_⟩
  intro M hM L I hlo hhi hI hr hbudget
  obtain ⟨har,hab⟩ := hb M (by omega) L I hhi hr hbudget
  obtain ⟨hslo,hshi⟩ := hs M (by omega) L I (fullRate M L) hlo hhi hI har hab
  have hlogone : 1 ≤ Real.log M := (le_max_left _ _).trans (hh M (by omega))
  have hlogtwo := (div_le_iff₀ hbetaMin).mp ((le_max_right _ _).trans (hh M (by omega)))
  have hLp : 1 ≤ L := by
    have hx : (1:ℝ) ≤ L := by nlinarith
    exact_mod_cast hx
  have hLq := hl M (by omega) L hhi
  let B := L+paperExcess M L I+2
  have hB : (B+1:ℝ) ≤ (betaMax+2)*Real.log M := by
    dsimp only [B]
    push_cast
    change (L:ℝ)+(paperExcess M L I:ℝ)+2 ≤ _ at hshi
    nlinarith
  have hBq := hq M (by omega) B hB
  have hY := hy M (by omega) B hB
  refine ⟨hLp,by omega,har,hab,hslo,hshi,by dsimp [B] at hBq; omega,
    by omega,hY.2.2.1,?_,?_⟩
  · exact hY.2.2.2
  · unfold sourceCylinder
    omega

/-- The actual geometry constructs the retained field's private-pivot geometry. -/
theorem actual_goodGeometry {M L : ℕ} {I betaMin betaMax : ℝ}
    (h : GeometryFacts M L I betaMin betaMax) :
    GoodGeometry (sourceCylinder M L I) (primeCutoff M) L (paperExcess M L I)
      (goodSites M (M-L) L (paperExcess M L I) (primeCutoff M)) := by
  apply goodSites_geometry h.length_pos (by have := h.strong_prime; omega)
    (by have := h.strong_prime; omega)
  unfold sourceCylinder
  omega

end
end PaperC.Prel8.MicroscopicActualGeometry
