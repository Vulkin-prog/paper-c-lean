import PaperCV282.BulkMarkedComparison
import PaperCV282.BulkMarkedGeometry
import PaperCV282.MacroscopicMarkedLedger
import PaperCV282.SaddleMarkTruncation

/-! # Relative signed marked bulk approximation, with the actual full F_Y kernel -/
namespace PaperC.V282.BulkMarkedRates

open Filter Topology BulkMarkedComparison BulkMarkedGeometry BulkMarkedFieldBounds
open MacroscopicMarkedLedger MacroscopicMaskGeometry MacroscopicArithmeticBounds
open HardPoissonRates SaddleParameters SaddleScales SaddleMarkTruncation SaddleCutoffAdmissibility
open PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson FinitePrimeEnvironment

noncomputable section

/-- The complete conditional mean uses the canonical cylinder for the observed prime algebra. -/
def bulkConditionalDistance (M L : ℕ) (delta : ℝ) : ℝ :=
  spatialConditionalDistance (hardCutoff M) (hardCutoff M) (bulkStarts M L delta) L

/-- The intensity multiplies both the exponential and polynomial errors. -/
def bulkRelativeRate (M L : ℕ) (epsilon eta : ℝ) : ℝ :=
  (fullRate M L : ℝ) * (Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) +
    (M : ℝ)^(-(1/(3 : ℝ))+epsilon))

theorem spatialConditionalDistance_eq_canonical {C Y : ℕ} (hYC : Y≤C) (sites : Finset ℕ) (L : ℕ) :
    spatialConditionalDistance C Y sites L = spatialConditionalDistance Y Y sites L :=
  meanAtomDistance_eq_canonical hYC _ _

/-- The ceiling used in the manuscript stays in a common band before the base length is chosen. -/
theorem critical_mark_band_eventually (beta : ℝ) (hbeta : 0<beta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, (L+1 : ℝ)≤beta*Real.log M →
      (L+criticalMarkCutoff M+2 : ℝ)≤(2*beta)*Real.log M := by
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ne,he⟩ := eventually_atTop.1 (criticalMarkCutoff_div_log_tendsto_zero.eventually (gt_mem_nhds hbeta))
  obtain ⟨Np,hp⟩ := eventually_atTop.1 (hlog.eventually (eventually_gt_atTop (0 : ℝ)))
  refine ⟨max Ne Np,?_⟩
  intro M hM L hL
  have hh := (div_lt_iff₀ (hp M (by omega))).mp (he M (by omega))
  linarith

/-- Theorem 7.7: a single threshold precedes the base length, with the rare-intensity cap explicit. -/
theorem theorem_seven_seven (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hdelta : 0<delta) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      (fullRate M L : ℝ)≤1 →
      bulkConditionalDistance M L delta ≤ 67*bulkRelativeRate M L epsilon eta := by
  have hbmax := hbetaMin.trans hbeta
  obtain ⟨Nb,hb⟩ := critical_mark_band_eventually betaMax hbmax
  obtain ⟨Nr,hr⟩ := marked_ledger_hard_rate_eventually hPNT betaMin (2*betaMax) delta epsilon eta
    hbetaMin (by linarith) hdelta hepsilon heta
  obtain ⟨Nt,ht⟩ := complete_tail_cost_le_eventually betaMin (2*betaMax) delta hbetaMin (by linarith) hdelta
  obtain ⟨Na,ha⟩ := saddleCutoff_nat_admissible_eventually 1 (4*betaMax) (by norm_num) (by positivity)
  obtain ⟨Nl,hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  have hnu : Tendsto (fun M : ℕ => saddleNu 1 (Real.log M)) atTop atTop :=
    (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨Nnu,hnu⟩ := eventually_atTop.1 (hnu.eventually (eventually_ge_atTop (0 : ℝ)))
  refine ⟨max 2 (max Nb (max Nr (max Nt (max Na (max Nl Nnu))))),?_⟩
  intro M hM L hlo hhi hrate
  let E := criticalMarkCutoff M
  let C := max (hardCutoff M) (M+L+E+1)
  let sites := bulkStarts M L delta
  have hL : 1≤L := hl M (by omega) L hlo
  have hband : (L+E+2 : ℝ)≤(2*betaMax)*Real.log M := hb M (by omega) L hhi
  have hhi' : ((L+E+2 : ℕ)+1 : ℝ)≤(4*betaMax)*Real.log M := by
    push_cast
    have he : (0 : ℝ)≤E := by positivity
    have hll : (1 : ℝ)≤L := by exact_mod_cast hL
    nlinarith
  have hY : 2*(L+E+2)≤hardCutoff M := (ha M (by omega) (L+E+2) hhi').2.2.1
  have hsites : sites⊆Finset.Icc ⌈(M : ℝ)^delta⌉₊ M := bulkStarts_subset_closed (by omega) hL
  have hsite : ∀x∈sites,2≤x := fun x hx =>
    (Finset.mem_Icc.mp (bulkStarts_subset_Icc (by omega) hL hdelta hx)).1
  have hC : ∀x∈sites,x+L+E+1≤C := by
    intro x hx
    have hh := (Finset.mem_Icc.mp (hsites hx)).2
    exact (by omega : x+L+E+1≤M+L+E+1).trans (le_max_right _ _)
  have h := complete_signed_field_le_ledger hAGG sites hsite hL hC hY
  have hledger := hr M (by omega) L E hlo hband C
    ((by omega : M+L≤M+L+E+1).trans (le_max_right _ _)) sites hsites
  have htail := ht M (by omega) L E hlo hband sites hsites
  have hgeom := mul_le_mul_of_nonneg_left (criticalMarkCutoff_geometric_tail M)
    (by positivity : (0 : ℝ)≤3*(fullRate M L : ℝ))
  have hnu0 := hnu M (by omega)
  have hexp : Real.exp (-saddleCutoff 1 (Real.log M)) ≤
      Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have htail' : ((MaskedArithmeticGeometry.fullDefectMass (L+E+1) sites : ℝ)+2*sites.card)/(2 : ℝ)^(L+E+1) ≤
      3*(fullRate M L : ℝ)*Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) := by
    apply htail.trans
    apply le_trans _ (mul_le_mul_of_nonneg_left hexp (by positivity))
    convert hgeom using 1
    ring
  have hcanon : spatialConditionalDistance C (hardCutoff M) sites L = bulkConditionalDistance M L delta :=
    spatialConditionalDistance_eq_canonical (le_max_left _ _) sites L
  rw [hcanon] at h
  have hs : 0≤Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M))+
      (M : ℝ)^(-(1/(3 : ℝ))+epsilon) := by positivity
  have hl0 : (0 : ℝ)≤(fullRate M L : ℝ) := by positivity
  have hb : (fullRate M L : ℝ)*(1+(fullRate M L : ℝ)) ≤ 2*(fullRate M L : ℝ) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hb hs
  unfold bulkRelativeRate
  have hp : 0≤(M : ℝ)^(-(1/(3 : ℝ))+epsilon) := by positivity
  nlinarith

end
end PaperC.V282.BulkMarkedRates
