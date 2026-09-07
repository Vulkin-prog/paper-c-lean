import PaperCV282.MacroTransportModel
import PaperCV282.BulkMarkedRates

/-! # Complete retained marked comparison without an intensity cap -/
namespace PaperC.V282.MacroTransportHardRetained

open MeasureTheory ProbabilityTheory Filter Topology BulkMarkedComparison BulkMarkedGeometry BulkMarkedFieldBounds
open MacroscopicMarkedLedger MacroscopicMaskGeometry MacroscopicArithmeticBounds BulkMarkedRates
open HardPoissonRates SaddleParameters SaddleScales SaddleMarkTruncation SaddleCutoffAdmissibility
open PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson FinitePrimeEnvironment
open InfiniteRademacher InfiniteCylinderTransfer BulkMarkedSource BulkMarkedTarget BulkMarkedTypes
open PrimeEnvironmentStableLift SharpConditioning InfiniteMassCoupling
open scoped BigOperators NNReal ENNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem retained_mean_hard_bound_eventually (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hdelta : 0<delta) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      bulkConditionalDistance M L delta ≤ 35*(fullRate M L : ℝ)*(1+(fullRate M L : ℝ))*
        (Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) +
          (M : ℝ)^(-(1/(3 : ℝ))+epsilon)) := by
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
  intro M hM L hlo hhi
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
  have hp : 0≤(M : ℝ)^(-(1/(3 : ℝ))+epsilon) := by positivity
  have htailFinal : 3*(fullRate M L : ℝ)*Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) ≤
      3*(fullRate M L : ℝ)*(1+(fullRate M L : ℝ))*
        (Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M))+
          (M : ℝ)^(-(1/(3 : ℝ))+epsilon)) := by
    have hl : 3*(fullRate M L : ℝ)≤3*(fullRate M L : ℝ)*(1+(fullRate M L : ℝ)) := by nlinarith
    exact mul_le_mul hl (by linarith) (Real.exp_nonneg _) (by positivity)
  linarith

/-- The same complete retained field conditioned on any positive event in the actual F_Y. -/
theorem retained_event_hard_bound_eventually (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hdelta : 0<delta) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      measureTotalVariation ((cond infiniteRademacherMeasure A).map
        (spatialMarkedSource (bulkStarts M L delta) L)) (spatialTargetMeasure (bulkStarts M L delta) L) ≤
      (35*(fullRate M L : ℝ)*(1+(fullRate M L : ℝ))*
        (Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) +
          (M : ℝ)^(-(1/(3 : ℝ))+epsilon)))/infiniteRademacherMeasure.real A := by
  obtain ⟨Mzero,hMzero⟩ := retained_mean_hard_bound_eventually hAGG hPNT betaMin betaMax delta epsilon eta
    hbetaMin hbeta hdelta hepsilon heta
  refine ⟨Mzero,?_⟩
  intro M hM L hlo hhi A hA hpos
  have hm := hMzero M hM L hlo hhi
  exact (fullFY_conditioned_stable_product_lift (le_refl (hardCutoff M))
    (spatialMarkedSource (bulkStarts M L delta) L) (measurable_spatialMarkedSource _ _)
    (spatialTargetMeasure (bulkStarts M L delta) L) _ hm
    (fun _ : InfiniteSample => ()) measurable_const A hA hpos).1

end
end PaperC.V282.MacroTransportHardRetained
