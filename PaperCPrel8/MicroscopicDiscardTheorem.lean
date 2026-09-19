import PaperCPrel8.MicroscopicDiscardRates
import PaperCV282.RareConditioningRates

/-! # Actual discarded-site probability under the paper budget -/
namespace PaperC.Prel8.MicroscopicDiscardTheorem
open MeasureTheory Set PaperC.InfiniteRademacher
open PaperC.Prel8.MicroscopicDiscardRates PaperC.Prel8.MicroscopicActualGeometry
open PaperC.Prel8.MicroscopicPaperBudget PaperC.Prel8.MicroscopicProfileBudget
open PaperC.Prel8.MicroscopicBadPivotCount PaperC.Prel8.MicroscopicDeletedSites
open PaperC.Prel8.IndependentScalarTail
open PaperC.V282.RareConditioningRates PaperC.V282.AllStartSoftPoisson
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.V282.LaishramUniformInput PaperC.V282.PostQuadraticLiterature PaperC.V282.PrimeEulerPNT
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The discarded-site event has the same uniform exponential-plus-power rate as the retained field. -/
theorem deleted_probability_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c c' epsilon : ℝ) (hbetaMin : 0 < betaMin) (hband : betaMin < betaMax)
    (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      ∀ A : Set InfiniteSample, 0 < infiniteRademacherMeasure.real A →
      1 ≤ siteRate M L →
      eventInformation A+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      infiniteRademacherMeasure.real (A ∩ hitEvent L
        (deletedStarts M (M-L) L (paperExcess M L (eventInformation A)) (primeCutoff M))) /
        infiniteRademacherMeasure.real A ≤
          3*Real.exp (-c'*saddleNu 1 (Real.log M))+(M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  let d := (c+c')/2
  let eta := (c-c')/2
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hbeta : 0 < betaMax := hbetaMin.trans hband
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hbetaMin hband (by linarith)
  obtain ⟨Mb,hb⟩ := paper_to_ambient_budget_eventually betaMax c d hbeta (by dsimp [d]; linarith)
  obtain ⟨Md,hd⟩ := conditional_deletion_hard_bound betaMin betaMax (betaMax+1) eta
    hbetaMin hband (by linarith) heta hLS hShorey hPNT hNR
  obtain ⟨Ms,hs⟩ := shallow_budget_rate epsilon hepsilon
  obtain ⟨Mh,hh⟩ := deep_budget_rate (betaMin*Real.log 2/8) c'
    (by have := Real.log_pos (by norm_num : (1:ℝ)<2); positivity) hc'
  refine ⟨max 1 (max Mg (max Mb (max Md (max Ms Mh)))), ?_⟩
  intro M hM L hlo hhi A hA hrate hbudget
  let I := eventInformation A
  have hI : 0 ≤ I := eventInformation_nonneg A hA
  have g := hg M (by omega) L I hlo hhi hI hrate hbudget
  have hambient := (hb M (by omega) L I hhi hrate hbudget).2
  have hlambda : 0 < (fullRate M L:ℝ) := by have := g.ambient_rate; linarith
  have hIV : I ≤ saddleCutoff 1 (Real.log M) := by
    have := Real.log_nonneg g.ambient_rate
    linarith [g.ambient_budget]
  have hd' := hd M (by omega) (M-L) L (paperExcess M L I) hlo hhi (Nat.sub_le M L)
    g.population g.support_short (by have := g.shifted_upper; linarith) A hA
  have hs' := hs M (by omega) I (fullRate M L) hlambda g.ambient_budget
  have hh' := hh M (by omega) I hIV
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
  have hinv := exp_eventInformation A hA
  calc
    _ ≤ _ := hd'
    _ = Real.exp I*((⌈Real.sqrt M⌉₊:ℝ)/(2:ℝ)^L) +
        Real.exp I*(((M-L:ℕ):ℝ)/(2:ℝ)^L)*
          Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) +
        2*(Real.exp I*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M)))) := by
      dsimp only [I]
      rw [hinv]
      ring
    _ ≤ _ := by linarith only [hshallow,hbad'.trans hbad,hh']

/-- The true excess tail on any interior start mask satisfies a uniform second-scale bound. -/
theorem tail_probability_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c c' : ℝ) (hbetaMin : 0 < betaMin) (hband : betaMin < betaMax)
    (hc : 0 < c) (hc' : 0 < c') :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      ∀ A : Set InfiniteSample, 0 < infiniteRademacherMeasure.real A →
      1 ≤ siteRate M L →
      eventInformation A+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc 2 M →
      infiniteRademacherMeasure.real (A ∩ PaperC.Prel8.MicroscopicDiscardBounds.excessTail
        L (paperExcess M L (eventInformation A)) mask) / infiniteRademacherMeasure.real A ≤
          3*Real.exp (-c'*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hbetaMin hband hc
  obtain ⟨Mt,ht⟩ := PaperC.Prel8.MicroscopicDiscardBounds.conditional_tail_bound_eventually
    betaMin (betaMax+1) hbetaMin (by linarith) hLS hShorey hPNT hNR
  obtain ⟨Md,hd⟩ := deep_budget_rate (betaMin*Real.log 2/8) c'
    (by have := Real.log_pos (by norm_num : (1:ℝ)<2); positivity) hc'
  obtain ⟨Mv,hv⟩ := PaperC.V282.SaddlePoissonScales.saddle_exponential_le_eventually
    1 1 c' 1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max 1 (max Mg (max Mt (max Md Mv))), ?_⟩
  intro M hM L hlo hhi A hA hr hb mask hmask
  let I := eventInformation A
  have hI : 0 ≤ I := eventInformation_nonneg A hA
  have g := hg M (by omega) L I hlo hhi hI hr hb
  have hIV : I ≤ saddleCutoff 1 (Real.log M) := by
    have := Real.log_nonneg g.ambient_rate
    linarith [g.ambient_budget]
  have htail := ht M (by omega) L (paperExcess M L I) g.shifted_lower g.shifted_upper mask
    (by intro x hx; have hh := Finset.mem_Icc.mp (hmask hx); exact ⟨hh.1,by omega⟩) A hA
  have hdeep := hd M (by omega) I hIV
  have hexp : Real.exp (-saddleCutoff 1 (Real.log M)) ≤ Real.exp (-c'*saddleNu 1 (Real.log M)) := by
    have hh := hv M (by omega)
    rw [Real.exp_le_one_iff] at hh
    apply Real.exp_le_exp.mpr
    nlinarith
  have hc : (mask.card:ℝ) ≤ M := by
    have h := Finset.card_le_card hmask
    simp only [Nat.card_Icc] at h
    exact_mod_cast (show mask.card ≤ M by omega)
  have hbulk := PaperC.Prel8.MicroscopicInformationCutoff.cutoff_tail_bound I
    (saddleCutoff 1 (Real.log M)) (fullRate M L).coe_nonneg
  have hmaskbulk : Real.exp I*((mask.card:ℝ)/(2:ℝ)^(L+paperExcess M L I+1)) ≤
      Real.exp (-saddleCutoff 1 (Real.log M))/2 := by
    apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hc (by positivity)) (Real.exp_pos I).le).trans
    convert hbulk using 1
    rw [fullRate_coe,show L+paperExcess M L I+1=L+(paperExcess M L I+1) by omega,pow_add]
    unfold paperExcess
    simp only [fullRate_coe]
    ring
  have hinv := exp_eventInformation A hA
  calc
    _ ≤ _ := htail
    _ = Real.exp I*((mask.card:ℝ)/(2:ℝ)^(L+paperExcess M L I+1)) +
        2*(Real.exp I*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M)))) := by
      dsimp only [I]
      rw [hinv]
      ring
    _ ≤ _ := by nlinarith [Real.exp_pos (-c'*saddleNu 1 (Real.log M))]

end
end PaperC.Prel8.MicroscopicDiscardTheorem
