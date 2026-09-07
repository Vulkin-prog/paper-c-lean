import PaperCV282.AffineCrossoverPhase
import PaperCV282.CrossoverResolvedLocationTarget

/-! # Physical location mixtures with an effective affine border codimension -/
namespace PaperC.V282.AffineCrossoverLocationTarget

open MeasureTheory Filter Topology BulkPopulation CrossoverLocationGrid
open CrossoverLocationMixture CrossoverLocationProjection CrossoverResolvedLocationTarget
open scoped NNReal ENNReal

noncomputable section

def borderWeight (M L : ℕ) (delta : ℝ) (d : ℕ) : ℝ≥0 :=
  ((2 : ℝ≥0)⁻¹)^d / (((2 : ℝ≥0)⁻¹)^d+bulkRate M L delta)

def bulkWeight (M L : ℕ) (delta : ℝ) (d : ℕ) : ℝ≥0 :=
  bulkRate M L delta / (((2 : ℝ≥0)⁻¹)^d+bulkRate M L delta)

theorem weights_sum (M L : ℕ) (delta : ℝ) (d : ℕ) :
    borderWeight M L delta d+bulkWeight M L delta d=1 := by
  unfold borderWeight bulkWeight
  rw [← add_div,div_self (by positivity : ((2 : ℝ≥0)⁻¹)^d+bulkRate M L delta≠0)]

theorem borderWeight_coe (M L : ℕ) (delta : ℝ) (d : ℕ) :
    (borderWeight M L delta d : ℝ)=
      ((2 : ℝ)⁻¹)^d / (((2 : ℝ)⁻¹)^d+(bulkRate M L delta : ℝ)) := by
  simp only [borderWeight,NNReal.coe_div,NNReal.coe_add,NNReal.coe_pow,NNReal.coe_inv,NNReal.coe_ofNat]

theorem bulkWeight_coe (M L : ℕ) (delta : ℝ) (d : ℕ) :
    (bulkWeight M L delta d : ℝ)=
      (bulkRate M L delta : ℝ) / (((2 : ℝ)⁻¹)^d+(bulkRate M L delta : ℝ)) := by
  simp only [bulkWeight,NNReal.coe_div,NNReal.coe_add,NNReal.coe_pow,NNReal.coe_inv,NNReal.coe_ofNat]

theorem bulkWeight_eq_one_sub (M L : ℕ) (delta : ℝ) (d : ℕ) :
    (bulkWeight M L delta d : ℝ)=1-(borderWeight M L delta d : ℝ) := by
  have h := congrArg ((↑) : ℝ≥0→ℝ) (weights_sum M L delta d)
  simp only [NNReal.coe_add,NNReal.coe_one] at h
  linarith

def physicalTargetLaw (M L : ℕ) (delta : ℝ) (d : ℕ) : ProbabilityMeasure ℝ :=
  mixtureLaw (borderWeight M L delta d) (bulkWeight M L delta d) (weights_sum M L delta d)
    (borderLocationLaw M) (bulkLocationLaw M L delta)

def resolvedTargetLaw (M L : ℕ) (delta : ℝ) (d : ℕ) : ProbabilityMeasure (Bool×ℝ) :=
  resolvedMixture (borderWeight M L delta d) (bulkWeight M L delta d) (weights_sum M L delta d)
    (microscopicLocationLaw L) (bulkLocationLaw M L delta)

/-- The common geometric input uses the true grid and the two actual border scales. -/
theorem target_laws_tendsto_of_weights
    (sizes lengths dimensions : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (a b : ℝ≥0) (hab : a+b=1)
    (ha : Tendsto (fun n => (borderWeight (sizes n) (lengths n) delta (dimensions n) : ℝ)) atTop (𝓝 (a : ℝ)))
    (hb : Tendsto (fun n => (bulkWeight (sizes n) (lengths n) delta (dimensions n) : ℝ)) atTop (𝓝 (b : ℝ))) :
    Tendsto (fun n => physicalTargetLaw (sizes n) (lengths n) delta (dimensions n)) atTop
      (𝓝 (mixtureLaw a b hab zeroLocationLaw unitIntervalLaw)) ∧
    Tendsto (fun n => resolvedTargetLaw (sizes n) (lengths n) delta (dimensions n)) atTop
      (𝓝 (resolvedMixture a b hab zeroLocationLaw unitIntervalLaw)) := by
  have hgrid := bulkLocationLaw_tendsto sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1))
  constructor
  · exact mixtureLaw_tendsto _ _ (fun n => weights_sum _ _ _ _) a b hab _ _ _ _ ha hb
      (borderLocationLaw_tendsto sizes hsizes) hgrid
  · exact resolvedMixture_tendsto _ _ (fun n => weights_sum _ _ _ _) a b hab _ _ _ _ ha hb
      (microscopicLocationLaw_tendsto lengths hlengths) hgrid

theorem target_laws_tendsto
    (sizes lengths dimensions : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (s : ℝ) (hphase : Tendsto (fun n => AffineCrossoverPhase.affinePhase
      (sizes n) (lengths n) (dimensions n)) atTop (𝓝 s)) :
    Tendsto (fun n => physicalTargetLaw (sizes n) (lengths n) delta (dimensions n)) atTop
      (𝓝 (crossoverLimitLaw s)) ∧
    Tendsto (fun n => resolvedTargetLaw (sizes n) (lengths n) delta (dimensions n)) atTop
      (𝓝 (resolvedLimitLaw s)) := by
  obtain ⟨ha,hb⟩ := AffineCrossoverPhase.mixture_weights_tendsto sizes lengths dimensions hsizes
    beta delta hdelta hdeltaOne hupper (hlengths.eventually (eventually_ge_atTop 1)) s hphase
  exact target_laws_tendsto_of_weights sizes lengths dimensions hsizes hlengths beta delta hdelta hdeltaOne
    hupper (phaseBorderWeight s) (phaseBulkWeight s) (phase_weights_sum s)
    (by
      change Tendsto _ atTop (𝓝 (1/(1+(2 : ℝ)^(-s))))
      simpa only [borderWeight_coe] using ha)
    (by
      change Tendsto _ atTop (𝓝 ((2 : ℝ)^(-s)/(1+(2 : ℝ)^(-s))))
      simpa only [bulkWeight_coe] using hb)

theorem target_laws_tendsto_border
    (sizes lengths dimensions : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hphase : Tendsto (fun n => AffineCrossoverPhase.affinePhase
      (sizes n) (lengths n) (dimensions n)) atTop atTop) :
    Tendsto (fun n => physicalTargetLaw (sizes n) (lengths n) delta (dimensions n)) atTop
      (𝓝 zeroLocationLaw) ∧
    Tendsto (fun n => resolvedTargetLaw (sizes n) (lengths n) delta (dimensions n)) atTop
      (𝓝 (labelledLaw false zeroLocationLaw)) := by
  have ha : Tendsto (fun n => (borderWeight (sizes n) (lengths n) delta (dimensions n) : ℝ)) atTop (𝓝 1) := by
    simpa only [borderWeight_coe] using AffineCrossoverPhase.border_weight_tendsto_one_of_phase_atTop
      sizes lengths dimensions hsizes beta delta hdelta hdeltaOne hupper
      (hlengths.eventually (eventually_ge_atTop 1)) hphase
  have hb : Tendsto (fun n => (bulkWeight (sizes n) (lengths n) delta (dimensions n) : ℝ)) atTop (𝓝 0) := by
    simpa only [bulkWeight_eq_one_sub,sub_self] using ha.const_sub 1
  have ht := target_laws_tendsto_of_weights sizes lengths dimensions hsizes hlengths beta delta
    hdelta hdeltaOne hupper 1 0 (by norm_num) ha hb
  have he : mixtureLaw 1 0 (by norm_num) zeroLocationLaw unitIntervalLaw=zeroLocationLaw := by
    apply Subtype.ext
    simp [mixtureLaw]
  have hf : resolvedMixture 1 0 (by norm_num) zeroLocationLaw unitIntervalLaw=labelledLaw false zeroLocationLaw := by
    apply Subtype.ext
    simp [resolvedMixture]
  simpa only [he,hf] using ht

theorem target_laws_tendsto_bulk
    (sizes lengths dimensions : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hphase : Tendsto (fun n => AffineCrossoverPhase.affinePhase
      (sizes n) (lengths n) (dimensions n)) atTop atBot) :
    Tendsto (fun n => physicalTargetLaw (sizes n) (lengths n) delta (dimensions n)) atTop
      (𝓝 unitIntervalLaw) ∧
    Tendsto (fun n => resolvedTargetLaw (sizes n) (lengths n) delta (dimensions n)) atTop
      (𝓝 (labelledLaw true unitIntervalLaw)) := by
  have ha : Tendsto (fun n => (borderWeight (sizes n) (lengths n) delta (dimensions n) : ℝ)) atTop (𝓝 0) := by
    simpa only [borderWeight_coe] using AffineCrossoverPhase.border_weight_tendsto_zero_of_phase_atBot
      sizes lengths dimensions hsizes beta delta hdelta hdeltaOne hupper
      (hlengths.eventually (eventually_ge_atTop 1)) hphase
  have hb : Tendsto (fun n => (bulkWeight (sizes n) (lengths n) delta (dimensions n) : ℝ)) atTop (𝓝 1) := by
    simpa only [bulkWeight_eq_one_sub,sub_zero] using ha.const_sub 1
  have ht := target_laws_tendsto_of_weights sizes lengths dimensions hsizes hlengths beta delta
    hdelta hdeltaOne hupper 0 1 (by norm_num) ha hb
  have he : mixtureLaw 0 1 (by norm_num) zeroLocationLaw unitIntervalLaw=unitIntervalLaw := by
    apply Subtype.ext
    simp [mixtureLaw]
  have hf : resolvedMixture 0 1 (by norm_num) zeroLocationLaw unitIntervalLaw=labelledLaw true unitIntervalLaw := by
    apply Subtype.ext
    simp [resolvedMixture]
  simpa only [he,hf] using ht

end
end PaperC.V282.AffineCrossoverLocationTarget
