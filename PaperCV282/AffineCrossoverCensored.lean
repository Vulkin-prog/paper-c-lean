import PaperCV282.AffineCrossoverLocationTransfer
import PaperCV282.CrossoverCensored

/-! # Right-censoring the actual affine-conditioned crossover record

The source is conditioned on the real intersection of the affine event and
non-vacancy. Only the integer bulk excess is clamped at the finite-word end;
the site, source label, sign, and boundary clock are retained. The target
remains the same complete, uncensored affine mixture.
-/
namespace PaperC.V282.AffineCrossoverCensored

open MeasureTheory ProbabilityTheory InfiniteRademacher CrossoverMarkedModel CrossoverMarkedTarget
open CrossoverBulkAtoms CrossoverRightCensor CrossoverCensored CrossoverSourceCoupling
open AffineCrossoverModel AffineCrossoverLocationTransfer BulkMarkedGeometry SharpConditioning
open RarePrefixGeometry CrossoverResolvedLocationSource CrossoverConditioningTools
open scoped NNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Censoring preserves the joint integer location and source label. -/
theorem censorRecord_recordInteger (M L : ℕ) (r : Record) :
    recordInteger (censorRecord M L r)=recordInteger r := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

/-- Censoring changes at most 1/card(sites) of the target mass, for every affine boundary weight. -/
theorem mixedLaw_censor_tv_le (M L : ℕ) (sites : Finset ℕ) (hs : sites.Nonempty)
    (hsites : ∀x∈sites,x≤M-L+1) (alpha : ℝ≥0) :
    measureTotalVariation ((AffineCrossoverTarget.mixedLaw sites hs L alpha).map (censorRecord M L))
      (AffineCrossoverTarget.mixedLaw sites hs L alpha)≤1/(sites.card : ℝ) := by
  letI _instProbabilityCensoredMixed := Measure.isProbabilityMeasure_map
    (μ := AffineCrossoverTarget.mixedLaw sites hs L alpha) (measurable_of_countable (censorRecord M L)).aemeasurable
  letI _instProbabilityCensoredBulk := Measure.isProbabilityMeasure_map
    (μ := bulkLaw sites hs) (measurable_of_countable (censorRecord M L)).aemeasurable
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro S hS
  have hb : borderLaw.real (censorRecord M L ⁻¹' S)=borderLaw.real S := by
    rw [← map_measureReal_apply (measurable_of_countable _) hS,borderLaw_censor]
  have hd := (discrepancy_le ((bulkLaw sites hs).map (censorRecord M L)) (bulkLaw sites hs) S hS).trans
    (bulkLaw_censor_tv_le M L sites hs hsites)
  rw [map_measureReal_apply (measurable_of_countable _) hS] at hd
  rw [map_measureReal_apply (measurable_of_countable _) hS,
    AffineCrossoverTarget.mixedLaw_real,AffineCrossoverTarget.mixedLaw_real,hb]
  have he : (AffineCrossoverTarget.borderWeight sites L alpha : ℝ)*borderLaw.real S+
      (AffineCrossoverTarget.bulkWeight sites L alpha : ℝ)*(bulkLaw sites hs).real (censorRecord M L ⁻¹' S)-
      ((AffineCrossoverTarget.borderWeight sites L alpha : ℝ)*borderLaw.real S+
        (AffineCrossoverTarget.bulkWeight sites L alpha : ℝ)*(bulkLaw sites hs).real S)=
      (AffineCrossoverTarget.bulkWeight sites L alpha : ℝ)*
        ((bulkLaw sites hs).real (censorRecord M L ⁻¹' S)-(bulkLaw sites hs).real S) := by ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0≤(AffineCrossoverTarget.bulkWeight sites L alpha : ℝ))]
  have hw : (AffineCrossoverTarget.bulkWeight sites L alpha : ℝ)≤1 := by
    have hh := congrArg (fun x : ℝ≥0 => (x : ℝ)) (AffineCrossoverTarget.weights_sum sites hs L alpha)
    push_cast at hh
    have ha : 0≤(AffineCrossoverTarget.borderWeight sites L alpha : ℝ) := by positivity
    linarith
  exact (mul_le_mul_of_nonneg_left hd (by positivity)).trans
    (mul_le_of_le_one_left (by positivity) hw)

/-- Literal law of the censored true record under A intersected with the hit event. -/
def censoredSourceLaw (M L : ℕ) (delta : ℝ) (A : Set InfiniteSample) : Measure Record :=
  (cond infiniteRademacherMeasure (A∩hitEvent M L)).map (censorRecord M L ∘ gamma M L delta)

theorem censoredSourceLaw_eq (M L : ℕ) (delta : ℝ) {A : Set InfiniteSample} (hA : MeasurableSet A) :
    censoredSourceLaw M L delta A=
      (sourceLaw (conditionedMeasure A) M L delta).map (censorRecord M L) := by
  rw [AffineCrossoverModel.sourceLaw_conditioned A hA,
    Measure.map_map (measurable_of_countable _) (measurable_gamma M L delta)]
  rfl

def censoredDistance (M L : ℕ) (delta : ℝ) (A : Set InfiniteSample) (alpha : ℝ≥0) : ℝ :=
  measureTotalVariation (censoredSourceLaw M L delta A) (AffineCrossoverTarget.targetLaw M L delta alpha)

/-- The finite censoring cost is independent of the rank and information of A. -/
theorem censoredDistance_le {M L : ℕ} (delta : ℝ) (alpha : ℝ≥0) {A : Set InfiniteSample}
    (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L))
    (hs : (bulkStarts M L delta).Nonempty) :
    censoredDistance M L delta A alpha≤
      actualDistance (conditionedMeasure A) M L delta alpha+1/((bulkStarts M L delta).card : ℝ) := by
  letI _instProbabilityGamma := AffineCrossoverLocationTransfer.sourceLaw_probability delta hA hpos
  letI _instProbabilityCensoredGamma := Measure.isProbabilityMeasure_map
    (μ := sourceLaw (conditionedMeasure A) M L delta) (measurable_of_countable (censorRecord M L)).aemeasurable
  letI _instProbabilityCensoredTarget := Measure.isProbabilityMeasure_map
    (μ := AffineCrossoverTarget.targetLaw M L delta alpha) (measurable_of_countable (censorRecord M L)).aemeasurable
  rw [censoredDistance,censoredSourceLaw_eq M L delta hA]
  have htri := variation_triangle ((sourceLaw (conditionedMeasure A) M L delta).map (censorRecord M L))
    ((AffineCrossoverTarget.targetLaw M L delta alpha).map (censorRecord M L))
    (AffineCrossoverTarget.targetLaw M L delta alpha)
  have hmap := measureTotalVariation_map_le (sourceLaw (conditionedMeasure A) M L delta)
    (AffineCrossoverTarget.targetLaw M L delta alpha) (measurable_of_countable (censorRecord M L))
  have htarget : measureTotalVariation
      ((AffineCrossoverTarget.targetLaw M L delta alpha).map (censorRecord M L))
      (AffineCrossoverTarget.targetLaw M L delta alpha)≤1/((bulkStarts M L delta).card : ℝ) := by
    rw [AffineCrossoverTarget.targetLaw_eq alpha hs]
    exact mixedLaw_censor_tv_le M L _ hs (fun x hx=>(mem_bulkStarts M L x delta).mp hx |>.2) alpha
  exact htri.trans (add_le_add hmap htarget)

end
end PaperC.V282.AffineCrossoverCensored
