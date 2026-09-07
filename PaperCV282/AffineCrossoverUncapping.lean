import PaperCV282.AffineCrossoverModel
import PaperCV282.CrossoverUncapping

/-! # Removing the prime-clock cap under a genuine conditional clock law

The source measure can be an affine conditioning of the infinite model.
The geometric survival is a true conditional probability; its later proof
uses the separate future-neutrality condition.  No source independence is
assumed in this finite coupling argument.
-/
namespace PaperC.V282.AffineCrossoverUncapping

open MeasureTheory ProbabilityTheory Set InfiniteRademacher CrossoverMarkedModel
open CrossoverMarkedCandidate CrossoverMarkedTarget CrossoverPrimeClockStable
open CrossoverSourceCoupling CrossoverConditioningTools CrossoverUncapping CrossoverBulkOnePoint
open RarePrefixGeometry MicroscopicBorderEvents PrimeClockDistribution SharpConditioning
open ConditionedCountableLaw GeometricClusterTarget
open scoped NNReal ENNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

theorem hit_probability_pos (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    {M L : ℕ} (hLM : L≤M) (hb : 0<mu.real (borderEvent L)) :
    0<mu.real (hitEvent M L) := by
  apply hb.trans_le
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  rw [hitEvent_eq_union hLM]
  exact subset_union_left

theorem clock_survival_of_actualRecord (mu : Measure InfiniteSample) (L J : ℕ)
    (hclock : (cond mu (borderEvent L)).map (actualClockRecord L J)=
      (geometricMeasure halfSuccess).map (fun n => (true,min n J))) :
    (cond mu (borderEvent L)).real {omega | J≤primeOvershoot L omega}=1/(2 : ℝ)^J := by
  have h := congrArg (fun nu : Measure (Bool×ℕ) => nu.real {z | J≤z.2}) hclock
  rw [map_measureReal_apply (measurable_actualClockRecord L J) (Set.to_countable _).measurableSet,
    map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet] at h
  have he : actualClockRecord L J ⁻¹' {z | J≤z.2}={omega | J≤primeOvershoot L omega} := by
    ext omega
    simp [actualClockRecord]
  have hf : (fun n : ℕ => (true,min n J)) ⁻¹' {z : Bool×ℕ | J≤z.2}=Set.Ici J := by
    ext n
    simp
  rw [he,hf] at h
  exact h.trans (CrossoverPrimeClockLaw.geometric_survival J)

theorem sourceLaw_cap_tv_le (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    {M L : ℕ} (delta : ℝ) (hLM : L≤M) (hb : 0<mu.real (borderEvent L)) (K : ℕ)
    (htail : (cond mu (borderEvent L)).real {omega | K+1≤primeOvershoot L omega}=1/(2 : ℝ)^(K+1)) :
    measureTotalVariation (AffineCrossoverModel.sourceLaw mu M L delta)
      ((AffineCrossoverModel.sourceLaw mu M L delta).map (capBorder K))≤1/(2 : ℝ)^(K+1) := by
  let H := hitEvent M L
  let E := borderEvent L∩{omega | K+1≤primeOvershoot L omega}
  have hp : 0<mu.real H := hit_probability_pos mu hLM hb
  letI _instProbabilityHit : IsProbabilityMeasure (cond mu H) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hp)
  have hBH : mu.real (borderEvent L)≤mu.real H := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    rw [show H=hitEvent M L from rfl,hitEvent_eq_union hLM]
    exact subset_union_left
  have hmass : mu.real E=(1/(2 : ℝ)^(K+1))*mu.real (borderEvent L) := by
    rw [cond_real_apply mu _ (measurableSet_borderEvent L)] at htail
    exact (div_eq_iff (ne_of_gt hb)).mp htail
  have hc := map_tv_le_of_ae_eq_off (cond mu H) E
    (measurable_gamma M L delta) (measurable_capGamma M L K delta)
    (Filter.Eventually.of_forall (gamma_cap_eq_off_prime_tail hLM))
  unfold AffineCrossoverModel.sourceLaw
  rw [Measure.map_map (measurable_of_countable _) (measurable_gamma M L delta)]
  apply hc.trans
  rw [cond_real_apply _ H (measurableSet_hitEvent M L)]
  apply (div_le_div_of_nonneg_right (measureReal_mono inter_subset_right) hp.le).trans
  rw [hmass]
  apply (div_le_iff₀ hp).mpr
  exact mul_le_mul_of_nonneg_left hBH (by positivity)

theorem sourceLaw_cap_tv_le_of_actualRecord (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    {M L : ℕ} (delta : ℝ) (hLM : L≤M) (hb : 0<mu.real (borderEvent L)) (K : ℕ)
    (hclock : (cond mu (borderEvent L)).map (actualClockRecord L (K+1))=
      (geometricMeasure halfSuccess).map (fun n => (true,min n (K+1)))) :
    measureTotalVariation (AffineCrossoverModel.sourceLaw mu M L delta)
      ((AffineCrossoverModel.sourceLaw mu M L delta).map (capBorder K))≤1/(2 : ℝ)^(K+1) :=
  sourceLaw_cap_tv_le mu delta hLM hb K (clock_survival_of_actualRecord mu L (K+1) hclock)

theorem mixed_border_tail_mass (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) (alpha : ℝ≥0) :
    (AffineCrossoverTarget.mixedLaw sites hs L alpha).real (borderTail K)=
      (AffineCrossoverTarget.borderWeight sites L alpha : ℝ)/(2 : ℝ)^(K+1) := by
  have hm : (bulkLaw sites hs).real (borderTail K)=0 := by
    rw [bulkLaw,map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    have he : bulkLabel sites ⁻¹' borderTail K=∅ := by
      ext j
      simp [borderTail,borderLabel,bulkLabel]
    rw [he,measureReal_empty]
  rw [AffineCrossoverTarget.mixedLaw_real,border_tail_mass,hm,mul_zero,add_zero]
  ring

theorem mixedLaw_cap_tv_le (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) (alpha : ℝ≥0) :
    measureTotalVariation (AffineCrossoverTarget.mixedLaw sites hs L alpha)
      ((AffineCrossoverTarget.mixedLaw sites hs L alpha).map (capBorder K))≤1/(2 : ℝ)^(K+1) := by
  have hc := map_tv_le_of_ae_eq_off (AffineCrossoverTarget.mixedLaw sites hs L alpha)
    (borderTail K) measurable_id (measurable_of_countable (capBorder K))
    (Filter.Eventually.of_forall fun r hr => (capBorder_eq_off_tail K r hr).symm)
  rw [Measure.map_id,mixed_border_tail_mass] at hc
  apply hc.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hw := congrArg (fun a : ℝ≥0 => (a : ℝ)) (AffineCrossoverTarget.weights_sum sites hs L alpha)
  push_cast at hw
  linarith [show (0 : ℝ)≤(AffineCrossoverTarget.bulkWeight sites L alpha : ℝ) by positivity]

theorem targetLaw_cap_tv_le (M L K : ℕ) (delta : ℝ) (alpha : ℝ≥0) :
    measureTotalVariation (AffineCrossoverTarget.targetLaw M L delta alpha)
      ((AffineCrossoverTarget.targetLaw M L delta alpha).map (capBorder K))≤1/(2 : ℝ)^(K+1) := by
  unfold AffineCrossoverTarget.targetLaw
  split_ifs with hs
  · exact mixedLaw_cap_tv_le _ hs L K alpha
  · exact borderLaw_cap_tv_le K

theorem actualDistance_le_capped_add_tail (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    {M L : ℕ} (delta : ℝ) (alpha : ℝ≥0) (hLM : L≤M) (hb : 0<mu.real (borderEvent L)) (K : ℕ)
    (hclock : (cond mu (borderEvent L)).map (actualClockRecord L (K+1))=
      (geometricMeasure halfSuccess).map (fun n => (true,min n (K+1)))) :
    AffineCrossoverModel.actualDistance mu M L delta alpha≤
      AffineCrossoverModel.cappedDistance mu M L K delta alpha+2/(2 : ℝ)^(K+1) := by
  letI _instProbabilitySource := AffineCrossoverModel.sourceLaw_probability mu M L delta
    (hit_probability_pos mu hLM hb)
  letI _instProbabilityCappedSource := Measure.isProbabilityMeasure_map
    (μ := AffineCrossoverModel.sourceLaw mu M L delta) (measurable_of_countable (capBorder K)).aemeasurable
  letI _instProbabilityCappedTarget := Measure.isProbabilityMeasure_map
    (μ := AffineCrossoverTarget.targetLaw M L delta alpha) (measurable_of_countable (capBorder K)).aemeasurable
  have h1 := variation_triangle (AffineCrossoverModel.sourceLaw mu M L delta)
    ((AffineCrossoverModel.sourceLaw mu M L delta).map (capBorder K)) (AffineCrossoverTarget.targetLaw M L delta alpha)
  have h2 := variation_triangle ((AffineCrossoverModel.sourceLaw mu M L delta).map (capBorder K))
    ((AffineCrossoverTarget.targetLaw M L delta alpha).map (capBorder K)) (AffineCrossoverTarget.targetLaw M L delta alpha)
  have hs := sourceLaw_cap_tv_le_of_actualRecord mu delta hLM hb K hclock
  have ht := targetLaw_cap_tv_le M L K delta alpha
  rw [measureTotalVariation_comm (AffineCrossoverTarget.targetLaw M L delta alpha)] at ht
  unfold AffineCrossoverModel.actualDistance AffineCrossoverModel.cappedDistance
  simp only [div_eq_mul_inv,one_mul] at hs ht ⊢
  linarith only [h1,h2,hs,ht]

end
end PaperC.V282.AffineCrossoverUncapping
