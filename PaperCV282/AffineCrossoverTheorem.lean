import PaperCV282.AffineCrossoverErrorsAffine
import PaperCV282.AffineCrossoverMarkedConvergence
import PaperCV282.AffineCrossoverFutureCutoff

/-! # The actual affine-conditioned crossover at every fixed clock cap

All error limits are derived from the rank budget. The zero-cap comparison
requires no neutrality of future primes. Its source is the original infinite
sample conditioned by the intersection of the affine cylinder and a real hit.
-/
namespace PaperC.V282.AffineCrossoverTheorem

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher Affine
open AffineCrossoverErrorsAffine AffineCrossoverModel AffineCrossoverCylinder
open AffineCrossoverNormalization AffineCrossoverMarkedConvergence AffineCrossoverFutureCutoff
open AffineBorderCylinders CrossoverBulkAtoms BulkMarkedGeometry
open RareConditioningRates HardPoissonRates AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput
open SaddleParameters SaddleScales MicroscopicNonvacancy MicroscopicBorderEvents RarePrefixEvents RarePrefixGeometry
open LaishramUniformInput PostQuadraticLiterature ConditionedCountableLaw
open scoped NNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- A probability extension at inadmissible initial indices; all conclusions restore the true conditioning. -/
def probabilityConditionedMeasure (A : Set InfiniteSample) : Measure InfiniteSample :=
  if 0 < infiniteRademacherMeasure.real A then conditionedMeasure A else infiniteRademacherMeasure

instance instProbabilityConditionedMeasure (A : Set InfiniteSample) :
    IsProbabilityMeasure (probabilityConditionedMeasure A) := by
  unfold probabilityConditionedMeasure
  split_ifs with h
  · exact conditionedMeasure_probability A h
  · infer_instance

theorem probabilityConditionedMeasure_eq (A : Set InfiniteSample)
    (h : 0 < infiniteRademacherMeasure.real A) : probabilityConditionedMeasure A=conditionedMeasure A := by
  simp only [probabilityConditionedMeasure,if_pos h]

theorem probabilityConditionedMeasure_absolutelyContinuous (A : Set InfiniteSample) :
    probabilityConditionedMeasure A ≪ infiniteRademacherMeasure := by
  unfold probabilityConditionedMeasure
  split_ifs
  · exact cond_absolutelyContinuous
  · exact Measure.AbsolutelyContinuous.rfl

variable (hAGG : ProcessAGGStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta c : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1) (hc : 0<c)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (W : ℕ→Type*) [∀ n,AddCommGroup (W n)] [∀ n,Module F₂ (W n)]
    (G : ∀ n,SampleSpace (hardCutoff (sizes n))→ₗ[F₂]W n) (b : ∀ n,W n)
    (hstack : ∀ᶠ n in atTop,∃ hLY : lengths n≤hardCutoff (sizes n),
      Compatible ((G n).prod (borderProjection hLY)) (b n,0))
    (hbudget : ∀ᶠ n in atTop,cylinderInformation (G n)≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n)))

include hAGG hLS hShorey hPNT hNR hsizes hlengths hbeta hdelta hdeltaOne hc hupper hrare hstack hbudget

/-- Actual rare mass, ordinary marked location, and absence of an interior source after the hit. -/
theorem theorem_seven_ten_zero_cap :
    let A := fun n => affineCylinder (G n) (b n)
    let alpha := fun n => conditionalBorderRate (A n) (lengths n)
    Tendsto (fun n => hitProbability (conditionedMeasure (A n)) (sizes n) (lengths n)/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1) ∧
    Tendsto (fun n => cappedDistance (conditionedMeasure (A n)) (sizes n) (lengths n) 0 delta (alpha n))
      atTop (𝓝 0) ∧
    Tendsto (fun n => (cond infiniteRademacherMeasure (A n∩hitEvent (sizes n) (lengths n))).real
      (interiorEvent (lengths n))) atTop (𝓝 0) := by
  dsimp only
  let A := fun n => affineCylinder (G n) (b n)
  let mu := fun n => probabilityConditionedMeasure (A n)
  let alpha := fun n => conditionalBorderRate (A n) (lengths n)
  have habs : ∀ n,mu n ≪ infiniteRademacherMeasure := fun n => probabilityConditionedMeasure_absolutelyContinuous (A n)
  have hmu : ∀ᶠ n in atTop,mu n=conditionedMeasure (A n) := by
    filter_upwards [hstack] with n hn
    obtain ⟨hLY,hs⟩ := hn
    exact probabilityConditionedMeasure_eq _ (affineCylinder_probability_pos _ _
      (stacked_compatible_implies_compatible _ _ hLY hs))
  have hM := hsizes.eventually (eventually_ge_atTop 2)
  have hL := hlengths.eventually (eventually_ge_atTop 1)
  have hLM := RarePrefixMass.logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper
  have hne := CrossoverRareScaleProbabilities.bulk_nonempty_eventually sizes lengths hsizes beta delta
    hdelta hdeltaOne hupper hL
  have hb := CrossoverRareScale.bulk_rate_tendsto_zero sizes lengths hsizes beta delta hdelta hdeltaOne hupper hL hrare
  have ha : ∀ᶠ n in atTop,0<alpha n := by
    filter_upwards [hstack] with n hn
    obtain ⟨hLY,hs⟩ := hn
    dsimp [alpha,A]
    rw [conditionalBorderRate_eq _ _ hLY hs]
    exact AffineCrossoverCylinder.borderRate_pos _ _
  have heq : ∀ᶠ n in atTop,(mu n).real (borderEvent (lengths n))=(alpha n : ℝ) :=
    hmu.mono fun n hn => by rw [hn];rfl
  obtain ⟨_,_,hi,hm,hd⟩ := affine_errors_under_rank_budget hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths 0 beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  have hi' : Tendsto (fun n=>(mu n).real (interiorEvent (lengths n))/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0) := by
    apply hi.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
    rfl
  have hm' : Tendsto (fun n=>(mu n).real (middleEvent (sizes n) (lengths n) delta)/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0) := by
    apply hm.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
    rfl
  have hd' : Tendsto (fun n=>jointDistance (mu n) (sizes n) (lengths n) 0 delta/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0) := by
    apply hd.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
    rfl
  have he : Tendsto (fun n=>((mu n).real (interiorEvent (lengths n))+
      (mu n).real (middleEvent (sizes n) (lengths n) delta))/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0) := by
    simpa only [add_div,add_zero] using hi'.add hm'
  have hh := hit_probability_ratio_tendsto_one mu sizes lengths delta alpha habs hM hL hLM hdelta ha heq 0 he hd' hb
  have hcap := cappedDistance_zero_tendsto_zero mu sizes lengths delta alpha habs hM hL hLM hdelta hne
    ha heq he hd' hb
  refine ⟨?_,?_,?_⟩
  · apply hh.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
  · apply hcap.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
  · have ht := conditional_interior_tendsto_zero mu sizes lengths delta alpha ha hh hi'
    apply ht.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
    change (cond (cond infiniteRademacherMeasure (A n)) (hitEvent (sizes n) (lengths n))).real _ = _
    rw [cond_cond_eq_cond_inter (measurableSet_affineCylinder (G n) (b n)) (measurableSet_hitEvent _ _)]

/-- Every fixed capped clock is genuinely geometric under eventual finite future neutrality. -/
theorem theorem_seven_ten_fixed_cap
    (hneutral : ∀ K,∀ᶠ n in atTop,FutureNeutralAt (G n) (lengths n) K) (K : ℕ) :
    let A := fun n => affineCylinder (G n) (b n)
    let alpha := fun n => conditionalBorderRate (A n) (lengths n)
    Tendsto (fun n => cappedDistance (conditionedMeasure (A n)) (sizes n) (lengths n) K delta (alpha n))
      atTop (𝓝 0) := by
  dsimp only
  let A := fun n => affineCylinder (G n) (b n)
  let mu := fun n => probabilityConditionedMeasure (A n)
  let alpha := fun n => conditionalBorderRate (A n) (lengths n)
  have habs : ∀ n,mu n ≪ infiniteRademacherMeasure := fun n => probabilityConditionedMeasure_absolutelyContinuous (A n)
  have hmu : ∀ᶠ n in atTop,mu n=conditionedMeasure (A n) := by
    filter_upwards [hstack] with n hn
    obtain ⟨hLY,hs⟩ := hn
    exact probabilityConditionedMeasure_eq _ (affineCylinder_probability_pos _ _
      (stacked_compatible_implies_compatible _ _ hLY hs))
  have hM := hsizes.eventually (eventually_ge_atTop 2)
  have hL := hlengths.eventually (eventually_ge_atTop 1)
  have hLM := RarePrefixMass.logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper
  have hne := CrossoverRareScaleProbabilities.bulk_nonempty_eventually sizes lengths hsizes beta delta
    hdelta hdeltaOne hupper hL
  have hb := CrossoverRareScale.bulk_rate_tendsto_zero sizes lengths hsizes beta delta hdelta hdeltaOne hupper hL hrare
  have ha : ∀ᶠ n in atTop,0<alpha n := by
    filter_upwards [hstack] with n hn
    obtain ⟨hLY,hs⟩ := hn
    dsimp [alpha,A]
    rw [conditionalBorderRate_eq _ _ hLY hs]
    exact AffineCrossoverCylinder.borderRate_pos _ _
  have heq : ∀ᶠ n in atTop,(mu n).real (borderEvent (lengths n))=(alpha n : ℝ) :=
    hmu.mono fun n hn => by rw [hn];rfl
  obtain ⟨_,_,hi,hm,hd⟩ := affine_errors_under_rank_budget hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths K beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  have hi' : Tendsto (fun n=>(mu n).real (interiorEvent (lengths n))/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0) := by
    apply hi.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
    rfl
  have hm' : Tendsto (fun n=>(mu n).real (middleEvent (sizes n) (lengths n) delta)/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0) := by
    apply hm.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
    rfl
  have hd' : Tendsto (fun n=>jointDistance (mu n) (sizes n) (lengths n) K delta/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0) := by
    apply hd.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
    rfl
  have he : Tendsto (fun n=>((mu n).real (interiorEvent (lengths n))+
      (mu n).real (middleEvent (sizes n) (lengths n) delta))/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0) := by
    simpa only [add_div,add_zero] using hi'.add hm'
  have hclock := capped_clock_law_eventually (fun n=>hardCutoff (sizes n)) lengths G b hstack hneutral K
  have hclock' : ∀ᶠ n in atTop,(cond (mu n) (borderEvent (lengths n))).map
      (CrossoverPrimeClockStable.actualClockRecord (lengths n) K)=
      (geometricMeasure GeometricClusterTarget.halfSuccess).map (fun j => (true,min j K)) := by
    filter_upwards [hmu,hclock] with n hn hc'
    rw [hn]
    exact hc'
  have ht := cappedDistance_tendsto_zero mu sizes lengths delta alpha habs hM hL hLM hdelta hne
    ha heq K hclock' he hd' hb
  apply ht.congr'
  filter_upwards [hmu] with n hn
  rw [hn]

end
end PaperC.V282.AffineCrossoverTheorem
