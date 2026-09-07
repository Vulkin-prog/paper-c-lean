import PaperCV282.AffineCrossoverTheorem
import PaperCV282.AffineCrossoverDeficit
import PaperCV282.AffineCrossoverFullScale
import PaperCV282.AffineCrossoverMicroscopic

/-! # The printed affine rare tail and microscopic concentration of Theorem 7.10 -/
namespace PaperC.V282.AffineCrossoverRareTheorem

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher Affine
open AffineCrossoverErrorsAffine AffineCrossoverModel AffineCrossoverCylinder AffineCrossoverDeficit
open AffineCrossoverTheorem AffineCrossoverNormalization AffineCrossoverFullScale
open AffineBorderCylinders CrossoverBulkAtoms BulkMarkedGeometry
open RareConditioningRates HardPoissonRates AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput
open SaddleParameters SaddleScales MicroscopicNonvacancy MicroscopicBorderEvents RarePrefixEvents RarePrefixGeometry
open LaishramUniformInput PostQuadraticLiterature ConditionedCountableLaw SharpConditioning
open scoped NNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

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

/-- The actual finite-prefix hit, with the literal rank deficit and full prefix intensity. -/
theorem theorem_seven_ten_rare_tail :
    Tendsto (fun n => hitProbability (conditionedMeasure (affineCylinder (G n) (b n))) (sizes n) (lengths n)/
      ((((2 : ℝ≥0)⁻¹)^borderDeficitAt (G n) (lengths n) : ℝ)+
        (fullRate (sizes n) (lengths n) : ℝ))) atTop (𝓝 1) := by
  have hh := (theorem_seven_ten_zero_cap hAGG hLS hShorey hPNT hNR sizes lengths hsizes hlengths
    beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget).1
  have ha : ∀ᶠ n in atTop,0<conditionalBorderRate (affineCylinder (G n) (b n)) (lengths n) := by
    filter_upwards [hstack] with n hn
    obtain ⟨hLY,hs⟩ := hn
    rw [conditionalBorderRate_eq _ _ hLY hs]
    exact AffineCrossoverCylinder.borderRate_pos _ _
  have ht := hit_full_rate_ratio_tendsto_one
    (fun n=>conditionedMeasure (affineCylinder (G n) (b n))) sizes lengths hsizes beta delta hdelta hdeltaOne
    hupper (hlengths.eventually (eventually_ge_atTop 1)) _ ha hh
  apply ht.congr'
  filter_upwards [hstack] with n hn
  obtain ⟨hLY,hs⟩ := hn
  rw [conditionalBorderRate_eq_deficit _ _ hLY hs]
  simp only [NNReal.coe_pow,NNReal.coe_inv]

/-- All three microscopic conclusions concern the actual affine condition: its mass ratio,
its entire conditional source measure, and the unique-border event. No future neutrality is used. -/
theorem theorem_seven_ten_microscopic :
    let A := fun n=>affineCylinder (G n) (b n)
    let d := fun n=>borderDeficitAt (G n) (lengths n)
    Tendsto (fun n=>(conditionedMeasure (A n)).real (microscopicEvent (lengths n))/
      ((((2 : ℝ≥0)⁻¹)^d n) : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun n=>measureTotalVariation
      (cond infiniteRademacherMeasure (A n∩microscopicEvent (lengths n)))
      (cond infiniteRademacherMeasure (A n∩borderEvent (lengths n)))) atTop (𝓝 0) ∧
    Tendsto (fun n=>(cond infiniteRademacherMeasure (A n∩microscopicEvent (lengths n))).real
      (uniqueBorderEvent (lengths n))) atTop (𝓝 1) := by
  dsimp only
  let A := fun n=>affineCylinder (G n) (b n)
  let mu := fun n=>probabilityConditionedMeasure (A n)
  have hmu : ∀ᶠ n in atTop,mu n=conditionedMeasure (A n) := by
    filter_upwards [hstack] with n hn
    obtain ⟨hLY,hs⟩ := hn
    exact probabilityConditionedMeasure_eq _ (affineCylinder_probability_pos _ _
      (stacked_compatible_implies_compatible _ _ hLY hs))
  have ha : ∀ᶠ n in atTop,0<(mu n).real (borderEvent (lengths n)) := by
    filter_upwards [hmu,hstack] with n hn hs
    obtain ⟨hLY,hs⟩ := hs
    rw [hn]
    change 0<(conditionalBorderRate (A n) (lengths n) : ℝ)
    rw [conditionalBorderRate_eq _ _ hLY hs]
    exact_mod_cast AffineCrossoverCylinder.borderRate_pos (G n) hLY
  obtain ⟨_,hia,_,_,_⟩ := affine_errors_under_rank_budget hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths 0 beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  have hi : Tendsto (fun n=>(mu n).real (interiorEvent (lengths n))/(mu n).real (borderEvent (lengths n)))
      atTop (𝓝 0) := by
    apply hia.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
    rfl
  obtain ⟨hm,ht,hu⟩ := AffineCrossoverMicroscopic.microscopic_localization mu lengths ha hi
  refine ⟨?_,?_,?_⟩
  · apply hm.congr'
    filter_upwards [hmu,hstack] with n hn hs
    obtain ⟨hLY,hs⟩ := hs
    rw [hn]
    change (conditionedMeasure (A n)).real (microscopicEvent (lengths n))/
      (conditionalBorderRate (A n) (lengths n) : ℝ)=_
    rw [conditionalBorderRate_eq_deficit _ _ hLY hs]
    simp only [NNReal.coe_pow,NNReal.coe_inv]
    rfl
  · apply ht.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
    change measureTotalVariation
      (cond (cond infiniteRademacherMeasure (A n)) (microscopicEvent (lengths n)))
      (cond (cond infiniteRademacherMeasure (A n)) (borderEvent (lengths n)))=_
    rw [cond_cond_eq_cond_inter (measurableSet_affineCylinder (G n) (b n)) (measurableSet_microscopicEvent _),
      cond_cond_eq_cond_inter (measurableSet_affineCylinder (G n) (b n)) (measurableSet_borderEvent _)]
  · apply hu.congr'
    filter_upwards [hmu] with n hn
    rw [hn]
    change (cond (cond infiniteRademacherMeasure (A n)) (microscopicEvent (lengths n))).real _=_
    rw [cond_cond_eq_cond_inter (measurableSet_affineCylinder (G n) (b n)) (measurableSet_microscopicEvent _)]

end
end PaperC.V282.AffineCrossoverRareTheorem
