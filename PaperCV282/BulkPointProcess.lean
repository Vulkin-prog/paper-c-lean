import PaperCV282.BulkMicroscopicRecord
import PaperCV282.SpatialPointEmbedding
import PaperCV282.SharpConditioningDiscrete

/-! # The bulk fields at their actual spatial locations x/M

The point measures retain integer multiplicities, all excesses and both
signs. Their comparison is a pushforward of the established complete
configuration comparison; the target law is the already constructed
independent Poisson configuration, at the displayed physical locations.
-/
namespace PaperC.V282.BulkPointProcess

open MeasureTheory ProbabilityTheory Filter Topology PointMeasureSpace
open InfiniteRademacher InfiniteConditionalWords InfiniteCylinderTransfer
open BulkMarkedTypes BulkMarkedSource BulkMarkedTarget BulkMarkedComparison BulkMarkedGeometry
open BulkMarkedAggregation BulkMarkedRates BulkMarkedConvergence BulkStartFieldComparison BulkMicroscopicRecord
open SharpConditioning SharpConditioningDiscrete InfiniteMassCoupling ConditionedCountableLaw
open CountablePrimeEventTransfer ConditionalStartProbability SectionThirteenFiniteBound
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling
open ConditionalAGGAverage PoissonFieldMeasure AllStartSoftPoisson HardPoissonRates PrimeEulerPNT ProcessAGGInput
open scoped BigOperators

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def markedPosition (M : ℕ) (sites : Finset ℕ) (j : SpatialMarkedIndex sites) : ℝ×(ℕ×F₂) :=
  ((j.1.val : ℝ)/M,j.2)

def markedPointEmbedding (M : ℕ) (sites : Finset ℕ) (config : SpatialMarkedConfig sites) :
    PointMeasure (ℝ×(ℕ×F₂)) := config.sum (fun j n => n • pointDirac (markedPosition M sites j))

def startPointEmbedding (M : ℕ) (sites : Finset ℕ) (k : {x // x∈sites}→ℕ) : PointMeasure ℝ :=
  ∑ x : {x // x∈sites}, k x • pointDirac ((x.val : ℝ)/M)

/-- The explicit source point measure, with positions, excesses and signs intact. -/
def markedPointSource (M L : ℕ) (delta : ℝ) : InfiniteSample→PointMeasure (ℝ×(ℕ×F₂)) :=
  markedPointEmbedding M (bulkStarts M L delta) ∘ spatialMarkedSource (bulkStarts M L delta) L

def startPointSource (M L : ℕ) (delta : ℝ) : InfiniteSample→PointMeasure ℝ :=
  startPointEmbedding M (bulkStarts M L delta) ∘ startField (bulkStarts M L delta) L

def markedPointTarget (M L : ℕ) (delta : ℝ) : Measure (PointMeasure (ℝ×(ℕ×F₂))) :=
  (spatialTargetMeasure (bulkStarts M L delta) L).map (markedPointEmbedding M (bulkStarts M L delta))

def startPointTarget (M L : ℕ) (delta : ℝ) : Measure (PointMeasure ℝ) :=
  (fieldMeasure (startFieldRates (bulkStarts M L delta) L)).map (startPointEmbedding M (bulkStarts M L delta))

theorem markedPosition_mem_unitInterval {M : ℕ} (hM : 0<M) {sites : Finset ℕ}
    (hsites : sites⊆Finset.Icc 2 M) (j : SpatialMarkedIndex sites) :
    (markedPosition M sites j).1∈Set.Icc (0 : ℝ) 1 := by
  have hj := Finset.mem_Icc.mp (hsites j.1.property)
  have hp : (0 : ℝ)<M := by exact_mod_cast hM
  exact ⟨div_nonneg (by positivity) hp.le,(div_le_one hp).mpr (by exact_mod_cast hj.2)⟩

/-- The mean compares actual conditional image measures on each full prime atom. -/
def mappedConditionalMean {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (C Y : ℕ) (f : InfiniteSample→α) (nu : Measure α) (embed : α→β) : ℝ :=
  uniformAverage (fun sigma : SmallSample C Y =>
    measureTotalVariation ((cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).map (embed ∘ f))
      (nu.map embed))

theorem mappedConditionalMean_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] (C Y : ℕ)
    (f : InfiniteSample→α) (hf : Measurable f) (nu : Measure α) [IsProbabilityMeasure nu]
    (embed : α→β) (he : Measurable embed) :
    mappedConditionalMean C Y f nu embed≤meanAtomDistance C Y f (observableLaw nu id) := by
  apply finiteUniformAverage_mono
  intro sigma
  let mu := cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)
  letI instProbabilityConditionalAtom : IsProbabilityMeasure mu :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _
      (ExactMarkedInfinite.signed_conditioning_atom_real_pos C Y sigma))
  letI instProbabilityImage : IsProbabilityMeasure (mu.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have h := measureTotalVariation_map_le (mu.map f) nu he
  rw [Measure.map_map he hf,measureTotalVariation_eq_mass (mu.map f) nu] at h
  have hs : observableLaw (mu.map f) id = conditionalObservableLaw infiniteRademacherMeasure
      (infiniteSmallPrimeAtom C Y sigma) f := by
    funext a
    exact (observableLaw_eq_map mu hf a).symm
  rw [hs] at h
  exact h

theorem mappedConditionalMean_nonneg {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (C Y : ℕ) (f : InfiniteSample→α) (hf : Measurable f) (nu : Measure α) [IsProbabilityMeasure nu]
    (embed : α→β) (he : Measurable embed) : 0≤mappedConditionalMean C Y f nu embed := by
  have hp (sigma : SmallSample C Y) :
      0≤measureTotalVariation ((cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).map (embed ∘ f))
        (nu.map embed) := by
    let mu := cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)
    letI instProbabilityConditionalAtom : IsProbabilityMeasure mu :=
      cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _
        (ExactMarkedInfinite.signed_conditioning_atom_real_pos C Y sigma))
    letI instProbabilitySourceImage : IsProbabilityMeasure (mu.map (embed ∘ f)) :=
      Measure.isProbabilityMeasure_map (he.comp hf).aemeasurable
    letI instProbabilityTargetImage : IsProbabilityMeasure (nu.map embed) :=
      Measure.isProbabilityMeasure_map he.aemeasurable
    exact SharpConditioning.measureTotalVariation_nonneg _ _
  unfold mappedConditionalMean uniformAverage
  exact div_nonneg (Finset.sum_nonneg (fun sigma _ => hp sigma)) (by positivity)

def markedPointConditionalDistance (M L : ℕ) (delta : ℝ) : ℝ :=
  mappedConditionalMean (hardCutoff M) (hardCutoff M) (spatialMarkedSource (bulkStarts M L delta) L)
    (spatialTargetMeasure (bulkStarts M L delta) L) (markedPointEmbedding M (bulkStarts M L delta))

def startPointConditionalDistance (M L : ℕ) (delta : ℝ) : ℝ :=
  mappedConditionalMean (hardCutoff M) (hardCutoff M) (startField (bulkStarts M L delta) L)
    (fieldMeasure (startFieldRates (bulkStarts M L delta) L)) (startPointEmbedding M (bulkStarts M L delta))

theorem markedPointConditionalDistance_le (M L : ℕ) (delta : ℝ) :
    markedPointConditionalDistance M L delta≤bulkConditionalDistance M L delta :=
  mappedConditionalMean_le _ _ _ (measurable_spatialMarkedSource _ _) _ _ (measurable_of_countable _)

theorem startPointConditionalDistance_le (M L : ℕ) (delta : ℝ) :
    startPointConditionalDistance M L delta≤bulkStartConditionalDistance M L delta := by
  have h := mappedConditionalMean_le (hardCutoff M) (hardCutoff M) _ (measurable_startField (bulkStarts M L delta) L)
    (fieldMeasure (startFieldRates (bulkStarts M L delta) L)) (startPointEmbedding M (bulkStarts M L delta))
    (measurable_of_countable _)
  have ht : observableLaw (fieldMeasure (startFieldRates (bulkStarts M L delta) L)) id =
      poissonFieldMass (startFieldRates (bulkStarts M L delta) L) := funext (fieldMeasure_real_singleton _)
  rw [ht] at h
  exact h

/-- Equation (7.15) also holds for the point measure at x/M, with exactly the same constant. -/
theorem equation_seven_fifteen_spatial (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hdelta : 0<delta) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀M≥Mzero, ∀L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M → (fullRate M L : ℝ)≤1 →
      markedPointConditionalDistance M L delta≤67*bulkRelativeRate M L epsilon eta := by
  obtain ⟨Mzero,hzero⟩ := theorem_seven_seven hAGG hPNT betaMin betaMax delta epsilon eta
    hbetaMin hbeta hdelta hepsilon heta
  exact ⟨Mzero,fun M hM L hlo hhi hr => (markedPointConditionalDistance_le M L delta).trans
    (hzero M hM L hlo hhi hr)⟩

/-- The signed point-process error is o(lambda) on the real continuum of spatial positions. -/
theorem marked_point_relative_convergence (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (L : ℕ→ℕ) (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta)
    (hupper : ∀ᶠ M in atTop,(L M : ℝ)≤beta*Real.log M)
    (hrare : Tendsto (fun M => (fullRate M (L M) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun M => markedPointConditionalDistance M (L M) delta/(fullRate M (L M) : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun M => div_nonneg
    (mappedConditionalMean_nonneg _ _ _ (measurable_spatialMarkedSource _ _) _ _ (measurable_of_countable _))
    (by positivity))
    (fun M => div_le_div_of_nonneg_right (markedPointConditionalDistance_le M (L M) delta) (by positivity))
    (signed_relative_convergence hAGG hPNT L beta delta hbeta hdelta hupper hrare)

/-- Equation (7.16) for the actual start point measure, not only its count vector. -/
theorem equation_seven_sixteen_spatial (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (L : ℕ→ℕ) (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta)
    (hupper : ∀ᶠ M in atTop,(L M : ℝ)≤beta*Real.log M)
    (hrare : Tendsto (fun M => (fullRate M (L M) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun M => startPointConditionalDistance M (L M) delta/(fullRate M (L M) : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun M => div_nonneg
    (mappedConditionalMean_nonneg _ _ _ (measurable_startField _ _) _ _ (measurable_of_countable _))
    (by positivity))
    (fun M => div_le_div_of_nonneg_right (startPointConditionalDistance_le M (L M) delta) (by positivity))
    (equation_seven_sixteen hAGG hPNT L beta delta hbeta hdelta hupper hrare)

/-- The recorded microscopic field and the bulk point measure share their true probability space. -/
def microscopicPointJointDistance (M L : ℕ) (delta : ℝ) : ℝ :=
  measureTotalVariation
    (infiniteRademacherMeasure.map (fun omega =>
      (MesoscopicStability.microscopicRecord L 0 omega,startPointSource M L delta omega)))
    ((infiniteRademacherMeasure.map (MesoscopicStability.microscopicRecord L 0)).prod (startPointTarget M L delta))

theorem microscopicPointJointDistance_le (M L : ℕ) (delta : ℝ) :
    microscopicPointJointDistance M L delta≤microscopicJointDistance M L delta := by
  let record := MesoscopicStability.microscopicRecord L 0
  let f := startField (bulkStarts M L delta) L
  let embed := startPointEmbedding M (bulkStarts M L delta)
  let nu := fieldMeasure (startFieldRates (bulkStarts M L delta) L)
  have hr : Measurable record := MesoscopicStability.measurable_microscopicRecord _ _
  have hf : Measurable f := measurable_startField _ _
  have he : Measurable embed := measurable_of_countable _
  letI instProbabilityRecord : IsProbabilityMeasure (infiniteRademacherMeasure.map record) :=
    Measure.isProbabilityMeasure_map hr.aemeasurable
  letI instProbabilityJoint : IsProbabilityMeasure (infiniteRademacherMeasure.map (fun omega => (record omega,f omega))) :=
    Measure.isProbabilityMeasure_map (hr.prodMk hf).aemeasurable
  have h := measureTotalVariation_map_le
    (infiniteRademacherMeasure.map (fun omega => (record omega,f omega)))
    ((infiniteRademacherMeasure.map record).prod nu) (measurable_id.prodMap he)
  rw [Measure.map_map (measurable_id.prodMap he) (hr.prodMk hf),
    ← Measure.map_prod_map _ _ measurable_id he,Measure.map_id] at h
  exact h

theorem microscopicPointJointDistance_nonneg (M L : ℕ) (delta : ℝ) :
    0≤microscopicPointJointDistance M L delta := by
  have hr := MesoscopicStability.measurable_microscopicRecord L 0
  have hf : Measurable (startPointSource M L delta) :=
    (measurable_of_countable _).comp (measurable_startField _ _)
  letI instProbabilityRecord : IsProbabilityMeasure (infiniteRademacherMeasure.map (MesoscopicStability.microscopicRecord L 0)) :=
    Measure.isProbabilityMeasure_map hr.aemeasurable
  letI instProbabilityJoint : IsProbabilityMeasure (infiniteRademacherMeasure.map (fun omega =>
      (MesoscopicStability.microscopicRecord L 0 omega,startPointSource M L delta omega))) :=
    Measure.isProbabilityMeasure_map (hr.prodMk hf).aemeasurable
  letI instProbabilityPointTarget : IsProbabilityMeasure (startPointTarget M L delta) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  exact SharpConditioning.measureTotalVariation_nonneg _ _

/-- The stronger first equality in (7.17), for the true joint spatial law. -/
theorem equation_seven_seventeen_spatial_relative (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (L : ℕ→ℕ) (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta)
    (hupper : ∀ᶠ M in atTop,(L M : ℝ)≤beta*Real.log M)
    (hrare : Tendsto (fun M => (fullRate M (L M) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun M => microscopicPointJointDistance M (L M) delta/(fullRate M (L M) : ℝ)) atTop (𝓝 0) :=
  squeeze_zero (fun M => div_nonneg (microscopicPointJointDistance_nonneg M (L M) delta) (by positivity))
    (fun M => div_le_div_of_nonneg_right (microscopicPointJointDistance_le M (L M) delta) (by positivity))
    (equation_seven_seventeen hAGG hPNT L beta delta hbeta hdelta hupper hrare)

/-- Equation (7.17) at the actual spatial locations, with the printed q_L+lambda denominator. -/
theorem equation_seven_seventeen_spatial (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (L : ℕ→ℕ) (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta)
    (hupper : ∀ᶠ M in atTop,(L M : ℝ)≤beta*Real.log M)
    (hrare : Tendsto (fun M => (fullRate M (L M) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun M => microscopicPointJointDistance M (L M) delta/
      (MicroscopicNonvacancy.microscopicProbability (L M)+(fullRate M (L M) : ℝ))) atTop (𝓝 0) := by
  have hp (M : ℕ) : 0≤MicroscopicNonvacancy.microscopicProbability (L M)+(fullRate M (L M) : ℝ) :=
    add_nonneg (MicroscopicNonvacancy.microscopicProbability_pos _).le (by positivity)
  exact squeeze_zero (fun M => div_nonneg (microscopicPointJointDistance_nonneg M (L M) delta) (hp M))
    (fun M => div_le_div_of_nonneg_right (microscopicPointJointDistance_le M (L M) delta) (hp M))
    (equation_seven_seventeen_total_scale hAGG hPNT L beta delta hbeta hdelta hupper hrare)

end
end PaperC.V282.BulkPointProcess
