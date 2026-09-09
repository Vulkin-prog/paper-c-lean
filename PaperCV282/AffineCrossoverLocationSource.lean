import PaperCV282.CrossoverResolvedLocationSource

/-! # True first-location laws under an additional event

The source measure is conditioned on the actual intersection `A ∩ hitEvent`.
The default probability law is used only when that intersection has zero mass.
-/
namespace PaperC.V282.AffineCrossoverLocationSource

open MeasureTheory ProbabilityTheory InfiniteRademacher RarePrefixGeometry
open CountableWeakTransfer SharpConditioning SharpConditioningDiscrete ConditionedCountableLaw
open scoped NNReal ENNReal

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def firstStartLaw (M L : ℕ) (A : Set InfiniteSample) : ProbabilityMeasure ℕ :=
  if hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L) then
    letI _instProbabilityConditional : IsProbabilityMeasure
        (cond infiniteRademacherMeasure (A∩hitEvent M L)) :=
      cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
    imageProbabilityLaw (cond infiniteRademacherMeasure (A∩hitEvent M L))
      (firstStart M L) (measurable_firstStart M L)
  else ⟨Measure.dirac 0,inferInstance⟩

def firstLocationLaw (M L : ℕ) (A : Set InfiniteSample) : ProbabilityMeasure ℝ :=
  imageProbabilityLaw (firstStartLaw M L A : Measure ℕ)
    (fun x : ℕ => (x : ℝ)/M) (measurable_of_countable _)

def resolvedIntegerLaw (M L : ℕ) (A : Set InfiniteSample) : ProbabilityMeasure (Bool×ℕ) :=
  imageProbabilityLaw (firstStartLaw M L A : Measure ℕ)
    (CrossoverResolvedLocationSource.resolvedInteger L) (measurable_of_countable _)

def resolvedSourceLaw (M L : ℕ) (A : Set InfiniteSample) : ProbabilityMeasure (Bool×ℝ) :=
  imageProbabilityLaw (resolvedIntegerLaw M L A : Measure (Bool×ℕ))
    (CrossoverResolvedLocationSource.resolvedPosition M L) (measurable_of_countable _)

def conditionalInteriorProbability (M L : ℕ) (A : Set InfiniteSample) : ℝ :=
  (cond infiniteRademacherMeasure (A∩hitEvent M L)).real (MicroscopicNonvacancy.interiorEvent L)

theorem firstStartLaw_eq {M L : ℕ} {A : Set InfiniteSample}
    (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) :
    (firstStartLaw M L A : Measure ℕ)=
      (cond infiniteRademacherMeasure (A∩hitEvent M L)).map (firstStart M L) := by
  letI instProbabilityConditional : IsProbabilityMeasure
      (cond infiniteRademacherMeasure (A∩hitEvent M L)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have he : firstStartLaw M L A =
      imageProbabilityLaw (cond infiniteRademacherMeasure (A∩hitEvent M L))
        (firstStart M L) (measurable_firstStart M L) := dif_pos hpos
  exact congrArg (fun nu : ProbabilityMeasure ℕ => (nu : Measure ℕ)) he

theorem firstLocationLaw_eq {M L : ℕ} {A : Set InfiniteSample}
    (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) :
    (firstLocationLaw M L A : Measure ℝ)=
      (cond infiniteRademacherMeasure (A∩hitEvent M L)).map
        (fun omega => (firstStart M L omega : ℝ)/M) := by
  change (firstStartLaw M L A : Measure ℕ).map (fun x : ℕ => (x : ℝ)/M)=_
  rw [firstStartLaw_eq hpos,Measure.map_map (measurable_of_countable _) (measurable_firstStart M L)]
  rfl

theorem resolvedIntegerLaw_eq {M L : ℕ} {A : Set InfiniteSample}
    (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) :
    (resolvedIntegerLaw M L A : Measure (Bool×ℕ))=
      (cond infiniteRademacherMeasure (A∩hitEvent M L)).map
        (CrossoverResolvedLocationSource.resolvedInteger L ∘ firstStart M L) := by
  change (firstStartLaw M L A : Measure ℕ).map (CrossoverResolvedLocationSource.resolvedInteger L)=_
  rw [firstStartLaw_eq hpos,Measure.map_map (measurable_of_countable _) (measurable_firstStart M L)]

theorem resolvedSourceLaw_eq {M L : ℕ} {A : Set InfiniteSample}
    (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) :
    (resolvedSourceLaw M L A : Measure (Bool×ℝ))=
      (cond infiniteRademacherMeasure (A∩hitEvent M L)).map
        (CrossoverResolvedLocationSource.resolvedFirstPosition M L) := by
  change (resolvedIntegerLaw M L A : Measure (Bool×ℕ)).map
    (CrossoverResolvedLocationSource.resolvedPosition M L)=_
  rw [resolvedIntegerLaw_eq hpos,Measure.map_map (measurable_of_countable _)
    ((measurable_of_countable _).comp (measurable_firstStart M L))]
  rfl

theorem conditioned_hit_eq_inter (M L : ℕ) {A : Set InfiniteSample} (hA : MeasurableSet A) :
    cond (cond infiniteRademacherMeasure A) (hitEvent M L)=
      cond infiniteRademacherMeasure (A∩hitEvent M L) :=
  cond_cond_eq_cond_inter hA (measurableSet_hitEvent M L) infiniteRademacherMeasure

theorem conditionalInteriorProbability_nonneg (M L : ℕ) (A : Set InfiniteSample) :
    0≤conditionalInteriorProbability M L A := measureReal_nonneg

end
end PaperC.V282.AffineCrossoverLocationSource
