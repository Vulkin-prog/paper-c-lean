import PaperCV282.UnsignedAggregateComparison
import PaperCV282.VariableMeasureWeakTransfer
import PaperCV282.PoissonGaussianLimit

/-!
# The literal source observables in the joint Poisson--Gaussian theorem

The lower coordinates are genuine start counts. The upper coordinates count
exact run lengths on the same sample. Conditional laws use the actual source
restriction, and weak transfer permits this restriction to vary with N.
-/
namespace PaperC.V282.PoissonGaussianSource

open MeasureTheory ProbabilityTheory WithLp Filter
open InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer
open InfiniteExactLengthProbabilityTransfer MarkedDetruncation ExactMarkedModel
open SpatialMarkedSource SpatialMarkedTypes MovingMarkedSource AggregateCoordinateIdentities
open UnsignedAggregateComparison ConditionedCountableLaw AllStartSoftPoisson
open CountableWeakTransfer VariableMeasureWeakTransfer PoissonGaussianTarget PoissonGaussianLimit
open GeometricMarkedConfiguration PoissonThresholdTarget
open scoped Topology NNReal

noncomputable section

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- An exact coefficient identity, before any limiting argument. -/
theorem unsignedAggregateSource_coefficient (N L e : ℕ) (omega : InfiniteSample) :
    unsignedAggregateSource N L omega e=infiniteExactLengthCount N L e omega := by
  change aggregateExcess N (spatialMarkedSource N L omega) e=_
  rw [aggregateExcess_coefficient]
  simp only [spatialMarkedSource_apply,spatialMarkedValue,sum_signedMarkValue]
  have h := (dyadicSiteEquiv N).sum_comp (fun x => exactMarkValue (infiniteValueBit omega) x.val L e)
  change (∑ x : Fin N, exactMarkValue (infiniteValueBit omega) (N+x.val) L e)=_
  calc
    _ = ∑ x : {x : ℕ // x ∈ dyadicBlock N}, exactMarkValue (infiniteValueBit omega) x.val L e := h
    _ = _ := by
      change (∑ x ∈ (dyadicBlock N).attach, exactMarkValue (infiniteValueBit omega) x.val L e)=_
      exact Finset.sum_attach (dyadicBlock N) (fun x => exactMarkValue (infiniteValueBit omega) x L e)

theorem measurable_source_startCount (N L : ℕ) : Measurable (infiniteDyadicStartCount N L) := by
  apply measurable_to_countable'
  intro k
  exact measurableSet_infiniteDyadicStartCountEvent N L k

theorem measurable_source_exactCount (N L e : ℕ) : Measurable (infiniteExactLengthCount N L e) := by
  have h : (fun omega => unsignedAggregateSource N L omega e)=infiniteExactLengthCount N L e :=
    funext (unsignedAggregateSource_coefficient N L e)
  rw [← h]
  exact (measurable_of_countable (fun config : ℕ →₀ ℕ => config e)).comp
    (measurable_unsignedAggregateSource N L)

def actualJointVector (N L J : ℕ) (excess : R → ℕ) (omega : InfiniteSample) :
    WithLp 2 ((EuclideanSpace ℝ (Fin (J+1))) × EuclideanSpace ℝ R) :=
  toLp 2 (toLp 2 (fun j : Fin (J+1) =>
    ((infiniteDyadicStartCount N (L+j.val) omega : ℝ)-(fullRate N L : ℝ)/(2 : ℝ)^j.val)/
      Real.sqrt (fullRate N L)),
    toLp 2 (fun r => (infiniteExactLengthCount N L (excess r) omega : ℝ)))

omit [Fintype R] [DecidableEq R] in
theorem measurable_actualJointVector (N L J : ℕ) (excess : R → ℕ) :
    Measurable (actualJointVector N L J excess) := by
  have hstart (j : Fin (J+1)) := measurable_source_startCount N (L+j.val)
  have hexact (r : R) := measurable_source_exactCount N L (excess r)
  unfold actualJointVector
  fun_prop

omit [Fintype R] [DecidableEq R] in
/-- Run termination identifies all thresholds simultaneously on the actual conditional measure. -/
theorem ae_actualJointVector_eq {N L : ℕ} (hN : 2≤N) (J : ℕ) (excess : R → ℕ)
    (C : Set InfiniteSample) :
    actualJointVector N L J excess =ᵐ[cond infiniteRademacherMeasure C]
      jointThresholdVector (fullRate N L) J excess ∘ unsignedAggregateSource N L := by
  filter_upwards [ae_source_thresholds_eq_startCounts_of_ac hN cond_absolutelyContinuous] with omega homega
  unfold actualJointVector jointThresholdVector normalizedThresholdVector
  apply congrArg (toLp 2)
  apply Prod.ext
  · apply congrArg (toLp 2)
    funext j
    have h := homega j.val
    change ThresholdPathEquivalence.tailCount (unsignedAggregateSource N L omega) j.val=
      infiniteDyadicStartCount N (L+j.val) omega at h
    rw [h]
  · apply congrArg (toLp 2)
    funext r
    rw [unsignedAggregateSource_coefficient]

def conditionalJointLaw (N L J : ℕ) (excess : R → ℕ) (C : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real C) :
    ProbabilityMeasure (WithLp 2 ((EuclideanSpace ℝ (Fin (J+1))) × EuclideanSpace ℝ R)) := by
  letI : IsProbabilityMeasure (cond infiniteRademacherMeasure C) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  exact imageProbabilityLaw (cond infiniteRademacherMeasure C) (actualJointVector N L J excess)
    (measurable_actualJointVector N L J excess)

omit [Fintype R] [DecidableEq R] in
theorem conditionalJointLaw_eq_image {N L : ℕ} (hN : 2≤N) (J : ℕ) (excess : R → ℕ)
    (C : Set InfiniteSample) (hpos : 0 < infiniteRademacherMeasure.real C) :
    (conditionalJointLaw N L J excess C hpos : Measure _) =
      (cond infiniteRademacherMeasure C).map
        (jointThresholdVector (fullRate N L) J excess ∘ unsignedAggregateSource N L) := by
  change (cond infiniteRademacherMeasure C).map (actualJointVector N L J excess)=_
  exact Measure.map_congr (ae_actualJointVector_eq hN J excess C)

omit [DecidableEq R] in
/-- Only this generic transfer lemma takes a vanishing aggregate error as input;
the paper endpoint derives it from the directional arithmetic estimate. -/
theorem source_joint_limit_of_aggregate_tv (sizes lengths : ℕ → ℕ) (J : ℕ)
    (excess : ℕ → R → ℕ) (criticalRates : R → ℝ≥0) (C : ℕ → Set InfiniteSample)
    (hpos : ∀ n, 0 < infiniteRademacherMeasure.real (C n))
    (hsizes : Tendsto sizes atTop atTop)
    (htv : Tendsto (fun n => conditionalUnsignedAggregateDistance (sizes n) (lengths n) (C n)) atTop (𝓝 0))
    (htarget : Tendsto (fun n => jointThresholdLaw (fullRate (sizes n) (lengths n)) J (excess n))
      atTop (𝓝 (poissonGaussianTarget J criticalRates))) :
    Tendsto (fun n => conditionalJointLaw (sizes n) (lengths n) J (excess n) (C n) (hpos n))
      atTop (𝓝 (poissonGaussianTarget J criticalRates)) := by
  letI (n : ℕ) : IsProbabilityMeasure (cond infiniteRademacherMeasure (C n)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (hpos n))
  have h := variable_lattice_weak_transfer (fun _ => ℕ →₀ ℕ)
    (fun n => cond infiniteRademacherMeasure (C n))
    (fun n => configurationMeasure (fullRate (sizes n) (lengths n)))
    (fun n => unsignedAggregateSource (sizes n) (lengths n))
    (fun n => measurable_unsignedAggregateSource (sizes n) (lengths n))
    (fun n => jointThresholdVector (fullRate (sizes n) (lengths n)) J (excess n))
    (poissonGaussianTarget J criticalRates) htv htarget
  apply h.congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop (2 : ℕ))] with n hn
  apply Subtype.ext
  exact (conditionalJointLaw_eq_image hn J (excess n) (C n) (hpos n)).symm

end
end PaperC.V282.PoissonGaussianSource
