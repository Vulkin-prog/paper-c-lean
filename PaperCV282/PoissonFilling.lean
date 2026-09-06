import PaperCV282.DirectionalSteinComparison
import PaperCV282.InfiniteMassCoupling
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Actual independent Poisson filling of a finite random vector

The finite mixture is identified with the observable on the genuine product
probability space. No retained site, or positive retained rate, is required.
-/
namespace PaperC.V282.PoissonFilling

open MeasureTheory ProbabilityTheory DirectionalSteinComparison ArratiaGoldsteinGordonInput
open IndependentThinning SteinFiniteExpectation PoissonFieldMeasure InfiniteMassCoupling
open FiniteFieldTotalVariation
open scoped BigOperators ENNReal NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

variable {Ω ι κ : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def finitePMFProbability (mu : FinitePMF Ω) : PMF Ω :=
  PMF.ofFintype (fun omega => ENNReal.ofReal (mu.prob omega)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun omega _ => mu.nonneg omega),mu.sum_prob]
    simp)

def filledLaw (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (fill : κ → ℝ≥0) (k : κ → ℕ) : ℝ :=
  finitePMFExpectation mu (fun omega =>
    observableLaw (fieldMeasure fill) (fun z => z+typedSum X kind Finset.univ omega) k)

omit [DecidableEq ι] in
theorem filledLaw_nonneg (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (fill : κ → ℝ≥0) (k : κ → ℕ) : 0≤filledLaw mu X kind fill k :=
  expectation_nonneg mu (fun _ => observableLaw_nonneg _ _ _)

omit [DecidableEq ι] in
theorem hasSum_filledLaw (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (fill : κ → ℝ≥0) : HasSum (filledLaw mu X kind fill) 1 := by
  have h := hasSum_sum (s := Finset.univ) (fun omega _ =>
    (hasSum_observableLaw (fieldMeasure fill)
      (measurable_of_countable (fun z => z+typedSum X kind Finset.univ omega))).mul_left (mu.prob omega))
  unfold filledLaw finitePMFExpectation
  simpa only [mul_one,mu.sum_prob] using h

omit [DecidableEq ι] in
theorem restricted_filledLaw_eq (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (fill : κ → ℝ≥0) (A : Set (κ → ℕ)) :
    (∑' k, if k∈A then filledLaw mu X kind fill k else 0)=
      finitePMFExpectation mu (fun omega =>
        (fieldMeasure fill).real {z | z+typedSum X kind Finset.univ omega∈A}) := by
  have hs (omega : Ω) : Summable (fun k => if k∈A then
      mu.prob omega*observableLaw (fieldMeasure fill)
        (fun z => z+typedSum X kind Finset.univ omega) k else 0) :=
    ((hasSum_observableLaw (fieldMeasure fill) (measurable_of_countable _)).summable.mul_left _).indicator _
  simp only [filledLaw,finitePMFExpectation]
  have heq (k : κ → ℕ) :
      (if k∈A then ∑ omega, mu.prob omega*observableLaw (fieldMeasure fill)
        (fun z => z+typedSum X kind Finset.univ omega) k else 0)=
      ∑ omega, if k∈A then mu.prob omega*observableLaw (fieldMeasure fill)
        (fun z => z+typedSum X kind Finset.univ omega) k else 0 := by
    by_cases h : k∈A <;> simp [h]
  simp_rw [heq]
  rw [Summable.tsum_finsetSum (fun omega _ => hs omega)]
  apply Finset.sum_congr rfl
  intro omega homega
  have hm (k : κ → ℕ) : (if k∈A then mu.prob omega*observableLaw (fieldMeasure fill)
      (fun z => z+typedSum X kind Finset.univ omega) k else 0)=
      mu.prob omega*(if k∈A then observableLaw (fieldMeasure fill)
        (fun z => z+typedSum X kind Finset.univ omega) k else 0) := by
    by_cases h : k∈A <;> simp [h]
  simp_rw [hm]
  rw [tsum_mul_left,restricted_observableLaw_eq_event (fieldMeasure fill) (measurable_of_countable _)]
  rfl

section SourceMeasure
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

def fillingMeasure (mu : FinitePMF Ω) (fill : κ → ℝ≥0) : Measure (Ω × (κ → ℕ)) :=
  (finitePMFProbability mu).toMeasure.prod (fieldMeasure fill)

instance instIsProbabilityMeasureFilling (mu : FinitePMF Ω) (fill : κ → ℝ≥0) :
    IsProbabilityMeasure (fillingMeasure mu fill) := by
  unfold fillingMeasure
  infer_instance

theorem integral_finitePMFProbability (mu : FinitePMF Ω) (f : Ω → ℝ) :
    (∫ omega, f omega ∂(finitePMFProbability mu).toMeasure)=finitePMFExpectation mu f := by
  rw [PMF.integral_eq_sum]
  simp only [finitePMFProbability,PMF.ofFintype_apply,ENNReal.toReal_ofReal (mu.nonneg _),smul_eq_mul,
    finitePMFExpectation]

omit [DecidableEq κ] [MeasurableSingletonClass Ω] in
/-- The two coordinates of the filling source are genuinely independent. -/
theorem independent_source_filling (mu : FinitePMF Ω) (fill : κ → ℝ≥0) :
    IndepFun (Prod.fst : Ω × (κ → ℕ) → Ω) Prod.snd (fillingMeasure mu fill) := by
  exact indepFun_prod measurable_id measurable_id

omit [DecidableEq ι] in
/-- The mixture is the actual law on the independent product source. -/
theorem filledLaw_eq_product (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (fill : κ → ℝ≥0) :
    filledLaw mu X kind fill = observableLaw (fillingMeasure mu fill)
      (fun pair => pair.2+typedSum X kind Finset.univ pair.1) := by
  funext k
  let F : Ω × (κ → ℕ) → ℝ := fun pair =>
    if pair.2+typedSum X kind Finset.univ pair.1=k then 1 else 0
  have hF : Integrable F (fillingMeasure mu fill) :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun pair => by dsimp [F];split_ifs <;> norm_num))
  have heq : observableLaw (fillingMeasure mu fill)
      (fun pair => pair.2+typedSum X kind Finset.univ pair.1) k =
      ∫ pair, F pair ∂fillingMeasure mu fill := by
    simpa only [observableLaw,F,Set.indicator_apply,Pi.one_apply,Set.mem_setOf_eq] using
      (integral_indicator_one (μ := fillingMeasure mu fill) (s := {pair | pair.2+typedSum X kind Finset.univ pair.1=k})
        (Set.to_countable _).measurableSet).symm
  rw [heq,fillingMeasure,integral_prod _ hF,integral_finitePMFProbability]
  apply expectation_congr
  intro omega
  simpa only [observableLaw,F,Set.indicator_apply,Pi.one_apply,Set.mem_setOf_eq] using
    (integral_indicator_one (μ := fieldMeasure fill) (s := {z | z+typedSum X kind Finset.univ omega=k})
      (Set.to_countable _).measurableSet).symm

end SourceMeasure
end
end PaperC.V282.PoissonFilling
