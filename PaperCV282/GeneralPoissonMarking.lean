import PaperCV282.CompoundPoissonMarking

/-! # Joint Poisson marking for an arbitrary measurable mark space

The actual source is a Poisson count, independent of a sequence of iid marks.
Disjoint finite categories retain their entire joint independent Poisson law.
-/
namespace PaperC.V282.GeneralPoissonMarking

open MeasureTheory ProbabilityTheory CompoundPoissonTransform PoissonFieldMeasure
open scoped BigOperators NNReal ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X]

def markSequenceMeasure (mu : Measure X) [IsProbabilityMeasure mu] : Measure (ℕ → X) :=
  Measure.infinitePi (fun _ : ℕ => mu)

instance instProbabilityMarkSequence (mu : Measure X) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (markSequenceMeasure mu) := by
  unfold markSequenceMeasure
  infer_instance

def markSampleMeasure (rate : ℝ≥0) (mu : Measure X) [IsProbabilityMeasure mu] :
    Measure (ℕ × (ℕ → X)) :=
  (poissonMeasure rate).prod (markSequenceMeasure mu)

instance instProbabilityMarkSample (rate : ℝ≥0) (mu : Measure X)
    [IsProbabilityMeasure mu] : IsProbabilityMeasure (markSampleMeasure rate mu) := by
  unfold markSampleMeasure
  infer_instance

theorem independent_marks (mu : Measure X) [IsProbabilityMeasure mu] :
    iIndepFun (fun i (marks : ℕ → X) => marks i) (markSequenceMeasure mu) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

theorem hasLaw_mark_coordinate (mu : Measure X) [IsProbabilityMeasure mu] (i : ℕ) :
    HasLaw (fun marks : ℕ → X => marks i) mu (markSequenceMeasure mu) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => mu) i).hasLaw

theorem integral_fixed_mark_product (mu : Measure X) [IsProbabilityMeasure mu]
    (f : X → ℂ) (hfmeas : Measurable f) (n : ℕ) :
    (∫ marks, ∏ i ∈ Finset.range n, f (marks i) ∂markSequenceMeasure mu) =
      (∫ h, f h ∂mu) ^ n := by
  have hdep : iIndepFun (fun i : ℕ => fun marks : ℕ → X => f (marks i))
      (markSequenceMeasure mu) :=
    iIndepFun_infinitePi (fun _ => hfmeas)
  have hn := hdep.precomp (fun i j (h : (i : ℕ) = (j : ℕ)) => Fin.ext h)
    (g := fun i : Fin n => i.val)
  have hp := hn.integral_fun_prod_eq_prod_integral
    (fun i => (hfmeas.comp (measurable_pi_apply i.val)).aestronglyMeasurable)
  have hcoord (i : Fin n) :
      (∫ marks : ℕ → X, f (marks i.val) ∂markSequenceMeasure mu) = ∫ h, f h ∂mu :=
    (hasLaw_mark_coordinate mu i.val).integral_comp hfmeas.aestronglyMeasurable
  simp_rw [hcoord] at hp
  calc
    _ = ∫ marks : ℕ → X, ∏ i : Fin n, f (marks i.val) ∂markSequenceMeasure mu := by
      congr 1
      funext marks
      exact (Fin.prod_univ_eq_prod_range (fun i => f (marks i)) n).symm
    _ = _ := by simpa using hp

theorem measurable_stopped_mark_product (f : X → ℂ) (hfmeas : Measurable f) :
    Measurable (fun sample : ℕ × (ℕ → X) => ∏ i ∈ Finset.range sample.1, f (sample.2 i)) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun marks : ℕ → X => ∏ i ∈ Finset.range n, f (marks i))
  exact Finset.measurable_prod _ (fun i _ =>
    hfmeas.comp (measurable_pi_apply i))

theorem stopped_mark_product_transform (rate : ℝ≥0) (mu : Measure X)
    [IsProbabilityMeasure mu] (f : X → ℂ) (hfmeas : Measurable f) (hf : ∀ h, ‖f h‖ ≤ 1) :
    (∫ sample, ∏ i ∈ Finset.range sample.1, f (sample.2 i) ∂markSampleMeasure rate mu) =
      Complex.exp ((rate : ℂ) * ((∫ h, f h ∂mu) - 1)) := by
  have hint : Integrable
      (fun sample : ℕ × (ℕ → X) => ∏ i ∈ Finset.range sample.1, f (sample.2 i))
      (markSampleMeasure rate mu) := by
    refine ⟨(measurable_stopped_mark_product f hfmeas).aestronglyMeasurable, ?_⟩
    apply HasFiniteIntegral.of_bounded (C := 1)
    exact Filter.Eventually.of_forall fun sample => by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hf (sample.2 i))
  rw [markSampleMeasure, integral_prod _ hint]
  simp_rw [integral_fixed_mark_product mu f hfmeas]
  exact integral_poisson_complex_powers _ _

def categoryCounts {I : Type*} [DecidableEq I] (category : X → Option I)
    (sample : ℕ × (ℕ → X)) (i : I) : ℕ :=
  ∑ j ∈ Finset.range sample.1, if category (sample.2 j) = some i then 1 else 0

theorem measurable_categoryCounts {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (category : X → Option I) (hcmeas : Measurable category) : Measurable (categoryCounts category) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun marks : ℕ → X => ∑ j ∈ Finset.range n,
    if category (marks j) = some i then 1 else 0)
  exact Finset.measurable_sum _ (fun j _ =>
    ((measurable_of_countable (fun h : Option I => if h = some i then (1 : ℕ) else 0)).comp
      hcmeas).comp (measurable_pi_apply j))

def categoryFactor {I : Type*} (category : X → Option I) (z : I → ℂ) (h : X) : ℂ :=
  (category h).elim 1 z

omit [MeasurableSpace X] in
theorem category_count_product {I : Type*} [Fintype I] [DecidableEq I]
    (category : X → Option I) (z : I → ℂ) (sample : ℕ × (ℕ → X)) :
    (∏ i, z i ^ categoryCounts category sample i) =
      ∏ j ∈ Finset.range sample.1, categoryFactor category z (sample.2 j) := by
  simp only [categoryCounts, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  cases hc : category (sample.2 j) with
  | none => simp [categoryFactor, hc]
  | some i => simp [categoryFactor, hc, apply_ite]

omit [MeasurableSpace X] in
theorem categoryFactor_norm_le {I : Type*} (category : X → Option I) (z : I → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (h : X) : ‖categoryFactor category z h‖ ≤ 1 := by
  cases hc : category h with
  | none => simp [categoryFactor, hc]
  | some i => simpa [categoryFactor, hc] using hz i

theorem integral_categoryFactor {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (mu : Measure X) [IsProbabilityMeasure mu] (category : X → Option I)
    (hcmeas : Measurable category) (z : I → ℂ) :
    (∫ h, categoryFactor category z h ∂mu) =
      1 + ∑ i, (mu.real {h | category h = some i} : ℂ) * (z i - 1) := by
  have heq : categoryFactor category z = fun h =>
      1 + ∑ i : I, if category h = some i then z i - 1 else 0 := by
    funext h
    cases hc : category h with
    | none => simp [categoryFactor, hc]
    | some i => simp [categoryFactor, hc]
  have hind (i : I) : (fun h : X => if category h = some i then z i - 1 else 0) =
      {h : X | category h = some i}.indicator (fun _ => z i - 1) := by
    funext h
    by_cases hc : category h = some i <;> simp [hc]
  have hm (i : I) : MeasurableSet {h : X | category h = some i} :=
    hcmeas (measurableSet_singleton _)
  have hi (i : I) : Integrable (fun h : X => if category h = some i then z i - 1 else 0) mu := by
    rw [hind]
    exact (integrable_const _).indicator (hm i)
  rw [heq, integral_add (integrable_const _) (integrable_finsetSum _ (fun i _ => hi i)),
    integral_const, integral_finsetSum _ (fun i _ => hi i)]
  simp only [probReal_univ, one_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hind, integral_indicator_const _ (hm i), Complex.real_smul]

def categoryRates {I : Type*} (rate : ℝ≥0) (mu : Measure X)
    (category : X → Option I) (i : I) : ℝ≥0 :=
  rate * (mu {h | category h = some i}).toNNReal

theorem categoryRates_coe {I : Type*} (rate : ℝ≥0) (mu : Measure X)
    (category : X → Option I) (i : I) :
    (categoryRates rate mu category i : ℝ) = (rate : ℝ) * mu.real {h | category h = some i} := by
  rw [categoryRates, NNReal.coe_mul]
  rfl

/-- A finite set of disjoint mark categories has the actual independent Poisson law. -/
theorem hasLaw_categoryCounts {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (rate : ℝ≥0) (mu : Measure X) [IsProbabilityMeasure mu] (category : X → Option I)
    (hcmeas : Measurable category) :
    HasLaw (categoryCounts category) (fieldMeasure (categoryRates rate mu category))
      (markSampleMeasure rate mu) := by
  refine ⟨(measurable_categoryCounts category hcmeas).aemeasurable, ?_⟩
  letI : IsProbabilityMeasure
      ((markSampleMeasure rate mu).map (categoryCounts category)) :=
    Measure.isProbabilityMeasure_map (measurable_categoryCounts category hcmeas).aemeasurable
  apply CompoundPoissonMarking.count_vector_law_eq_of_unit_transforms
  intro z hz
  rw [integral_map (measurable_categoryCounts category hcmeas).aemeasurable
    (measurable_of_countable (fun k : I → ℕ => ∏ i, z i ^ k i)).aestronglyMeasurable]
  simp_rw [category_count_product]
  have hfm : Measurable (categoryFactor category z) :=
    (measurable_of_countable (fun c : Option I => c.elim 1 z)).comp hcmeas
  rw [stopped_mark_product_transform rate mu (categoryFactor category z) hfm
      (categoryFactor_norm_le category z (fun i => (hz i).le)),
    integral_categoryFactor mu category hcmeas, CompoundPoissonMarking.field_product_transform]
  congr 1
  rw [add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (categoryRates rate mu category i : ℂ) =
    ((rate : ℝ) * mu.real {h | category h = some i} : ℝ) from
      congrArg (fun x : ℝ => (x : ℂ)) (categoryRates_coe rate mu category i)]
  push_cast
  ring

end
end PaperC.V282.GeneralPoissonMarking
