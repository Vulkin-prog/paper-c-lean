import PaperCV282.CompoundPoissonTransform
import PaperCV282.GeometricClusterTruncation

/-!
# Joint transforms for the actual marked Poisson sample

The coordinate labels remain present throughout. Uniqueness uses the
characteristic function of the whole vector, not just its coordinate means.
-/

namespace PaperC.V282.CompoundPoissonMarking

open MeasureTheory ProbabilityTheory CompoundPoissonTarget CompoundPoissonTransform
open GeometricClusterTruncation PoissonFieldMeasure
open scoped BigOperators NNReal ENNReal

noncomputable section

theorem integral_fixed_mark_product (mu : Measure ℕ) [IsProbabilityMeasure mu]
    (f : ℕ → ℂ) (n : ℕ) :
    (∫ marks, ∏ i ∈ Finset.range n, f (marks i) ∂markSequenceMeasure mu) =
      (∫ h, f h ∂mu) ^ n := by
  have hdep : iIndepFun (fun i : ℕ => fun marks : ℕ → ℕ => f (marks i))
      (markSequenceMeasure mu) :=
    iIndepFun_infinitePi (fun _ => measurable_of_countable _)
  have hn := hdep.precomp (fun i j (h : (i : ℕ) = (j : ℕ)) => Fin.ext h)
    (g := fun i : Fin n => i.val)
  have hp := hn.integral_fun_prod_eq_prod_integral
    (fun i => ((measurable_of_countable f).comp (measurable_pi_apply i.val)).aestronglyMeasurable)
  have hcoord (i : Fin n) :
      (∫ marks : ℕ → ℕ, f (marks i.val) ∂markSequenceMeasure mu) = ∫ h, f h ∂mu :=
    (hasLaw_mark_coordinate mu i.val).integral_comp (measurable_of_countable _).aestronglyMeasurable
  simp_rw [hcoord] at hp
  calc
    _ = ∫ marks : ℕ → ℕ, ∏ i : Fin n, f (marks i.val) ∂markSequenceMeasure mu := by
      congr 1
      funext marks
      exact (Fin.prod_univ_eq_prod_range (fun i => f (marks i)) n).symm
    _ = _ := by simpa using hp

theorem measurable_stopped_mark_product (f : ℕ → ℂ) :
    Measurable (fun sample : ℕ × (ℕ → ℕ) => ∏ i ∈ Finset.range sample.1, f (sample.2 i)) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun marks : ℕ → ℕ => ∏ i ∈ Finset.range n, f (marks i))
  exact Finset.measurable_prod _ (fun i _ =>
    (measurable_of_countable f).comp (measurable_pi_apply i))

theorem stopped_mark_product_transform (rate : ℝ≥0) (mu : Measure ℕ)
    [IsProbabilityMeasure mu] (f : ℕ → ℂ) (hf : ∀ h, ‖f h‖ ≤ 1) :
    (∫ sample, ∏ i ∈ Finset.range sample.1, f (sample.2 i) ∂compoundSampleMeasure rate mu) =
      Complex.exp ((rate : ℂ) * ((∫ h, f h ∂mu) - 1)) := by
  have hint : Integrable
      (fun sample : ℕ × (ℕ → ℕ) => ∏ i ∈ Finset.range sample.1, f (sample.2 i))
      (compoundSampleMeasure rate mu) := by
    refine ⟨(measurable_stopped_mark_product f).aestronglyMeasurable, ?_⟩
    apply HasFiniteIntegral.of_bounded (C := 1)
    exact Filter.Eventually.of_forall fun sample => by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hf (sample.2 i))
  rw [compoundSampleMeasure, integral_prod _ hint]
  simp_rw [integral_fixed_mark_product]
  exact integral_poisson_complex_powers _ _

/-- Unit torus transforms determine a count vector's entire distribution. -/
theorem count_vector_law_eq_of_unit_transforms {I : Type*} [Fintype I]
    (mu nu : Measure (I → ℕ)) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ z : I → ℂ, (∀ i, ‖z i‖ = 1) →
      (∫ k, ∏ i, z i ^ k i ∂mu) = ∫ k, ∏ i, z i ^ k i ∂nu) : mu = nu := by
  classical
  let castVector : (I → ℕ) → (I → ℝ) := fun k i => k i
  have hemb : MeasurableEmbedding castVector := by
    refine ⟨?_, measurable_of_countable _, ?_⟩
    · intro k l hkl
      funext i
      exact Nat.cast_injective (congrFun hkl i)
    · intro s hs
      exact ((Set.to_countable s).image castVector).measurableSet
  apply hemb.map_injective
  apply Measure.ext_of_charFunDual
  funext ell
  rw [charFunDual_apply, charFunDual_apply,
    integral_map hemb.measurable.aemeasurable (by fun_prop),
    integral_map hemb.measurable.aemeasurable (by fun_prop)]
  let z : I → ℂ := fun i => Complex.exp ((ell (Pi.single i (1 : ℝ)) : ℂ) * Complex.I)
  have hz (i : I) : ‖z i‖ = 1 := by simp [z]
  have heq (k : I → ℕ) :
      Complex.exp ((ell (castVector k) : ℂ) * Complex.I) = ∏ i, z i ^ k i := by
    have hvec : castVector k = ∑ i : I, (k i : ℝ) • Pi.single i (1 : ℝ) := by
      funext j
      simp [castVector, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rw [hvec, map_sum]
    simp only [map_smul, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_natCast, Finset.sum_mul, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simpa only [heq] using h z hz

def categoryCounts {I : Type*} [DecidableEq I] (category : ℕ → Option I)
    (sample : ℕ × (ℕ → ℕ)) (i : I) : ℕ :=
  ∑ j ∈ Finset.range sample.1, if category (sample.2 j) = some i then 1 else 0

theorem measurable_categoryCounts {I : Type*} [Fintype I] [DecidableEq I]
    (category : ℕ → Option I) : Measurable (categoryCounts category) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun marks : ℕ → ℕ => ∑ j ∈ Finset.range n,
    if category (marks j) = some i then 1 else 0)
  exact Finset.measurable_sum _ (fun j _ =>
    (measurable_of_countable (fun h : ℕ => if category h = some i then (1 : ℕ) else 0)).comp
      (measurable_pi_apply j))

def categoryFactor {I : Type*} (category : ℕ → Option I) (z : I → ℂ) (h : ℕ) : ℂ :=
  (category h).elim 1 z

theorem category_count_product {I : Type*} [Fintype I] [DecidableEq I]
    (category : ℕ → Option I) (z : I → ℂ) (sample : ℕ × (ℕ → ℕ)) :
    (∏ i, z i ^ categoryCounts category sample i) =
      ∏ j ∈ Finset.range sample.1, categoryFactor category z (sample.2 j) := by
  simp only [categoryCounts, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  cases hc : category (sample.2 j) with
  | none => simp [categoryFactor, hc]
  | some i => simp [categoryFactor, hc, apply_ite]

theorem categoryFactor_norm_le {I : Type*} (category : ℕ → Option I) (z : I → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (h : ℕ) : ‖categoryFactor category z h‖ ≤ 1 := by
  cases hc : category h with
  | none => simp [categoryFactor, hc]
  | some i => simpa [categoryFactor, hc] using hz i

theorem integral_categoryFactor {I : Type*} [Fintype I] [DecidableEq I]
    (mu : Measure ℕ) [IsProbabilityMeasure mu] (category : ℕ → Option I) (z : I → ℂ) :
    (∫ h, categoryFactor category z h ∂mu) =
      1 + ∑ i, (mu.real {h | category h = some i} : ℂ) * (z i - 1) := by
  have heq : categoryFactor category z = fun h =>
      1 + ∑ i : I, if category h = some i then z i - 1 else 0 := by
    funext h
    cases hc : category h with
    | none => simp [categoryFactor, hc]
    | some i => simp [categoryFactor, hc]
  have hind (i : I) : (fun h : ℕ => if category h = some i then z i - 1 else 0) =
      {h : ℕ | category h = some i}.indicator (fun _ => z i - 1) := by
    funext h
    by_cases hc : category h = some i <;> simp [hc]
  have hm (i : I) : MeasurableSet {h : ℕ | category h = some i} :=
    (Set.to_countable _).measurableSet
  have hi (i : I) : Integrable (fun h : ℕ => if category h = some i then z i - 1 else 0) mu := by
    rw [hind]
    exact (integrable_const _).indicator (hm i)
  rw [heq, integral_add (integrable_const _) (integrable_finsetSum _ (fun i _ => hi i)),
    integral_const, integral_finsetSum _ (fun i _ => hi i)]
  simp only [probReal_univ, one_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hind, integral_indicator_const _ (hm i), Complex.real_smul]

def categoryRates {I : Type*} (rate : ℝ≥0) (mu : Measure ℕ)
    (category : ℕ → Option I) (i : I) : ℝ≥0 :=
  rate * (mu {h | category h = some i}).toNNReal

theorem categoryRates_coe {I : Type*} (rate : ℝ≥0) (mu : Measure ℕ)
    (category : ℕ → Option I) (i : I) :
    (categoryRates rate mu category i : ℝ) = (rate : ℝ) * mu.real {h | category h = some i} := by
  rw [categoryRates, NNReal.coe_mul]
  rfl

theorem field_product_transform {I : Type*} [Fintype I]
    (rate : I → ℝ≥0) (z : I → ℂ) :
    (∫ k : I → ℕ, ∏ i, z i ^ k i ∂fieldMeasure rate) =
      Complex.exp (∑ i, (rate i : ℂ) * (z i - 1)) := by
  have hdep := (independent_coordinates rate).comp
    (fun i => fun n : ℕ => z i ^ n) (fun _ => measurable_of_countable _)
  have hp := hdep.integral_fun_prod_eq_prod_integral
    (fun i => ((measurable_of_countable (fun n : ℕ => z i ^ n)).comp
      (measurable_pi_apply i)).aestronglyMeasurable)
  have hi (i : I) : (∫ k : I → ℕ, z i ^ k i ∂fieldMeasure rate) =
      Complex.exp ((rate i : ℂ) * (z i - 1)) :=
    ((hasLaw_coordinate rate i).integral_comp
      (measurable_of_countable (fun n : ℕ => z i ^ n)).aestronglyMeasurable).trans
        (integral_poisson_complex_powers _ _)
  simp only [Function.comp_apply] at hp
  simp_rw [hi] at hp
  rw [← Complex.exp_sum] at hp
  exact hp

/-- A finite set of disjoint mark categories has the actual independent Poisson law. -/
theorem hasLaw_categoryCounts {I : Type*} [Fintype I] [DecidableEq I]
    (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu] (category : ℕ → Option I) :
    HasLaw (categoryCounts category) (fieldMeasure (categoryRates rate mu category))
      (compoundSampleMeasure rate mu) := by
  refine ⟨(measurable_categoryCounts category).aemeasurable, ?_⟩
  letI : IsProbabilityMeasure
      ((compoundSampleMeasure rate mu).map (categoryCounts category)) :=
    Measure.isProbabilityMeasure_map (measurable_categoryCounts category).aemeasurable
  apply count_vector_law_eq_of_unit_transforms
  intro z hz
  rw [integral_map (measurable_categoryCounts category).aemeasurable
    (measurable_of_countable (fun k : I → ℕ => ∏ i, z i ^ k i)).aestronglyMeasurable]
  simp_rw [category_count_product]
  rw [stopped_mark_product_transform rate mu _ (categoryFactor_norm_le category z (fun i => (hz i).le)),
    integral_categoryFactor, field_product_transform]
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
end PaperC.V282.CompoundPoissonMarking
