import PaperCV282.PoissonFilling
import PaperCV282.PoissonPolynomialIntegrability

/-! # Exact cost of introducing the independent Poisson filling

The cost is the sum of the added rates, proved through the actual nonzero
probability of the filling. There is no restriction on retained marginals.
-/
namespace PaperC.V282.PoissonFillingCoupling

open MeasureTheory PoissonFilling PoissonFillingIdentity PoissonPolynomialIntegrability
open PoissonFieldMeasure InfiniteMassCoupling DirectionalSteinComparison
open FiniteFieldTotalVariation ArratiaGoldsteinGordonInput IndependentThinning SteinFiniteExpectation
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

variable {Ω ι κ : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem integral_filling_coordinate (fill : κ → ℝ≥0) (i : κ) :
    (∫ z, (z i : ℝ) ∂fieldMeasure fill)=(fill i : ℝ) := by
  have h := poisson_filling_integral fill i (fun _ => (1 : ℝ))
  simpa using h

/-- A nonempty filling has total count at least one. -/
theorem filling_nonzero_probability_le (fill : κ → ℝ≥0) :
    (fieldMeasure fill).real {z : κ → ℕ | z≠0}≤∑ j, (fill j : ℝ) := by
  have hi : Integrable (fun z : κ → ℕ => if z≠0 then (1 : ℝ) else 0) (fieldMeasure fill) :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by split_ifs <;> norm_num))
  have he := integral_indicator_one (μ := fieldMeasure fill)
    ((Set.to_countable {z : κ → ℕ | z≠0}).measurableSet)
  simp only [Set.indicator_apply,Pi.one_apply,Set.mem_setOf_eq] at he
  rw [← he]
  simp_rw [← integral_filling_coordinate fill]
  rw [← integral_finsetSum Finset.univ (fun j _ => integrable_poisson_coordinate fill j)]
  apply integral_mono hi (integrable_finsetSum Finset.univ (fun j _ => integrable_poisson_coordinate fill j))
  intro z
  change (if z≠0 then (1 : ℝ) else 0)≤∑ j, (z j : ℝ)
  by_cases hz : z=0
  · simp [hz]
  · rw [if_pos hz]
    obtain ⟨j,hj⟩ : ∃ j, z j≠0 := by
      by_contra h
      apply hz
      funext j
      exact not_ne_iff.mp (not_exists.mp h j)
    have h := (Nat.one_le_iff_ne_zero.mpr hj).trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
    exact_mod_cast h

/-- Adding the filling changes any one translated test event by at most its nonzero probability. -/
theorem translated_test_error_le (fill : κ → ℝ≥0) (v : κ → ℕ) (A : Set (κ → ℕ)) :
    |(if v∈A then (1 : ℝ) else 0)-(fieldMeasure fill).real {z | z+v∈A}|≤
      ∑ j, (fill j : ℝ) := by
  have h := InfiniteMassCoupling.event_discrepancy_le_disagreement (fieldMeasure fill)
    (fun _ : κ → ℕ => v) (fun z => z+v) A
  have he : (fieldMeasure fill).real ((fun _ : κ → ℕ => v) ⁻¹' A)=
      (if v∈A then (1 : ℝ) else 0) := by
    by_cases hv : v∈A <;> simp [Set.preimage,hv]
  rw [he] at h
  apply h.trans
  apply (measureReal_mono (μ := fieldMeasure fill) (s₂ := {z : κ → ℕ | z≠0}) _).trans
    (filling_nonzero_probability_le fill)
  intro z hz hzero
  apply hz
  simp [hzero]

omit [DecidableEq ι] in
/-- The exact generic deletion-to-filling budget for a finite retained vector. -/
theorem unfilled_to_filled_tv_le (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (fill : κ → ℝ≥0) :
    massTotalVariation (finiteFieldLaw mu (typedSum X kind Finset.univ))
      (filledLaw mu X kind fill)≤∑ j, (fill j : ℝ) := by
  apply massTotalVariation_le_of_test_sets (hasSum_finiteFieldLaw mu _)
    (hasSum_filledLaw mu X kind fill) (finiteFieldLaw_nonneg mu _) (filledLaw_nonneg mu X kind fill)
  intro A
  rw [restricted_finiteFieldLaw_eq_eventProbability,restricted_filledLaw_eq]
  have he : eventProbability mu (fun omega => typedSum X kind Finset.univ omega∈A)=
      finitePMFExpectation mu (fun omega => if typedSum X kind Finset.univ omega∈A then (1 : ℝ) else 0) := by
    unfold eventProbability finitePMFExpectation
    apply Finset.sum_congr rfl
    intro omega homega
    split_ifs <;> simp_all
  rw [he,← expectation_sub]
  apply (abs_expectation_le mu _).trans
  apply (expectation_mono mu (fun omega => translated_test_error_le fill
    (typedSum X kind Finset.univ omega) A)).trans_eq
  exact expectation_const mu _

end
end PaperC.V282.PoissonFillingCoupling
