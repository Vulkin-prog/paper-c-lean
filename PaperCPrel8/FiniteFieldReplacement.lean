import PaperCV282.PoissonFillingCoupling

/-! # Independent Poisson replacement of arbitrary deleted field coordinates -/
namespace PaperC.Prel8.FiniteFieldReplacement
open MeasureTheory
open V282.PoissonFilling V282.PoissonFillingCoupling V282.InfiniteMassCoupling
open V282.PoissonFieldMeasure V282.FiniteFieldTotalVariation V282.SteinFiniteExpectation
open ArratiaGoldsteinGordonInput IndependentThinning
open scoped BigOperators NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]

/-- The actual independent Poisson mixture added to a retained vector. -/
def replacementLaw (mu : FinitePMF Ω) (W : Ω → ι → ℕ) (good : Finset ι)
    (fill : ι → ℝ≥0) (z : ι → ℕ) : ℝ :=
  finitePMFExpectation mu (fun w ↦
    observableLaw (fieldMeasure fill) (fun y ↦ y+retainedField good W w) z)

omit [DecidableEq ι] in
theorem replacement_nonneg (mu : FinitePMF Ω) (W : Ω → ι → ℕ) (good : Finset ι)
    (fill : ι → ℝ≥0) (z : ι → ℕ) : 0 ≤ replacementLaw mu W good fill z :=
  expectation_nonneg mu (fun _ ↦ observableLaw_nonneg _ _ _)

omit [DecidableEq ι] in
theorem replacement_hasSum (mu : FinitePMF Ω) (W : Ω → ι → ℕ) (good : Finset ι)
    (fill : ι → ℝ≥0) : HasSum (replacementLaw mu W good fill) 1 := by
  have h := hasSum_sum (s := Finset.univ) (fun w _ ↦
    (hasSum_observableLaw (fieldMeasure fill)
      (measurable_of_countable (fun y ↦ y+retainedField good W w))).mul_left (mu.prob w))
  unfold replacementLaw finitePMFExpectation
  simpa only [mul_one,mu.sum_prob] using h

/-- Adding the independent field costs at most its total intensity. -/
theorem retained_to_replacement (mu : FinitePMF Ω) (W : Ω → ι → ℕ) (good : Finset ι)
    (fill : ι → ℝ≥0) :
    massTotalVariation (finiteFieldLaw mu (retainedField good W))
      (replacementLaw mu W good fill) ≤ ∑ i, (fill i : ℝ) := by
  -- Reuse the fully normalized finite mixture argument, replacing its typed sum
  -- by the current retained vector pointwise.
  apply massTotalVariation_le_of_test_sets (hasSum_finiteFieldLaw mu _)
    (replacement_hasSum mu W good fill) (finiteFieldLaw_nonneg mu _)
    (replacement_nonneg mu W good fill)
  intro A
  rw [restricted_finiteFieldLaw_eq_eventProbability]
  have hs (w : Ω) : Summable (fun z ↦ if z ∈ A then
      mu.prob w * observableLaw (fieldMeasure fill) (fun y ↦ y+retainedField good W w) z else 0) :=
    ((hasSum_observableLaw (fieldMeasure fill) (measurable_of_countable _)).summable.mul_left _).indicator _
  have hr : (∑' z, if z ∈ A then replacementLaw mu W good fill z else 0) =
      finitePMFExpectation mu (fun w ↦ (fieldMeasure fill).real {y | y+retainedField good W w ∈ A}) := by
    unfold replacementLaw finitePMFExpectation
    have he (z : ι → ℕ) : (if z ∈ A then ∑ w, mu.prob w *
        observableLaw (fieldMeasure fill) (fun y ↦ y+retainedField good W w) z else 0) =
        ∑ w, if z ∈ A then mu.prob w *
          observableLaw (fieldMeasure fill) (fun y ↦ y+retainedField good W w) z else 0 := by
      by_cases h : z ∈ A <;> simp [h]
    simp_rw [he]
    rw [Summable.tsum_finsetSum (fun w _ ↦ hs w)]
    apply Finset.sum_congr rfl
    intro w _
    have he' (z : ι → ℕ) : (if z ∈ A then mu.prob w *
        observableLaw (fieldMeasure fill) (fun y ↦ y+retainedField good W w) z else 0) =
        mu.prob w * (if z ∈ A then
          observableLaw (fieldMeasure fill) (fun y ↦ y+retainedField good W w) z else 0) := by
      by_cases h : z ∈ A <;> simp [h]
    simp_rw [he']
    rw [tsum_mul_left,restricted_observableLaw_eq_event (fieldMeasure fill) (measurable_of_countable _)]
    rfl
  rw [hr]
  have he : eventProbability mu (fun w ↦ retainedField good W w ∈ A) =
      finitePMFExpectation mu (fun w ↦ if retainedField good W w ∈ A then (1:ℝ) else 0) := by
    unfold eventProbability finitePMFExpectation
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> simp_all
  rw [he,← expectation_sub]
  apply (abs_expectation_le mu _).trans
  exact (expectation_mono mu (fun w ↦ translated_test_error_le fill (retainedField good W w) A)).trans_eq
    (expectation_const mu _)

/-- Actual deletion followed by independent filling, with separate source and target costs. -/
theorem replacement_bound (mu : FinitePMF Ω) (W : Ω → ι → ℕ) (good : Finset ι)
    (fill : ι → ℝ≥0) :
    massTotalVariation (finiteFieldLaw mu W) (replacementLaw mu W good fill) ≤
      (∑ i ∈ badFieldSites good, eventProbability mu (fun w ↦ W w i ≠ 0)) + ∑ i, (fill i : ℝ) := by
  apply (massTotalVariation_triangle (hasSum_finiteFieldLaw mu W).summable
    (hasSum_finiteFieldLaw mu (retainedField good W)).summable
    (replacement_hasSum mu W good fill).summable (finiteFieldLaw_nonneg mu W)
    (finiteFieldLaw_nonneg mu _) (replacement_nonneg mu W good fill)).trans
  exact add_le_add (massTotalVariation_retainedField_le_bad_sites mu good W)
    (retained_to_replacement mu W good fill)

end
end PaperC.Prel8.FiniteFieldReplacement
