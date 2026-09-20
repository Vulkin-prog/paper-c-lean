import PaperCV282.SteinFiniteExpectation

/-! # Actual finite laws conditioned on a positive-probability event -/
namespace PaperC.Prel8.FiniteConditioning
open PaperC.ArratiaGoldsteinGordonInput PaperC.IndependentThinning
open PaperC.V282.SteinFiniteExpectation
open scoped BigOperators
noncomputable section
variable {Ω : Type*} [Fintype Ω]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Normalized restriction of the source law, retaining the complete sample space. -/
def conditional (μ : FinitePMF Ω) (A : Ω → Prop) (hA : 0 < eventProbability μ A) :
    FinitePMF Ω where
  prob ω := (if A ω then μ.prob ω else 0) / eventProbability μ A
  nonneg ω := div_nonneg (by split_ifs; exact μ.nonneg ω; rfl) hA.le
  sum_prob := by
    rw [← Finset.sum_div]
    exact div_self hA.ne'

/-- Conditional expectations are the usual normalized restricted expectations. -/
theorem expectation_conditional (μ : FinitePMF Ω) (A : Ω → Prop)
    (hA : 0 < eventProbability μ A) (f : Ω → ℝ) :
    finitePMFExpectation (conditional μ A hA) f =
      finitePMFExpectation μ (fun ω => if A ω then f ω else 0) / eventProbability μ A := by
  simp only [finitePMFExpectation, conditional, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> ring

/-- The conditional event probability has the expected intersection numerator. -/
theorem probability_conditional (μ : FinitePMF Ω) (A B : Ω → Prop)
    (hA : 0 < eventProbability μ A) :
    eventProbability (conditional μ A hA) B =
      eventProbability μ (fun ω => A ω ∧ B ω) / eventProbability μ A := by
  simp only [eventProbability, conditional, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp_all

/-- Conditioning increases any nonnegative expectation by at most the inverse event mass. -/
theorem expectation_conditional_le (μ : FinitePMF Ω) (A : Ω → Prop)
    (hA : 0 < eventProbability μ A) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    finitePMFExpectation (conditional μ A hA) f ≤
      finitePMFExpectation μ f / eventProbability μ A := by
  rw [expectation_conditional]
  apply div_le_div_of_nonneg_right _ hA.le
  apply expectation_mono
  intro ω
  split_ifs
  · rfl
  · exact hf ω

end
end PaperC.Prel8.FiniteConditioning
