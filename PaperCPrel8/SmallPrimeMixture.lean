import PaperCPrel8.FiniteConditioning
import PaperC.Probability.ConditionalAGGAverage

/-! # Mixtures over arbitrary events in the small-prime trace -/
namespace PaperC.Prel8.SmallPrimeMixture
open PaperC.Prel8.FiniteConditioning
open PaperC.ConditionalAGGAverage PaperC.ConditionalStartProbability
open PaperC.IndependentThinning PaperC.ArratiaGoldsteinGordonInput
open PaperC.V282.SteinFiniteExpectation
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exact disintegration of the uniform source into its two actual prime blocks. -/
theorem expectation_split (C Y : ℕ) (f : SampleSpace C → ℝ) :
    finitePMFExpectation (FinitePMF.uniform (SampleSpace C)) f =
      finitePMFExpectation (FinitePMF.uniform (SmallSample C Y))
        (fun σ => finitePMFExpectation (FinitePMF.uniform (LargeSample C Y))
          (fun η => f (assemble C Y σ η))) := by
  have hs := Equiv.sum_comp (sampleSplitEquiv C Y).symm f
  change (∑ p : SmallSample C Y × LargeSample C Y, f (assemble C Y p.1 p.2)) = ∑ ω, f ω at hs
  simp only [Fintype.sum_prod_type] at hs
  simp only [finitePMFExpectation, FinitePMF.uniform_prob, ← Finset.mul_sum,
    card_sampleSpace_eq_mul C Y, Nat.cast_mul]
  rw [← hs]
  simp only [Finset.mul_sum, mul_inv_rev]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro η _
  ring

/-- Uniform fibre bounds survive conditioning on any positive small-prime event. -/
theorem conditional_fiber_bound (C Y : ℕ) (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) (f : SampleSpace C → ℝ) (K : ℝ)
    (hf : ∀ σ, finitePMFExpectation (FinitePMF.uniform (LargeSample C Y))
      (fun η => f (assemble C Y σ η)) ≤ K) :
    finitePMFExpectation (conditional (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω)) hA) f ≤ K := by
  rw [expectation_conditional, div_le_iff₀ hA]
  rw [← finitePMFExpectation_indicator]
  rw [expectation_split C Y, expectation_split C Y]
  have hh (σ : SmallSample C Y) :
      finitePMFExpectation (FinitePMF.uniform (LargeSample C Y))
        (fun η => if A (restrictSmall C Y (assemble C Y σ η)) then f (assemble C Y σ η) else 0) ≤
      K * finitePMFExpectation (FinitePMF.uniform (LargeSample C Y))
        (fun η => if A (restrictSmall C Y (assemble C Y σ η)) then 1 else 0) := by
    simp only [restrictSmall_assemble]
    by_cases ha : A σ
    · simp only [ha, ite_true, expectation_const, mul_one]
      exact hf σ
    · simp [ha, expectation_const]
  rw [← expectation_const_mul]
  exact expectation_mono _ hh

end
end PaperC.Prel8.SmallPrimeMixture
