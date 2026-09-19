import PaperCPrel8.SmallPrimeMixture
import PaperCPrel8.AffinePalmEnvironment

/-! # Actual conditioned arithmetic law as its small/large prime product -/
namespace PaperC.Prel8.ArithmeticEnvironmentLaw
open Finset ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
open V282.SteinFiniteExpectation FiniteConditioning AffinePalmEnvironment
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The real event mass agrees in the full prime cylinder and its small-prime factor. -/
theorem trace_probability (C Y : ℕ) (A : SmallSample C Y → Prop) :
    eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w))=
      eventProbability (FinitePMF.uniform (SmallSample C Y)) A := by
  rw [← finitePMFExpectation_indicator,← finitePMFExpectation_indicator,
    SmallPrimeMixture.expectation_split]
  apply expectation_congr
  intro e
  simpa only [restrictSmall_assemble] using
    expectation_const (FinitePMF.uniform (LargeSample C Y)) (if A e then (1:ℝ) else 0)

/-- Complete law identity for every observable, including overlapping starts and planted words. -/
theorem conditional_expectation (C Y : ℕ) (A : SmallSample C Y → Prop)
    (hA : 0<eventProbability (FinitePMF.uniform (SmallSample C Y)) A)
    (hfull : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)))
    (f : SampleSpace C → ℝ) :
    finitePMFExpectation (conditional (FinitePMF.uniform (SampleSpace C))
      (fun w ↦ A (restrictSmall C Y w)) hfull) f=
    finitePMFExpectation (productPMF (conditional (FinitePMF.uniform (SmallSample C Y)) A hA)
      (FinitePMF.uniform (LargeSample C Y))) (fun z ↦ f (assemble C Y z.1 z.2)) := by
  rw [expectation_product,expectation_conditional,expectation_conditional,trace_probability,
    SmallPrimeMixture.expectation_split]
  congr 1
  apply expectation_congr
  intro e
  simp only [restrictSmall_assemble]
  by_cases he : A e
  · simp only [he,ite_true]
  · simp only [he,ite_false,expectation_const]

/-- The same identity after additionally conditioning on any positive-probability plant. -/
theorem conditional_plant_expectation (C Y : ℕ) (A : SmallSample C Y → Prop)
    (hA : 0<eventProbability (FinitePMF.uniform (SmallSample C Y)) A)
    (hfull : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)))
    (P : SampleSpace C → Prop)
    (hp : 0<eventProbability (conditional (FinitePMF.uniform (SampleSpace C))
      (fun w ↦ A (restrictSmall C Y w)) hfull) P)
    (hp' : 0<eventProbability (productPMF (conditional (FinitePMF.uniform (SmallSample C Y)) A hA)
      (FinitePMF.uniform (LargeSample C Y))) (fun z ↦ P (assemble C Y z.1 z.2)))
    (f : SampleSpace C → ℝ) :
    finitePMFExpectation (conditional (conditional (FinitePMF.uniform (SampleSpace C))
      (fun w ↦ A (restrictSmall C Y w)) hfull) P hp) f=
    finitePMFExpectation (conditional
      (productPMF (conditional (FinitePMF.uniform (SmallSample C Y)) A hA)
        (FinitePMF.uniform (LargeSample C Y))) (fun z ↦ P (assemble C Y z.1 z.2)) hp')
      (fun z ↦ f (assemble C Y z.1 z.2)) := by
  rw [expectation_conditional _ _ hp,expectation_conditional _ _ hp']
  have hm := conditional_expectation C Y A hA hfull (fun w ↦ if P w then (1:ℝ) else 0)
  rw [finitePMFExpectation_indicator,finitePMFExpectation_indicator] at hm
  rw [hm,conditional_expectation C Y A hA hfull]

end
end PaperC.Prel8.ArithmeticEnvironmentLaw
