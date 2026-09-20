import PaperCPrel8.ArithmeticPalmMatrices

/-! # The arithmetic signed centered coefficient and normalized Palm polynomial -/
namespace PaperC.Prel8.ArithmeticPalmFourier
open Finset ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
open _root_.PaperC.Affine V282.SteinFiniteExpectation V282.ExactMarkedModel
open RegularPlantPresence AffinePalmEnvironment CenteredAffineBlocks CenteredPalmFourier
open ArithmeticPalmMatrices FiniteConditioning
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual small-prime law times fair large-prime coordinates, conditioned by the actual raw plant. -/
def arithmeticPalmLaw (mu : FinitePMF (SmallSample C Y)) (j e : Fin k → ℕ) (s : Fin k → F₂)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : RoughKernelRegularity.Regular (L+E+1) Y j) :=
  conditional (productPMF mu (FinitePMF.uniform (LargeSample C Y)))
    (plant (smallRaw C Y L j e) (largeRaw C Y L j e) (word (L := L) e s))
    (regular_plant_probability_pos mu j e s hj he hC hr)

def arithmeticCoefficient (mu : FinitePMF (SmallSample C Y)) (j e : Fin k → ℕ)
    (s : Fin k → F₂) (x : ι → ℕ) : ℝ :=
  coefficient mu (smallRaw C Y L j e) (largeRaw C Y L j e) (word (L := L) e s)
    (fun i ↦ smallStart C Y (x i) L) (fun i ↦ largeStartSystem C Y (x i) L) (fun _ ↦ startRhs L)

/-- The actual arithmetic centered moment equals p^|S| times the literal signed coefficient.
The small-prime distribution is arbitrary and may be any positive event-conditioned law. -/
theorem arithmetic_centered_moment (mu : FinitePMF (SmallSample C Y)) (hL : 1≤L)
    (j e : Fin k → ℕ) (s : Fin k → F₂) (x : ι → ℕ)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : RoughKernelRegularity.Regular (L+E+1) Y j) :
    finitePMFExpectation (arithmeticPalmLaw mu j e s hj he hC hr)
      (fun z ↦ ∏ i, ((if startAt (ConditionalStartProbability.assemble C Y z.1 z.2) (x i) L then (1:ℝ) else 0)-
        1/(2:ℝ)^L))=(1/(2:ℝ)^L)^Fintype.card ι*arithmeticCoefficient (L := L) mu j e s x := by
  have h := centered_moment mu (smallRaw C Y L j e) (largeRaw C Y L j e)
    (regular_largeRaw_surjective j e hj he hC hr) (word (L := L) e s)
    (fun i ↦ smallStart C Y (x i) L) (fun i ↦ largeStartSystem C Y (x i) L) (fun _ ↦ startRhs L)
    (regular_plant_probability_pos mu j e s hj he hC hr)
  simpa only [block_eq_start hL,referenceRate_fin,arithmeticPalmLaw,arithmeticCoefficient] using h

/-- The subset form matches the finite powerset expansion of R_z(t). -/
theorem arithmetic_centered_subset (mu : FinitePMF (SmallSample C Y)) (hL : 1≤L)
    (j e : Fin k → ℕ) (s : Fin k → F₂) (S : Finset ℕ)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : RoughKernelRegularity.Regular (L+E+1) Y j) :
    finitePMFExpectation (arithmeticPalmLaw mu j e s hj he hC hr)
      (fun z ↦ ∏ x∈S, ((if startAt (ConditionalStartProbability.assemble C Y z.1 z.2) x L then (1:ℝ) else 0)-
        1/(2:ℝ)^L))=(1/(2:ℝ)^L)^S.card*arithmeticCoefficient (L := L) mu j e s (fun x : S ↦ x.val) := by
  have h := arithmetic_centered_moment mu hL j e s (fun x : S ↦ x.val) hj he hC hr
  rw [Fintype.card_coe] at h
  convert h using 1
  apply expectation_congr
  intro z
  exact (Finset.prod_coe_sort S (fun x : ℕ ↦
    ((if startAt (ConditionalStartProbability.assemble C Y z.1 z.2) x L then (1:ℝ) else 0)-1/(2:ℝ)^L))).symm

/-- The complete finite signed polynomial, including singleton corrections and overlaps. -/
theorem arithmetic_normalized_polynomial (mu : FinitePMF (SmallSample C Y)) (hL : 1≤L)
    (j e : Fin k → ℕ) (s : Fin k → F₂) (G : Finset ℕ)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : RoughKernelRegularity.Regular (L+E+1) Y j)
    (t : ℝ) (ht : 1-t*(1/(2:ℝ)^L)≠0) :
    finitePMFExpectation (arithmeticPalmLaw mu j e s hj he hC hr)
      (fun z ↦ ∏ x∈G, (1-t*(if startAt (ConditionalStartProbability.assemble C Y z.1 z.2) x L then (1:ℝ) else 0)))/
      (1-t*(1/(2:ℝ)^L))^G.card=
    ∑ S∈G.powerset, (-t*(1/(2:ℝ)^L)/(1-t*(1/(2:ℝ)^L)))^S.card*
      arithmeticCoefficient (L := L) mu j e s (fun x : S ↦ x.val) := by
  rw [PalmVoidPolynomial.normalized_expectation _ G _ _ t ht]
  apply sum_congr rfl
  intro S hS
  rw [arithmetic_centered_subset mu hL j e s S hj he hC hr]
  rw [← mul_assoc,← mul_pow]
  congr 2
  ring

/-- The constant coefficient is exactly one, including for an empty plant. -/
theorem arithmetic_empty_coefficient (mu : FinitePMF (SmallSample C Y)) (hL : 1≤L)
    (j e : Fin k → ℕ) (s : Fin k → F₂)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : RoughKernelRegularity.Regular (L+E+1) Y j) :
    arithmeticCoefficient (L := L) mu j e s (fun x : (∅ : Finset ℕ) ↦ x.val)=1 := by
  have h := arithmetic_centered_subset mu hL j e s ∅ hj he hC hr
  simpa only [prod_empty,expectation_const,card_empty,pow_zero,one_mul] using h.symm

end
end PaperC.Prel8.ArithmeticPalmFourier
