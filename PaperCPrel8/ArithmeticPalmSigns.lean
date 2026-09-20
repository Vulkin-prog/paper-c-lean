import PaperCPrel8.ArithmeticPalmFourier

/-! # The actual arithmetic normalized void under independent fair target signs -/
namespace PaperC.Prel8.ArithmeticPalmSigns
open Finset ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
open V282.SteinFiniteExpectation ArithmeticPalmFourier
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E k : ℕ}

/-- Literal normalized avoidance polynomial on the arithmetic Palm law. -/
def normalizedAvoidance (mu : FinitePMF (SmallSample C Y)) (j e : Fin k → ℕ) (s : Fin k → F₂)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : RoughKernelRegularity.Regular (L+E+1) Y j) (G : Finset ℕ) (t : ℝ) : ℝ :=
  finitePMFExpectation (arithmeticPalmLaw mu j e s hj he hC hr)
    (fun z ↦ ∏ x∈G, (1-t*(if startAt (ConditionalStartProbability.assemble C Y z.1 z.2) x L then (1:ℝ) else 0)))/
      (1-t*(1/(2:ℝ)^L))^G.card

/-- Positivity and finiteness require no estimate on any centered coefficient. -/
theorem normalizedAvoidance_nonneg (mu : FinitePMF (SmallSample C Y)) (hL : 1≤L)
    (j e : Fin k → ℕ) (s : Fin k → F₂)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : RoughKernelRegularity.Regular (L+E+1) Y j) (G : Finset ℕ)
    {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) : 0≤normalizedAvoidance mu j e s hj he hC hr G t := by
  have hpow : (1:ℝ)<2^L := one_lt_pow₀ (by norm_num) (by omega)
  have hp : 0<1/(2:ℝ)^L := by positivity
  have hp1 : 1/(2:ℝ)^L<1 := (div_lt_one (by positivity)).mpr hpow
  have htp := mul_le_mul_of_nonneg_right ht1 hp.le
  unfold normalizedAvoidance
  apply div_nonneg _ (pow_nonneg (by nlinarith) _)
  apply expectation_nonneg
  intro z
  apply prod_nonneg
  intro x hx
  split_ifs <;> nlinarith

/-- At one, the numerator is the genuine no-additional-start event. -/
theorem at_one (mu : FinitePMF (SmallSample C Y))
    (j e : Fin k → ℕ) (s : Fin k → F₂)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : RoughKernelRegularity.Regular (L+E+1) Y j) (G : Finset ℕ) :
    normalizedAvoidance mu j e s hj he hC hr G 1=
      eventProbability (arithmeticPalmLaw mu j e s hj he hC hr)
        (fun z ↦ ∀ x∈G, ¬startAt (ConditionalStartProbability.assemble C Y z.1 z.2) x L)/
          (1-1/(2:ℝ)^L)^G.card := by
  unfold normalizedAvoidance
  simp only [one_mul]
  congr 1
  have hh := PalmVoidPolynomial.avoidance_probability (arithmeticPalmLaw mu j e s hj he hC hr)
    G (fun x z ↦ decide (startAt (ConditionalStartProbability.assemble C Y z.1 z.2) x L))
  simpa using hh

/-- The displayed G.6 target-sign bound for the actual arithmetic void polynomial.
Its Walsh coefficients are constructed from the fair target law, not supplied as hypotheses. -/
theorem arithmetic_target_sign_bound (mu : FinitePMF (SmallSample C Y)) (hL : 1≤L)
    (j e : Fin k → ℕ)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : RoughKernelRegularity.Regular (L+E+1) Y j) (G : Finset ℕ) :
    let R := fun s : Fin k → F₂ ↦ normalizedAvoidance mu j e s hj he hC hr G 1
    finitePMFExpectation (FinitePMF.uniform (Fin k → F₂)) (fun s ↦ max (1-R s) 0)≤
      min 1 (max (1-PalmWalsh.coefficients R 0) 0+
        (1/2:ℝ)*Real.sqrt (PalmWalsh.energy (PalmWalsh.coefficients R))) := by
  dsimp only
  apply PalmWalsh.observable_target_sign_bound
  intro s
  exact normalizedAvoidance_nonneg mu hL j e s hj he hC hr G (by norm_num) (by norm_num)

end
end PaperC.Prel8.ArithmeticPalmSigns
