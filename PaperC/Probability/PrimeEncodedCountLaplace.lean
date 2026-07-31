import PaperC.Probability.PrimeEncodedCountVector
import PaperC.Probability.DirichletAtomConvergence
import PaperC.Probability.SectionThirteenFiniteBound
import PaperC.Probability.SectionThirteenCouplings
import PaperC.Probability.ConditionalAGGAverage
import PaperC.Probability.ConditionalExpectationAverage
import PaperC.Probability.IndependentThinning
import PaperC.Probability.InfiniteLaplaceTransfer

/-!
# Prime-encoded exact-length counts and marked Laplace tests

The joint count vector with marks `0, ..., E` is encoded by the product of
the first `E + 1` primes raised to its coordinates.  This file identifies:

* its finite-cylinder pushforward mass on `ℕ`;
* the atoms of that mass with the original joint atoms;
* inverse-power transforms of the encoded mass with the marked Laplace
  expectation for the constant logarithmic test
  `s * log (Nat.nth Nat.Prime e)`.

All identities here are exact and finite.  The asymptotic marked Laplace
theorem is used only later, in Corollary 14.9.
-/

open scoped BigOperators Topology

namespace PaperC
namespace PrimeEncodedCountLaplace

open MeasureTheory Set
open ArratiaGoldsteinGordonInput
open ConditionalAGGAverage
open ExactLengthCountVectorTransfer
open IndependentThinning
open InfiniteLaplaceTransfer
open MarkedConditionalDependencyGraph
open MixedLengthAffine
open PrimeEncodedCountVector
open SectionThirteenCouplings
open SectionThirteenFiniteBound
open DirichletAtomConvergence

noncomputable section

noncomputable local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Finite encoded source law -/

/-- Law of the prime code of the complete finite-cylinder count vector. -/
def finiteEncodedExactLengthCountLaw
    (N L E : ℕ) (m : ℕ) : ℝ :=
  finiteNatLaw
    (fullUniformPMF (markedCylinderCutoff N L E))
    (fun σ ↦
      primeCode (finiteExactLengthCountVector N L E σ)) m

theorem finiteEncodedExactLengthCountLaw_nonneg
    (N L E m : ℕ) :
    0 ≤ finiteEncodedExactLengthCountLaw N L E m :=
  finiteNatLaw_nonneg _ _ _

theorem hasSum_finiteEncodedExactLengthCountLaw
    (N L E : ℕ) :
    HasSum (finiteEncodedExactLengthCountLaw N L E) 1 :=
  hasSum_finiteNatLaw _ _

/-- The encoded law has no atom at zero because every prime code is positive. -/
@[simp]
theorem finiteEncodedExactLengthCountLaw_zero
    (N L E : ℕ) :
    finiteEncodedExactLengthCountLaw N L E 0 = 0 := by
  classical
  unfold finiteEncodedExactLengthCountLaw finiteNatLaw
  apply Finset.sum_eq_zero
  intro σ _hσ
  rw [if_neg]
  exact ne_of_gt
    (primeCode_pos (finiteExactLengthCountVector N L E σ))

/--
The atom at the code of `k` is exactly the joint atom of the original
count vector.
-/
theorem finiteEncodedExactLengthCountLaw_primeCode
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    finiteEncodedExactLengthCountLaw N L E (primeCode k) =
      finiteExactLengthCountVectorLaw N L E k := by
  classical
  unfold finiteEncodedExactLengthCountLaw finiteNatLaw
  calc
    (∑ σ,
        if primeCode (finiteExactLengthCountVector N L E σ) =
            primeCode k then
          (fullUniformPMF (markedCylinderCutoff N L E)).prob σ
        else 0) =
        eventProbability
          (fullUniformPMF (markedCylinderCutoff N L E))
          (fun σ ↦ finiteExactLengthCountVector N L E σ = k) := by
      unfold eventProbability
      apply Finset.sum_congr rfl
      intro σ _hσ
      simp only [primeCode_injective.eq_iff]
      split_ifs <;> rfl
    _ = finiteExactLengthCountVectorLaw N L E k := by
      rw [eventProbability_fullUniformPMF_eq,
        finiteUniformProbability_eq_uniformEventProbability]
      rfl

/-! ## Inverse-power transforms of finite pushforwards -/

/--
The inverse-power transform of a finite pushforward is the corresponding
finite expectation.
-/
theorem inversePowerTransform_finiteNatLaw_eq_expectation
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → ℕ) (s : ℕ) :
    inversePowerTransform (finiteNatLaw μ Z) s =
      finitePMFExpectation μ
        (fun ω ↦ ((Z ω : ℝ)⁻¹) ^ s) := by
  classical
  let support : Finset ℕ := Finset.univ.image Z
  have hout :
      ∀ k ∉ support,
        finiteNatLaw μ Z k * ((k : ℝ)⁻¹) ^ s = 0 := by
    intro k hk
    have hk0 : finiteNatLaw μ Z k = 0 := by
      unfold finiteNatLaw
      apply Finset.sum_eq_zero
      intro ω _hω
      rw [if_neg]
      intro hZ
      apply hk
      exact Finset.mem_image.mpr
        ⟨ω, Finset.mem_univ _, hZ⟩
    rw [hk0, zero_mul]
  unfold inversePowerTransform
  rw [tsum_eq_sum hout]
  unfold finiteNatLaw finitePMFExpectation
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _hω
  have hmem : Z ω ∈ support :=
    Finset.mem_image.mpr
      ⟨ω, Finset.mem_univ _, rfl⟩
  simp [hmem]

/-! ## Prime logarithms -/

theorem log_primeCode {d : ℕ} (k : Fin d → ℕ) :
    Real.log (((primeCode k : ℕ) : ℝ)) =
      ∑ e : Fin d,
        (k e : ℝ) *
          Real.log ((Nat.nth Nat.Prime e.1 : ℕ) : ℝ) := by
  unfold primeCode
  push_cast
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro e _he
    rw [Real.log_pow]
  · intro e _he
    exact pow_ne_zero _ (by
      exact_mod_cast (Nat.prime_nth_prime e.1).ne_zero)

/-- Constant marked test whose coefficients encode the count vector. -/
def primeLogTest (s : ℝ) : ℝ → ℕ → ℝ :=
  fun _ e ↦
    s * Real.log ((Nat.nth Nat.Prime e : ℕ) : ℝ)

theorem continuousOn_primeLogTest
    (s : ℝ) (e : ℕ) (A : Set ℝ) :
    ContinuousOn (fun t ↦ primeLogTest s t e) A :=
  continuousOn_const

theorem primeLogTest_nonneg
    {s : ℝ} (hs : 0 ≤ s) (t : ℝ) (e : ℕ) :
    0 ≤ primeLogTest s t e := by
  unfold primeLogTest
  apply mul_nonneg hs
  apply Real.log_nonneg
  exact_mod_cast
    ((by norm_num : 1 ≤ (2 : ℕ)).trans
      (Nat.prime_nth_prime e).two_le)

/--
The inverse-power weight of a prime code factors coordinatewise into the
Laplace weights attached to `primeLogTest`.
-/
theorem inversePrimeCodeWeight_eq_prod
    {d : ℕ} (k : Fin d → ℕ) (s : ℕ) :
    ((((primeCode k : ℕ) : ℝ)⁻¹) ^ s) =
      ∏ e : Fin d,
        (Real.exp
          (-((s : ℝ) *
            Real.log ((Nat.nth Nat.Prime e.1 : ℕ) : ℝ)))) ^ (k e) := by
  have hcpos : (0 : ℝ) < ((primeCode k : ℕ) : ℝ) := by
    exact_mod_cast primeCode_pos k
  calc
    ((((primeCode k : ℕ) : ℝ)⁻¹) ^ s) =
        (Real.exp
          (-Real.log (((primeCode k : ℕ) : ℝ)))) ^ s := by
      rw [Real.exp_neg, Real.exp_log hcpos]
    _ = Real.exp
          ((s : ℝ) *
            (-Real.log (((primeCode k : ℕ) : ℝ)))) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp
          (∑ e : Fin d,
            (k e : ℝ) *
              (-((s : ℝ) *
                Real.log
                  ((Nat.nth Nat.Prime e.1 : ℕ) : ℝ)))) := by
      congr 1
      rw [log_primeCode]
      rw [← Finset.sum_neg_distrib]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      ring
    _ = ∏ e : Fin d,
        (Real.exp
          (-((s : ℝ) *
            Real.log
              ((Nat.nth Nat.Prime e.1 : ℕ) : ℝ)))) ^ (k e) := by
      simp_rw [← Real.exp_nat_mul]
      rw [Real.exp_sum]

/-! ## Identification with the marked functional -/

theorem markedPrimeLogExponent_eq
    (N L E : ℕ)
    (σ : SampleSpace (markedCylinderCutoff N L E))
    (s : ℝ) :
    (∑ x ∈ dyadicBlock N,
      ∑ e ∈ Finset.range (E + 1),
        if exactLengthAt σ x (excessRowCount L e) then
          primeLogTest s ((x : ℝ) / (N : ℝ)) e
        else 0) =
      s * Real.log
        (((primeCode
          (finiteExactLengthCountVector N L E σ) : ℕ) : ℝ)) := by
  rw [log_primeCode]
  simp only [primeLogTest]
  rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro ef _hef
  change
    (∑ x ∈ dyadicBlock N,
      if exactLengthAt σ x (excessRowCount L ef.1) then
        s * Real.log ((Nat.nth Nat.Prime ef.1 : ℕ) : ℝ)
      else 0) =
      s *
        (((finiteExactLengthCountVector N L E σ ef : ℕ) : ℝ) *
          Real.log
            ((Nat.nth Nat.Prime ef.1 : ℕ) : ℝ))
  unfold finiteExactLengthCountVector
    finiteExactLengthCountVectorOn
  push_cast
  rw [Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases h :
      exactLengthAt σ x (excessRowCount L ef.1)
  · simp [h]
  · simp [h]

theorem finiteMarkedLaplaceFunctional_primeLogTest
    (N L E : ℕ)
    (σ : SampleSpace (markedCylinderCutoff N L E))
    (s : ℕ) :
    finiteMarkedLaplaceFunctional
        (markedCylinderCutoff N L E) N L E
        (primeLogTest (s : ℝ)) σ =
      ((((primeCode
        (finiteExactLengthCountVector N L E σ) : ℕ) : ℝ)⁻¹) ^ s) := by
  unfold finiteMarkedLaplaceFunctional
  rw [markedPrimeLogExponent_eq]
  have hcpos :
      (0 : ℝ) <
        ((primeCode
          (finiteExactLengthCountVector N L E σ) : ℕ) : ℝ) := by
    exact_mod_cast
      primeCode_pos (finiteExactLengthCountVector N L E σ)
  calc
    Real.exp
        (-((s : ℝ) *
          Real.log
            ((primeCode
              (finiteExactLengthCountVector N L E σ) : ℕ) : ℝ))) =
        Real.exp
          ((s : ℝ) *
            (-Real.log
              ((primeCode
                (finiteExactLengthCountVector N L E σ) : ℕ) : ℝ))) := by
      congr 1
      ring
    _ =
        (Real.exp
          (-Real.log
            ((primeCode
              (finiteExactLengthCountVector N L E σ) : ℕ) : ℝ))) ^ s := by
      rw [Real.exp_nat_mul]
    _ =
        ((((primeCode
          (finiteExactLengthCountVector N L E σ) : ℕ) : ℝ)⁻¹) ^ s) := by
      rw [Real.exp_neg, Real.exp_log hcpos]

/-- Exact finite-PMF representation of the source marked expectation. -/
theorem infiniteMarkedLaplaceExpectation_eq_uniformPMFExpectation
    (N L E : ℕ) (g : ℝ → ℕ → ℝ) :
    infiniteMarkedLaplaceExpectation N L E g =
      finitePMFExpectation
        (FinitePMF.uniform
          (SampleSpace (markedCylinderCutoff N L E)))
        (finiteMarkedLaplaceFunctional
          (markedCylinderCutoff N L E) N L E g) := by
  rw [infiniteMarkedLaplaceExpectation_eq_finite_dyadicCutoff]
  unfold finiteMarkedLaplaceExpectation
  rw [
    ConditionalExpectationAverage.finiteRademacherIntegral_eq_uniformPMFExpectation]
  rfl

/--
Every inverse-power transform of the encoded source law is literally the
marked Laplace expectation for the corresponding prime-logarithmic test.
-/
theorem inversePowerTransform_finiteEncodedExactLengthCountLaw_eq
    (N L E s : ℕ) :
    inversePowerTransform
        (finiteEncodedExactLengthCountLaw N L E) s =
      infiniteMarkedLaplaceExpectation N L E
        (primeLogTest (s : ℝ)) := by
  unfold finiteEncodedExactLengthCountLaw
  rw [inversePowerTransform_finiteNatLaw_eq_expectation]
  rw [infiniteMarkedLaplaceExpectation_eq_uniformPMFExpectation]
  unfold finitePMFExpectation
  apply Finset.sum_congr rfl
  intro σ _hσ
  rw [finiteMarkedLaplaceFunctional_primeLogTest]
  unfold fullUniformPMF
  rfl

end

end PrimeEncodedCountLaplace
end PaperC
