import PaperC.Model.FiniteRademacher
import PaperC.Probability.FactorialMoment
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact expectations on finite Rademacher cylinders

All quantities in a fixed dyadic block depend on finitely many prime signs.
This file records the elementary finite-sum identities needed to pass from
indicator counts to their exact rational expectations.
-/

open scoped BigOperators

namespace PaperC

/-- Expectation under the uniform law on a finite prime-sign cylinder,
represented as an exact rational number. -/
noncomputable def uniformExpectation {M : ℕ}
    (f : SampleSpace M → ℚ) : ℚ :=
  (∑ ω : SampleSpace M, f ω) /
    (Fintype.card (SampleSpace M) : ℚ)

/-- The expectation of an event indicator is its uniform event probability. -/
theorem uniformExpectation_indicator {M : ℕ}
    (P : SampleSpace M → Prop) [DecidablePred P] :
    uniformExpectation (fun ω => if P ω then (1 : ℚ) else 0) =
      uniformEventProbability P := by
  classical
  simp [uniformExpectation, uniformEventProbability]

/-- The exact expectation of the dyadic count is the sum of its one-point
start probabilities. -/
theorem uniformExpectation_dyadicCount (N L : ℕ) :
    uniformExpectation
        (fun ω : DyadicSample N L => (dyadicCount N L ω : ℚ)) =
      dyadicExpectation N L := by
  classical
  simp only [uniformExpectation, dyadicCount, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, dyadicExpectation, startProbability,
    uniformEventProbability]
  have hcomm :
      (∑ ω : DyadicSample N L, ∑ x ∈ dyadicBlock N,
          if startAt ω x L then (1 : ℚ) else 0) =
        ∑ x ∈ dyadicBlock N, ∑ ω : DyadicSample N L,
          if startAt ω x L then (1 : ℚ) else 0 := by
    exact Finset.sum_comm
  rw [hcomm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  simp

end PaperC
