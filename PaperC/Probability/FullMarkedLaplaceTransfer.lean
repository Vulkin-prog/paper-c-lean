import PaperC.Probability.InfiniteLaplaceTransfer

/-!
# Complete marked Laplace functional under the source law

The finite Stein--Chen argument of Section 14 is naturally indexed by a
fixed mark cutoff.  The limiting point process, however, contains every
finite exact excess.  This module defines its literal source Laplace
functional by summing over all marks and proves that a test which vanishes
above `E` agrees pointwise, and hence in expectation, with the truncated
functional used by the finite argument.

No limiting or probabilistic input is used in this raccord.
-/

open scoped BigOperators

namespace PaperC
namespace FullMarkedLaplaceTransfer

open InfiniteLaplaceTransfer
open InfiniteRademacher
open MeasureTheory
open MixedLengthAffine

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/--
Literal Laplace functional of the complete marked source process.  The
outer sum ranges over starts in the dyadic block and the inner sum over
every finite exact excess.
-/
def infiniteFullMarkedLaplaceFunctional
    (N L : ℕ) (g : ℝ → ℕ → ℝ)
    (ω : InfiniteSample) : ℝ :=
  Real.exp
    (-(∑ x ∈ dyadicBlock N,
      ∑' e : ℕ,
        if ExactLengthEvent (infiniteValueBit ω) x
            (excessRowCount L e) then
          g ((x : ℝ) / (N : ℝ)) e
        else 0))

/-- Expectation of the complete marked Laplace functional under the
unrestricted Rademacher source law. -/
def infiniteFullMarkedLaplaceExpectation
    (N L : ℕ) (g : ℝ → ℕ → ℝ) : ℝ :=
  ∫ ω, infiniteFullMarkedLaplaceFunctional N L g ω
    ∂infiniteRademacherMeasure

/--
For a test vanishing above `E`, the complete functional is literally the
finite-mark functional used by the Stein--Chen argument.
-/
theorem infiniteFullMarkedLaplaceFunctional_eq_truncated
    (N L E : ℕ) (g : ℝ → ℕ → ℝ)
    (hvanish : ∀ t e, E < e → g t e = 0)
    (ω : InfiniteSample) :
    infiniteFullMarkedLaplaceFunctional N L g ω =
      infiniteMarkedLaplaceFunctional N L E g ω := by
  classical
  unfold infiniteFullMarkedLaplaceFunctional
    infiniteMarkedLaplaceFunctional
  congr 2
  apply Finset.sum_congr rfl
  intro x _hx
  apply tsum_eq_sum
  intro e he
  have hEe : E < e := by
    have hnot : ¬e < E + 1 := by
      simpa only [Finset.mem_range] using he
    omega
  by_cases hexact :
      ExactLengthEvent (infiniteValueBit ω) x
        (excessRowCount L e)
  · rw [if_pos hexact, hvanish _ e hEe]
  · rw [if_neg hexact]

/-- Compactly mark-supported complete functionals are measurable, by their
exact identification with a finite cylinder observable. -/
theorem measurable_infiniteFullMarkedLaplaceFunctional_of_vanishesAbove
    (N L E : ℕ) (g : ℝ → ℕ → ℝ)
    (hvanish : ∀ t e, E < e → g t e = 0) :
    Measurable (infiniteFullMarkedLaplaceFunctional N L g) := by
  have hfun :
      infiniteFullMarkedLaplaceFunctional N L g =
        infiniteMarkedLaplaceFunctional N L E g := by
    funext ω
    exact infiniteFullMarkedLaplaceFunctional_eq_truncated
      N L E g hvanish ω
  rw [hfun]
  exact measurable_infiniteMarkedLaplaceFunctional N L E g

/--
Expectation-level form of the exact full/truncated identification.
-/
theorem infiniteFullMarkedLaplaceExpectation_eq_truncated
    (N L E : ℕ) (g : ℝ → ℕ → ℝ)
    (hvanish : ∀ t e, E < e → g t e = 0) :
    infiniteFullMarkedLaplaceExpectation N L g =
      infiniteMarkedLaplaceExpectation N L E g := by
  unfold infiniteFullMarkedLaplaceExpectation
    infiniteMarkedLaplaceExpectation
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦
    infiniteFullMarkedLaplaceFunctional_eq_truncated
      N L E g hvanish ω

end

end FullMarkedLaplaceTransfer
end PaperC
