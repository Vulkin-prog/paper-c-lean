import PaperC.Model.InfiniteRademacher
import PaperC.Probability.ExactLengthDecomposition

/-!
# Exact run lengths in the infinite Rademacher model

Lemma 14.5 makes the deterministic exact-length decomposition applicable
almost surely.  This module records the resulting event-level identity

`J_{x,L} = ∑ e, K_{x,e}`

in the stronger form that, whenever `J_{x,L}` occurs, there is a unique
excess `e` for which `K_{x,e}` occurs.
-/

open MeasureTheory Filter

namespace PaperC
namespace InfiniteExactLengthDecomposition

open InfiniteRademacher
open ExactLengthDecomposition
open MixedLengthAffine

/- The infinite model uses the discrete measurable structure on `F₂`.
Reinstall it locally when forming almost-everywhere statements in this
downstream module. -/
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/--
Bit-valued form of Lemma 14.5.  Distinct integer phases have distinct
underlying parity bits.
-/
theorem ae_tailChangesAt_infiniteValueBit :
    ∀ᵐ ω ∂infiniteRademacherMeasure, ∀ x : ℕ, 2 ≤ x →
      TailChangesAt (infiniteValueBit ω) x := by
  filter_upwards [lemma_fourteen_four] with ω hω
  intro x hx
  obtain ⟨n, hxn, hn⟩ := hω x hx
  refine ⟨n, hxn, ?_⟩
  intro hbits
  apply hn
  simp only [infiniteRandomValue, hbits]

/--
Almost-sure exact-length decomposition, simultaneously for every source
position `x ≥ 2` and every positive requested run length `L`.
-/
theorem ae_startEvent_iff_existsUnique_exactLengthEvent :
    ∀ᵐ ω ∂infiniteRademacherMeasure,
      ∀ x : ℕ, 2 ≤ x → ∀ L : ℕ, 1 ≤ L →
        (StartEvent (infiniteValueBit ω) x L ↔
          ∃! e : ℕ,
            ExactLengthEvent (infiniteValueBit ω) x
              (excessRowCount L e)) := by
  filter_upwards [ae_tailChangesAt_infiniteValueBit] with ω hω
  intro x hx L hL
  exact startEvent_iff_existsUnique_exactLengthEvent
    hL (hω x hx)

/--
Fixed-parameter version matching the line immediately following Lemma 14.5
in the manuscript.
-/
theorem ae_startEvent_iff_existsUnique_exactLengthEvent_fixed
    {x L : ℕ} (hx : 2 ≤ x) (hL : 1 ≤ L) :
    ∀ᵐ ω ∂infiniteRademacherMeasure,
      (StartEvent (infiniteValueBit ω) x L ↔
        ∃! e : ℕ,
          ExactLengthEvent (infiniteValueBit ω) x
            (excessRowCount L e)) := by
  filter_upwards [ae_startEvent_iff_existsUnique_exactLengthEvent]
    with ω hω
  exact hω x hx L hL

/--
Cardinal version of the almost-sure identity
`J_{x,L} = ∑ₑ K_{x,e}`, stated without choosing a decidability instance for
the start event.  On the start branch the active-excess set has cardinal one;
on its complement it has cardinal zero.
-/
theorem ae_exactExcessSet_cardinal :
    ∀ᵐ ω ∂infiniteRademacherMeasure,
      ∀ x : ℕ, 2 ≤ x → ∀ L : ℕ, 1 ≤ L →
        (StartEvent (infiniteValueBit ω) x L →
          (exactExcessSet (infiniteValueBit ω) x L).ncard = 1) ∧
        (¬ StartEvent (infiniteValueBit ω) x L →
          (exactExcessSet (infiniteValueBit ω) x L).ncard = 0) := by
  filter_upwards [ae_tailChangesAt_infiniteValueBit] with ω hω
  intro x hx L hL
  constructor
  · intro hStart
    exact ncard_exactExcessSet_of_start hL (hω x hx) hStart
  · intro hStart
    exact ncard_exactExcessSet_of_not_start hStart

end InfiniteExactLengthDecomposition
end PaperC
