import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

/-!
# Second factorial moment of a finite indicator sum

This file isolates the algebraic identity behind the second factorial-moment
calculation in Paper C.  It is deterministic: probability enters only later,
when the idempotent summands are interpreted as event indicators.
-/

open scoped BigOperators

namespace PaperC

variable {ι R : Type*} [DecidableEq ι]

/-- The second factorial power of a finite sum of idempotents is the sum of
the ordered off-diagonal products.

The result is valid in every commutative ring.  In particular, no probability
space or expectation is needed for this algebraic step. -/
theorem factorialMoment_eq_sum_offDiag [CommRing R]
    (s : Finset ι) (f : ι → R)
    (h_idem : ∀ i ∈ s, f i * f i = f i) :
    (∑ i ∈ s, f i) * ((∑ i ∈ s, f i) - 1) =
      ∑ p ∈ s.offDiag, f p.1 * f p.2 := by
  have h_square :
      (∑ i ∈ s, f i) * (∑ i ∈ s, f i) =
        ∑ p ∈ s ×ˢ s, f p.1 * f p.2 := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have h_split :
      (∑ p ∈ s ×ˢ s, f p.1 * f p.2) =
        (∑ p ∈ s.diag, f p.1 * f p.2) +
          ∑ p ∈ s.offDiag, f p.1 * f p.2 := by
    rw [← Finset.diag_union_offDiag,
      Finset.sum_union (Finset.disjoint_diag_offDiag s)]
  have h_diag :
      (∑ p ∈ s.diag, f p.1 * f p.2) = ∑ i ∈ s, f i := by
    rw [Finset.sum_diag]
    exact Finset.sum_congr rfl h_idem
  calc
    (∑ i ∈ s, f i) * ((∑ i ∈ s, f i) - 1) =
        (∑ i ∈ s, f i) * (∑ i ∈ s, f i) - ∑ i ∈ s, f i := by ring
    _ = (∑ p ∈ s ×ˢ s, f p.1 * f p.2) - ∑ i ∈ s, f i := by
      rw [h_square]
    _ = ((∑ p ∈ s.diag, f p.1 * f p.2) +
          ∑ p ∈ s.offDiag, f p.1 * f p.2) - ∑ i ∈ s, f i := by
      rw [h_split]
    _ = ∑ p ∈ s.offDiag, f p.1 * f p.2 := by
      rw [h_diag]
      ring

/-- Integer-valued specialization to indicators of propositions. -/
theorem intIndicator_factorialMoment (s : Finset ι)
    (P : ι → Prop) [DecidablePred P] :
    (∑ i ∈ s, if P i then (1 : ℤ) else 0) *
        ((∑ i ∈ s, if P i then (1 : ℤ) else 0) - 1) =
      ∑ p ∈ s.offDiag, if P p.1 ∧ P p.2 then (1 : ℤ) else 0 := by
  have h :=
    factorialMoment_eq_sum_offDiag (R := ℤ) s
      (fun i => if P i then (1 : ℤ) else 0) (by
        intro i hi
        by_cases hPi : P i <;> simp [hPi])
  simpa only [ite_mul, one_mul, zero_mul, ite_and] using h

/-- Rational-valued specialization to indicators of propositions. -/
theorem ratIndicator_factorialMoment (s : Finset ι)
    (P : ι → Prop) [DecidablePred P] :
    (∑ i ∈ s, if P i then (1 : ℚ) else 0) *
        ((∑ i ∈ s, if P i then (1 : ℚ) else 0) - 1) =
      ∑ p ∈ s.offDiag, if P p.1 ∧ P p.2 then (1 : ℚ) else 0 := by
  have h :=
    factorialMoment_eq_sum_offDiag (R := ℚ) s
      (fun i => if P i then (1 : ℚ) else 0) (by
        intro i hi
        by_cases hPi : P i <;> simp [hPi])
  simpa only [ite_mul, one_mul, zero_mul, ite_and] using h

end PaperC
