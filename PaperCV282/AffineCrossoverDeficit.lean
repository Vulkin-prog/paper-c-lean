import PaperCV282.AffineCrossoverErrorsAffine

/-! # A proof-independent sequence of affine border deficits

At the finitely many initial indices where L exceeds the exposed cutoff,
the definition uses the border coordinates that are present. Whenever
L is inside the cutoff it is exactly pi(L) minus the border overlap.
-/
namespace PaperC.V282.AffineCrossoverDeficit

open Affine InfiniteRademacher AffineBorderCylinders AffineCrossoverCylinder
open AffineCrossoverErrorsAffine
open scoped NNReal

noncomputable section
local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {Y L : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]

def borderDeficitAt (G : SampleSpace Y→ₗ[F₂]W) (L : ℕ) : ℕ :=
  borderDeficit G (Nat.min_le_right L Y)

theorem borderDeficitAt_eq (G : SampleSpace Y→ₗ[F₂]W) (hLY : L≤Y) :
    borderDeficitAt G L=borderDeficit G hLY := by
  simp only [borderDeficitAt,Nat.min_eq_left hLY]

theorem borderDeficitAt_formula (G : SampleSpace Y→ₗ[F₂]W) (hLY : L≤Y) :
    borderDeficitAt G L=Nat.primeCounting L-borderOverlap G hLY := by
  rw [borderDeficitAt_eq G hLY]
  rfl

/-- Exact equality with the true conditional probability, not an asymptotic rate definition. -/
theorem conditionalBorderRate_eq_deficit (G : SampleSpace Y→ₗ[F₂]W) (b : W) (hLY : L≤Y)
    (hstack : Compatible (G.prod (borderProjection hLY)) (b,0)) :
    conditionalBorderRate (affineCylinder G b) L=((2 : ℝ≥0)⁻¹)^borderDeficitAt G L := by
  rw [conditionalBorderRate_eq G b hLY hstack,borderDeficitAt_eq G hLY]
  simp only [borderRate,one_div,inv_pow]

end
end PaperC.V282.AffineCrossoverDeficit
