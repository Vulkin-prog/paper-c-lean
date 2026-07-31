import PaperC.Affine.TwoStartSystem
import Mathlib.Data.Nat.ModEq
import Lean.Elab.Tactic.Omega

/-!
# Residue classes attached to start vertices

A cell of a CRT certificate records a vertex offset.  This module assigns to
that offset the natural residue class of every start whose corresponding
vertex label is divisible by the selected prime.  It supplies the concrete
residue map needed to instantiate Lemma 7.1 with residual cells.
-/

namespace PaperC
namespace CRT

open Affine

/--
The residue representing the solutions of `p ∣ x + k`.

The value may equal `p` when `k % p = 0`; this is harmless because residues
in the natural CRT API are interpreted modulo `p`.
-/
def additiveStartResidue (p k : ℕ) : ℕ :=
  p - (k % p)

/-- The defining residue becomes zero after adding its offset. -/
theorem dvd_additiveStartResidue_add
    (p k : ℕ) (hp : 0 < p) :
    p ∣ additiveStartResidue p k + k := by
  let r := k % p
  have hr : r < p := Nat.mod_lt k hp
  have hk : r + p * (k / p) = k := by
    simpa [r] using Nat.mod_add_div k p
  refine ⟨k / p + 1, ?_⟩
  dsimp [additiveStartResidue]
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- A congruence to `additiveStartResidue` is exactly divisibility after adding `k`. -/
theorem modEq_additiveStartResidue_iff_dvd_add
    (p k x : ℕ) (hp : 0 < p) :
    x ≡ additiveStartResidue p k [MOD p] ↔ p ∣ x + k := by
  have hres : additiveStartResidue p k + k ≡ 0 [MOD p] :=
    (dvd_additiveStartResidue_add p k hp).modEq_zero_nat
  constructor
  · intro hx
    exact Nat.modEq_zero_iff_dvd.mp ((hx.add_right k).trans hres)
  · intro hdvd
    exact Nat.ModEq.add_right_cancel' k
      (hdvd.modEq_zero_nat.trans hres.symm)

/--
Canonical residue attached to a vertex of a complete start block.

The root has label `x - 1`, hence residue `1`; every other vertex has label
`x + (v - 1)`.
-/
def startResidue {L : ℕ} (p : ℕ) (v : Fin (L + 1)) : ℕ :=
  if v.1 = 0 then 1 else additiveStartResidue p (v.1 - 1)

/--
Concrete bridge from a residual certificate cell to a natural CRT class.
-/
theorem modEq_startResidue_iff_dvd_startCompleteVertexLabel
    {L p x : ℕ} (v : Fin (L + 1))
    (hp : 0 < p) (hx : 1 ≤ x) :
    x ≡ startResidue p v [MOD p] ↔
      p ∣ startCompleteVertexLabel x L v := by
  by_cases hv : v.1 = 0
  · simp only [startResidue, hv, if_pos,
      startCompleteVertexLabel]
    constructor
    · intro h
      exact (Nat.modEq_iff_dvd' hx).mp h.symm
    · intro h
      exact ((Nat.modEq_iff_dvd' hx).mpr h).symm
  · simp only [startResidue, hv, if_neg,
      startCompleteVertexLabel]
    exact modEq_additiveStartResidue_iff_dvd_add
      p (v.1 - 1) x hp

end CRT
end PaperC
