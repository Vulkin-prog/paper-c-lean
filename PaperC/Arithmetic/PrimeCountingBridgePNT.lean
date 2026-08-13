import PaperC.Arithmetic.PrimeNumberTheoremInput
import PrimeNumberTheoremAnd.Consequences

namespace PaperC.PrimeNumberTheoremInput

open Filter Asymptotics
open scoped Topology

noncomputable section

noncomputable def primeUpToEquivPrimesLE (L : ℕ) :
    PrimeUpTo L ≃ {p : ℕ // p ∈ Nat.primesLE L} where
  toFun p :=
    ⟨p.1.1, Nat.mem_primesLE.mpr
      ⟨Nat.le_of_lt_succ p.1.2, p.2⟩⟩
  invFun p :=
    ⟨⟨p.1, Nat.lt_succ_iff.mpr
      (Nat.mem_primesLE.mp p.2).1⟩,
      (Nat.mem_primesLE.mp p.2).2⟩
  left_inv p := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

theorem count_eq_primeCounting (L : ℕ) :
    PrimesUpTo.count L = Nat.primeCounting L := by
  calc
    PrimesUpTo.count L =
        Fintype.card {p : ℕ // p ∈ Nat.primesLE L} :=
      Fintype.card_congr (primeUpToEquivPrimesLE L)
    _ = (Nat.primesLE L).card := Fintype.card_coe _
    _ = Nat.primeCounting L := Nat.primesLE_card_eq_primeCounting L

theorem primeCounting_isEquivalent_nat :
    (fun L : ℕ ↦ (Nat.primeCounting L : ℝ)) ~[atTop]
      (fun L : ℕ ↦ (L : ℝ) / Real.log (L : ℝ)) := by
  simpa only [Function.comp_apply, Nat.floor_natCast] using
    pi_alt'.comp_tendsto
      (tendsto_natCast_atTop_atTop :
        Tendsto ((↑) : ℕ → ℝ) atTop atTop)

end
end PaperC.PrimeNumberTheoremInput
