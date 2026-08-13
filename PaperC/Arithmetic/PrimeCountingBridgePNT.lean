import PaperC.Arithmetic.PrimeNumberTheoremInput

namespace PaperC.PrimeNumberTheoremInput

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

end
end PaperC.PrimeNumberTheoremInput
