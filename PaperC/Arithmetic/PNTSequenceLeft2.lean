import PaperC.Arithmetic.PNTSequenceTransport2

namespace PaperC.PrimeNumberTheoremInput

open Filter

theorem composed_primeCounting_apply (L : Nat) :
    ((fun x : Real => (Nat.primeCounting ⌊x⌋₊ : Real)) ∘
        ((↑) : Nat → Real)) L =
      (Nat.primeCounting L : Real) := by
  simp only [Function.comp_apply, Nat.floor_natCast]

end PaperC.PrimeNumberTheoremInput
