import PaperC.Arithmetic.PNTSequenceLeft2

namespace PaperC.PrimeNumberTheoremInput

theorem composed_scale_apply (L : Nat) :
    ((fun x : Real => x / Real.log x) ∘
        ((↑) : Nat → Real)) L =
      (L : Real) / Real.log (L : Real) := rfl

end PaperC.PrimeNumberTheoremInput
