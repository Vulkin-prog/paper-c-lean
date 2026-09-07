import PaperCV282.TerminalSliceContainer
import PaperC.Diophantine.ComponentNormalization
import PaperC.Arithmetic.PrimesUpTo

/-! # Genuine lower families in the terminal value container -/
namespace PaperC.V282.TerminalContainerLowerFinite

open LargeOddKernel TerminalKernelCount ComponentNormalization PrimesUpTo
open scoped BigOperators

noncomputable section

/-- Multiplying by a positive square does not alter any large odd kernel. -/
theorem largeOddKernel_mul_square {n a : ℕ} (hn : 0<n) (ha : 0<a) (B : ℕ) :
    largeOddKernel B (n*a^2)=largeOddKernel B n := by
  unfold largeOddKernel
  congr 1
  ext p
  simp only [mem_largeOddPrimeSupport_iff,
    parityVec_mul hn.ne' (pow_ne_zero 2 ha.ne'),parityVec_pow_two,add_zero]

/-- Prime times square representations with positive square parameter are unique. -/
theorem prime_square_injective {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 0<a) (hb : 0<b) (h : p*a^2=q*b^2) : p=q ∧ a=b := by
  have h1 := squarefree_factor_unique hp.pos ha hp.squarefree (rfl : p*a^2=p*a^2)
  have h2 := squarefree_factor_unique hq.pos hb hq.squarefree h
  have hpq : p=q := h1.trans h2.symm
  rw [← hpq] at h
  have hsq : a^2=b^2 := Nat.eq_of_mul_eq_mul_left hp.pos h
  exact ⟨hpq,by nlinarith⟩

/-- An injective family of actual values, with no small/large-prime restriction on B. -/
theorem prime_square_family_card_le (B T X R A : ℕ) (hR : R≤T) (hsize : R*A^2≤X) :
    count R*A≤(boundedLargeKernelValues B T X).card := by
  classical
  let f : Fin (count R) × Fin A → {n : ℕ // n∈boundedLargeKernelValues B T X} := fun v =>
    ⟨smallPrime R v.1*(v.2.val+1)^2,mem_boundedLargeKernelValues.mpr ⟨by
      have hp := (smallPrime_prime R v.1).pos
      exact Nat.one_le_iff_ne_zero.mpr (by positivity), by
      have ha : v.2.val+1≤A := by omega
      exact (Nat.mul_le_mul (smallPrime_le R v.1) (Nat.pow_le_pow_left ha 2)).trans hsize, by
      rw [largeOddKernel_mul_square (smallPrime_prime R v.1).pos (by omega)]
      exact (largeOddKernel_le (smallPrime_prime R v.1).pos).trans ((smallPrime_le R v.1).trans hR)⟩⟩
  have hf : Function.Injective f := by
    intro v w h
    have hn := congrArg Subtype.val h
    have hh := prime_square_injective (smallPrime_prime R v.1) (smallPrime_prime R w.1)
      (by omega : 0<v.2.val+1) (by omega : 0<w.2.val+1) hn
    apply Prod.ext
    · exact smallPrime_injective R hh.1
    · apply Fin.ext
      omega
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

/-- The elementary square-root construction already attains exponent three quarters. -/
theorem sqrt_prime_family_card_le (B T X : ℕ) (hT : Nat.sqrt X≤T) :
    count (Nat.sqrt X)*Nat.sqrt (Nat.sqrt X)≤(boundedLargeKernelValues B T X).card := by
  apply prime_square_family_card_le B T X (Nat.sqrt X) (Nat.sqrt (Nat.sqrt X)) hT
  exact (Nat.mul_le_mul_left _ (Nat.sqrt_le' _)).trans (by simpa [pow_two] using Nat.sqrt_le X)

end
end PaperC.V282.TerminalContainerLowerFinite
