import PaperCPrel8.RoughKernelAllocation

/-! # Private-pivot regularity and the deterministic hosting obstruction

Raw occurrences retain both the block and offset. Repeated vertices therefore
cannot masquerade as one occurrence in the private-prime condition.
-/
namespace PaperC.Prel8.RoughKernelRegularity
open Finset LargeOddKernel
noncomputable section

/-- Every raw occurrence has a large odd prime private to that occurrence. -/
def Regular {k : ℕ} (Q Y : ℕ) (J : Fin k → ℕ) : Prop :=
  ∀ i : Fin k, ∀ a : Fin (Q+1), ∃ p ∈ largeOddPrimeSupport Y (J i+a.val),
    ∀ l : Fin k, ∀ b : Fin (Q+1), l ≠ i ∨ b ≠ a → ¬ p ∣ J l+b.val

/-- A prime larger than the diameter cannot divide two different vertices of one block. -/
theorem private_in_block (j Q p : ℕ) (hp : Q < p) (a b : Fin (Q+1))
    (ha : p ∣ j+a.val) (hb : p ∣ j+b.val) : a = b := by
  have h := Nat.ModEq.add_left_cancel' j (ha.modEq_zero_nat.trans hb.modEq_zero_nat.symm)
  apply Fin.ext
  exact h.eq_of_lt_of_lt (by have := a.isLt; omega) (by have := b.isLt; omega)

/-- One support with nonempty rough kernels is automatically private-pivot regular. -/
theorem single_regular (j Q Y : ℕ) (hY : Q < Y)
    (hk : ∀ a : Fin (Q+1), 1 < largeOddKernel Y (j+a.val)) :
    Regular Q Y (fun _ : Fin 1 ↦ j) := by
  intro i a
  have hs : (largeOddPrimeSupport Y (j+a.val)).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    have := hk a
    simp [largeOddKernel,he] at this
  obtain ⟨p,hp⟩ := hs
  refine ⟨p,hp,?_⟩
  intro l b hne hdiv
  have ha := Nat.dvd_of_mem_primeFactors (largeOddPrimeSupport_subset_primeFactors Y (j+a.val) hp)
  have hlarge := (prime_and_large_of_mem_largeOddPrimeSupport hp).2
  have hab := private_in_block j Q p (by omega) a b ha hdiv
  rcases hne with hli | hba
  · exact hli (Subsingleton.elim _ _)
  · exact hba hab.symm

/-- Failure of regularity forces every rough prime at some source occurrence into another block. -/
theorem failure_hosted {k : ℕ} (Q Y : ℕ) (J : Fin k → ℕ) (hY : Q < Y)
    (hbad : ¬Regular Q Y J) :
    ∃ i : Fin k, ∃ a : Fin (Q+1), ∀ p ∈ largeOddPrimeSupport Y (J i+a.val),
      ∃ l : Fin k, l ≠ i ∧ ∃ b : Fin (Q+1), p ∣ J l+b.val := by
  classical
  unfold Regular at hbad
  push Not at hbad
  obtain ⟨i,a,h⟩ := hbad
  refine ⟨i,a,?_⟩
  intro p hp
  obtain ⟨l,b,hne,hdiv⟩ := h p hp
  refine ⟨l,?_,b,hdiv⟩
  intro he
  subst l
  have ha := Nat.dvd_of_mem_primeFactors (largeOddPrimeSupport_subset_primeFactors Y (J i+a.val) hp)
  have hlarge := (prime_and_large_of_mem_largeOddPrimeSupport hp).2
  have hab := private_in_block (J i) Q p (by omega) a b ha hdiv
  exact hne.resolve_left (not_not.mpr rfl) hab.symm

end
end PaperC.Prel8.RoughKernelRegularity
