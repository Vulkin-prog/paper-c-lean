import PaperCPrel8.RegularTargetSaddle
import PaperCPrel8.RegularPlantPresence

/-! # From the intrinsic regular target geometry to exact arithmetic presence -/
namespace PaperC.Prel8.RegularTargetPresence
open Finset LargeOddKernel RoughKernelRegularity RegularPlantPresence
open V282.PrescribedValues V282.SignedExactMarks V282.ExactMarkedModel
open ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
noncomputable section

/-- The private primes certified by maximal-support regularity restrict to all
actual raw occurrences, as genuine coordinates of the finite prime cylinder. -/
theorem exists_private_raw {C k L E Y : ℕ} (j e : Fin k → ℕ)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : Regular (L+E+1) Y j) :
    ∃ q : Raw (L := L) e → PrimeUpTo C,
      (∀ a, Y<(q a).val.val) ∧
      (∀ a, parityVec (vertices (L := L) j e a) (q a).val.val=1) ∧
      (∀ a b, b≠a → ¬(q a).val.val∣vertices (L := L) j e b) := by
  let offset : Raw (L := L) e → Fin (L+E+1+1) := fun a ↦ ⟨a.2.val,by have := a.2.isLt; have := he a.1; omega⟩
  choose p hp hprivate using hr
  have hple (a : Raw (L := L) e) : p a.1 (offset a)≤C := by
    have hd := Nat.dvd_of_mem_primeFactors (largeOddPrimeSupport_subset_primeFactors _ _ (hp a.1 (offset a)))
    have hl := Nat.le_of_dvd (show 0<j a.1+(offset a).val by have := hj a.1; omega) hd
    have ha := (offset a).isLt
    have hc := hC a.1
    omega
  let q : Raw (L := L) e → PrimeUpTo C := fun a ↦
    ⟨⟨p a.1 (offset a),by have := hple a; omega⟩,(prime_and_large_of_mem_largeOddPrimeSupport (hp a.1 (offset a))).1⟩
  refine ⟨q,?_,?_,?_⟩
  · intro a
    exact (prime_and_large_of_mem_largeOddPrimeSupport (hp a.1 (offset a))).2
  · intro a
    have hn := (mem_largeOddPrimeSupport_iff.mp (hp a.1 (offset a))).2
    change parityVec (vertices (L := L) j e a) (q a).val.val≠0 at hn
    generalize hx : parityVec (vertices (L := L) j e a) (q a).val.val=x at hn ⊢
    fin_cases x
    · exact (hn rfl).elim
    · rfl
  · intro a b hba
    apply hprivate a.1 (offset a) b.1 (offset b)
    by_contra h
    push Not at h
    apply hba
    rcases a with ⟨i,a⟩
    rcases b with ⟨l,b⟩
    have hi : l=i := h.1
    subst l
    apply congrArg (Sigma.mk i)
    apply Fin.ext
    exact congrArg (fun x : Fin (L+E+1+1) ↦ x.val) h.2


/-- Actual regular geometry supplies every pivot premise of exact conditional
presence; no separate prime-selection or parity assumption is left. -/
theorem regular_presence {C k L E Y : ℕ} (hL : 1≤L) (j e : Fin k → ℕ) (s : Fin k → F₂)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : Regular (L+E+1) Y j) (A : SmallSample C Y → Prop)
    (hA : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w))) :
    eventProbability (FiniteConditioning.conditional (FinitePMF.uniform (SampleSpace C))
      (fun w ↦ A (restrictSmall C Y w)) hA)
      (fun w ↦ ∀ i, SignedExactMark (valueBit w) (j i+1) L (e i) (s i)) =
        ∏ i, (signedMarkRate L (e i):ℝ) := by
  obtain ⟨q,hqY,hodd,hprivate⟩ := exists_private_raw j e hj he hC hr
  exact presence_conditional hL j e s q hqY hodd hprivate A hA

end
end PaperC.Prel8.RegularTargetPresence
