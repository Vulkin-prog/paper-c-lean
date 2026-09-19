import PaperCPrel8.SignedPalmForcing
import PaperCPrel8.FiniteConditioning

/-! # Exact presence of a private-prime regular plant

The index type records raw vertex occurrences, not just their integer values.
Thus repeated vertices cannot evade the private-prime assumption. No estimate
for the target probability of such regularity is claimed here.
-/
namespace PaperC.Prel8.RegularPlantPresence
open PaperC PaperC.V282.PrescribedValues PaperC.V282.SignedExactMarks PaperC.V282.ExactMarkedModel
open PaperC.ConditionalStartProbability PaperC.ArratiaGoldsteinGordonInput PaperC.IndependentThinning
open PaperC.Prel8.HardConditionalForcing PaperC.Prel8.SignedPalmForcing PaperC.Prel8.FiniteConditioning
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {M Y L : ℕ} {T : Type*} [Fintype T] [DecidableEq T]

abbrev Raw (e : T → ℕ) := (i : T) × Fin (L+e i+2)

def vertices (j e : T → ℕ) : Raw (L := L) e → ℕ := fun a => j a.1+a.2.val

def word (e : T → ℕ) (s : T → F₂) : Raw (L := L) e → F₂ :=
  fun a => signedExactWord L (e a.1) (s a.1) a.2

/-- Private odd-valuation primes give a literal identity minor on all occurrences. -/
theorem private_basis {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hodd : ∀ a, parityVec (v a) (q a).val.val=1)
    (hprivate : ∀ a b, b ≠ a → ¬(q a).val.val ∣ v b) (a : ι) :
    valueSystem M v (Pi.single (q a) 1)=Pi.single a 1 := by
  apply valueSystem_prime_basis
  · exact hodd a
  · intro b hb
    simp [parityVec_apply,Nat.factorization_eq_zero_of_not_dvd (hprivate a b hb)]

/-- The simultaneous prescribed raw equations are exactly all requested signed marks. -/
theorem word_iff (hL : 1 ≤ L) (j e : T → ℕ) (s : T → F₂) (omega : SampleSpace M) :
    valueSystem M (vertices (L := L) j e) omega=word (L := L) e s ↔
      ∀ i, SignedExactMark (valueBit omega) (j i+1) L (e i) (s i) := by
  constructor
  · intro h i
    apply (signedWord_iff hL (s i) omega).mp
    funext a
    exact congrFun h ⟨i,a⟩
  · intro h
    funext a
    exact congrFun ((signedWord_iff hL (s a.1) omega).mpr (h a.1)) a.2

/-- G.3's exact presence factorization, under the literal private-prime geometry. -/
theorem presence_small_event (hL : 1 ≤ L) (j e : T → ℕ) (s : T → F₂)
    (q : Raw (L := L) e → PrimeUpTo M)
    (hqY : ∀ a, Y < (q a).val.val)
    (hodd : ∀ a, parityVec (vertices (L := L) j e a) (q a).val.val=1)
    (hprivate : ∀ a b, b ≠ a → ¬(q a).val.val ∣ vertices (L := L) j e b)
    (A : SmallSample M Y → Prop) :
    eventProbability (FinitePMF.uniform (SampleSpace M))
      (fun omega => A (restrictSmall M Y omega) ∧
        ∀ i, SignedExactMark (valueBit omega) (j i+1) L (e i) (s i)) =
      eventProbability (FinitePMF.uniform (SampleSpace M)) (fun omega => A (restrictSmall M Y omega))*
        ∏ i, (signedMarkRate L (e i):ℝ) := by
  have h := word_small_event_probability (vertices (L := L) j e) q
    (private_basis _ q hodd hprivate) hqY (word (L := L) e s) A
  have hc : ((Fintype.card (Raw (L := L) e → F₂):ℝ))⁻¹=∏ i, (signedMarkRate L (e i):ℝ) := by
    simp only [Fintype.card_fun,ZMod.card,Fintype.card_sigma,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_prod,
      signedMarkRate_coe,one_div,Finset.prod_inv_distrib,← Finset.prod_pow_eq_pow_sum]
  simpa only [word_iff hL,hc] using h

/-- Every positive small-prime conditioning event retains exactly the same plant probability. -/
theorem presence_conditional (hL : 1 ≤ L) (j e : T → ℕ) (s : T → F₂)
    (q : Raw (L := L) e → PrimeUpTo M)
    (hqY : ∀ a, Y < (q a).val.val)
    (hodd : ∀ a, parityVec (vertices (L := L) j e a) (q a).val.val=1)
    (hprivate : ∀ a b, b ≠ a → ¬(q a).val.val ∣ vertices (L := L) j e b)
    (A : SmallSample M Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace M)) (fun omega => A (restrictSmall M Y omega))) :
    eventProbability (conditional (FinitePMF.uniform (SampleSpace M))
      (fun omega => A (restrictSmall M Y omega)) hA)
      (fun omega => ∀ i, SignedExactMark (valueBit omega) (j i+1) L (e i) (s i)) =
      ∏ i, (signedMarkRate L (e i):ℝ) := by
  rw [probability_conditional,presence_small_event hL j e s q hqY hodd hprivate A]
  exact mul_div_cancel_left₀ _ hA.ne'

end
end PaperC.Prel8.RegularPlantPresence
