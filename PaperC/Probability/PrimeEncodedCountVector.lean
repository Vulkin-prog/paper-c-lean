import PaperC.Probability.ExactLengthCountVectorTransfer
import Mathlib.NumberTheory.PrimeCounting

/-!
# Prime encoding of finite count vectors

A vector in `ℕ^d` is encoded by the product of the first `d` primes raised
to its coordinates.  Unique factorization makes this encoding injective.

This elementary encoding is useful when passing from convergence of
multivariate Laplace transforms to convergence of joint atoms: constant
test coefficients `s * log(p_i)` turn the marked Laplace transform into the
Dirichlet transform of the encoded positive-integer-valued random variable.
-/

open scoped BigOperators

namespace PaperC
namespace PrimeEncodedCountVector

noncomputable section

/-- Product-of-prime-powers encoding of a finite natural-valued vector. -/
def primeCode {d : ℕ} (k : Fin d → ℕ) : ℕ :=
  ∏ e : Fin d, (Nat.nth Nat.Prime e.1) ^ k e

/-- Every prime code is a positive integer. -/
theorem primeCode_pos {d : ℕ} (k : Fin d → ℕ) :
    0 < primeCode k := by
  unfold primeCode
  exact Finset.prod_pos fun e _ ↦
    pow_pos (Nat.prime_nth_prime e.1).pos _

/-- The enumeration of the primes has no repetitions. -/
theorem nthPrime_injective :
    Function.Injective (Nat.nth Nat.Prime) := by
  intro i j h
  simpa only [Nat.primeCounting'_nth_eq] using
    congrArg Nat.primeCounting' h

/--
The exponent of the prime assigned to coordinate `e` in `primeCode k` is
literally `k e`.
-/
theorem factorization_primeCode {d : ℕ} (k : Fin d → ℕ)
    (e : Fin d) :
    (primeCode k).factorization (Nat.nth Nat.Prime e.1) = k e := by
  classical
  unfold primeCode
  rw [Nat.factorization_prod]
  · simp only [Nat.factorization_pow, Nat.Prime.factorization,
      Nat.prime_nth_prime]
    change
      Finsupp.applyAddHom (Nat.nth Nat.Prime e.1)
        (∑ x : Fin d,
          k x • Finsupp.single (Nat.nth Nat.Prime x.1) 1) = k e
    rw [map_sum
      (Finsupp.applyAddHom (Nat.nth Nat.Prime e.1) :
        (ℕ →₀ ℕ) →+ ℕ)]
    rw [Finset.sum_eq_single e]
    · simp [Finsupp.single_apply]
    · intro j _ hj
      have hprime :
          Nat.nth Nat.Prime j.1 ≠ Nat.nth Nat.Prime e.1 := by
        exact fun h ↦ hj (Fin.ext (nthPrime_injective h))
      simp [Finsupp.single_apply, hprime, hprime.symm]
    · simp
  · intro i _
    exact pow_ne_zero _ (Nat.prime_nth_prime i.1).ne_zero

/-- Unique factorization makes `primeCode` injective. -/
theorem primeCode_injective {d : ℕ} :
    Function.Injective (@primeCode d) := by
  intro k l h
  funext e
  rw [← factorization_primeCode k e, h,
    factorization_primeCode l e]

/-! ## Pushforward of a mass through an injective code -/

/--
Mass on `ℕ` obtained by extending a mass on `α` by zero along an injective
code.  The chosen preimage is harmless because all uses assume injectivity.
-/
def injectivePushforwardMass
    {α : Type*} (code : α → ℕ) (p : α → ℝ) (m : ℕ) : ℝ :=
  by
    classical
    exact if h : m ∈ Set.range code then p (Classical.choose h) else 0

theorem injectivePushforwardMass_apply
    {α : Type*} {code : α → ℕ}
    (hcode : Function.Injective code)
    (p : α → ℝ) (x : α) :
    injectivePushforwardMass code p (code x) = p x := by
  classical
  let hx : code x ∈ Set.range code := ⟨x, rfl⟩
  rw [injectivePushforwardMass, dif_pos hx]
  congr 1
  exact hcode (Classical.choose_spec hx)

theorem injectivePushforwardMass_eq_zero_of_not_mem_range
    {α : Type*} {code : α → ℕ} {p : α → ℝ} {m : ℕ}
    (hm : m ∉ Set.range code) :
    injectivePushforwardMass code p m = 0 := by
  classical
  rw [injectivePushforwardMass, dif_neg hm]

theorem injectivePushforwardMass_nonneg
    {α : Type*} {code : α → ℕ} {p : α → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (m : ℕ) :
    0 ≤ injectivePushforwardMass code p m := by
  classical
  rw [injectivePushforwardMass]
  by_cases h : m ∈ Set.range code
  · rw [dif_pos h]
    exact hp0 _
  · rw [dif_neg h]

theorem hasSum_injectivePushforwardMass
    {α : Type*} {code : α → ℕ}
    (hcode : Function.Injective code)
    {p : α → ℝ} {a : ℝ} (hp : HasSum p a) :
    HasSum (injectivePushforwardMass code p) a := by
  apply
    (hcode.hasSum_iff
      (fun m hm ↦
        injectivePushforwardMass_eq_zero_of_not_mem_range hm)).mp
  have heq :
      injectivePushforwardMass code p ∘ code = p := by
    funext x
    exact injectivePushforwardMass_apply hcode p x
  rw [heq]
  exact hp

theorem summable_injectivePushforwardMass
    {α : Type*} {code : α → ℕ}
    (hcode : Function.Injective code)
    {p : α → ℝ} (hp : Summable p) :
    Summable (injectivePushforwardMass code p) :=
  (hasSum_injectivePushforwardMass hcode hp.hasSum).summable

theorem tsum_injectivePushforwardMass_mul
    {α : Type*} {code : α → ℕ}
    (hcode : Function.Injective code)
    (p : α → ℝ) (w : ℕ → ℝ) :
    (∑' m : ℕ, injectivePushforwardMass code p m * w m) =
      ∑' x : α, p x * w (code x) := by
  let f : ℕ → ℝ :=
    fun m ↦ injectivePushforwardMass code p m * w m
  have hsupp : Function.support f ⊆ Set.range code := by
    intro m hm
    by_contra hmRange
    apply hm
    simp only [f, Function.mem_support]
    rw [injectivePushforwardMass_eq_zero_of_not_mem_range hmRange,
      zero_mul]
  have hsum := hcode.tsum_eq hsupp
  rw [← hsum]
  apply tsum_congr
  intro x
  simp only [f]
  rw [injectivePushforwardMass_apply hcode p x]

end

end PrimeEncodedCountVector
end PaperC
