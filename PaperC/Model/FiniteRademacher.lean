import PaperC.Arithmetic.ParityVector
import PaperC.Runs.Starts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Sets
import Mathlib.LinearAlgebra.Pi

/-!
# The finite cylindrical extended-Rademacher model

For every fixed collection of integer windows, only finitely many prime signs
are observed.  This module makes that finite model explicit.  It is the model
in which the affine identities and all finite-block probabilities should first
be proved.
-/

open scoped BigOperators

namespace PaperC

/-- Prime numbers represented below an inclusive cutoff `M`. -/
def PrimeUpTo (M : ℕ) := {p : Fin (M + 1) // Nat.Prime p.1}

instance (M : ℕ) : Fintype (PrimeUpTo M) :=
  Subtype.fintype _

noncomputable instance (M : ℕ) : DecidableEq (PrimeUpTo M) :=
  Classical.decEq (PrimeUpTo M)

/-- A finite assignment of independent Rademacher bits to the primes at most
`M`.  The uniform law on this type is the finite cylinder law. -/
abbrev SampleSpace (M : ℕ) := PrimeUpTo M → F₂

/-- Additive exponent of the random multiplicative value, restricted to the
prime coordinates at most `M`. -/
noncomputable def valueBit {M : ℕ} (ω : SampleSpace M) (n : ℕ) : F₂ :=
  ∑ p : PrimeUpTo M, ω p * parityVec n p.1

/-- `valueBit` is linear in the prime-sign assignment. -/
noncomputable def valueLinear (M n : ℕ) : SampleSpace M →ₗ[F₂] F₂ where
  toFun := fun ω => valueBit ω n
  map_add' := by
    intro ω η
    simp [valueBit, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c ω
    simp [valueBit, Finset.mul_sum, mul_assoc]

@[simp]
theorem valueLinear_apply {M n : ℕ} (ω : SampleSpace M) :
    valueLinear M n ω = valueBit ω n :=
  rfl

/-- Complete multiplicativity in additive coordinates. -/
theorem valueBit_mul {M a b : ℕ} (ω : SampleSpace M)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    valueBit ω (a * b) = valueBit ω a + valueBit ω b := by
  simp [valueBit, parityVec_mul ha hb, mul_add, Finset.sum_add_distrib]

/-- The character `z ↦ (-1)^z` on `F₂`. -/
def phase (z : F₂) : ℤ :=
  if z = 0 then 1 else -1

@[simp]
theorem phase_zero : phase 0 = 1 := by
  simp [phase]

theorem phase_add (a b : F₂) : phase (a + b) = phase a * phase b := by
  revert a b
  decide

/-- The finite extended-Rademacher value attached to `ω`. -/
noncomputable def randomMultiplicativeValue {M : ℕ}
    (ω : SampleSpace M) (n : ℕ) : ℤ :=
  phase (valueBit ω n)

theorem randomMultiplicativeValue_mul {M a b : ℕ} (ω : SampleSpace M)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    randomMultiplicativeValue ω (a * b) =
      randomMultiplicativeValue ω a * randomMultiplicativeValue ω b := by
  simp only [randomMultiplicativeValue, valueBit_mul ω ha hb, phase_add]

/-- The inclusive prime cutoff sufficient for all vertices used by starts in
the dyadic block `[N,2N)`. -/
def dyadicCutoff (N L : ℕ) : ℕ :=
  2 * N + L

abbrev DyadicSample (N L : ℕ) := SampleSpace (dyadicCutoff N L)

/-- The integer block `I_N = {N, ..., 2N-1}`. -/
def dyadicBlock (N : ℕ) : Finset ℕ :=
  Finset.Ico N (2 * N)

/-- Every vertex in a start window based in the dyadic block lies below the
chosen prime cutoff.  This is the finite-cylinder adequacy check used when
relating the model to the unrestricted multiplicative function. -/
theorem startWindow_le_dyadicCutoff {N L x j : ℕ}
    (hx : x ∈ dyadicBlock N) (hj : j < L) :
    x + j ≤ dyadicCutoff N L := by
  simp only [dyadicBlock, Finset.mem_Ico] at hx
  unfold dyadicCutoff
  omega

/-- Under the paper's standing assumption `N ≥ 2`, every start index in the
dyadic block is positive (indeed at least two). -/
theorem two_le_of_mem_dyadicBlock {N x : ℕ}
    (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N) :
    2 ≤ x := by
  have hx' : N ≤ x := (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).1
  exact le_trans hN hx'

/-- The start event in the finite cylinder model. -/
noncomputable def startAt {M : ℕ} (ω : SampleSpace M) (x L : ℕ) : Prop :=
  StartEvent (valueBit ω) x L

/-- Number of starts in a dyadic block for one prime-sign assignment. -/
noncomputable def dyadicCount (N L : ℕ) (ω : DyadicSample N L) : ℕ := by
  classical
  exact ∑ x ∈ dyadicBlock N, if startAt ω x L then 1 else 0

/-- Uniform probability of a decidable event on a finite cylinder, represented
as an exact rational number. -/
noncomputable def uniformEventProbability {M : ℕ}
    (P : SampleSpace M → Prop) [DecidablePred P] : ℚ :=
  ((Finset.univ.filter P).card : ℚ) /
    (Fintype.card (SampleSpace M) : ℚ)

/-- Probability that a start occurs at `x` in the prime cylinder cut off at
`dyadicCutoff N L`.

For `x ∈ dyadicBlock N`, `startWindow_le_dyadicCutoff` shows that this cylinder
contains every prime coordinate observed by the run window, so it agrees with
the unrestricted model.  Outside the covered range this remains a deliberately
truncated-cylinder definition. -/
noncomputable def startProbability (N L x : ℕ) : ℚ :=
  by
    classical
    exact uniformEventProbability (M := dyadicCutoff N L)
      (fun ω => startAt ω x L)

/-- Exact finite-cylinder expectation of the dyadic start count. -/
noncomputable def dyadicExpectation (N L : ℕ) : ℚ :=
  ∑ x ∈ dyadicBlock N, startProbability N L x

end PaperC
