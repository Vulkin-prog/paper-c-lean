import PaperC.Arithmetic.ComponentSquareClass
import PaperC.Diophantine.PellInput
import Mathlib.Tactic.Ring

/-!
# Normalization of a bounded component

This file formalizes the arithmetic normalization at the start of Lemma 9.3.
If

`P * Q = d * z²`

with all four integers positive and `d` squarefree, then the squarefree part
of `Q` is forced by `d * P`.  We choose it canonically as the product of the
primes occurring to odd order in `d * P`.  In particular it divides `d * P`,
so every polynomial bound for `d * P` transfers without loss.

The second half records the exact algebraic reductions used by the
degree-two and degree-at-least-three branches of Lemma 9.4.  The counting
inputs remain ordinary hypotheses through the named Pell and
Evertse--Silverman statements.
-/

namespace PaperC
namespace ComponentNormalization

open DefectivePredicate LargeOddKernel

/-! ## The canonical squarefree kernel -/

/--
The full squarefree kernel of `n`: the product of the primes occurring to odd
order in `n`.
-/
noncomputable def squarefreeKernel (n : ℕ) : ℕ :=
  (oddPrimeSupport n).prod id

/-- Every member of the odd support is prime. -/
theorem prime_of_mem_oddPrimeSupport'
    {n p : ℕ} (hp : p ∈ oddPrimeSupport n) :
    p.Prime :=
  LargeOddKernel.prime_of_mem_oddPrimeSupport hp

/-- The full squarefree kernel is squarefree. -/
theorem squarefree_prod_primes
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (s.prod id) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert p s hp ih =>
      have hpPrime : p.Prime :=
        hs p (Finset.mem_insert_self p s)
      have hsPrime : ∀ q ∈ s, q.Prime := by
        intro q hq
        exact hs q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hp]
      apply (Nat.squarefree_mul ?_).mpr
      · exact ⟨hpPrime.squarefree, ih hsPrime⟩
      · apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hpPrime (hsPrime q hq)).mpr
        intro hpq
        apply hp
        rwa [hpq]

/-- The full squarefree kernel is squarefree. -/
theorem squarefreeKernel_squarefree (n : ℕ) :
    Squarefree (squarefreeKernel n) := by
  rw [squarefreeKernel]
  exact squarefree_prod_primes _ fun p hp ↦
    prime_of_mem_oddPrimeSupport' hp

/-- The full squarefree kernel is always positive. -/
theorem squarefreeKernel_pos (n : ℕ) :
    0 < squarefreeKernel n := by
  rw [squarefreeKernel]
  exact Finset.prod_pos fun p hp ↦
    (prime_of_mem_oddPrimeSupport' hp).pos

/--
Canonical decomposition into the full squarefree kernel and a positive
square, for a positive integer.
-/
theorem canonical_squarefree_decomposition
    {n : ℕ} (hn : 0 < n) :
    0 < squarefreeKernel n ∧
      Squarefree (squarefreeKernel n) ∧
      0 < canonicalSquarePart n ∧
      n = squarefreeKernel n * canonicalSquarePart n ^ 2 := by
  refine ⟨squarefreeKernel_pos n, squarefreeKernel_squarefree n,
    Nat.pos_of_ne_zero (canonicalSquarePart_ne_zero hn.ne'), ?_⟩
  simpa [squarefreeKernel] using
    canonical_odd_mul_sq_decomposition hn.ne'

/-- The canonical squarefree kernel divides the integer it normalizes. -/
theorem squarefreeKernel_dvd
    {n : ℕ} (hn : 0 < n) :
    squarefreeKernel n ∣ n := by
  refine ⟨canonicalSquarePart n ^ 2, ?_⟩
  exact (canonical_squarefree_decomposition hn).2.2.2

/-- Consequently, the canonical squarefree kernel is no larger than `n`. -/
theorem squarefreeKernel_le
    {n : ℕ} (hn : 0 < n) :
    squarefreeKernel n ≤ n :=
  Nat.le_of_dvd hn (squarefreeKernel_dvd hn)

/--
The full squarefree kernel depends only on the parity vector.  This is the
canonicality principle used in Lemma 9.3.
-/
theorem squarefreeKernel_eq_of_parityVec_eq
    {m n : ℕ} (hparity : parityVec m = parityVec n) :
    squarefreeKernel m = squarefreeKernel n := by
  unfold squarefreeKernel
  congr 1
  ext p
  rw [mem_oddPrimeSupport_iff_parityVec_ne_zero,
    mem_oddPrimeSupport_iff_parityVec_ne_zero, hparity]

/--
A positive squarefree factor in a decomposition `n = e v²` is necessarily
the canonical squarefree kernel.
-/
theorem squarefree_factor_unique
    {n e v : ℕ}
    (he : 0 < e)
    (hv : 0 < v)
    (heSquarefree : Squarefree e)
    (hfactor : n = e * v ^ 2) :
    e = squarefreeKernel n := by
  have hparity :
      parityVec n = parityVec e := by
    rw [hfactor, parityVec_mul he.ne' (pow_ne_zero 2 hv.ne'),
      parityVec_pow_two, add_zero]
  have hprimeFactors :
      e.primeFactors = oddPrimeSupport n := by
    ext p
    constructor
    · intro hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpDvd : p ∣ e := Nat.dvd_of_mem_primeFactors hp
      have hpFactorization : e.factorization p = 1 :=
        Nat.factorization_eq_one_of_squarefree
          heSquarefree hpPrime hpDvd
      rw [mem_oddPrimeSupport_iff_parityVec_ne_zero, hparity,
        parityVec_apply, hpFactorization]
      decide
    · intro hp
      have hpParityN :
          parityVec n p ≠ 0 :=
        mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hp
      have hpParityE : parityVec e p ≠ 0 := by
        simpa only [hparity] using hpParityN
      exact Finsupp.support_mapRange
        (mem_oddPrimeSupport_iff_parityVec_ne_zero.mpr hpParityE)
  calc
    e = ∏ p ∈ e.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree heSquarefree).symm
    _ = ∏ p ∈ oddPrimeSupport n, p := by
      rw [hprimeFactors]
    _ = squarefreeKernel n := by
      rfl

/-- Both canonical factors are unique once positivity is imposed. -/
theorem squarefree_decomposition_unique
    {n e v : ℕ}
    (hn : 0 < n)
    (he : 0 < e)
    (hv : 0 < v)
    (heSquarefree : Squarefree e)
    (hfactor : n = e * v ^ 2) :
    e = squarefreeKernel n ∧
      v = canonicalSquarePart n := by
  have heq : e = squarefreeKernel n :=
    squarefree_factor_unique he hv heSquarefree hfactor
  have hcanonical :=
    (canonical_squarefree_decomposition hn).2.2.2
  have hsquares :
      v ^ 2 = canonicalSquarePart n ^ 2 := by
    apply mul_left_cancel₀ he.ne'
    rw [← hfactor, heq]
    exact hcanonical
  exact ⟨heq,
    Nat.pow_left_injective (by decide : 2 ≠ 0) hsquares⟩

/-! ## Lemma 9.3: exact normalization -/

/--
Parity transfer through `P * Q = d * z²`: the parity vector of `Q` is the
one of `d * P`.
-/
theorem parityVec_right_factor
    {P Q d z : ℕ}
    (hP : 0 < P)
    (hQ : 0 < Q)
    (hd : 0 < d)
    (hz : 0 < z)
    (hequation : P * Q = d * z ^ 2) :
    parityVec Q = parityVec (d * P) := by
  have hpq :
      parityVec P + parityVec Q = parityVec d := by
    calc
      parityVec P + parityVec Q =
          parityVec (P * Q) :=
        (parityVec_mul hP.ne' hQ.ne').symm
      _ = parityVec (d * z ^ 2) := by
        rw [hequation]
      _ = parityVec d := by
        rw [parityVec_mul hd.ne' (pow_ne_zero 2 hz.ne'),
          parityVec_pow_two, add_zero]
  have hdouble :
      parityVec P + parityVec P = 0 := by
    rw [← parityVec_mul hP.ne' hP.ne',
      parityVec_mul_self]
  calc
    parityVec Q =
        parityVec P + (parityVec P + parityVec Q) := by
      rw [← add_assoc, hdouble, zero_add]
    _ = parityVec P + parityVec d := by
      rw [hpq]
    _ = parityVec d + parityVec P := add_comm _ _
    _ = parityVec (d * P) :=
      (parityVec_mul hd.ne' hP.ne').symm

/--
Exact canonical form of Lemma 9.3.

The normalized factor is not merely existential: it is exactly the
squarefree kernel of `d * P`, and hence is independent of `Q` and `z`.
-/
theorem canonical_normalization
    {P Q d z : ℕ}
    (hP : 0 < P)
    (hQ : 0 < Q)
    (hd : 0 < d)
    (hz : 0 < z)
    (_hdSquarefree : Squarefree d)
    (hequation : P * Q = d * z ^ 2) :
    let e := squarefreeKernel (d * P)
    let v := canonicalSquarePart Q
    0 < e ∧
      Squarefree e ∧
      0 < v ∧
      Q = e * v ^ 2 ∧
      e ∣ d * P ∧
      e ≤ d * P := by
  dsimp
  have hdP : 0 < d * P := Nat.mul_pos hd hP
  have hkernel :
      squarefreeKernel Q = squarefreeKernel (d * P) :=
    squarefreeKernel_eq_of_parityVec_eq
      (parityVec_right_factor hP hQ hd hz hequation)
  refine ⟨squarefreeKernel_pos (d * P),
    squarefreeKernel_squarefree (d * P),
    Nat.pos_of_ne_zero (canonicalSquarePart_ne_zero hQ.ne'),
    ?_, squarefreeKernel_dvd hdP, squarefreeKernel_le hdP⟩
  calc
    Q = squarefreeKernel Q * canonicalSquarePart Q ^ 2 :=
      (canonical_squarefree_decomposition hQ).2.2.2
    _ = squarefreeKernel (d * P) *
        canonicalSquarePart Q ^ 2 := by
      rw [hkernel]

/--
Existential version matching the prose statement of Lemma 9.3, including
canonicality and the sharp elementary bound `e ≤ dP`.
-/
theorem exists_normalized_right_factor
    {P Q d z : ℕ}
    (hP : 0 < P)
    (hQ : 0 < Q)
    (hd : 0 < d)
    (hz : 0 < z)
    (hdSquarefree : Squarefree d)
    (hequation : P * Q = d * z ^ 2) :
    ∃ e v : ℕ,
      0 < e ∧
      Squarefree e ∧
      0 < v ∧
      Q = e * v ^ 2 ∧
      e = squarefreeKernel (d * P) ∧
      e ∣ d * P ∧
      e ≤ d * P := by
  refine ⟨squarefreeKernel (d * P), canonicalSquarePart Q, ?_⟩
  simpa using
    (canonical_normalization hP hQ hd hz hdSquarefree hequation)

/--
Polynomial-height transfer used after Lemma 9.3.  If `d` and `P` have
exponents `Kd` and `KP`, then the canonical normalized factor has exponent
`Kd + KP`.
-/
theorem canonical_normalization_polynomial_bound
    {N Kd KP P Q d z : ℕ}
    (hP : 0 < P)
    (hQ : 0 < Q)
    (hd : 0 < d)
    (hz : 0 < z)
    (hdSquarefree : Squarefree d)
    (hequation : P * Q = d * z ^ 2)
    (hdBound : d ≤ N ^ Kd)
    (hPBound : P ≤ N ^ KP) :
    squarefreeKernel (d * P) ≤ N ^ (Kd + KP) := by
  calc
    squarefreeKernel (d * P) ≤ d * P :=
      (canonical_normalization
        hP hQ hd hz hdSquarefree hequation).2.2.2.2.2
    _ ≤ N ^ Kd * N ^ KP :=
      Nat.mul_le_mul hdBound hPBound
    _ = N ^ (Kd + KP) := by
      rw [pow_add]

/-! ## Lemma 9.4: exact Diophantine reductions -/

/-! ### Degree one -/

/-- A single shifted factor equal to a fixed square class. -/
def oneShiftEquation
    (e j : ℕ) (solution : ℕ × ℕ) : Prop :=
  solution.1 + j = e * solution.2 ^ 2

/--
For a fixed square parameter, the degree-one equation determines the mobile
start uniquely.
-/
theorem snd_injective_on_oneShiftEquation
    {e j : ℕ} {u v : ℕ × ℕ}
    (hu : oneShiftEquation e j u)
    (hv : oneShiftEquation e j v)
    (hsnd : u.2 = v.2) :
    u = v := by
  apply Prod.ext
  · unfold oneShiftEquation at hu hv
    rw [hsnd] at hu
    omega
  · exact hsnd

/--
The square parameter of a positive degree-one solution with `y ≤ Y` is at
most `√(Y+j)`.
-/
theorem oneShiftEquation_root_le_sqrt
    {e j Y : ℕ} {solution : ℕ × ℕ}
    (he : 0 < e)
    (hsolution : oneShiftEquation e j solution)
    (hy : solution.1 ≤ Y) :
    solution.2 ≤ Nat.sqrt (Y + j) := by
  rw [Nat.le_sqrt']
  calc
    solution.2 ^ 2 ≤ e * solution.2 ^ 2 := by
      exact Nat.le_mul_of_pos_left _ he
    _ = solution.1 + j := hsolution.symm
    _ ≤ Y + j := Nat.add_le_add_right hy j

/--
Exact finite count for the degree-one branch of Lemma 9.4:
there are at most `√(Y+j)+1` pairs `(y,v)` with `y≤Y`.
-/
theorem oneShiftEquation_atMost_sqrt
    (e j Y : ℕ) (he : 0 < e) :
    EvertseSilvermanInput.HasAtMostSolutions
      (fun solution : ℕ × ℕ ↦
        oneShiftEquation e j solution ∧ solution.1 ≤ Y)
      (Nat.sqrt (Y + j) + 1) := by
  intro s hs
  let root : ℕ × ℕ → ℕ := fun solution ↦ solution.2
  have hinjective :
      ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s →
        root u = root v → u = v := by
    intro u hu v hv huv
    exact snd_injective_on_oneShiftEquation
      (hs u hu).1 (hs v hv).1 huv
  have hsubset :
      s.image root ⊆ Finset.range (Nat.sqrt (Y + j) + 1) := by
    intro z hz
    obtain ⟨solution, hsolution, rfl⟩ :=
      Finset.mem_image.mp hz
    rw [Finset.mem_range]
    change solution.2 < Nat.sqrt (Y + j) + 1
    have hroot :=
      oneShiftEquation_root_le_sqrt
        he (hs solution hsolution).1 (hs solution hsolution).2
    omega
  calc
    s.card = (s.image root).card := by
      symm
      rw [Finset.card_image_iff]
      exact hinjective
    _ ≤ (Finset.range (Nat.sqrt (Y + j) + 1)).card :=
      Finset.card_le_card hsubset
    _ = Nat.sqrt (Y + j) + 1 := Finset.card_range _

/-! ### Degree two -/

/-- The degree-two shifted-product equation. -/
def twoShiftEquation
    (j₁ j₂ : ℤ) (e : ℕ) (solution : ℤ × ℤ) : Prop :=
  (solution.1 + j₁) * (solution.1 + j₂) =
    (e : ℤ) * solution.2 ^ 2

/--
The substitution used for the degree-two branch:
`U = 2y + j₁ + j₂`, `V = 2v`.
-/
def toPellPair
    (j₁ j₂ : ℤ) (solution : ℤ × ℤ) : ℤ × ℤ :=
  (2 * solution.1 + j₁ + j₂, 2 * solution.2)

/-- The degree-two substitution is injective. -/
theorem toPellPair_injective
    (j₁ j₂ : ℤ) :
    Function.Injective (toPellPair j₁ j₂) := by
  intro u v huv
  have hfirstImage :
      (toPellPair j₁ j₂ u).1 =
        (toPellPair j₁ j₂ v).1 :=
    congrArg (fun z : ℤ × ℤ => z.1) huv
  change
    2 * u.1 + j₁ + j₂ =
      2 * v.1 + j₁ + j₂ at hfirstImage
  have hfirst : u.1 = v.1 := by
    omega
  have hsecondImage :
      (toPellPair j₁ j₂ u).2 =
        (toPellPair j₁ j₂ v).2 :=
    congrArg (fun z : ℤ × ℤ => z.2) huv
  change 2 * u.2 = 2 * v.2 at hsecondImage
  have hsecond : u.2 = v.2 := by
    omega
  exact Prod.ext_iff.mpr ⟨hfirst, hsecond⟩

/--
Exact completion of the square:

`(y+j₁)(y+j₂)=e v²`

maps injectively to

`U²-eV²=(j₁-j₂)²`.
-/
theorem twoShiftEquation_maps_to_pell
    {j₁ j₂ : ℤ} {e : ℕ} {solution : ℤ × ℤ}
    (hsolution : twoShiftEquation j₁ j₂ e solution) :
    PellInput.pellEquation
      1 e ((j₁ - j₂) ^ 2)
      (toPellPair j₁ j₂ solution) := by
  simp only [twoShiftEquation] at hsolution
  simp only [PellInput.pellEquation, toPellPair]
  push_cast
  nlinarith

/--
Exceptional squareclass `e=1`: the completed-square Pell equation factors
into a divisor equation.  This is the exact algebraic reduction used for the
elementary branch of Lemma 9.4.
-/
theorem twoShiftEquation_one_factorization
    {j₁ j₂ : ℤ} {solution : ℤ × ℤ}
    (hsolution : twoShiftEquation j₁ j₂ 1 solution) :
    let U := (toPellPair j₁ j₂ solution).1
    let V := (toPellPair j₁ j₂ solution).2
    (U - V) * (U + V) = (j₁ - j₂) ^ 2 := by
  dsimp
  have hpell :=
    twoShiftEquation_maps_to_pell hsolution
  simp only [PellInput.pellEquation] at hpell
  norm_num at hpell
  nlinarith

/--
A source box phrased so that the degree-two substitution lands exactly in
the Pell box.  This separates the algebraic reduction from later polynomial
height bookkeeping.
-/
def twoShiftPellBox
    (j₁ j₂ : ℤ) (e H : ℕ)
    (solution : ℤ × ℤ) : Prop :=
  twoShiftEquation j₁ j₂ e solution ∧
    (toPellPair j₁ j₂ solution).1.natAbs ≤ H ∧
    (toPellPair j₁ j₂ solution).2.natAbs ≤ H

/--
Any finite Pell count transfers unchanged to the original degree-two
shifted equation.
-/
theorem twoShiftPellBox_atMost
    {j₁ j₂ : ℤ} {e H : ℕ} {R : ℝ}
    (hPell :
      PellInput.HasAtMostSolutionsReal
        (PellInput.pellBox
          1 e ((j₁ - j₂) ^ 2) H)
        R) :
    PellInput.HasAtMostSolutionsReal
      (twoShiftPellBox j₁ j₂ e H)
      R := by
  intro s hs
  let f : ℤ × ℤ → ℤ × ℤ :=
    toPellPair j₁ j₂
  have hf : Function.Injective f := by
    simpa only [f] using toPellPair_injective j₁ j₂
  have himage :
      ∀ solution ∈ s.image f,
        PellInput.pellBox
          1 e ((j₁ - j₂) ^ 2) H
          solution := by
    intro solution hsolution
    obtain ⟨original, horiginal, rfl⟩ :=
      Finset.mem_image.mp hsolution
    have horiginal' := hs original horiginal
    refine ⟨twoShiftEquation_maps_to_pell horiginal'.1,
      horiginal'.2.1, horiginal'.2.2⟩
  have hcount := hPell (s.image f) himage
  simpa only [Finset.card_image_of_injective _ hf] using hcount

/--
Polynomial-box formulation of the nonsquare degree-two branch of Lemma 9.4.

The shifts are required to be distinct, the normalized factor is positive
and squarefree, and the nonsquare condition is kept explicit in exactly the
form expected by `PellPolynomialBoxStatement`.
-/
def TwoShiftPolynomialBoxStatement : Prop :=
  ∀ K : ℕ, 0 < K →
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (e : ℕ) (j₁ j₂ : ℤ),
        0 < e →
        Squarefree e →
        j₁ ≠ j₂ →
        ¬ IsSquare ((1 : ℚ) / (e : ℚ)) →
        e ≤ N ^ K →
        ((j₁ - j₂) ^ 2).natAbs ≤ N ^ K →
        PellInput.HasAtMostSolutionsReal
          (twoShiftPellBox j₁ j₂ e (N ^ K))
          (PellInput.expLogLogBound c N)

/--
The registered generalized-Pell package implies the exact degree-two
polynomial-box statement.  All changes of variables and the transfer of the
finite count are proved in Lean.
-/
theorem twoShiftPolynomialBox_of_pell
    (hPell : PellInput.PellPolynomialBoxStatement) :
    TwoShiftPolynomialBoxStatement := by
  intro K hK
  obtain ⟨c, hc, N₀, hN₀⟩ := hPell K hK
  refine ⟨c, hc, max N₀ 1, ?_⟩
  intro N hN e j₁ j₂ he heSquarefree hj
    hnonsquare heBound hdeltaBound
  have hNN₀ : N₀ ≤ N :=
    (le_max_left N₀ 1).trans hN
  have hNone : 1 ≤ N :=
    (le_max_right N₀ 1).trans hN
  have hOneBound : 1 ≤ N ^ K :=
    one_le_pow₀ hNone
  have hdeltaNe : (j₁ - j₂) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (sub_ne_zero.mpr hj)
  have hcount :=
    hN₀ N hNN₀ 1 e ((j₁ - j₂) ^ 2)
      (by omega) he (by simp) heSquarefree
      hnonsquare hdeltaNe hOneBound heBound hdeltaBound
  exact twoShiftPellBox_atMost hcount

/--
Version of the degree-two interface exposing only the primitive registered
bridge from `PellInput`.
-/
theorem twoShiftPolynomialBox_of_generalizedPell
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    TwoShiftPolynomialBoxStatement :=
  twoShiftPolynomialBox_of_pell
    (PellInput.pellPolynomialBox_of_generalizedPell hPell)

/--
The normalized equation for the degree-at-least-three branch of Lemma 9.4.
-/
def normalizedShiftedEquation
    {r : ℕ} (P d : ℕ) (shift : Fin r → ℤ)
    (solution : ℤ × ℤ) : Prop :=
  EvertseSilvermanInput.shiftedSquareEquation
    shift (squarefreeKernel (d * P) : ℤ) solution

/--
Conditional degree-at-least-three count after canonical normalization.
The sole external mathematical input is the registered
Evertse--Silverman statement.
-/
theorem normalizedShiftedEquation_atMost_of_evertseSilverman
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    {r P d : ℕ} (shift : Fin r → ℤ)
    (hr : 3 ≤ r)
    (hshift : Function.Injective shift)
    (_hP : 0 < P)
    (_hd : 0 < d) :
    EvertseSilvermanInput.HasAtMostSolutions
      (normalizedShiftedEquation P d shift)
      (r +
        EvertseSilvermanInput.explicitBound
          shift (squarefreeKernel (d * P) : ℤ)) := by
  have hkernelPos :
      0 < squarefreeKernel (d * P) :=
    squarefreeKernel_pos (d * P)
  apply
    EvertseSilvermanInput.shiftedSquareEquation_atMost_of_evertseSilverman
      hES shift (squarefreeKernel (d * P) : ℤ)
      hr hshift
  · exact_mod_cast hkernelPos.ne'
  · simpa [EvertseSilvermanInput.IsSquarefreeInteger] using
      squarefreeKernel_squarefree (d * P)

end ComponentNormalization
end PaperC
