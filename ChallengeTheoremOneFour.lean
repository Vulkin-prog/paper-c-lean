import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.NumberTheory.ArithmeticFunction.Misc

noncomputable section

/-!
# Paper C external-audit challenge: Theorem 1.4 and Corollary 11.3

This file gives a standalone Mathlib-only declaration boundary for the exact
finite moments and homogeneous two-start mass needed to state Paper C,
Theorem 1.4 and Corollary 11.3.  It imports no project-local module.

The two results are conditional on exactly two ordinary literature premises:
the source-shaped Evertse--Silverman abscissa bound and the source-shaped
Nicolas--Robin divisor-logarithm bound declared explicitly below.
Arratia--Goldstein--Gordon is not used for these moment and homogeneous-mass
statements.  The generalized-Pell and quadratic-order conductor consequences
are proved internally on the solution side.

The main source is `paper_C_complete_v09_en.pdf`, SHA-256
`ccef4908838fc3b428aed862937a6a3a9129fc6e378fa7368384a9ed45b05189`:
Theorem 1.4 is on printed/PDF p. 4 and Corollary 11.3 is on p. 38.
-/

open scoped BigOperators

namespace PaperCAudit

/-! ## Finite Rademacher cylinder -/

/-- The two-element field used to encode signs additively. -/
abbrev F₂ := ZMod 2

/-- Prime-exponent parity vector. -/
noncomputable def parityVec (n : ℕ) : ℕ →₀ F₂ :=
  n.factorization.mapRange (fun e : ℕ => (e : F₂)) (by simp)

/-- Bit type used by start events. -/
abbrev Bit := ZMod 2

/-- A maximal constant stretch of length at least `L` starts at `x`. -/
def StartEvent (g : ℕ → Bit) (x L : ℕ) : Prop :=
  g (x - 1) + g x = 1 ∧
    ∀ j : ℕ, j < L → g (x + j) = g x

/-- Primes at most the inclusive cutoff `M`. -/
def PrimeUpTo (M : ℕ) := {p : Fin (M + 1) // Nat.Prime p.1}

instance (M : ℕ) : Fintype (PrimeUpTo M) :=
  Subtype.fintype _

noncomputable instance (M : ℕ) : DecidableEq (PrimeUpTo M) :=
  Classical.decEq (PrimeUpTo M)

/-- Uniform cylinder sample space of independent prime bits. -/
abbrev SampleSpace (M : ℕ) := PrimeUpTo M → F₂

/-- Additive value of the random multiplicative function. -/
noncomputable def valueBit {M : ℕ} (ω : SampleSpace M) (n : ℕ) : F₂ :=
  ∑ p : PrimeUpTo M, ω p * parityVec n p.1

/-- Inclusive prime cutoff covering all observed start windows. -/
def dyadicCutoff (N L : ℕ) : ℕ :=
  2 * N + L

/-- Canonical finite cylinder for the dyadic observable. -/
abbrev DyadicSample (N L : ℕ) := SampleSpace (dyadicCutoff N L)

/-- Dyadic block `I_N={N,...,2N-1}`. -/
def dyadicBlock (N : ℕ) : Finset ℕ :=
  Finset.Ico N (2 * N)

/-- Start predicate evaluated in a finite prime cylinder. -/
noncomputable def startAt {M : ℕ} (ω : SampleSpace M) (x L : ℕ) : Prop :=
  StartEvent (valueBit ω) x L

/-- Number of starts in the dyadic block. -/
noncomputable def dyadicCount (N L : ℕ) (ω : DyadicSample N L) : ℕ := by
  classical
  exact ∑ x ∈ dyadicBlock N, if startAt ω x L then 1 else 0

namespace CriticalRunWindow

/-- Literal manuscript window `|L-log₂ N|≤C`. -/
def InRunLengthWindow (C : ℝ) (N L : ℕ) : Prop :=
  |(L : ℝ) - Real.log N / Real.log 2| ≤ C

end CriticalRunWindow

/-- Uniform big-oh with a threshold independent of `L`. -/
def UniformBigOOn
    (admissible : ℕ → ℕ → Prop) (f g : ℕ → ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ≤ K * |g N L|

/-! ## The two ordinary literature premises -/

namespace EvertseSilvermanInput

/-- Finitary assertion that a predicate has at most `M` solutions. -/
def HasAtMostSolutions
    {α : Type*} [DecidableEq α]
    (P : α → Prop) (M : ℕ) : Prop :=
  ∀ s : Finset α, (∀ z ∈ s, P z) → s.card ≤ M

/-- Shifted split product. -/
def shiftedProduct {d : ℕ} (shift : Fin d → ℤ) (X : ℤ) : ℤ :=
  ∏ r, (X + shift r)

/-- Product of pairwise root differences. -/
def pairDifferenceProduct {d : ℕ} (shift : Fin d → ℤ) : ℕ :=
  ∏ r : Fin d, ∏ s : Fin d,
    if r < s then (shift r - shift s).natAbs else 1

/-- Number of bad places in the split specialization. -/
noncomputable def badPlaceCount
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) : ℕ :=
  1 + (2 * e.natAbs * pairDifferenceProduct shift).primeFactors.card

/-- Explicit Evertse--Silverman abscissa bound. -/
noncomputable def explicitAbscissaBound
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) : ℕ :=
  7 ^ (4 + 9 * badPlaceCount shift e)

/-- Squarefreeness for a possibly negative integer. -/
def IsSquarefreeInteger (e : ℤ) : Prop :=
  Squarefree e.natAbs

/-- Split equation `Z²=e∏(X+hᵣ)`. -/
def splitQuadraticEquation
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ)
    (solution : ℤ × ℤ) : Prop :=
  solution.2 ^ 2 = e * shiftedProduct shift solution.1

/-- Predicate for a nonzero ordinate above an abscissa. -/
def nonzeroSplitQuadraticAbscissa
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) (X : ℤ) : Prop :=
  ∃ Z : ℤ, Z ≠ 0 ∧ splitQuadraticEquation shift e (X, Z)

/-- Evertse--Silverman Theorem 1(b), specialized as in Paper C Lemma 9.1.
Audit bridge: `ES86-T1b-Q-split-n2`. -/
def EvertseSilvermanAbscissaStatement : Prop :=
  ∀ {d : ℕ} (shift : Fin d → ℤ) (e : ℤ),
    3 ≤ d →
    Function.Injective shift →
    e ≠ 0 →
    IsSquarefreeInteger e →
    HasAtMostSolutions
      (nonzeroSplitQuadraticAbscissa shift e)
      (explicitAbscissaBound shift e)

end EvertseSilvermanInput

namespace PellInput

/-- Safe exact majorant used for Nicolas--Robin. -/
def nicolasRobinConstant : ℝ :=
  2 * Real.log 2

/-- Nicolas--Robin divisor-logarithm premise used in Paper C Lemma 9.2.
Audit bridge: `NR83-T1-divisor-log-bound`. -/
def NicolasRobinDivisorLogBoundStatement : Prop :=
  ∀ n : ℕ, 64 ≤ n →
    Real.log (n.divisors.card : ℝ) *
        Real.log (Real.log (n : ℝ)) ≤
      nicolasRobinConstant * Real.log (n : ℝ)

end PellInput

/-! ## Exact finite expectations and affine relation rank -/

/-- `valueBit` as a linear form in the finite prime-sign assignment.
Reference: Paper C, §2. Bridge: none. -/
noncomputable def valueLinear (M n : ℕ) :
    SampleSpace M →ₗ[F₂] F₂ where
  toFun := fun ω => valueBit ω n
  map_add' := by
    intro ω η
    simp [valueBit, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c ω
    simp [valueBit, Finset.mul_sum, mul_assoc]

/-- Uniform probability of an event on a finite Rademacher cylinder.
Reference: Paper C, §§2 and 12. Bridge: none. -/
noncomputable def uniformEventProbability {M : ℕ}
    (P : SampleSpace M → Prop) [DecidablePred P] : ℚ :=
  ((Finset.univ.filter P).card : ℚ) /
    (Fintype.card (SampleSpace M) : ℚ)

/-- Finite-cylinder probability of a start.
Reference: Paper C, §§2 and 12. Bridge: none. -/
noncomputable def startProbability (N L x : ℕ) : ℚ := by
  classical
  exact uniformEventProbability (M := dyadicCutoff N L)
    (fun ω => startAt ω x L)

/-- Exact first moment of the dyadic start count.
Reference: Paper C, Theorem 1.4, equation (1.2). Bridge: none. -/
noncomputable def dyadicExpectation (N L : ℕ) : ℚ :=
  ∑ x ∈ dyadicBlock N, startProbability N L x

/-- Exact expectation under the uniform finite-cylinder law.
Reference: Paper C, §12. Bridge: none. -/
noncomputable def uniformExpectation {M : ℕ}
    (f : SampleSpace M → ℚ) : ℚ :=
  (∑ ω : SampleSpace M, f ω) /
    (Fintype.card (SampleSpace M) : ℚ)

namespace Affine

/-- The field with two elements used for affine start systems. -/
abbrev 𝔽₂ := PaperCAudit.F₂

open scoped Classical

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

section Relations

variable {V β : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V]
variable [Fintype β] [DecidableEq β]

/-- Dot product with a fixed row vector. -/
def dotLinear (w : β → 𝔽₂) : (β → 𝔽₂) →ₗ[𝔽₂] 𝔽₂ where
  toFun y := dotProduct w y
  map_add' y z := dotProduct_add w y z
  map_smul' c y := dotProduct_smul c w y

/-- Linear functional induced by a row relation. -/
def relationFunctional (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (u : β → 𝔽₂) :
    V →ₗ[𝔽₂] 𝔽₂ :=
  (dotLinear u).comp A

/-- Transpose map whose kernel is the relation space. -/
def relationMap (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :
    (β → 𝔽₂) →ₗ[𝔽₂] (V →ₗ[𝔽₂] 𝔽₂) where
  toFun := relationFunctional A
  map_add' u v := by
    ext x
    simp [relationFunctional, dotLinear, add_dotProduct]
  map_smul' c u := by
    ext x
    simp [relationFunctional, dotLinear, smul_dotProduct]

/-- Space of homogeneous relations among the rows of `A`. -/
abbrev RelationSpace (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :=
  LinearMap.ker (relationMap A)

end Relations

section RelationRank

variable {V β : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V]
variable [Fintype β]

local instance relationSpaceFintype
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :
    Fintype (RelationSpace A) :=
  Fintype.ofFinite _

/-- Relation defect `ρ`, the dimension of the homogeneous relation space. -/
def relationRho (A : V →ₗ[𝔽₂] (β → 𝔽₂)) : ℕ :=
  Module.finrank 𝔽₂ (RelationSpace A)

end RelationRank

/-- One row of the affine system encoding a run start. -/
noncomputable def startRow (M x L : ℕ) (i : Fin L) :
    SampleSpace M →ₗ[F₂] F₂ :=
  if i.1 = 0 then
    valueLinear M (x - 1) + valueLinear M x
  else
    valueLinear M x + valueLinear M (x + i.1)

/-- Affine linear system encoding one start. -/
noncomputable def startSystem (M x L : ℕ) :
    SampleSpace M →ₗ[F₂] (Fin L → F₂) :=
  LinearMap.pi (startRow M x L)

/-- A row of the joint system of two starts. -/
def twoStartRow (M x y L : ℕ) :
    Sum (Fin L) (Fin L) → SampleSpace M →ₗ[F₂] F₂
  | Sum.inl i => startRow M x L i
  | Sum.inr i => startRow M y L i

/-- Joint affine system of two starts. -/
def twoStartSystem (M x y L : ℕ) :
    SampleSpace M →ₗ[F₂] (Sum (Fin L) (Fin L) → F₂) :=
  LinearMap.pi (twoStartRow M x y L)

end Affine

namespace RationalMassFinite

/-- Ordered pairs in the dyadic block separated by more than `L`.
Reference: Paper C, Proposition 11.2. Bridge: none. -/
def separatedDyadicPairs (N L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun pair =>
    L < Nat.dist pair.1 pair.2

end RationalMassFinite

namespace ResidualMasses

/-- A separated ordered dyadic pair. -/
abbrev SeparatedDyadicPair (N L : ℕ) :=
  {pair : ℕ × ℕ // pair ∈ RationalMassFinite.separatedDyadicPairs N L}

/-- Homogeneous relation dimension attached to a separated pair. -/
noncomputable def pairRho
    {N L : ℕ} (pair : SeparatedDyadicPair N L) : ℕ :=
  Affine.relationRho
    (Affine.twoStartSystem
      (dyadicCutoff N L) pair.1.1 pair.1.2 L)

end ResidualMasses

namespace PropositionElevenTwo

/-- Homogeneous weight `2^ρ-1` of one separated pair. -/
noncomputable def homogeneousWeight
    {N L : ℕ} (pair : ResidualMasses.SeparatedDyadicPair N L) : ℕ :=
  2 ^ ResidualMasses.pairRho pair - 1

/-- Literal finite homogeneous sum. -/
noncomputable def homogeneousMassNat
    {N L : ℕ} (_hN : 2 ≤ N) : ℕ :=
  ∑ pair : ResidualMasses.SeparatedDyadicPair N L,
    homogeneousWeight pair

/-- The paper's homogeneous mass, totalized to zero below `N=2`.
The administrative first argument is fixed to `3` in the audited results. -/
noncomputable def homogeneousMass
    (_A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (homogeneousMassNat (L := L) hN : ℝ)
  else 0

end PropositionElevenTwo

/-! ## Quantified asymptotic predicates and exact moment errors -/

/-- Uniform little-oh with a threshold independent of `L`. -/
def UniformLittleOOn
    (admissible : ℕ → ℕ → Prop) (f g : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ≤ ε * |g N L|

/-- Uniform `N^(1/2+o(1))` in reciprocal-power form. -/
def UniformHalfPowerSubpolynomialOn
    (admissible : ℕ → ℕ → Prop) (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ^ (2 * k) ≤ (N : ℝ) ^ (k + 1)

/-- Uniform `N^(-1/2+o(1))`, with one factor of `N` moved left. -/
def UniformNegativeHalfPowerSubpolynomialOn
    (admissible : ℕ → ℕ → Prop) (f : ℕ → ℕ → ℝ) : Prop :=
  UniformHalfPowerSubpolynomialOn admissible
    (fun N L => (N : ℝ) * f N L)

namespace SectionTwelveMoments

/-- Exact variance under the finite uniform law. -/
noncomputable def uniformVariance
    {M : ℕ} (f : SampleSpace M → ℚ) : ℚ :=
  uniformExpectation
    (fun ω => (f ω - uniformExpectation f) ^ 2)

/-- Exact second falling-factorial moment of the dyadic count. -/
noncomputable def dyadicSecondFactorialMoment
    (N L : ℕ) : ℚ :=
  uniformExpectation
    (fun ω : DyadicSample N L =>
      (dyadicCount N L ω : ℚ) *
        ((dyadicCount N L ω : ℚ) - 1))

/-- Exact finite variance of the dyadic count. -/
noncomputable def dyadicVariance (N L : ℕ) : ℚ :=
  uniformVariance
    (fun ω : DyadicSample N L => (dyadicCount N L ω : ℚ))

/-- Critical Poisson parameter `λ=N/2^L`. -/
noncomputable def criticalMean (N L : ℕ) : ℝ :=
  (N : ℝ) / (2 : ℝ) ^ L

/-- Error of the exact first moment from `λ`. -/
noncomputable def dyadicFirstMomentPoissonError
    (N L : ℕ) : ℝ :=
  (dyadicExpectation N L : ℝ) - criticalMean N L

/-- Error of the second falling-factorial moment from `λ²`. -/
noncomputable def dyadicSecondFactorialPoissonError
    (N L : ℕ) : ℝ :=
  (dyadicSecondFactorialMoment N L : ℝ) -
    (criticalMean N L) ^ 2

/-- Error of the variance from `λ`. -/
noncomputable def dyadicVariancePoissonError
    (N L : ℕ) : ℝ :=
  (dyadicVariance N L : ℝ) - criticalMean N L

end SectionTwelveMoments

namespace PropositionElevenThree

/-- Quantitative scale in Corollary 11.3. -/
noncomputable def quantitativeHomogeneousScale
    (c : ℝ) (N _L : ℕ) : ℝ :=
  (N : ℝ) ^ 2 *
    Real.exp
      (-c * Real.sqrt (Real.log N) /
        Real.log (Real.log N))

end PropositionElevenThree

end PaperCAudit

/-!
## Audited results

Both statements use the exact literal critical window.  `hES` and `hDivisor`
are the two and only two literature assumptions consumed by either endpoint.
-/

/-- Paper C, Theorem 1.4: first two moments, homogeneous sum, and variance. -/
theorem paper_c_theorem_one_four_moments
    {C : ℝ} (hC : 0 ≤ C)
    (hES :
      PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement) :
    PaperCAudit.UniformNegativeHalfPowerSubpolynomialOn
        (PaperCAudit.CriticalRunWindow.InRunLengthWindow C)
        PaperCAudit.SectionTwelveMoments.dyadicFirstMomentPoissonError ∧
      PaperCAudit.UniformLittleOOn
        (PaperCAudit.CriticalRunWindow.InRunLengthWindow C)
        PaperCAudit.SectionTwelveMoments.dyadicSecondFactorialPoissonError
        (fun _ _ => 1) ∧
      PaperCAudit.UniformLittleOOn
        (PaperCAudit.CriticalRunWindow.InRunLengthWindow C)
        (PaperCAudit.PropositionElevenTwo.homogeneousMass 3)
        (fun N _ => (N : ℝ) ^ 2) ∧
      PaperCAudit.UniformLittleOOn
        (PaperCAudit.CriticalRunWindow.InRunLengthWindow C)
        PaperCAudit.SectionTwelveMoments.dyadicVariancePoissonError
        (fun _ _ => 1) := by sorry

/-- Paper C, Corollary 11.3: quantitative homogeneous-sum estimate. -/
theorem paper_c_corollary_eleven_three
    {C : ℝ} (hC : 0 ≤ C)
    (hES :
      PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ c_R : ℝ, 0 < c_R ∧
      PaperCAudit.UniformBigOOn
        (PaperCAudit.CriticalRunWindow.InRunLengthWindow C)
        (PaperCAudit.PropositionElevenTwo.homogeneousMass 3)
        (PaperCAudit.PropositionElevenThree.quantitativeHomogeneousScale
          c_R) := by sorry

end
