import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PaperC

noncomputable section

/-!
# Paper C external-audit solution: Theorem 1.1 on a finite cylinder

This file independently reproduces the human-readable interface of
`Challenge.lean` in the fresh `PaperCAudit` namespace, without importing the
Challenge.  It additionally imports the frozen Paper C core and closes the
audited statement by the canonical endpoint.  Comparator therefore compares
the statement together with its complete declarative closure under the exact
same global names, types, and bodies.

Presentation notes relative to the frozen English paper:

* The paper uses an infinite product of independent prime signs.  For fixed
  `N,L`, the observable is cylindrical.  Here it is evaluated on the finite
  uniform cylinder containing all primes at most `2*N+L`.  The separate
  `ChallengeTransfer.lean` target states the exact equality with the infinite
  law.
* Bits in `ZMod 2` encode signs: bit addition is multiplication of signs.
* The cylinder cutoff is deliberately generous rather than minimal; unused
  prime coordinates integrate out under the uniform law.
* The paper defines starts for `x ≥ 2` and the multiplicative function on
  positive integers.  Here `StartEvent` and `randomMultiplicativeValue` are
  totalized to `ℕ`; subtraction at `x = 0` is truncated and the
  multiplicativity lemma assumes nonzero factors.  These extra values are
  never observed in the eventual dyadic conclusion, since the restrictions
  `N ≥ 2` and `L ≥ 1` may be absorbed into `N₀`.
* Total variation is the discrete half-`ℓ¹` expression.  The paper writes the
  equivalent supremum-over-events convention.
* `UniformBigOOn` spells out `∃ K ≥ 0, ∃ N₀, ∀ N ≥ N₀, ∀ L` in the critical
  window, so the threshold is independent of `L` and may depend on `C`.
* The paper fixes `C > 0`; the library proves the harmless strengthening
  `C ≥ 0`.  An explicit `L ≥ 1` is unnecessary because the eventual critical
  window forces it.

The main result is Theorem 1.1 on printed/PDF page 3 of
`paper_C_complete_v08_en.pdf`, SHA-256
`2f7c7b9fe3522059f0eb5fb7bf7871f0c3247e30aec534b1caa63abff5c8c927`.
-/

open scoped BigOperators NNReal NumberField Pointwise

namespace PaperCAudit

/-! ## Finite Rademacher cylinder and the completely multiplicative function

Reference: Paper C, Sections 1–2.  Audit bridge: none; these are internal,
source-exact model definitions.  The additive parity representation below is
exactly the sign model used in the paper.
-/

/-- Two-element field used to encode signs additively.
Reference: Paper C, §2. Bridge: none. Relation: `0,1` encode `+1,-1`. -/
abbrev F₂ := ZMod 2

/-- Prime-exponent parity vector.
Reference: Paper C, §2. Bridge: none. Relation: exact parity-vector encoding. -/
noncomputable def parityVec (n : ℕ) : ℕ →₀ F₂ :=
  n.factorization.mapRange (fun e : ℕ => (e : F₂)) (by simp)

/-- Multiplication becomes addition of parity vectors for nonzero integers.
Reference: Paper C, §2. Bridge: none. Relation: exact multiplicative identity. -/
theorem parityVec_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    parityVec (a * b) = parityVec a + parityVec b := by
  ext p
  simp [parityVec, Nat.factorization_mul ha hb]

/-- Bit type used by start events.
Reference: Paper C, §1. Bridge: none. Relation: additive sign encoding. -/
abbrev Bit := ZMod 2

/-- A maximal constant stretch of length at least `L` starts at `x`.
Reference: Paper C, definition of `J_{x,L}`, p. 3. Bridge: none. Relation:
the first conjunct pins the left edge and the second leaves excess length free. -/
def StartEvent (g : ℕ → Bit) (x L : ℕ) : Prop :=
  g (x - 1) + g x = 1 ∧
    ∀ j : ℕ, j < L → g (x + j) = g x

/-- Primes at most the inclusive cutoff `M`.
Reference: Paper C, finite-cylinder presentation of §§2 and 13. Bridge: none.
Relation: a readable finite replacement for the corresponding coordinates of
the infinite product. -/
def PrimeUpTo (M : ℕ) := {p : Fin (M + 1) // Nat.Prime p.1}

/-- Finite enumeration of the cylinder coordinates.
Reference: Paper C, §§2 and 13. Bridge: none. Relation: administrative
finite enumeration of the exact cylinder coordinate type. -/
instance (M : ℕ) : Fintype (PrimeUpTo M) :=
  Subtype.fintype _

/-- Decidable equality for the finite cylinder coordinates.
Reference: Paper C, §§2 and 13. Bridge: none. Relation: administrative
decidable equality on the exact cylinder coordinate type. -/
noncomputable instance (M : ℕ) : DecidableEq (PrimeUpTo M) :=
  Classical.decEq (PrimeUpTo M)

/-- Uniform cylinder sample space of independent prime bits.
Reference: Paper C, §§2 and 13. Bridge: none. Relation: exact finite product. -/
abbrev SampleSpace (M : ℕ) := PrimeUpTo M → F₂

/-- Additive value of the random multiplicative function.
Reference: Paper C, §2. Bridge: none. Relation: exact prime-parity pairing. -/
noncomputable def valueBit {M : ℕ} (ω : SampleSpace M) (n : ℕ) : F₂ :=
  ∑ p : PrimeUpTo M, ω p * parityVec n p.1

/-- Complete multiplicativity in additive coordinates.
Reference: Paper C, §2. Bridge: none. Relation: exact identity. -/
theorem valueBit_mul {M a b : ℕ} (ω : SampleSpace M)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    valueBit ω (a * b) = valueBit ω a + valueBit ω b := by
  simp [valueBit, parityVec_mul ha hb, mul_add, Finset.sum_add_distrib]

/-- Character converting a bit to a sign.
Reference: Paper C, §§1–2. Bridge: none. Relation: exact `(-1)^z` map. -/
def phase (z : F₂) : ℤ :=
  if z = 0 then 1 else -1

/-- Character law needed for complete multiplicativity.
Reference: Paper C, §2. Bridge: none. Relation: exact two-element check. -/
theorem phase_add (a b : F₂) : phase (a + b) = phase a * phase b := by
  revert a b
  decide

/-- Finite-cylinder extended Rademacher function.
Reference: Paper C, pp. 1–3. Bridge: none. Relation: exact sign-valued model. -/
noncomputable def randomMultiplicativeValue {M : ℕ}
    (ω : SampleSpace M) (n : ℕ) : ℤ :=
  phase (valueBit ω n)

/-- The associated sign-valued function is completely multiplicative.
Reference: Paper C, pp. 1–3. Bridge: none. Relation: exact defining property. -/
theorem randomMultiplicativeValue_mul {M a b : ℕ} (ω : SampleSpace M)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    randomMultiplicativeValue ω (a * b) =
      randomMultiplicativeValue ω a * randomMultiplicativeValue ω b := by
  simp only [randomMultiplicativeValue, valueBit_mul ω ha hb, phase_add]

/-- Inclusive prime cutoff covering every start window in `[N,2N)`.
Reference: Paper C, finite-cylinder implementation of §§2 and 13. Bridge: none.
Relation: generous cutoff `2N+L`; unused coordinates do not alter the law. -/
def dyadicCutoff (N L : ℕ) : ℕ :=
  2 * N + L

/-- Canonical finite cylinder for the dyadic observable.
Reference: Paper C, §§2 and 13. Bridge: none. Relation: exact finite sample. -/
abbrev DyadicSample (N L : ℕ) := SampleSpace (dyadicCutoff N L)

/-- Dyadic block `I_N = {N,...,2N-1}`.
Reference: Paper C, p. 3. Bridge: none. Relation: exact. -/
def dyadicBlock (N : ℕ) : Finset ℕ :=
  Finset.Ico N (2 * N)

/-- Start predicate evaluated on a finite prime cylinder.
Reference: Paper C, `J_{x,L}`, p. 3. Bridge: none. Relation: exact bit form. -/
noncomputable def startAt {M : ℕ} (ω : SampleSpace M) (x L : ℕ) : Prop :=
  StartEvent (valueBit ω) x L

/-- Number `Z_{N,L}` of starts in the dyadic block.
Reference: Paper C, Theorem 1.1, p. 3. Bridge: none. Relation: exact count. -/
noncomputable def dyadicCount (N L : ℕ) (ω : DyadicSample N L) : ℕ := by
  classical
  exact ∑ x ∈ dyadicBlock N, if startAt ω x L then 1 else 0

/-! ## Finite law, Poisson law, and total variation

Reference: Paper C, §§12–13 and Theorem 1.1.  Audit bridge: none for the
definitions themselves.  The half-`ℓ¹` normalization is displayed explicitly.
-/

/-- Finite probability mass function.
Reference: Paper C, finite conditioning in §§12–13. Bridge: none. Relation:
exact finite probability-space representation. -/
structure FinitePMF (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_prob : ∑ a, prob a = 1

namespace FinitePMF

/-- Uniform law on a nonempty finite type.
Reference: Paper C, finite prime cylinder in §13. Bridge: none. Relation: exact. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] :
    FinitePMF α where
  prob _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := by positivity
  sum_prob := by
    classical
    simp [Fintype.card_ne_zero]

end FinitePMF

namespace SectionThirteenFiniteBound

/-- Half-`ℓ¹` total variation on mass functions on `ℕ`.
Reference: Paper C, Theorem 1.1, p. 3, and §13. Bridge: none. Relation: equal
to the paper's supremum-over-events distance for discrete probability laws. -/
noncomputable def natTotalVariation (p q : ℕ → ℝ) : ℝ :=
  ((2 : ℕ) : ℝ)⁻¹ * ∑' k : ℕ, |p k - q k|

/-- Law of a natural-valued observable on a finite probability space.
Reference: Paper C, §13. Bridge: none. Relation: exact pushforward mass. -/
noncomputable def finiteNatLaw
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → ℕ) (k : ℕ) : ℝ := by
  classical
  exact ∑ ω, if Z ω = k then μ.prob ω else 0

end SectionThirteenFiniteBound

namespace ArratiaGoldsteinGordonInput

open ProbabilityTheory

/-! The following finite probability definitions also make the first
literature premise fully explicit.  Reference: Arratia–Goldstein–Gordon,
Ann. Probab. 17 (1989), Theorem 1, p. 10.  Audit bridge:
`AGG89-T1-finite-dependency-b3-zero`.  Relation: finite indicator family,
closed graph neighborhoods, exact outside-vector independence, hence `b₃=0`,
with the conservative bound `2*(b₁+b₂)` used in Paper C Theorem 13.7,
pp. 40–41.
-/

universe u v

/-- Probability of an event under a finite mass function.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: finite-event probability used to spell out the paper's dependency-
graph specialization in Theorem 13.7, pp. 40–41. -/
noncomputable def eventProbability
    {Ω : Type u} [Fintype Ω]
    (μ : FinitePMF Ω) (event : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if event ω then μ.prob ω else 0

theorem eventProbability_nonneg
    {Ω : Type u} [Fintype Ω]
    (μ : FinitePMF Ω) (event : Ω → Prop) :
    0 ≤ eventProbability μ event := by
  classical
  unfold eventProbability
  exact Finset.sum_nonneg fun ω _ ↦ by
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl

/-- Bernoulli marginal `p_α`.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: exact finite form of the marginal entering `b₁` and `b₂` in
Paper C Theorem 13.7, pp. 40–41. -/
noncomputable def marginal
    {Ω : Type u} {ι : Type v} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (α : ι) : ℝ :=
  eventProbability μ fun ω ↦ X α ω = true

/-- Joint Bernoulli mass `p_{αβ}`.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: exact joint marginal used in the paper's `b₂` term. -/
noncomputable def jointMarginal
    {Ω : Type u} {ι : Type v} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (α β : ι) : ℝ :=
  eventProbability μ fun ω ↦ X α ω = true ∧ X β ω = true

theorem marginal_nonneg
    {Ω : Type u} {ι : Type v} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (α : ι) :
    0 ≤ marginal μ X α :=
  eventProbability_nonneg μ _

/-- Mean parameter `λ = ∑ p_α`.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: exact Poisson parameter used in Paper C Theorem 13.7. -/
noncomputable def poissonParameter
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) : ℝ :=
  ∑ α, marginal μ X α

theorem poissonParameter_nonneg
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) :
    0 ≤ poissonParameter μ X := by
  unfold poissonParameter
  exact Finset.sum_nonneg fun α _ ↦ marginal_nonneg μ X α

/-- Poisson parameter packaged as a nonnegative real.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: type-level nonnegativity packaging of the same `λ`; the paper
writes an ordinary nonnegative real. -/
noncomputable def poissonRate
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) : ℝ≥0 :=
  ⟨poissonParameter μ X, poissonParameter_nonneg μ X⟩

/-- Closed dependency neighborhood `B_α`.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: exact closed neighborhood used by Paper C Theorem 13.7. -/
noncomputable def closedNeighborhood
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (α : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun β ↦ β = α ∨ G.Adj α β

/-- Indices outside the selected dependency neighborhood.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: readable subtype presentation of the complement of `B_α`. -/
def OutsideIndex
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (α : ι) :=
  {β : ι // β ∉ closedNeighborhood G α}

/-- Event that the outside indicator vector equals a prescribed pattern.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: atom-by-atom finite formulation of independence from all indicators
outside the paper's dependency neighborhood. -/
def HasOutsidePattern
    {Ω : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → Bool) (G : SimpleGraph ι) (α : ι)
    (pattern : OutsideIndex G α → Bool) (ω : Ω) : Prop :=
  ∀ β : OutsideIndex G α, X β.1 ω = pattern β

/-- Exact independence of each indicator from the complete outside vector.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: finite-vector independence is the hypothesis that makes `b₃=0` in
the specialization consumed by Paper C Theorem 13.7. -/
def HasExactDependencyGraph
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) : Prop :=
  ∀ (α : ι) (value : Bool)
      (pattern : OutsideIndex G α → Bool),
    eventProbability μ (fun ω ↦
        X α ω = value ∧ HasOutsidePattern X G α pattern ω) =
      eventProbability μ (fun ω ↦ X α ω = value) *
        eventProbability μ (HasOutsidePattern X G α pattern)

/-- First Chen–Stein term `b₁`.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: exact finite sum denoted `b₁` in Paper C Theorem 13.7. -/
noncomputable def bOne
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) : ℝ :=
  ∑ α, ∑ β ∈ closedNeighborhood G α,
    marginal μ X α * marginal μ X β

/-- Second Chen–Stein term `b₂`.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: exact off-diagonal finite sum denoted `b₂` in Paper C
Theorem 13.7. -/
noncomputable def bTwo
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) : ℝ :=
  ∑ α, ∑ β ∈ (closedNeighborhood G α).erase α,
    jointMarginal μ X α β

/-- Natural-valued sum of the indicator family.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: Boolean-count presentation of the sum `W` used in the cited bound. -/
noncomputable def indicatorSum
    {Ω : Type u} {ι : Type v} [Fintype ι]
    (X : ι → Ω → Bool) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter fun α ↦ X α ω = true).card

/-- Law of the indicator sum.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: exact finite mass function of `W`, corresponding to the paper's
start-count law. -/
noncomputable def indicatorSumLaw
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (k : ℕ) : ℝ :=
  eventProbability μ fun ω ↦ indicatorSum X ω = k

/-- Poisson law with the matching rate.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: exact Poisson comparator with mean `λ = ∑ p_α`. -/
noncomputable def matchingPoissonLaw
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (k : ℕ) : ℝ :=
  poissonPMFReal (poissonRate μ X) k

/-- Half-`ℓ¹` distance from the indicator-sum law to its matching Poisson law.
Reference: Arratia–Goldstein–Gordon (1989), Theorem 1, p. 10.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: the explicit half-`ℓ¹` normalization corresponding to the paper's
discrete total-variation convention. -/
noncomputable def totalVariationToPoisson
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) : ℝ :=
  ((2 : ℕ) : ℝ)⁻¹ * ∑' k : ℕ,
    |indicatorSumLaw μ X k - matchingPoissonLaw μ X k|

/-- Arratia–Goldstein–Gordon literature premise.
Reference: Theorem 1, p. 10, DOI 10.1214/aop/1176991491.
Audit bridge: `AGG89-T1-finite-dependency-b3-zero`.
Relation: exact finite specialization used as Paper C Theorem 13.7,
pp. 40–41; exact outside dependence sets `b₃` to zero. -/
def ArratiaGoldsteinGordonStatement : Prop :=
  ∀ (Ω : Type) (ι : Type)
      [Fintype Ω] [Fintype ι] [DecidableEq ι]
      (μ : FinitePMF Ω) (X : ι → Ω → Bool)
      (G : SimpleGraph ι),
    HasExactDependencyGraph μ X G →
      totalVariationToPoisson μ X ≤
        2 * (bOne μ X G + bTwo μ X G)

end ArratiaGoldsteinGordonInput

namespace SectionThirteenCouplings

open ProbabilityTheory
open SectionThirteenFiniteBound

/-- Uniform PMF on the complete prime-sign cylinder.
Reference: Paper C, §13. Bridge: none. Relation: exact finite product law. -/
noncomputable def fullUniformPMF (M : ℕ) : FinitePMF (SampleSpace M) :=
  FinitePMF.uniform _

/-- Law of the complete dyadic start count.
Reference: Paper C, Theorem 1.1, p. 3, and §13. Bridge: none. Relation:
finite-cylinder law exactly transferred to the infinite model separately. -/
noncomputable def fullDyadicStartLaw (N L : ℕ) : ℕ → ℝ :=
  finiteNatLaw
    (fullUniformPMF (dyadicCutoff N L))
    (dyadicCount N L)

/-- Target rate `λ_N = N/2^L`.
Reference: Paper C, Theorem 1.1, p. 3. Bridge: none. Relation: exact. -/
noncomputable def targetPoissonRate (N L : ℕ) : ℝ≥0 :=
  ⟨(N : ℝ) / ((2 : ℕ) : ℝ) ^ L, by positivity⟩

/-- Poisson law at the target rate.
Reference: Paper C, Theorem 1.1, p. 3. Bridge: none. Relation: exact. -/
noncomputable def targetPoissonLaw (N L : ℕ) : ℕ → ℝ :=
  poissonPMFReal (targetPoissonRate N L)

end SectionThirteenCouplings

namespace CriticalRunWindow

/-- Critical window `|L-log₂ N| ≤ C`.
Reference: Paper C, Theorem 1.1, p. 3. Bridge: none. Relation: exact, with
`log₂ N` written as `log N / log 2`. -/
def InRunLengthWindow (C : ℝ) (N L : ℕ) : Prop :=
  |(L : ℝ) - Real.log N / Real.log ((2 : ℕ) : ℝ)| ≤ C

end CriticalRunWindow

/-- Uniform Big-O with all quantifiers exposed.
Reference: Paper C, convention `O_C` used in Theorem 1.1. Bridge: none.
Relation: `K,N₀` may depend on `C`, while `N₀` is uniform in admissible `L`. -/
def UniformBigOOn
    (admissible : ℕ → ℕ → Prop) (f g : ℕ → ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ≤ K * |g N L|

namespace SectionThirteenRate

/-- Rate `1/(log log N)^2`.
Reference: Paper C, (1.1), p. 3, proved in Corollary 13.10, pp. 41–42.
Bridge: none. Relation: exact displayed rate; small `N` values are irrelevant
because `UniformBigOOn` only constrains the eventual tail. -/
noncomputable def inverseLogLogSquaredRate (N _L : ℕ) : ℝ :=
  1 / (Real.log (Real.log N)) ^ 2

end SectionThirteenRate

namespace SectionThirteenCritical

open SectionThirteenCouplings SectionThirteenFiniteBound

/-- Total variation in Theorem 1.1.
Reference: Paper C, Theorem 1.1, p. 3. Bridge: none. Relation: exact
finite-cylinder law versus `Pois(N*2⁻ᴸ)`, using half-`ℓ¹`. -/
noncomputable def fullDyadicTargetPoissonTotalVariation (N L : ℕ) : ℝ :=
  natTotalVariation
    (fullDyadicStartLaw N L)
    (targetPoissonLaw N L)

end SectionThirteenCritical

/-! ## Evertse–Silverman literature premise

Reference: J.-H. Evertse and J. H. Silverman, *Uniform bounds for the
number of solutions to Y^n=f(X)*, Math. Proc. Camb. Phil. Soc. 100 (1986),
Theorem 1(b), p. 238, DOI 10.1017/S0305004100066068.
Audit bridge: `ES86-T1b-Q-split-n2`.  Relation: specialization to `K=L=ℚ`,
a split polynomial and exponent two, supplying Lemma 9.1, (9.2), pp. 27–28.
-/

namespace EvertseSilvermanInput

/-- Finitary assertion that a predicate has at most `M` solutions.
Reference: Evertse–Silverman (1986), Theorem 1(b), p. 238.
Audit bridge: `ES86-T1b-Q-split-n2`.
Relation: readable finite-cardinality form of the bound used in Paper C
Lemma 9.1, pp. 27–28. -/
def HasAtMostSolutions
    {α : Type*} [DecidableEq α]
    (P : α → Prop) (M : ℕ) : Prop :=
  ∀ s : Finset α, (∀ z ∈ s, P z) → s.card ≤ M

/-- Shifted split product.
Reference: Evertse–Silverman (1986), Theorem 1(b), p. 238.
Audit bridge: `ES86-T1b-Q-split-n2`.
Relation: specialization of the polynomial `f(X)` to the split product used in
Paper C Lemma 9.1. -/
def shiftedProduct {d : ℕ} (shift : Fin d → ℤ) (X : ℤ) : ℤ :=
  ∏ r, (X + shift r)

/-- Product of pairwise root differences.
Reference: Evertse–Silverman (1986), Theorem 1(b), p. 238.
Audit bridge: `ES86-T1b-Q-split-n2`.
Relation: exact discriminant-support factor entering the paper's bad-place
count in (9.2), pp. 27–28. -/
def pairDifferenceProduct {d : ℕ} (shift : Fin d → ℤ) : ℕ :=
  ∏ r : Fin d, ∏ s : Fin d,
    if r < s then (shift r - shift s).natAbs else 1

/-- Number of bad places in the split specialization.
Reference: Evertse–Silverman (1986), Theorem 1(b), p. 238.
Audit bridge: `ES86-T1b-Q-split-n2`.
Relation: explicit split-`ℚ`, exponent-two bad-place count used in Paper C
(9.2), pp. 27–28. -/
noncomputable def badPlaceCount
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) : ℕ :=
  1 + (2 * e.natAbs * pairDifferenceProduct shift).primeFactors.card

/-- Explicit Evertse–Silverman abscissa bound.
Reference: Evertse–Silverman (1986), Theorem 1(b), p. 238.
Audit bridge: `ES86-T1b-Q-split-n2`.
Relation: the paper's specialized `7^(4+9s)` abscissa bound in (9.2). -/
noncomputable def explicitAbscissaBound
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) : ℕ :=
  7 ^ (4 + 9 * badPlaceCount shift e)

/-- Squarefreeness for a possibly negative integer.
Reference: Evertse–Silverman (1986), Theorem 1(b), p. 238.
Audit bridge: `ES86-T1b-Q-split-n2`.
Relation: integer wrapper for the squarefree coefficient hypothesis in Paper C
Lemma 9.1. -/
def IsSquarefreeInteger (e : ℤ) : Prop :=
  Squarefree e.natAbs

/-- Split equation `Z²=e∏(X+hᵣ)`.
Reference: Evertse–Silverman (1986), Theorem 1(b), p. 238.
Audit bridge: `ES86-T1b-Q-split-n2`.
Relation: exact exponent-two split equation used in Paper C Lemma 9.1. -/
def splitQuadraticEquation
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ)
    (solution : ℤ × ℤ) : Prop :=
  solution.2 ^ 2 = e * shiftedProduct shift solution.1

/-- Predicate for a nonzero ordinate above an abscissa.
Reference: Evertse–Silverman (1986), Theorem 1(b), p. 238.
Audit bridge: `ES86-T1b-Q-split-n2`.
Relation: projects the paper's solution count to abscissae while retaining its
nonzero-ordinate restriction. -/
def nonzeroSplitQuadraticAbscissa
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) (X : ℤ) : Prop :=
  ∃ Z : ℤ, Z ≠ 0 ∧ splitQuadraticEquation shift e (X, Z)

/-- Evertse–Silverman literature premise.
Reference: Theorem 1(b), p. 238, DOI 10.1017/S0305004100066068.
Audit bridge: `ES86-T1b-Q-split-n2`.
Relation: abscissa count used by Paper C Lemma 9.1, (9.2), pp. 27–28;
the elementary factor for ordinates is proved inside Paper C. -/
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

/-! ## Historical conductor interface and Nicolas–Robin literature premise -/

namespace PellInput

/-- Integral quadratic element attached to a solution pair.
Reference: Paper C, Lemma 9.2, pp. 28–29. Bridge: none. Relation: exact. -/
def toZsqrtd (D : ℕ) (s : ℤ × ℤ) : ℤ√(D : ℤ) :=
  ⟨s.1, s.2⟩

/-- Historical data interface for descent from the maximal quadratic order.
The source-shaped factorisation was motivated by Halter--Koch; the production
proof now realizes this `Fin 4` interface internally by reduction modulo two. -/
structure QuadraticOrderConductorData (D : ℕ) (M : ℤ) where
  K : Type
  [fieldK : Field K]
  [numberFieldK : NumberField K]
  [quadraticK : Algebra.IsQuadraticExtension ℚ K]
  idealOf :
    ℤ × ℤ →
      {I : Ideal (𝓞 K) //
        I ∣ Ideal.span ({(M : 𝓞 K)} : Set (𝓞 K))}
  conductorColour : ℤ × ℤ → Fin 4
  same_principalIdeal_of_same_extension :
    ∀ s t : ℤ × ℤ,
      s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M →
      t.1 ^ 2 - (D : ℤ) * t.2 ^ 2 = M →
      conductorColour s = conductorColour t →
      idealOf s = idealOf t →
      Ideal.span ({toZsqrtd D s} : Set (ℤ√(D : ℤ))) =
        Ideal.span ({toZsqrtd D t} : Set (ℤ√(D : ℤ)))

/-- Historical conductor-fibre compatibility interface, now discharged by the
internal quadratic-order construction in `PaperC`.  It is retained here only
so the declarative audit namespace records the former boundary exactly. -/
def QuadraticOrderConductorFiberBoundStatement : Prop :=
  ∀ (D : ℕ) (M : ℤ),
    0 < D →
    Squarefree D →
    ¬ IsSquare (D : ℚ) →
    M ≠ 0 →
    Nonempty (QuadraticOrderConductorData D M)

/-- Safe exact majorant used for Nicolas–Robin.
Reference: J.-L. Nicolas and G. Robin, *Majorations explicites pour le
nombre de diviseurs de N*, CMB 26 (1983), Théorème 1, p. 485.
Audit bridge: `NR83-T1-divisor-log-bound`. Relation: safe value `2`, avoiding
use of the rounded printed decimal `1.5379`. -/
def nicolasRobinConstant : ℝ :=
  ((2 : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ)

/-- Nicolas–Robin literature premise.
Reference: Théorème 1, p. 485, DOI 10.4153/CMB-1983-078-5.
Audit bridge: `NR83-T1-divisor-log-bound`.
Relation: direct logarithmic divisor inequality above `n=64`, used in Paper C
Lemma 9.2, (9.3), pp. 28–29; all Pell-envelope consequences are proved in Lean. -/
def NicolasRobinDivisorLogBoundStatement : Prop :=
  ∀ n : ℕ, 64 ≤ n →
    Real.log (n.divisors.card : ℝ) *
        Real.log (Real.log (n : ℝ)) ≤
      nicolasRobinConstant * Real.log (n : ℝ)

end PellInput
end PaperCAudit


end

/-! ## Explicit translations to the frozen Paper C endpoint

The finite probability records in the readable AGG premise and the quadratic-
order conductor records are intentionally distinct interface structures.  The
two private lemmas below make those non-definitional record translations
explicit.  All remaining interface definitions reduce definitionally to the
frozen endpoint.
-/

noncomputable section

private theorem auditAGG_to_paperC
    (h : PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement) :
    PaperC.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement := by
  classical
  letI (p : Prop) : Decidable p := Classical.propDecidable p
  unfold PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement at h
  unfold PaperC.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement
  intro Ω ι instΩ instι instDec μ X G hdep
  let μAudit : PaperCAudit.FinitePMF Ω :=
    { prob := μ.prob
      nonneg := μ.nonneg
      sum_prob := μ.sum_prob }
  have hdepAudit :
      PaperCAudit.ArratiaGoldsteinGordonInput.HasExactDependencyGraph μAudit X G := by
    simpa [
      PaperCAudit.ArratiaGoldsteinGordonInput.HasExactDependencyGraph,
      PaperC.ArratiaGoldsteinGordonInput.HasExactDependencyGraph,
      PaperCAudit.ArratiaGoldsteinGordonInput.HasOutsidePattern,
      PaperC.ArratiaGoldsteinGordonInput.HasOutsidePattern,
      PaperCAudit.ArratiaGoldsteinGordonInput.OutsideIndex,
      PaperC.ArratiaGoldsteinGordonInput.OutsideIndex,
      PaperCAudit.ArratiaGoldsteinGordonInput.closedNeighborhood,
      PaperC.ArratiaGoldsteinGordonInput.closedNeighborhood,
      PaperCAudit.ArratiaGoldsteinGordonInput.eventProbability,
      PaperC.ArratiaGoldsteinGordonInput.eventProbability,
      μAudit] using hdep
  have hRate :
      PaperCAudit.ArratiaGoldsteinGordonInput.poissonRate μAudit X =
        PaperC.ArratiaGoldsteinGordonInput.poissonRate μ X := by
    apply Subtype.ext
    rfl
  have bound := h Ω ι μAudit X G hdepAudit
  simp only [
    PaperCAudit.ArratiaGoldsteinGordonInput.totalVariationToPoisson,
    PaperC.ArratiaGoldsteinGordonInput.totalVariationToPoisson,
    PaperCAudit.ArratiaGoldsteinGordonInput.indicatorSumLaw,
    PaperC.ArratiaGoldsteinGordonInput.indicatorSumLaw,
    PaperCAudit.ArratiaGoldsteinGordonInput.matchingPoissonLaw,
    PaperC.ArratiaGoldsteinGordonInput.matchingPoissonLaw,
    PaperCAudit.ArratiaGoldsteinGordonInput.bOne,
    PaperC.ArratiaGoldsteinGordonInput.bOne,
    PaperCAudit.ArratiaGoldsteinGordonInput.bTwo,
    PaperC.ArratiaGoldsteinGordonInput.bTwo,
    PaperCAudit.ArratiaGoldsteinGordonInput.marginal,
    PaperC.ArratiaGoldsteinGordonInput.marginal,
    PaperCAudit.ArratiaGoldsteinGordonInput.jointMarginal,
    PaperC.ArratiaGoldsteinGordonInput.jointMarginal,
    PaperCAudit.ArratiaGoldsteinGordonInput.eventProbability,
    PaperC.ArratiaGoldsteinGordonInput.eventProbability,
    PaperCAudit.ArratiaGoldsteinGordonInput.indicatorSum,
    PaperC.ArratiaGoldsteinGordonInput.indicatorSum,
    PaperCAudit.ArratiaGoldsteinGordonInput.closedNeighborhood,
    PaperC.ArratiaGoldsteinGordonInput.closedNeighborhood,
    μAudit, hRate] at bound ⊢
  exact bound

theorem paper_c_theorem_one_one_finite_cylinder
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG :
      PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement) :
    PaperCAudit.UniformBigOOn
      (PaperCAudit.CriticalRunWindow.InRunLengthWindow C)
      PaperCAudit.SectionThirteenCritical.fullDyadicTargetPoissonTotalVariation
      PaperCAudit.SectionThirteenRate.inverseLogLogSquaredRate := by
  exact
    PaperC.CorollaryThirteenTen.theorem_one_one_uniformBigO_canonical
      hC (auditAGG_to_paperC hAGG) hES hDivisor

end
