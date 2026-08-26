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
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

/-!
# Paper C external-audit challenge: Theorem 1.2

This trusted statement module imports only Mathlib.  It exposes the three
clauses of Paper C, Theorem 1.2 through the exact finite-cylinder and infinite
source-model observables used by the formalization.  The three ordinary
literature premises are explicit theorem arguments rather than Lean axioms.

Clauses (ii) and (iii) use the formalization's source-facing
Laplace-functional characterizations.  Clause (iii) includes the separate
uniform mark-tightness assertion required for de-truncation.
-/

open scoped BigOperators ENNReal NNReal NumberField Pointwise Topology
open Filter MeasureTheory Set

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
  (2 : ℝ)⁻¹ * ∑' k : ℕ, |p k - q k|

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
  (2 : ℝ)⁻¹ * ∑' k : ℕ,
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


end SectionThirteenCouplings

namespace CriticalRunWindow

/-- Critical window `|L-log₂ N| ≤ C`.
Reference: Paper C, Theorem 1.1, p. 3. Bridge: none. Relation: exact, with
`log₂ N` written as `log N / log 2`. -/
def InRunLengthWindow (C : ℝ) (N L : ℕ) : Prop :=
  |(L : ℝ) - Real.log N / Real.log 2| ≤ C

end CriticalRunWindow

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

/-! ## Nicolas--Robin literature premise -/

namespace PellInput

/-- Safe exact majorant used for Nicolas–Robin.
Reference: J.-L. Nicolas and G. Robin, *Majorations explicites pour le
nombre de diviseurs de N*, CMB 26 (1983), Théorème 1, p. 485.
Audit bridge: `NR83-T1-divisor-log-bound`. Relation: safe value `2`, avoiding
use of the rounded printed decimal `1.5379`. -/
def nicolasRobinConstant : ℝ :=
  2 * Real.log 2

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

/-! ## Infinite source model -/

namespace InfiniteRademacher

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Infinite assignments of independent prime bits. -/
abbrev InfiniteSample := ℕ → F₂

/-- Uniform law of one Rademacher bit. -/
noncomputable def coordinateMeasure : Measure F₂ :=
  (PMF.uniformOfFintype F₂).toMeasure

/-- Probability normalization of the coordinate law. -/
noncomputable instance instIsProbabilityMeasureCoordinateMeasure :
    IsProbabilityMeasure coordinateMeasure := by
  unfold coordinateMeasure
  infer_instance

/-- Infinite product law of the prime bits. -/
noncomputable def infiniteRademacherMeasure : Measure InfiniteSample :=
  Measure.infinitePi (fun _ : ℕ => coordinateMeasure)

/-- Infinite-model parity functional. -/
noncomputable def infiniteValueBit (ω : InfiniteSample) (n : ℕ) : F₂ :=
  (parityVec n).sum fun p e => ω (Nat.primeCounting' p) * e

end InfiniteRademacher

/-! ## Deterministically masked count -/

namespace MaskedPoissonCritical

open SectionThirteenCouplings
open SectionThirteenFiniteBound

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Target rate `|A_N|2⁻ᴸ` for a deterministic mask. -/
noncomputable def maskedTargetPoissonRate
    (L : ℕ) (mask : Finset ℕ) : ℝ≥0 :=
  ⟨(mask.card : ℝ) / (2 : ℝ) ^ L, by positivity⟩

/-- Poisson law at the masked target rate. -/
noncomputable def maskedTargetPoissonLaw
    (L : ℕ) (mask : Finset ℕ) : ℕ → ℝ :=
  ProbabilityTheory.poissonPMFReal (maskedTargetPoissonRate L mask)

/-- Literal masked start count on the complete cylinder. -/
noncomputable def fullMaskedDyadicCount
    (N L : ℕ) (mask : Finset ℕ)
    (ω : SampleSpace (dyadicCutoff N L)) : ℕ :=
  ∑ x ∈ mask, if startAt ω x L then 1 else 0

/-- Law of the complete masked start count. -/
noncomputable def fullMaskedDyadicStartLaw
    (N L : ℕ) (mask : Finset ℕ) : ℕ → ℝ :=
  finiteNatLaw
    (fullUniformPMF (dyadicCutoff N L))
    (fullMaskedDyadicCount N L mask)

/-- Total variation in Theorem 1.2(i). -/
noncomputable def maskedPoissonTotalVariation
    (N L : ℕ) (mask : Finset ℕ) : ℝ :=
  natTotalVariation
    (fullMaskedDyadicStartLaw N L mask)
    (maskedTargetPoissonLaw L mask)

end MaskedPoissonCritical

/-! ## Spatial source observable -/

namespace SpatialMarkedParameters

/-- Exact critical scale `N / 2^L`. -/
def criticalSpatialScale (N L : ℕ) : ℝ :=
  (N : ℝ) / (2 : ℝ) ^ L

end SpatialMarkedParameters

namespace InfiniteLaplaceTransfer

open InfiniteRademacher

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Literal spatial Laplace functional under the infinite source model. -/
def infiniteSpatialLaplaceFunctional
    (N L : ℕ) (g : ℝ → ℝ)
    (ω : InfiniteSample) : ℝ :=
  Real.exp
    (-(∑ x ∈ dyadicBlock N,
      if StartEvent (infiniteValueBit ω) x L then
        g ((x : ℝ) / (N : ℝ))
      else 0))

/-- Spatial expectation under the literal infinite Rademacher law. -/
def infiniteSpatialLaplaceExpectation
    (N L : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∫ ω, infiniteSpatialLaplaceFunctional N L g ω
    ∂infiniteRademacherMeasure

end InfiniteLaplaceTransfer

/-! ## Complete marked source observable and mark tails -/

namespace MixedLengthAffine

/-- Bit-valued exact-run event with `q` affine rows. -/
def ExactLengthEvent (g : ℕ → F₂) (x q : ℕ) : Prop :=
  g (x - 1) + g x = 1 ∧
    (∀ j : ℕ, 0 < j → j + 1 < q → g x = g (x + j)) ∧
    g x + g (x + (q - 1)) = 1

/-- Number of affine rows attached to excess length `e`. -/
def excessRowCount (L e : ℕ) : ℕ :=
  L + e + 1

end MixedLengthAffine

namespace FullMarkedLaplaceTransfer

open InfiniteRademacher
open MixedLengthAffine

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Literal Laplace functional of the complete marked source process. -/
def infiniteFullMarkedLaplaceFunctional
    (N L : ℕ) (g : ℝ → ℕ → ℝ)
    (ω : InfiniteSample) : ℝ :=
  Real.exp
    (-(∑ x ∈ dyadicBlock N,
      ∑' e : ℕ,
        if ExactLengthEvent (infiniteValueBit ω) x
            (excessRowCount L e) then
          g ((x : ℝ) / (N : ℝ)) e
        else 0))

/-- Expectation of the complete marked Laplace functional. -/
def infiniteFullMarkedLaplaceExpectation
    (N L : ℕ) (g : ℝ → ℕ → ℝ) : ℝ :=
  ∫ ω, infiniteFullMarkedLaplaceFunctional N L g ω
    ∂infiniteRademacherMeasure

end FullMarkedLaplaceTransfer

namespace MarkedDetruncation

open InfiniteRademacher
open MixedLengthAffine

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Event that the marked process contains a mark strictly larger than `E`. -/
def infiniteMarkTailEvent (N L E : ℕ) : Set InfiniteSample :=
  {ω | ∃ x ∈ dyadicBlock N, ∃ e : ℕ, E < e ∧
    ExactLengthEvent (infiniteValueBit ω) x
      (excessRowCount L e)}

/-- Source probability that some mark exceeds `E`. -/
def infiniteMarkTailProbability (N L E : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    (infiniteMarkTailEvent N L E)).toReal

end MarkedDetruncation

/-! ## Laplace-functional endpoint predicates -/

namespace SectionFourteenClosure

open FullMarkedLaplaceTransfer
open InfiniteLaplaceTransfer
open MarkedDetruncation
open SpatialMarkedParameters

/-- A nonnegative continuous test with finite support in the mark coordinate. -/
structure CompactMarkedTest where
  cutoff : ℕ
  toFun : ℝ → ℕ → ℝ
  continuousOn : ∀ e ≤ cutoff,
    ContinuousOn (fun t ↦ toFun t e) (Set.Icc (1 : ℝ) 2)
  nonnegative : ∀ t e, 0 ≤ toFun t e
  vanishesAbove : ∀ t e, cutoff < e → toFun t e = 0

/-- Full marked PPP target written using the finite support witness. -/
def compactMarkedPPPLaplaceTarget
    (rate : ℝ) (g : CompactMarkedTest) : ℝ :=
  Real.exp
    (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
      ∑ e ∈ Finset.range (g.cutoff + 1),
        (1 / (2 : ℝ) ^ (e + 1)) *
          (1 - Real.exp (-g.toFun t e))))

/-- Laplace-functional characterization of `PPP(rate · dt)` on `[1,2)`. -/
def SpatialPPPLaplaceCharacterization
    (Lseq : ℕ → ℕ) (rate : ℝ) : Prop :=
  ∀ g : ℝ → ℝ,
    ContinuousOn g (Set.Icc (1 : ℝ) 2) →
    (∀ t, 0 ≤ g t) →
    Tendsto
      (fun N : ℕ ↦
        infiniteSpatialLaplaceExpectation N (Lseq N) g)
      atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          (1 - Real.exp (-g t))))))

/-- Laplace-functional characterization of the marked limiting PPP. -/
def MarkedPPPLaplaceCharacterization
    (Lseq : ℕ → ℕ) (rate : ℝ) : Prop :=
  ∀ g : CompactMarkedTest,
    Tendsto
      (fun N : ℕ ↦
        infiniteFullMarkedLaplaceExpectation
          N (Lseq N) g.toFun)
      atTop
      (𝓝 (compactMarkedPPPLaplaceTarget rate g))

/-- Uniform tightness of the discrete mark coordinate. -/
def MarkedMarksUniformlyTight
    (Lseq : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ E N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      infiniteMarkTailProbability N (Lseq N) E ≤ ε

end SectionFourteenClosure
end PaperCAudit

/-- Paper C, Theorem 1.2(i): uniform masked Poisson approximation. -/
theorem paper_c_theorem_one_two_i_deterministic_masks
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG :
      PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ L : ℕ, PaperCAudit.CriticalRunWindow.InRunLengthWindow C N L →
          ∀ mask : Finset ℕ, mask ⊆ PaperCAudit.dyadicBlock N →
            PaperCAudit.MaskedPoissonCritical.maskedPoissonTotalVariation
              N L mask ≤ ε := by sorry

/-- Paper C, Theorem 1.2(ii), in Laplace-functional form. -/
theorem paper_c_theorem_one_two_ii_spatial_laplace
    (hAGG :
      PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C rate : ℝ} (hC : 0 ≤ C)
    (hES :
      PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        PaperCAudit.CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hscale :
      Tendsto
        (fun N : ℕ ↦
          PaperCAudit.SpatialMarkedParameters.criticalSpatialScale N (Lseq N))
        atTop (𝓝 rate)) :
    PaperCAudit.SectionFourteenClosure.SpatialPPPLaplaceCharacterization
      Lseq rate := by sorry

/-- Paper C, Theorem 1.2(iii), marked Laplace form plus mark tightness. -/
theorem paper_c_theorem_one_two_iii_marked_laplace_and_tightness
    (hAGG :
      PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C rate : ℝ} (hC : 0 ≤ C)
    (hES :
      PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        PaperCAudit.CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hscale :
      Tendsto
        (fun N : ℕ ↦
          PaperCAudit.SpatialMarkedParameters.criticalSpatialScale N (Lseq N))
        atTop (𝓝 rate)) :
    PaperCAudit.SectionFourteenClosure.MarkedPPPLaplaceCharacterization
        Lseq rate ∧
      PaperCAudit.SectionFourteenClosure.MarkedMarksUniformlyTight Lseq := by sorry

end
