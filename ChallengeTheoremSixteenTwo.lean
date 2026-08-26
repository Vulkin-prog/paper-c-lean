import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure

noncomputable section

/-!
# Paper C external-audit challenge: Theorem 16.2 and Corollary 16.4

This Mathlib-only file exposes the three canonical forms of Theorem 16.2
(finite cylinder with exact mean, finite cylinder recentered at `M / 2^L`,
and the infinite product model) together with the canonical finite-prefix law
of Corollary 16.4.  Its six ordinary hypotheses are exactly the registered
PNT, Laishram--Shorey, Nicolas--Robin, Balasubramanian--Shorey,
Arratia--Goldstein--Gordon, and Evertse--Silverman source propositions.

Reference: `paper_C_complete_v09_en.pdf`, SHA-256
`ccef4908838fc3b428aed862937a6a3a9129fc6e378fa7368384a9ed45b05189`,
Theorem 16.2 on pp. 54--55 and Corollary 16.4 on p. 55.
-/

open scoped BigOperators ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory Set

namespace PaperCAudit

/-! ## Finite and infinite Rademacher models -/

abbrev F₂ := ZMod 2

noncomputable def parityVec (n : ℕ) : ℕ →₀ F₂ :=
  n.factorization.mapRange (fun e : ℕ ↦ (e : F₂)) (by simp)

abbrev Bit := ZMod 2

def StartEvent (g : ℕ → Bit) (x L : ℕ) : Prop :=
  g (x - 1) + g x = 1 ∧
    ∀ j : ℕ, j < L → g (x + j) = g x

def PrimeUpTo (M : ℕ) := {p : Fin (M + 1) // Nat.Prime p.1}

instance (M : ℕ) : Fintype (PrimeUpTo M) :=
  Subtype.fintype _

noncomputable instance (M : ℕ) : DecidableEq (PrimeUpTo M) :=
  Classical.decEq (PrimeUpTo M)

abbrev SampleSpace (M : ℕ) := PrimeUpTo M → F₂

noncomputable def valueBit {M : ℕ} (ω : SampleSpace M) (n : ℕ) : F₂ :=
  ∑ p : PrimeUpTo M, ω p * parityVec n p.1

def dyadicCutoff (N L : ℕ) : ℕ :=
  2 * N + L

noncomputable def startAt {M : ℕ} (ω : SampleSpace M) (x L : ℕ) : Prop :=
  StartEvent (valueBit ω) x L

namespace InfiniteRademacher

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

abbrev InfiniteSample := ℕ → F₂

noncomputable def coordinateMeasure : Measure F₂ :=
  (PMF.uniformOfFintype F₂).toMeasure

noncomputable instance instIsProbabilityMeasureCoordinateMeasure :
    IsProbabilityMeasure coordinateMeasure := by
  unfold coordinateMeasure
  infer_instance

noncomputable def infiniteRademacherMeasure : Measure InfiniteSample :=
  Measure.infinitePi (fun _ : ℕ ↦ coordinateMeasure)

noncomputable def infiniteValueBit (ω : InfiniteSample) (n : ℕ) : F₂ :=
  (parityVec n).sum fun p e ↦ ω (Nat.primeCounting' p) * e

end InfiniteRademacher

/-! ## Finite laws and the AGG proposition -/

structure FinitePMF (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_prob : ∑ a, prob a = 1

namespace FinitePMF

noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] :
    FinitePMF α where
  prob _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := by positivity
  sum_prob := by
    classical
    simp [Fintype.card_ne_zero]

end FinitePMF

namespace SectionThirteenFiniteBound

noncomputable def natTotalVariation (p q : ℕ → ℝ) : ℝ :=
  ((2 : ℕ) : ℝ)⁻¹ * ∑' k : ℕ, |p k - q k|

noncomputable def finiteNatLaw
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → ℕ) (k : ℕ) : ℝ := by
  classical
  exact ∑ ω, if Z ω = k then μ.prob ω else 0

end SectionThirteenFiniteBound

namespace ArratiaGoldsteinGordonInput

universe u v

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

noncomputable def marginal
    {Ω : Type u} {ι : Type v} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (α : ι) : ℝ :=
  eventProbability μ fun ω ↦ X α ω = true

noncomputable def jointMarginal
    {Ω : Type u} {ι : Type v} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (α β : ι) : ℝ :=
  eventProbability μ fun ω ↦ X α ω = true ∧ X β ω = true

theorem marginal_nonneg
    {Ω : Type u} {ι : Type v} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (α : ι) :
    0 ≤ marginal μ X α :=
  eventProbability_nonneg μ _

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

noncomputable def poissonRate
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) : ℝ≥0 :=
  ⟨poissonParameter μ X, poissonParameter_nonneg μ X⟩

noncomputable def closedNeighborhood
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (α : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun β ↦ β = α ∨ G.Adj α β

def OutsideIndex
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (α : ι) :=
  {β : ι // β ∉ closedNeighborhood G α}

def HasOutsidePattern
    {Ω : Type u} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → Bool) (G : SimpleGraph ι) (α : ι)
    (pattern : OutsideIndex G α → Bool) (ω : Ω) : Prop :=
  ∀ β : OutsideIndex G α, X β.1 ω = pattern β

def HasExactDependencyGraph
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) : Prop :=
  ∀ (α : ι) (value : Bool) (pattern : OutsideIndex G α → Bool),
    eventProbability μ (fun ω ↦
        X α ω = value ∧ HasOutsidePattern X G α pattern ω) =
      eventProbability μ (fun ω ↦ X α ω = value) *
        eventProbability μ (HasOutsidePattern X G α pattern)

noncomputable def bOne
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) : ℝ :=
  ∑ α, ∑ β ∈ closedNeighborhood G α,
    marginal μ X α * marginal μ X β

noncomputable def bTwo
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) : ℝ :=
  ∑ α, ∑ β ∈ (closedNeighborhood G α).erase α,
    jointMarginal μ X α β

noncomputable def indicatorSum
    {Ω : Type u} {ι : Type v} [Fintype ι]
    (X : ι → Ω → Bool) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter fun α ↦ X α ω = true).card

noncomputable def indicatorSumLaw
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (k : ℕ) : ℝ :=
  eventProbability μ fun ω ↦ indicatorSum X ω = k

noncomputable def matchingPoissonLaw
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (k : ℕ) : ℝ :=
  poissonPMFReal (poissonRate μ X) k

noncomputable def totalVariationToPoisson
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) : ℝ :=
  ((2 : ℕ) : ℝ)⁻¹ * ∑' k : ℕ,
    |indicatorSumLaw μ X k - matchingPoissonLaw μ X k|

def ArratiaGoldsteinGordonStatement : Prop :=
  ∀ (Ω : Type) (ι : Type)
      [Fintype Ω] [Fintype ι] [DecidableEq ι]
      (μ : FinitePMF Ω) (X : ι → Ω → Bool)
      (G : SimpleGraph ι),
    HasExactDependencyGraph μ X G →
      totalVariationToPoisson μ X ≤
        2 * (bOne μ X G + bTwo μ X G)

end ArratiaGoldsteinGordonInput

/-! ## The other five published input propositions -/

namespace PrimesUpTo

abbrev count (H : ℕ) : ℕ :=
  Fintype.card (PrimeUpTo H)

end PrimesUpTo

namespace PrimeNumberTheoremInput

def PrimeNumberTheoremStatement : Prop :=
  Tendsto
    (fun L : ℕ ↦
      (PrimesUpTo.count L : ℝ) * Real.log (L : ℝ) / (L : ℝ))
    atTop (nhds 1)

end PrimeNumberTheoremInput

namespace LaishramShoreyInput

def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (n + i)

def exceptionCorrection (k : ℕ) : ℕ :=
  if k = 2 then 3
  else if k ≤ 6 then 2
  else if k ≤ 16 then 1
  else 0

def LaishramShoreyStatement : Prop :=
  ∀ n k : ℕ, 2 ≤ k → k < n →
    min
        (PrimesUpTo.count k + (3 * PrimesUpTo.count k) / 4 - 1 +
          exceptionCorrection k)
        (PrimesUpTo.count (2 * k) - 1) ≤
      (consecutiveProduct n k).primeFactors.card

end LaishramShoreyInput

namespace BalasubramanianShoreyInput

noncomputable def mu (k : ℕ) (θ : ℝ) : ℝ :=
  (k : ℝ) *
    (1 -
      Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ) +
      Real.log (Real.log (Real.log (k : ℝ))) / Real.log (k : ℝ) +
      θ / Real.log (k : ℝ))

def IsSmoothAt (k b : ℕ) : Prop :=
  ∀ p ∈ b.primeFactors, p ≤ k

def DenseSquareSubproduct
    (k m : ℕ) (offsets : Finset ℕ) (b y : ℕ) : Prop :=
  2 ≤ offsets.card ∧
  offsets.card ≤ k ∧
  offsets ⊆ Finset.Icc 1 k ∧
  0 < b ∧
  0 < y ∧
  (∏ d ∈ offsets, (m + d)) = b * y ^ 2 ∧
  IsSmoothAt k b

def BalasubramanianShoreyStatement : Prop :=
  ∃ θ₀ : ℝ, ∃ C₂ : ℕ,
    ∀ (k m : ℕ) (offsets : Finset ℕ) (b y : ℕ),
      27 ≤ k →
      k ^ 2 < m →
      mu k θ₀ ≤ (offsets.card : ℝ) →
      DenseSquareSubproduct k m offsets b y →
      k ≤ C₂

end BalasubramanianShoreyInput

namespace EvertseSilvermanInput

def HasAtMostSolutions
    {α : Type*} [DecidableEq α]
    (P : α → Prop) (M : ℕ) : Prop :=
  ∀ s : Finset α, (∀ z ∈ s, P z) → s.card ≤ M

def shiftedProduct {d : ℕ} (shift : Fin d → ℤ) (X : ℤ) : ℤ :=
  ∏ r, (X + shift r)

def pairDifferenceProduct {d : ℕ} (shift : Fin d → ℤ) : ℕ :=
  ∏ r : Fin d, ∏ s : Fin d,
    if r < s then (shift r - shift s).natAbs else 1

noncomputable def badPlaceCount
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) : ℕ :=
  1 + (2 * e.natAbs * pairDifferenceProduct shift).primeFactors.card

noncomputable def explicitAbscissaBound
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) : ℕ :=
  7 ^ (4 + 9 * badPlaceCount shift e)

def IsSquarefreeInteger (e : ℤ) : Prop :=
  Squarefree e.natAbs

def splitQuadraticEquation
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ)
    (solution : ℤ × ℤ) : Prop :=
  solution.2 ^ 2 = e * shiftedProduct shift solution.1

def nonzeroSplitQuadraticAbscissa
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) (X : ℤ) : Prop :=
  ∃ Z : ℤ, Z ≠ 0 ∧ splitQuadraticEquation shift e (X, Z)

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

def nicolasRobinConstant : ℝ :=
  ((2 : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ)

def NicolasRobinDivisorLogBoundStatement : Prop :=
  ∀ n : ℕ, 64 ≤ n →
    Real.log (n.divisors.card : ℝ) *
        Real.log (Real.log (n : ℝ)) ≤
      nicolasRobinConstant * Real.log (n : ℝ)

end PellInput

/-! ## Uniform asymptotics and Theorem 16.2 -/

namespace CriticalRunWindow

def InRunLengthWindow (C : ℝ) (N L : ℕ) : Prop :=
  |(L : ℝ) - Real.log N / Real.log ((2 : ℕ) : ℝ)| ≤ C

end CriticalRunWindow

def UniformLittleOOn
    (admissible : ℕ → ℕ → Prop) (f g : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ≤ ε * |g N L|

namespace TheoremSixteenTwo

open ArratiaGoldsteinGordonInput
open InfiniteRademacher
open SectionThirteenFiniteBound

def globalCylinderCutoff (M L : ℕ) : ℕ :=
  dyadicCutoff M L

def globalStartIndices (M : ℕ) : Finset ℕ :=
  Finset.Ico 2 M

noncomputable def globalStartCount
    (M L : ℕ) (ω : SampleSpace (globalCylinderCutoff M L)) : ℕ := by
  classical
  exact ∑ x ∈ globalStartIndices M,
    if startAt ω x L then 1 else 0

noncomputable def globalUniformPMF (M L : ℕ) :
    FinitePMF (SampleSpace (globalCylinderCutoff M L)) :=
  FinitePMF.uniform _

noncomputable def globalStartLaw (M L : ℕ) : ℕ → ℝ :=
  finiteNatLaw (globalUniformPMF M L) (globalStartCount M L)

noncomputable def commonCylinderStartProbability (M L x : ℕ) : ℝ :=
  eventProbability (globalUniformPMF M L) (fun ω ↦ startAt ω x L)

noncomputable def globalStartMean (M L : ℕ) : ℝ :=
  ∑ x ∈ globalStartIndices M,
    commonCylinderStartProbability M L x

noncomputable def globalStartRate (M L : ℕ) : ℝ≥0 :=
  ⟨globalStartMean M L, by
    unfold globalStartMean commonCylinderStartProbability
    exact Finset.sum_nonneg fun x _ ↦ eventProbability_nonneg _ _⟩

noncomputable def criticalScale (M L : ℕ) : ℝ :=
  (M : ℝ) / ((2 : ℕ) : ℝ) ^ L

noncomputable def globalEmptyProbability (M L : ℕ) : ℝ :=
  globalStartLaw M L 0

def TheoremSixteenTwoStatement (C : ℝ) : Prop :=
  UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (globalStartRate M L)))
      (fun _ _ ↦ 1) ∧
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦ globalStartMean M L - criticalScale M L)
      criticalScale ∧
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        globalEmptyProbability M L - Real.exp (-globalStartMean M L))
      (fun _ _ ↦ 1)

noncomputable def infiniteGlobalStartCount
    (M L : ℕ) (ω : InfiniteSample) : ℕ := by
  classical
  exact ∑ x ∈ globalStartIndices M,
    if StartEvent (infiniteValueBit ω) x L then 1 else 0

def infiniteGlobalStartCountEvent (M L k : ℕ) : Set InfiniteSample :=
  {ω | infiniteGlobalStartCount M L ω = k}

noncomputable def infiniteGlobalStartLaw (M L k : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    (infiniteGlobalStartCountEvent M L k)).toReal

noncomputable def infiniteGlobalEmptyProbability (M L : ℕ) : ℝ :=
  infiniteGlobalStartLaw M L 0

def TheoremSixteenTwoInfiniteModelStatement (C : ℝ) : Prop :=
  UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (infiniteGlobalStartLaw M L)
          (poissonPMFReal (globalStartRate M L)))
      (fun _ _ ↦ 1) ∧
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦ globalStartMean M L - criticalScale M L)
      criticalScale ∧
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        infiniteGlobalEmptyProbability M L -
          Real.exp (-globalStartMean M L))
      (fun _ _ ↦ 1)

end TheoremSixteenTwo

namespace TheoremSixteenTwoRecentered

open SectionThirteenFiniteBound TheoremSixteenTwo

noncomputable def criticalScaleRate (M L : ℕ) : ℝ≥0 :=
  ⟨criticalScale M L, by
    unfold criticalScale
    positivity⟩

def RecenteredTheoremSixteenTwoStatement (C : ℝ) : Prop :=
  UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (criticalScaleRate M L)))
      (fun _ _ ↦ 1) ∧
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        globalEmptyProbability M L - Real.exp (-criticalScale M L))
      (fun _ _ ↦ 1)

end TheoremSixteenTwoRecentered

/-! ## Corollary 16.4: the finite-prefix law -/

namespace CorollaryPrefixLaw

open InfiniteRademacher

def PrefixConstantStretch (g : ℕ → F₂) (M x L : ℕ) : Prop :=
  1 ≤ x ∧ x + L ≤ M + 1 ∧
    ∀ j : ℕ, j < L → g (x + j) = g x

def prefixHasConstantStretch (g : ℕ → F₂) (M L : ℕ) : Prop :=
  ∃ x : ℕ, PrefixConstantStretch g M x L

def prefixConstantStretchLengths (g : ℕ → F₂) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (M + 1)).filter (prefixHasConstantStretch g M)

theorem prefixConstantStretchLengths_nonempty (g : ℕ → F₂) (M : ℕ) :
    (prefixConstantStretchLengths g M).Nonempty := by
  refine ⟨0, ?_⟩
  simp only [prefixConstantStretchLengths, Finset.mem_filter,
    Finset.mem_range, Nat.zero_lt_succ, true_and]
  exact ⟨1, by simp [PrefixConstantStretch]⟩

def prefixLongestConstantStretch (g : ℕ → F₂) (M : ℕ) : ℕ :=
  (prefixConstantStretchLengths g M).max'
    (prefixConstantStretchLengths_nonempty g M)

def prefixBoundaryEvent (g : ℕ → F₂) (L : ℕ) : Prop :=
  ∀ j : ℕ, j < L → g (1 + j) = g 1

def prefixInteriorStartIndices (M L : ℕ) : Finset ℕ :=
  Finset.Ico 2 (M - L + 2)

def prefixStartCount (g : ℕ → F₂) (M L : ℕ) : ℕ := by
  classical
  exact (if prefixBoundaryEvent g L then 1 else 0) +
    ∑ x ∈ prefixInteriorStartIndices M L,
      if StartEvent g x L then 1 else 0

def infinitePrefixStartCount (M L : ℕ) (ω : InfiniteSample) : ℕ :=
  prefixStartCount (infiniteValueBit ω) M L

def infinitePrefixLongestConstantStretch (M : ℕ) (ω : InfiniteSample) : ℕ :=
  prefixLongestConstantStretch (infiniteValueBit ω) M

def infinitePrefixStartCountEvent (M L k : ℕ) : Set InfiniteSample :=
  {ω | infinitePrefixStartCount M L ω = k}

noncomputable def infinitePrefixStartLaw (M L k : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    (infinitePrefixStartCountEvent M L k)).toReal

end CorollaryPrefixLaw

namespace CorollaryPrefixLawCanonical

open CorollaryPrefixLaw InfiniteRademacher
open SectionThirteenFiniteBound
open TheoremSixteenTwo TheoremSixteenTwoRecentered

noncomputable def infinitePrefixLongestStretchBelowProbability (M L : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    {ω | infinitePrefixLongestConstantStretch M ω < L}).toReal

def CorollaryPrefixLawStatement (C : ℝ) : Prop :=
  UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (infinitePrefixStartLaw M L)
          (poissonPMFReal (criticalScaleRate M L)))
      (fun _ _ ↦ 1) ∧
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        infinitePrefixLongestStretchBelowProbability M L -
          Real.exp (-criticalScale M L))
      (fun _ _ ↦ 1)

end CorollaryPrefixLawCanonical
end PaperCAudit

/-! ## Audited declarations -/

theorem paper_c_theorem_sixteen_two_finite_cylinder
    {C : ℝ} (hC : 0 < C)
    (hPNT : PaperCAudit.PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS : PaperCAudit.LaishramShoreyInput.LaishramShoreyStatement)
    (hDivisor : PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (hBS : PaperCAudit.BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG : PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES : PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    PaperCAudit.TheoremSixteenTwo.TheoremSixteenTwoStatement C := by sorry

theorem paper_c_theorem_sixteen_two_finite_cylinder_recentered
    {C : ℝ} (hC : 0 < C)
    (hPNT : PaperCAudit.PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS : PaperCAudit.LaishramShoreyInput.LaishramShoreyStatement)
    (hDivisor : PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (hBS : PaperCAudit.BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG : PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES : PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    PaperCAudit.TheoremSixteenTwoRecentered.RecenteredTheoremSixteenTwoStatement C := by sorry

theorem paper_c_theorem_sixteen_two_infinite_model
    {C : ℝ} (hC : 0 < C)
    (hPNT : PaperCAudit.PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS : PaperCAudit.LaishramShoreyInput.LaishramShoreyStatement)
    (hDivisor : PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (hBS : PaperCAudit.BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG : PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES : PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    PaperCAudit.TheoremSixteenTwo.TheoremSixteenTwoInfiniteModelStatement C := by sorry

theorem paper_c_corollary_sixteen_four_prefix_law
    {C : ℝ} (hC : 0 < C)
    (hPNT : PaperCAudit.PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS : PaperCAudit.LaishramShoreyInput.LaishramShoreyStatement)
    (hDivisor : PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (hBS : PaperCAudit.BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG : PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES : PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    PaperCAudit.CorollaryPrefixLawCanonical.CorollaryPrefixLawStatement C := by sorry

end
