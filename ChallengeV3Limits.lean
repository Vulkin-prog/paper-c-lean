import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Int.AbsoluteValue
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Multiset.Interval
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Dist
import Mathlib.InformationTheory.Hamming
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Topology.Instances.ZMod

/-!
# Paper C V3PREL: threshold staircase, Poisson--Gaussian bridge, D.1 and D.4

This autonomous statement boundary imports only Mathlib. All source laws,
conditioning events and analytic literature arguments are explicit. The
joint limit is weak convergence of the actual source probability laws.
D.4 is represented by its whole locally finite process and complete compact
test Laplace functional; no separate vague-topology type is hidden here.
The exact declaration list and fidelity boundary accompany the configuration.
-/
noncomputable section
namespace PaperCV3Audit
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators NNReal ENNReal

abbrev F₂ := ZMod 2
local instance instMeasurableSpaceF2 : MeasurableSpace F₂ := ⊤
abbrev InfiniteSample := ℕ → F₂
def coordinateMeasure : Measure F₂ := (PMF.uniformOfFintype F₂).toMeasure
instance instProbabilityCoordinate : IsProbabilityMeasure coordinateMeasure := by
  unfold coordinateMeasure; infer_instance
def infiniteRademacherMeasure : Measure InfiniteSample :=
  Measure.infinitePi (fun _ : ℕ => coordinateMeasure)
instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure; infer_instance
def parityVec (n : ℕ) : ℕ →₀ F₂ :=
  n.factorization.mapRange (fun e : ℕ => (e : F₂)) (by simp)
def infiniteValueBit (omega : InfiniteSample) (n : ℕ) : F₂ :=
  (parityVec n).sum (fun p e => omega (Nat.primeCounting' p) * e)
def StartEvent (g : ℕ → F₂) (x L : ℕ) : Prop :=
  g (x-1) + g x = 1 ∧ ∀ j : ℕ, j<L → g (x+j)=g x
def dyadicBlock (N : ℕ) : Finset ℕ := Finset.Ico N (2*N)
def ExactLengthEvent (g : ℕ → F₂) (x q : ℕ) : Prop :=
  g (x-1)+g x=1 ∧ (∀ j : ℕ, 0<j → j+1<q → g x=g (x+j)) ∧ g x+g (x+(q-1))=1
def infiniteExactLengthCount (N L e : ℕ) (omega : InfiniteSample) : ℕ :=
  ∑ x∈dyadicBlock N, if ExactLengthEvent (infiniteValueBit omega) x (L+e+1) then 1 else 0
def maskedCount (L : ℕ) (mask : Finset ℕ) (omega : InfiniteSample) : ℕ :=
  ∑ x∈mask, if StartEvent (infiniteValueBit omega) x L then 1 else 0
def fullRate (N L : ℕ) : ℝ≥0 := ⟨(N : ℝ)/2^L, by positivity⟩
def maskRate (L : ℕ) (mask : Finset ℕ) : ℝ≥0 := ⟨(mask.card : ℝ)/2^L, by positivity⟩
def PrimeUpTo (Y : ℕ) := {p : Fin (Y+1) // Nat.Prime p.val}
abbrev SampleSpace (Y : ℕ) := PrimeUpTo Y → F₂
def restrictToFinite (Y : ℕ) (omega : InfiniteSample) : SampleSpace Y :=
  fun p => omega (Nat.primeCounting' p.val)
@[reducible] def primeSigma (Y : ℕ) : MeasurableSpace InfiniteSample :=
  MeasurableSpace.comap (restrictToFinite Y) inferInstance
def observedAtom (Y : ℕ) (omega : InfiniteSample) : Set InfiniteSample :=
  {eta | restrictToFinite Y eta=restrictToFinite Y omega}
def massTV {α : Type*} (p q : α → ℝ) : ℝ := (2 : ℝ)⁻¹ * ∑' k, |p k-q k|
def observableLaw {Ω α : Type*} [MeasurableSpace Ω] (mu : Measure Ω) (f : Ω → α) : α → ℝ :=
  fun k => mu.real {omega | f omega=k}
def conditionalLaw {Ω α : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (A : Set Ω) (f : Ω → α) : α → ℝ := observableLaw (cond mu A) f
def environmentDistance {α : Type*} (Y : ℕ) (f : InfiniteSample → α)
    (q : α → ℝ) (omega : InfiniteSample) : ℝ :=
  massTV (conditionalLaw infiniteRademacherMeasure (observedAtom Y omega) f) q

namespace Process
/- The only process premise is the published finite AGG bound with an exact
independence graph. Neither its indicators nor its graph are arithmetic. -/
structure FinitePMF (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ a, 0≤prob a
  sum_prob : ∑ a, prob a=1

def eventProbability {Ω : Type*} [Fintype Ω] (mu : FinitePMF Ω) (A : Ω → Prop) : ℝ :=
  ∑ omega, if A omega then mu.prob omega else 0
def marginal {Ω ι : Type*} [Fintype Ω] (mu : FinitePMF Ω) (X : ι → Ω → Bool) (i : ι) : ℝ :=
  eventProbability mu (fun omega => X i omega=true)
theorem marginal_nonneg {Ω ι : Type*} [Fintype Ω] (mu : FinitePMF Ω)
    (X : ι → Ω → Bool) (i : ι) : 0 ≤ marginal mu X i := by
  unfold marginal eventProbability
  exact Finset.sum_nonneg (fun omega _ => by split_ifs; exact mu.nonneg omega; exact le_rfl)
def closedNeighborhood {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (i : ι) : Finset ι := Finset.univ.filter (fun j => j=i ∨ G.Adj i j)
def OutsideIndex {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) (i : ι) :=
  {j : ι // j ∉ closedNeighborhood G i}
def HasOutsidePattern {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → Bool) (G : SimpleGraph ι) (i : ι)
    (pattern : OutsideIndex G i → Bool) (omega : Ω) : Prop := ∀ j, X j.val omega=pattern j
def HasExactDependencyGraph {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (mu : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι) : Prop :=
  ∀ (i : ι) (v : Bool) (pattern : OutsideIndex G i → Bool),
    eventProbability mu (fun omega => X i omega=v ∧ HasOutsidePattern X G i pattern omega) =
      eventProbability mu (fun omega => X i omega=v) * eventProbability mu (HasOutsidePattern X G i pattern)
def bOne {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (mu : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι) : ℝ :=
  ∑ i, ∑ j∈closedNeighborhood G i, marginal mu X i*marginal mu X j
def bTwo {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (mu : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι) : ℝ :=
  ∑ i, ∑ j∈(closedNeighborhood G i).erase i,
    eventProbability mu (fun omega => X i omega=true ∧ X j omega=true)
def indicatorField {Ω ι : Type*} (X : ι → Ω → Bool) (omega : Ω) (i : ι) : ℕ :=
  if X i omega=true then 1 else 0
def fieldRates {Ω ι : Type*} [Fintype Ω] (mu : FinitePMF Ω) (X : ι → Ω → Bool) (i : ι) : ℝ≥0 :=
  ⟨marginal mu X i, marginal_nonneg mu X i⟩
def finiteFieldLaw {Ω α : Type*} [Fintype Ω] (mu : FinitePMF Ω) (f : Ω → α) (k : α) : ℝ :=
  ∑ omega, if f omega=k then mu.prob omega else 0
def poissonFieldMass {ι : Type*} [Fintype ι] (rate : ι → ℝ≥0) (k : ι → ℕ) : ℝ :=
  ∏ i, (poissonMeasure (rate i)).real {k i}
def ProcessAGGStatement : Prop :=
  ∀ (Ω ι : Type) [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (mu : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι),
    HasExactDependencyGraph mu X G →
    massTV (finiteFieldLaw mu (indicatorField X)) (poissonFieldMass (fieldRates mu X)) ≤
      2*(bOne mu X G+bTwo mu X G)
end Process

namespace Analysis
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

/- The PNT premise is the ordinary prime-counting remainder, not a weighted
estimate or an arithmetic conclusion. Ei has the manuscript normalization. -/
def exponentialIntegralAnchor : ℝ := Real.eulerMascheroniConstant +
  ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) * ((n + 1).factorial : ℝ))
def exponentialIntegral (u : ℝ) : ℝ :=
  exponentialIntegralAnchor + ∫ t in (1 : ℝ)..u, Real.exp t / t
def PrimeNumberTheoremRemainder : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ A : ℝ, 2 ≤ A ∧ ∀ t : ℝ, A ≤ t →
    |(Nat.primeCounting ⌊t⌋₊ : ℝ) - exponentialIntegral (Real.log t)| ≤ eta * t / Real.log t

/- Hard/soft saddle scales are actual functions, with explicit totalization
below their existence threshold. Epsilon selects the unique root above it.
The Solution proves equality to the development's chosen root internally. -/
def saddleCostParam (u : ℝ) : ℝ := Real.exp u - exponentialIntegral u
def saddleRatio (u : ℝ) : ℝ := Real.exp u / u
def saddleParameterBase : ℝ := max 2 (3 - saddleCostParam 2)
def saddleHeight (a u : ℝ) : ℝ := a * saddleRatio u * saddleCostParam u
def saddleThreshold (a : ℝ) : ℝ := saddleHeight a saddleParameterBase
def saddleParameter (a H : ℝ) : ℝ :=
  if 0 < a ∧ saddleThreshold a ≤ H then
    Classical.epsilon (fun u : ℝ => saddleParameterBase ≤ u ∧ saddleHeight a u = H)
  else saddleParameterBase
def saddleCutoff (a H : ℝ) : ℝ := a * saddleCostParam (saddleParameter a H)
def saddleNu (a H : ℝ) : ℝ := H / saddleCutoff a H
def hardCutoff (N : ℕ) : ℕ := ⌊Real.exp (saddleCutoff 1 (Real.log N))⌋₊
def softCutoff (N : ℕ) : ℕ := ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊

/- Scalar solution input: Krokowski, arXiv:1505.01417v3, (2.14)-(2.15).
Only existence and the two analytic factors are external theorem arguments. -/
def poissonMass (rate : ℝ≥0) (k : ℕ) : ℝ := (poissonMeasure rate).real {k}
def poissonSetMass (rate : ℝ≥0) (A : Set ℕ) : ℝ :=
  ∑' k, if k ∈ A then poissonMass rate k else 0
def firstSteinFactor (rate : ℝ≥0) : ℝ := if rate = 0 then 1 else min 1 (rate : ℝ)⁻¹
def zeroSteinFactor (rate : ℝ≥0) : ℝ := if rate = 0 then 1 else min 1 (Real.sqrt (rate : ℝ))⁻¹
def SteinSolutionBounds (rate : ℝ≥0) (c d : ℝ) : Prop :=
  ∀ A : Set ℕ, ∃ f : ℕ → ℝ,
    (∀ k : ℕ, (rate : ℝ) * f (k+1) - (k : ℝ) * f k =
      (if k ∈ A then 1 else 0) - poissonSetMass rate A) ∧
    (∀ k, |f k| ≤ c) ∧ (∀ k, |f (k+1)-f k| ≤ d)
def ScalarSteinFactorsStatement : Prop :=
  ∀ rate : ℝ≥0, 0 < rate → SteinSolutionBounds rate (zeroSteinFactor rate) (firstSteinFactor rate)

/- Companion C.3, Barbour (1988), Lemmas 2-3, p.179. The same solution
satisfies the entrywise bound and the weighted quadratic bound. The false
unweighted Euclidean quadratic bound from the earlier overlay is absent. -/
def addPoint {κ : Type*} [DecidableEq κ] (z : κ → ℕ) (i : κ) : κ → ℕ := z + Pi.single i 1
def removePoint {κ : Type*} [DecidableEq κ] (z : κ → ℕ) (i : κ) : κ → ℕ := z - Pi.single i 1
def firstDifference {κ : Type*} [DecidableEq κ] (g : (κ → ℕ) → ℝ) (i : κ) (z : κ → ℕ) : ℝ :=
  g (addPoint z i) - g z
def secondDifference {κ : Type*} [DecidableEq κ] (g : (κ → ℕ) → ℝ) (i j : κ) (z : κ → ℕ) : ℝ :=
  g (addPoint (addPoint z i) j) - g (addPoint z i) - g (addPoint z j) + g z
def steinGenerator {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ≥0) (g : (κ → ℕ) → ℝ) (z : κ → ℕ) : ℝ :=
  ∑ i, ((t i : ℝ) * firstDifference g i z + (z i : ℝ) * (g (removePoint z i) - g z))
def poissonFieldMass {κ : Type*} [Fintype κ] (t : κ → ℝ≥0) (z : κ → ℕ) : ℝ :=
  ∏ i, poissonMass (t i) (z i)
def poissonTestMass {κ : Type*} [Fintype κ] (t : κ → ℝ≥0) (A : Set (κ → ℕ)) : ℝ :=
  ∑' z, if z ∈ A then poissonFieldMass t z else 0
def directionalCoefficient {κ : Type*} [Fintype κ] (t : κ → ℝ≥0) : ℝ :=
  (1 + 2 * max 0 (Real.log (2 * ∑ i, (t i : ℝ)))) / 2
def hessianQuadratic {κ : Type*} [Fintype κ] [DecidableEq κ]
    (g : (κ → ℕ) → ℝ) (z : κ → ℕ) (alpha : κ → ℝ) : ℝ :=
  ∑ i, ∑ j, alpha i * alpha j * secondDifference g i j z
def DirectionalSolutionBounds {κ : Type*} [Fintype κ] [DecidableEq κ] (t : κ → ℝ≥0) : Prop :=
  ∀ A : Set (κ → ℕ), ∃ g : (κ → ℕ) → ℝ,
    (∀ z, steinGenerator t g z = (if z ∈ A then 1 else 0) - poissonTestMass t A) ∧
    (∀ z i j, |secondDifference g i j z| ≤ 1) ∧
    (∀ z alpha, |hessianQuadratic g z alpha| ≤
      directionalCoefficient t * ∑ i, (alpha i)^2 / (t i : ℝ))
def DirectionalSteinFactorsStatement : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ], 2 ≤ Fintype.card κ →
    ∀ t : κ → ℝ≥0, (∀ i, 0 < t i) → DirectionalSolutionBounds t
end Analysis

namespace Limits
open Analysis MeasureTheory ProbabilityTheory Filter WithLp
open scoped Topology BigOperators NNReal ENNReal

/- True counts at several thresholds, paired with exact-length critical counts. -/
def startCount (N L : ℕ) := maskedCount L (dyadicBlock N)
def criticalBase (N : ℕ) : ℕ := ⌊Real.log N/Real.log 2⌋₊
def dyadicPhase (N : ℕ) : ℝ := Real.log N/Real.log 2-criticalBase N
def movingLength (N d : ℕ) : ℕ := criticalBase N-d
def criticalExcess (R : Finset ℤ) (d : ℕ) (r : R) : ℕ := ((d : ℤ)+r.val).toNat
def criticalPoissonRates (theta : ℝ) (R : Finset ℤ) (r : R) : ℝ≥0 :=
  ⟨(2 : ℝ)^(theta-(r.val : ℝ)-1), Real.rpow_nonneg (by norm_num) _⟩
def eventInformation (C : Set InfiniteSample) : ℝ := -Real.log (infiniteRademacherMeasure.real C)
def aggregateLogCost (I rate : ℝ) : ℝ := I+Real.log rate
def actualJointVector {R : Type*} [Fintype R] (N L J : ℕ) (excess : R → ℕ)
    (omega : InfiniteSample) : WithLp 2 (EuclideanSpace ℝ (Fin (J+1)) × EuclideanSpace ℝ R) :=
  toLp 2 (toLp 2 (fun j : Fin (J+1) =>
    ((startCount N (L+j.val) omega : ℝ)-(fullRate N L : ℝ)/(2 : ℝ)^j.val)/Real.sqrt (fullRate N L)),
    toLp 2 (fun r => (infiniteExactLengthCount N L (excess r) omega : ℝ)))

/- Explicit Gaussian covariance and the independent Poisson coordinates. -/
def thresholdCovariance (J : ℕ) : Matrix (Fin (J+1)) (Fin (J+1)) ℝ :=
  fun j k => 1/(2 : ℝ)^max j.val k.val
def gaussianThresholdLaw (J : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin (J+1))) :=
  ⟨multivariateGaussian 0 (thresholdCovariance J), inferInstance⟩
def realPoissonLaw (rate : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨(poissonMeasure rate).map (fun n : ℕ => (n : ℝ)),
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩
def euclideanProductLaw {I : Type*} [Fintype I] (laws : I → ProbabilityMeasure ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ I) :=
  ⟨(Measure.pi (fun i => (laws i : Measure ℝ))).map (toLp 2),
    Measure.isProbabilityMeasure_map (by fun_prop)⟩
def poissonGaussianTarget {R : Type*} [Fintype R] (J : ℕ) (rates : R → ℝ≥0) :
    ProbabilityMeasure (WithLp 2 (EuclideanSpace ℝ (Fin (J+1)) × EuclideanSpace ℝ R)) :=
  ⟨((gaussianThresholdLaw J : Measure _).prod
      (euclideanProductLaw (fun r => realPoissonLaw (rates r)) : Measure _)).map (toLp 2),
    Measure.isProbabilityMeasure_map (by fun_prop)⟩
def standardizedProjection (J : ℕ) (j : Fin (J+1)) : EuclideanSpace ℝ (Fin (J+1)) →L[ℝ] ℝ :=
  (2 : ℝ)^((j.val : ℝ)/2) • EuclideanSpace.proj j
def innovationProjection (J : ℕ) (j : Fin J) : EuclideanSpace ℝ (Fin (J+1)) →L[ℝ] ℝ :=
  (2 : ℝ)^((1 : ℝ)/2) • standardizedProjection J j.succ - standardizedProjection J j.castSucc
def arNoiseProjection (J : ℕ) (i : Option (Fin J)) : EuclideanSpace ℝ (Fin (J+1)) →L[ℝ] ℝ :=
  match i with
  | none => standardizedProjection J 0
  | some j => innovationProjection J j

/- D.1: quantitative local probabilities and upper moderate tails. -/
def poissonEntropy (u : ℝ) : ℝ := u*Real.log u-u+1
def poissonLocalApprox (rate : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-rate*poissonEntropy (n/rate))/Real.sqrt (2*Real.pi*n)
def gaussianLatticeMass (rate t : ℝ) : ℝ := Real.exp (-(t^2)/2)/Real.sqrt (2*Real.pi*rate)
def normalTail (t : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Ici t)
def restrictedCountLaw (N L : ℕ) (C : Set InfiniteSample) (k : ℕ) : ℝ :=
  infiniteRademacherMeasure.real ({omega | startCount N L omega=k} ∩ C) /
    infiniteRademacherMeasure.real C
def hardTailCost (I rate t : ℝ) : ℝ := I+max 0 (Real.log rate)+t^2/2+Real.log (1+t)

/- D.4: the whole locally finite process on [1,2] × Z. The source
configuration is specified at every site, exact length and sign. Epsilon
only chooses this unique finite-support function; the Solution proves it
equals the actual configuration, with no existence premise in the theorem. -/
abbrev SpatialMarkedConfig (N : ℕ) := (Fin N × (ℕ × F₂)) →₀ ℕ
def spatialMarkedValue (N L : ℕ) (omega : InfiniteSample) (j : Fin N × (ℕ × F₂)) : ℕ :=
  if ExactLengthEvent (infiniteValueBit omega) (N+j.1.val) (L+j.2.1+1) ∧
    infiniteValueBit omega (N+j.1.val)=j.2.2 then 1 else 0
def spatialMarkedSource (N L : ℕ) (omega : InfiniteSample) : SpatialMarkedConfig N :=
  Classical.epsilon (fun c : SpatialMarkedConfig N => ∀ j, c j=spatialMarkedValue N L omega j)
def centeredSourceMeasure (N : ℕ) (omega : InfiniteSample) : Measure (ℝ × ℤ) :=
  (spatialMarkedSource N 0 omega).sum (fun j n => (n : ℝ≥0∞) •
    Measure.dirac (((N+j.1.val : ℕ) : ℝ)/N, (j.2.1 : ℤ)-criticalBase N))
def integerLevelRate (theta : ℝ) (r : ℤ) : ℝ≥0 :=
  ⟨(2 : ℝ)^(theta-(r : ℝ)-1), by positivity⟩
def integerHalfRate (theta : ℝ) (m : ℤ) : ℝ≥0 :=
  ⟨(2 : ℝ)^(theta-(m : ℝ)), by positivity⟩
def integerCountMeasure (theta : ℝ) : Measure (ℤ → ℕ) :=
  Measure.infinitePi (fun r => poissonMeasure (integerLevelRate theta r))
def unitIntervalUniformMeasure : Measure unitInterval := volume.comap ((↑) : unitInterval → ℝ)
instance instProbabilityUnitIntervalUniform : IsProbabilityMeasure unitIntervalUniformMeasure := by
  constructor
  rw [unitIntervalUniformMeasure,comap_subtype_coe_apply measurableSet_Icc,
    Set.image_univ,Subtype.range_coe]
  norm_num [Real.volume_Icc]
def markSequenceMeasure : Measure (ℕ → unitInterval) :=
  Measure.infinitePi (fun _ : ℕ => unitIntervalUniformMeasure)
instance instProbabilityMarkSequence : IsProbabilityMeasure markSequenceMeasure := by
  unfold markSequenceMeasure; infer_instance
def markSampleMeasure (rate : ℝ≥0) : Measure (ℕ × (ℕ → unitInterval)) :=
  (poissonMeasure rate).prod markSequenceMeasure
instance instProbabilityMarkSample (rate : ℝ≥0) : IsProbabilityMeasure (markSampleMeasure rate) := by
  unfold markSampleMeasure; infer_instance
abbrev IntegerSpatialSample := ℤ → (ℕ × (ℕ → unitInterval))
/- Keep the product sigma-algebra explicit in both independent environments.
This also fixes the declaration identity used by the strict Comparator. -/
instance instMeasurableIntegerSpatialSample : MeasurableSpace IntegerSpatialSample :=
  @MeasurableSpace.pi ℤ (fun _ => ℕ × (ℕ → unitInterval)) (fun _ =>
    @Prod.instMeasurableSpace ℕ (ℕ → unitInterval) Nat.instMeasurableSpace
      (@MeasurableSpace.pi ℕ (fun _ => unitInterval) (fun _ =>
        @Subtype.instMeasurableSpace ℝ (fun x => x ∈ unitInterval) Real.measurableSpace)))
def integerSpatialSampleMeasure (theta : ℝ) : Measure IntegerSpatialSample :=
  Measure.infinitePi (fun r => markSampleMeasure (integerLevelRate theta r))
def integerPointRow (sample : IntegerSpatialSample) (r : ℤ) : Measure (ℝ × ℤ) :=
  ∑ i∈Finset.range ((sample r).1), Measure.dirac (1+((sample r).2 i : ℝ), r)
def integerPointMeasure (sample : IntegerSpatialSample) : Measure (ℝ × ℤ) :=
  Measure.sum (integerPointRow sample)
def laplaceFunctional (theta : ℝ) (g : ℝ × ℤ → ℝ) : ℝ :=
  Real.exp (-(∫ t in Set.Ico (1 : ℝ) 2,
    ∑' r : ℤ, (integerLevelRate theta r : ℝ)*(1-Real.exp (-g (t,r)))))
def intensityLog (N L : ℕ) : ℝ := Real.log (fullRate N L : ℝ)/Real.log 2
def intensityPhase (N L : ℕ) : ℝ := Int.fract (intensityLog N L)
def extremeThreshold (N L : ℕ) (j : ℤ) : ℕ := (⌊intensityLog N L⌋+j).toNat
def extremeProbability (N L : ℕ) (j : ℤ) : ℝ :=
  infiniteRademacherMeasure.real
    {omega | ¬∃ x∈dyadicBlock N, ∃ e : ℕ, extremeThreshold N L j<e ∧
      ExactLengthEvent (infiniteValueBit omega) x (L+e+1)}
end Limits

namespace Limits
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

/- Fix the same discrete sign topology in both comparison environments. -/
instance instTopologicalSign : TopologicalSpace F₂ := ⊥
instance instDiscreteTopologySign : DiscreteTopology F₂ := ⟨rfl⟩

/- Actual finite point measures with the Borel sigma-algebra of weak convergence. -/
def PointMeasure (X : Type*) [MeasurableSpace X] := FiniteMeasure X
instance instTopologicalPointMeasure (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] : TopologicalSpace (PointMeasure X) :=
  inferInstanceAs (TopologicalSpace (FiniteMeasure X))
instance instMeasurablePointMeasure (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] : MeasurableSpace (PointMeasure X) := borel (PointMeasure X)
instance instBorelPointMeasure (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] : BorelSpace (PointMeasure X) := ⟨rfl⟩
instance instAddCommMonoidPointMeasure (X : Type*) [MeasurableSpace X] : AddCommMonoid (PointMeasure X) :=
  inferInstanceAs (AddCommMonoid (FiniteMeasure X))
def pointDirac {X : Type*} [MeasurableSpace X] (x : X) : PointMeasure X :=
  (diracProba x).toFiniteMeasure
def fixedPointMeasure {X : Type*} [MeasurableSpace X] (n : ℕ) (marks : ℕ → X) : PointMeasure X :=
  ∑ i ∈ Finset.range n, pointDirac (marks i)

/- The measurable inverse only totalizes the null set of infinite upper tails. -/
local instance instMeasurableHalfCounts : MeasurableSpace (ℕ →₀ ℕ) := ⊤
local instance instMeasurableSingletonHalfCounts : MeasurableSingletonClass (ℕ →₀ ℕ) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
theorem measurableEmbedding_halfCounts :
    MeasurableEmbedding (fun c : ℕ →₀ ℕ => (c : ℕ → ℕ)) :=
  ⟨(fun _ _ h => Finsupp.ext (congrFun h)), measurable_of_countable _, fun {_} _ =>
    (Set.to_countable _).image _ |>.measurableSet⟩
def recoverHalfCounts (v : ℕ → ℕ) : ℕ →₀ ℕ := measurableEmbedding_halfCounts.invFun v
def spatialHalfCounts (m : ℤ) (sample : IntegerSpatialSample) : ℕ →₀ ℕ :=
  recoverHalfCounts (fun e : ℕ => (sample (m+e)).1)
def fullHalfCount (m : ℤ) (sample : IntegerSpatialSample) : ℕ :=
  (spatialHalfCounts m sample).sum (fun _ n => n)
def halfLinePointConfiguration (m : ℤ) (sample : IntegerSpatialSample) :
    PointMeasure (ℝ × (ℕ × F₂)) :=
  (spatialHalfCounts m sample).sum (fun e n => fixedPointMeasure n
    (fun i => (1+((sample (m+e)).2 i : ℝ),(e,(0 : F₂)))))
def upperPointLaw (theta : ℝ) (m : ℤ) : Measure (PointMeasure (ℝ × (ℕ × F₂))) :=
  (integerSpatialSampleMeasure theta).map (halfLinePointConfiguration m)

/- The comparison construction uses one Poisson count and genuinely iid
pairs (uniform position, independent nonnegative geometric excess). -/
def halfSuccess : unitInterval := ⟨1/2, by norm_num, by norm_num⟩
def halfMarkMeasure : Measure (unitInterval × ℕ) :=
  unitIntervalUniformMeasure.prod (geometricMeasure halfSuccess)
instance instProbabilityHalfMark : IsProbabilityMeasure halfMarkMeasure := by
  unfold halfMarkMeasure; infer_instance
def halfMarkSequenceMeasure : Measure (ℕ → unitInterval × ℕ) :=
  Measure.infinitePi (fun _ : ℕ => halfMarkMeasure)
def halfPoissonSampleMeasure (rate : ℝ≥0) : Measure (ℕ × (ℕ → unitInterval × ℕ)) :=
  (poissonMeasure rate).prod halfMarkSequenceMeasure
def halfContinuousMark (x : unitInterval × ℕ) : ℝ × (ℕ × F₂) :=
  (1+(x.1 : ℝ),(x.2,0))
def fixedHalfPoints (n : ℕ) (marks : ℕ → unitInterval × ℕ) : PointMeasure (ℝ × (ℕ × F₂)) :=
  fixedPointMeasure n (fun i => halfContinuousMark (marks i))
def poissonHalfPoints (sample : ℕ × (ℕ → unitInterval × ℕ)) : PointMeasure (ℝ × (ℕ × F₂)) :=
  fixedHalfPoints sample.1 sample.2
def poissonHalfPointLaw (theta : ℝ) (m : ℤ) : Measure (PointMeasure (ℝ × (ℕ × F₂))) :=
  (halfPoissonSampleMeasure (integerHalfRate theta m)).map poissonHalfPoints
def fixedHalfPointLaw (n : ℕ) : Measure (PointMeasure (ℝ × (ℕ × F₂))) :=
  halfMarkSequenceMeasure.map (fixedHalfPoints n)
def upperPosition (m : ℤ) (x : ℝ × (ℕ × F₂)) : ℝ × ℤ := (x.1,m+x.2.1)
end Limits

open Analysis Limits Process Set Real MeasureTheory ProbabilityTheory Filter WithLp
open scoped Topology NNReal ENNReal BigOperators

/-- PaperC.V282.PoissonGaussianTheorem.theorem_five_ten. -/
theorem paper_c_v3_limits_joint_poisson_gaussian (hStein : Analysis.DirectionalSteinFactorsStatement)
    (hPNT : Analysis.PrimeNumberTheoremRemainder) (c : ℝ) (hc : 0<c)
    (sizes depths : ℕ → ℕ) (theta : ℝ) (R : Finset ℤ) (J : ℕ)
    (hsizes : Tendsto sizes atTop atTop) (hdepths : Tendsto depths atTop atTop)
    (hsmall : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (hphase : Tendsto (fun n => dyadicPhase (sizes n)) atTop (𝓝 theta))
    (C : ℕ → Set InfiniteSample)
    (hC : ∀ᶠ n in atTop, MeasurableSet[primeSigma (Analysis.hardCutoff (sizes n))] (C n))
    (hpos : ∀ n, 0 < infiniteRademacherMeasure.real (C n))
    (hbudget : ∀ᶠ n in atTop,
      aggregateLogCost (eventInformation (C n)) (fullRate (sizes n) (movingLength (sizes n) (depths n))) ≤
        Analysis.saddleCutoff 1 (Real.log (sizes n))-c*Analysis.saddleNu 1 (Real.log (sizes n))) :
    ∃ laws : ℕ → ProbabilityMeasure (WithLp 2 (EuclideanSpace ℝ (Fin (J+1)) × EuclideanSpace ℝ R)),
      (∀ n, (laws n : Measure _) = (cond infiniteRademacherMeasure (C n)).map
        (actualJointVector (sizes n) (movingLength (sizes n) (depths n)) J (criticalExcess R (depths n)))) ∧
      Tendsto laws atTop (𝓝 (poissonGaussianTarget J (criticalPoissonRates theta R))) := by sorry

/-- PaperC.V282.GaussianThresholdCovariance.gaussianThresholdLaw_covariance. -/
theorem paper_c_v3_limits_gaussian_covariance (J : ℕ) (j k : Fin (J+1)) :
    cov[fun x => x j, fun x => x k;
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1))))] =
        1 / (2 : ℝ)^max j.val k.val := by sorry

/-- PaperC.V282.GaussianThresholdAR.standardizedProjection_covariance. -/
theorem paper_c_v3_limits_ar_covariance (J : ℕ) (j k : Fin (J+1)) :
    cov[standardizedProjection J j, standardizedProjection J k;
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1))))] =
      (2 : ℝ)^(-|(j.val : ℝ)-(k.val : ℝ)|/2) := by sorry

/-- PaperC.V282.GaussianThresholdAR.standardized_ar_recursion. -/
theorem paper_c_v3_limits_ar_recursion (J : ℕ) (j : Fin J)
    (x : EuclideanSpace ℝ (Fin (J+1))) :
    standardizedProjection J j.succ x =
      (2 : ℝ)^(-(1 : ℝ)/2) * standardizedProjection J j.castSucc x +
      (2 : ℝ)^(-(1 : ℝ)/2) * innovationProjection J j x := by sorry

/-- PaperC.V282.GaussianThresholdAR.arNoises_independent. -/
theorem paper_c_v3_limits_ar_independent_innovations (J : ℕ) :
    iIndepFun (fun i : Option (Fin J) => arNoiseProjection J i)
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1)))) := by sorry

/-- PaperC.V282.GaussianThresholdAR.hasLaw_arNoise. -/
theorem paper_c_v3_limits_ar_normal_innovations (J : ℕ) (i : Option (Fin J)) :
    HasLaw (arNoiseProjection J i) (gaussianReal 0 1) (gaussianThresholdLaw J : Measure _) := by sorry

/-- PaperC.V282.PoissonStirlingBounds.poisson_local_bounds. -/
theorem paper_c_v3_limits_local_stirling_bounds {rate : ℝ} (hr : 0 < rate) {n : ℕ} (hn : 0 < n) :
    exp (-(1 / (12 * n))) * poissonLocalApprox rate n ≤
        exp (-rate) * rate ^ n / n.factorial ∧
      exp (-rate) * rate ^ n / n.factorial ≤ poissonLocalApprox rate n := by sorry

/-- PaperC.V282.PoissonStirlingBounds.poisson_local_relative_error. -/
theorem paper_c_v3_limits_local_stirling_relative_error {rate : ℝ} (hr : 0 < rate) {n : ℕ} (hn : 0 < n) :
    |(exp (-rate) * rate ^ n / n.factorial) / poissonLocalApprox rate n - 1| ≤
      1 / (12 * n) := by sorry

/-- PaperC.V282.PoissonQuantitativeCentral.poisson_gaussian_local_ratio_tendsto_one. -/
theorem paper_c_v3_limits_poisson_local_limit (rates : ℕ→ℝ≥0) (n : ℕ→ℕ) (t : ℕ→ℝ) (K : ℝ)
    (hrate : Tendsto (fun k => (rates k : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(rates k : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (hround : ∀ᶠ k in atTop,|(n k : ℝ)-((rates k : ℝ)+t k*sqrt (rates k))|≤K) :
    Tendsto (fun k => (poissonMeasure (rates k)).real {n k}/gaussianLatticeMass (rates k) (t k))
      atTop (𝓝 1) := by sorry

/-- PaperC.V282.PoissonQuantitativeModerate.poisson_moderate_relative_error. -/
theorem paper_c_v3_limits_poisson_moderate_bound : ∃ C : ℝ, 0<C ∧ ∀ rate : ℝ≥0, (4096 : ℝ)≤rate →
    ∀ t : ℝ, 0≤t → t^3/Real.sqrt rate≤1 →
    |(poissonMeasure rate).real (Ici ⌈(rate : ℝ)+Real.sqrt rate*t⌉₊)/normalTail t-1| ≤
      C*((1+t^3)/Real.sqrt rate) := by sorry

/-- PaperC.V282.PoissonQuantitativeModerateLimit.poisson_moderate_ratio_tendsto_one. -/
theorem paper_c_v3_limits_poisson_moderate_limit (rates : ℕ→ℝ≥0) (t : ℕ→ℝ)
    (hrate : Tendsto (fun k => (rates k : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(rates k : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (htnonneg : ∀ᶠ k in atTop,0≤t k) :
    Tendsto (fun k => (poissonMeasure (rates k)).real
      (Ici ⌈(rates k : ℝ)+sqrt (rates k)*t k⌉₊)/normalTail (t k)) atTop (𝓝 1) := by sorry

/-- PaperC.V282.PoissonQuantitativeBerry.poisson_gaussian_CDF_error. -/
theorem paper_c_v3_limits_poisson_gaussian_cdf_bound : ∃ C : ℝ, 0<C ∧ ∀ rate : ℝ≥0, 0<rate → ∀ t : ℝ,
    |(poissonMeasure rate).real {n : ℕ | ((n : ℝ)-(rate : ℝ))/Real.sqrt rate≤t} -
      (gaussianReal 0 1).real (Iic t)| ≤ C/Real.sqrt rate := by sorry

/-- PaperC.V282.HardLocalClosureCentral.hard_central_local_probabilities. -/
theorem paper_c_v3_limits_hard_central_local (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (c c' : ℝ) (hc' : 0<c') (hcc : c'<c)
    (sizes lengths counts : ℕ→ℕ) (C : ℕ→Set InfiniteSample) (t : ℕ→ℝ) (K : ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(fullRate (sizes k) (lengths k) : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (hround : ∀ᶠ k in atTop, |(counts k : ℝ)-((fullRate (sizes k) (lengths k) : ℝ)+
      t k*sqrt (fullRate (sizes k) (lengths k) : ℝ))|≤K)
    (hC : ∀ᶠ k in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance] (C k))
    (hpos : ∀ᶠ k in atTop, 0 < infiniteRademacherMeasure.real (C k))
    (hbudget : ∀ᶠ k in atTop,
      eventInformation (C k)+(3/2 : ℝ)*log (fullRate (sizes k) (lengths k) : ℝ)+(t k)^2/2 ≤
        saddleCutoff 1 (log (sizes k))-c*saddleNu 1 (log (sizes k))) :
    Tendsto (fun k => restrictedCountLaw (sizes k) (lengths k) (C k) (counts k) /
      (poissonMeasure (fullRate (sizes k) (lengths k))).real {counts k}) atTop (𝓝 1) ∧
    Tendsto (fun k => restrictedCountLaw (sizes k) (lengths k) (C k) (counts k) /
      gaussianLatticeMass (fullRate (sizes k) (lengths k)) (t k)) atTop (𝓝 1) := by sorry

/-- PaperC.V282.SoftLocalClosureCentral.soft_central_local_probabilities. -/
theorem paper_c_v3_limits_soft_central_local (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (c c' : ℝ) (hc' : 0<c') (hcc : c'<c)
    (sizes lengths counts : ℕ→ℕ) (C : ℕ→Set InfiniteSample) (t : ℕ→ℝ) (K : ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(fullRate (sizes k) (lengths k) : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (hround : ∀ᶠ k in atTop, |(counts k : ℝ)-((fullRate (sizes k) (lengths k) : ℝ)+
      t k*sqrt (fullRate (sizes k) (lengths k) : ℝ))|≤K)
    (hC : ∀ᶠ k in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff (sizes k))) inferInstance] (C k))
    (hpos : ∀ᶠ k in atTop, 0 < infiniteRademacherMeasure.real (C k))
    (hbudget : ∀ᶠ k in atTop,
      2*eventInformation (C k)+2*log (fullRate (sizes k) (lengths k) : ℝ)+(t k)^2 ≤
        saddleCutoff 2 (log (sizes k))-c*saddleNu 2 (log (sizes k))) :
    Tendsto (fun k => restrictedCountLaw (sizes k) (lengths k) (C k) (counts k) /
      (poissonMeasure (fullRate (sizes k) (lengths k))).real {counts k}) atTop (𝓝 1) ∧
    Tendsto (fun k => restrictedCountLaw (sizes k) (lengths k) (C k) (counts k) /
      gaussianLatticeMass (fullRate (sizes k) (lengths k)) (t k)) atTop (𝓝 1) := by sorry

/-- PaperC.V282.PoissonQuantitativeTailRates.hard_conditional_tail_normal_ratio_tendsto_one. -/
theorem paper_c_v3_limits_hard_moderate_tail (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0<c)
    (sizes lengths : ℕ→ℕ) (t : ℕ→ℝ) (C : ℕ→Set InfiniteSample)
    (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(fullRate (sizes k) (lengths k) : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (hadmissible : ∀ᶠ k in atTop,
      betaMin*log (sizes k)≤(lengths k+1 : ℝ) ∧
      (lengths k+1 : ℝ)≤betaMax*log (sizes k) ∧
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance] (C k) ∧
      0 < infiniteRademacherMeasure.real (C k) ∧ 0≤t k ∧
      hardTailCost (eventInformation (C k)) (fullRate (sizes k) (lengths k)) (t k) ≤
        saddleCutoff 1 (log (sizes k))-c*saddleNu 1 (log (sizes k))) :
    Tendsto (fun k => (cond infiniteRademacherMeasure (C k)).real
      {omega | ⌈(fullRate (sizes k) (lengths k) : ℝ)+sqrt (fullRate (sizes k) (lengths k))*t k⌉₊≤
        startCount (sizes k) (lengths k) omega}/normalTail (t k)) atTop (𝓝 1) := by sorry

/-- PaperC.V282.D4ClosureLaplaceTheorem.companion_D4_laplace_moving. -/
theorem paper_c_v3_limits_integer_process_moving_laplace (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (g : ℝ × ℤ → ℝ) (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) (hgc : HasCompactSupport g)
    (c : ℝ) (hc : 0 < c) (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop, MeasurableSet[MeasurableSpace.comap
      (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop, eventInformation (A n) ≤
      saddleCutoff 1 (log (sizes n))-c*saddleNu 1 (log (sizes n))) :
    Tendsto (fun n =>
      (∫ omega, exp (-(∫ z, g z ∂centeredSourceMeasure (sizes n) omega))
        ∂cond infiniteRademacherMeasure (A n)) - laplaceFunctional (dyadicPhase (sizes n)) g)
      atTop (𝓝 0) := by sorry

/-- PaperC.V282.D4ClosureLaplaceTheorem.companion_D4_laplace_phase_limit. -/
theorem paper_c_v3_limits_integer_process_phase_limit (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (theta : ℝ) (hphase : Tendsto (fun n => dyadicPhase (sizes n)) atTop (𝓝 theta))
    (g : ℝ × ℤ → ℝ) (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) (hgc : HasCompactSupport g)
    (c : ℝ) (hc : 0 < c) (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop, MeasurableSet[MeasurableSpace.comap
      (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop, eventInformation (A n) ≤
      saddleCutoff 1 (log (sizes n))-c*saddleNu 1 (log (sizes n))) :
    Tendsto (fun n => ∫ omega, exp (-(∫ z, g z ∂centeredSourceMeasure (sizes n) omega))
      ∂cond infiniteRademacherMeasure (A n)) atTop (𝓝 (laplaceFunctional theta g)) := by sorry

/-- PaperC.V282.D4ClosureLaplaceTarget.integer_target_laplace. -/
theorem paper_c_v3_limits_integer_process_target_laplace (theta : ℝ) (g : ℝ × ℤ → ℝ)
    (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) (hgc : HasCompactSupport g) :
    (∫ sample : IntegerSpatialSample, exp (-(∫ z, g z ∂integerPointMeasure sample))
      ∂integerSpatialSampleMeasure theta) = laplaceFunctional theta g := by sorry

/-- PaperC.V282.D4ClosurePointMeasure.integerPointMeasure_compact_finite. -/
theorem paper_c_v3_limits_integer_process_locally_finite (sample : IntegerSpatialSample)
    (K : Set (ℝ × ℤ)) (hK : IsCompact K) : integerPointMeasure sample K < ⊤ := by sorry

/-- PaperC.V282.D4ClosureInfiniteMass.ae_integerPointMeasure_univ_top. -/
theorem paper_c_v3_limits_integer_process_infinite_mass (theta : ℝ) :
    ∀ᵐ sample ∂integerSpatialSampleMeasure theta, integerPointMeasure sample Set.univ=⊤ := by sorry

/-- PaperC.V282.D4ClosureIntegerLevels.independent_integer_counts. -/
theorem paper_c_v3_limits_integer_process_independent_counts (theta : ℝ) :
    iIndepFun (fun r (counts : ℤ → ℕ) => counts r) (integerCountMeasure theta) := by sorry

/-- PaperC.V282.D4ClosureIntegerLevels.hasLaw_integer_coordinate. -/
theorem paper_c_v3_limits_integer_process_poisson_counts (theta : ℝ) (r : ℤ) :
    HasLaw (fun counts : ℤ → ℕ => counts r) (poissonMeasure (integerLevelRate theta r))
      (integerCountMeasure theta) := by sorry

/-- PaperC.V282.D4ClosurePointLaws.ae_spatial_upper_tails_finite. -/
theorem paper_c_v3_limits_integer_process_finite_upper_tails (theta : ℝ) :
    ∀ᵐ sample ∂integerSpatialSampleMeasure theta,
      ∀ m : ℤ, (Function.support (fun e : ℕ => (sample (m+e)).1)).Finite := by sorry

/-- PaperC.V282.D4ClosurePointLaws.conditional_level_positions. -/
theorem paper_c_v3_limits_integer_process_conditioned_positions (theta : ℝ) (r : ℤ) (n : ℕ)
    (hn : (poissonMeasure (integerLevelRate theta r)) {n} ≠ 0) :
    (cond (integerSpatialSampleMeasure theta) {sample | (sample r).1 = n}).map
      (fun sample : IntegerSpatialSample => sample r) =
      (Measure.dirac n).prod (markSequenceMeasure) := by sorry

/-- PaperC.V282.D4ClosureExtremeTheorem.companion_D4_extreme. -/
theorem paper_c_v3_limits_extreme_phase_limit (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ→ℕ) (theta : ℝ) (j : ℤ)
    (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop)
    (hphase : Tendsto (fun k => intensityPhase (sizes k) (lengths k)) atTop (𝓝 theta)) :
    Tendsto (fun k => extremeProbability (sizes k) (lengths k) j) atTop
      (𝓝 (exp (-((2 : ℝ)^(theta-(j : ℝ)-1))))) := by sorry

/-- PaperCV282/D4GridIdentificationTheorem.lean:hasLaw_spatialHalfCount. -/
theorem paper_c_v3_limits_d4_full_half_count_law (theta : ℝ) (m : ℤ) :
    HasLaw (Limits.fullHalfCount m) (poissonMeasure (Limits.integerHalfRate theta m))
      (Limits.integerSpatialSampleMeasure theta) := by sorry

/-- PaperCV282/D4ClosureSpatialIdentification.lean:halfLinePointLaw_eq_poisson. -/
theorem paper_c_v3_limits_d4_entire_upper_point_law (theta : ℝ) (m : ℤ) :
    Limits.upperPointLaw theta m=Limits.poissonHalfPointLaw theta m := by sorry

/-- PaperCV282/D4ClosureSpatialIdentification.lean:conditional_halfLinePointConfiguration. -/
theorem paper_c_v3_limits_d4_conditional_upper_point_law (theta : ℝ) (m : ℤ) (n : ℕ) :
    (cond (Limits.integerSpatialSampleMeasure theta)
      {sample | Limits.fullHalfCount m sample=n}).map (Limits.halfLinePointConfiguration m)=
      Limits.fixedHalfPointLaw n := by sorry

/-- PaperCV282/D4ClosureWholeRestriction.lean:ae_halfLinePointConfiguration_is_restriction. -/
theorem paper_c_v3_limits_d4_half_line_is_whole_restriction (theta : ℝ) (m : ℤ) :
    ∀ᵐ sample ∂Limits.integerSpatialSampleMeasure theta,
      ((Limits.halfLinePointConfiguration m sample).val.map (Limits.upperPosition m))=
        (Limits.integerPointMeasure sample).restrict (Set.univ ×ˢ Set.Ici m) := by sorry

end PaperCV3Audit
