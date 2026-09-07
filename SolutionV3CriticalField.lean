import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Int.AbsoluteValue
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Multiset.Interval
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Dist
import Mathlib.InformationTheory.Hamming
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import PaperCV282.SpatialMarkedStatistics
import PaperCV282.MeanScalarBudget
import PaperCV282.SoftRateAssembly
import PaperCV282.SpatialBoundedInformation
import PaperCV282.SpatialMarkedMovableBudget
import PaperCV282.QuenchedScalarBand
import PaperCV282.SpatialMarkedDiffuse
import PaperCV282.PrimeEnvironmentStableLift
import PaperCV282.MeanSpatialBudget

/-!
# V3PREL critical-field and conditional-transfer audit interface

The independently copied interface imports Mathlib; the proofs below import the substantive development. Its companion Solution independently
copies these transparent definitions and proves every selected declaration.
Bits encode multiplicative signs. The source is the actual infinite product
of prime signs. All excesses and both signs are retained in the complete field.
The diffuse target is a genuine Poisson number of independent marks, with
uniform positions on [1,2], geometric excesses and fair signs.

Only three published inputs are visible arguments: the ordinary PNT remainder,
the scalar analytic Stein factors, and the finite process AGG inequality with
an exact dependency graph. Arithmetic defects and affine relations are computed
from the windows; no desired arithmetic or Poisson approximation is assumed.
The separate scalar and process intensity domains are retained explicitly.
-/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
namespace PaperCV3Audit
local instance instDecidableProp (p : Prop) : Decidable p := Classical.propDecidable p
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

end Analysis

namespace CriticalField
open Analysis Process
@[reducible] def SpatialIndex (N : ℕ) := Fin N × (ℕ × F₂)
@[reducible] def SpatialConfig (N : ℕ) := SpatialIndex N →₀ ℕ
instance instMeasurableConfig (N : ℕ) : MeasurableSpace (SpatialConfig N) := ⊤
instance instSingletonConfig (N : ℕ) : MeasurableSingletonClass (SpatialConfig N) := by infer_instance
/- Epsilon specifies the unique finitely supported array with these actual
coefficients. Existence is proved internally in the Solution, not assumed. -/
def spatialSource (N L : ℕ) (omega : InfiniteSample) : SpatialConfig N :=
  Classical.epsilon (fun c => ∀ j : SpatialIndex N, c j =
    if ExactLengthEvent (infiniteValueBit omega) (N+j.1.val) (L+j.2.1+1) ∧
      infiniteValueBit omega (N+j.1.val)=j.2.2 then 1 else 0)
instance instMeasurableCluster : MeasurableSpace (ℕ →₀ ℕ) := ⊤
instance instSingletonCluster : MeasurableSingletonClass (ℕ →₀ ℕ) := by infer_instance
def halfSuccess : unitInterval := ⟨1/2, by norm_num, by norm_num⟩
def geometricClusterMeasure : Measure ℕ := (geometricMeasure halfSuccess).map Nat.succ
instance instProbabilityGeometric : IsProbabilityMeasure geometricClusterMeasure := by
  unfold geometricClusterMeasure
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
def clusterConfiguration (sample : ℕ × (ℕ → ℕ)) : ℕ →₀ ℕ :=
  ∑ i∈Finset.range sample.1, if 0<sample.2 i then Finsupp.single (sample.2 i-1) 1 else 0
theorem measurable_clusterConfiguration : Measurable clusterConfiguration := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun marks : ℕ → ℕ => ∑ i∈Finset.range n,
    if 0 < marks i then Finsupp.single (marks i-1) 1 else 0)
  exact Finset.measurable_sum _ (fun i _ =>
    (measurable_of_countable (fun h : ℕ => if 0<h then
      (Finsupp.single (h-1) 1 : ℕ →₀ ℕ) else 0)).comp (measurable_pi_apply i))
def configurationMeasure (rate : ℝ≥0) : Measure (ℕ →₀ ℕ) :=
  ((poissonMeasure rate).prod (Measure.infinitePi (fun _ : ℕ => geometricClusterMeasure))).map
    clusterConfiguration
instance instProbabilityConfiguration (rate : ℝ≥0) : IsProbabilityMeasure (configurationMeasure rate) := by
  unfold configurationMeasure
  exact Measure.isProbabilityMeasure_map measurable_clusterConfiguration.aemeasurable
def flattenRows (N : ℕ) (rows : (Fin N × F₂) → (ℕ →₀ ℕ)) : SpatialConfig N :=
  Finsupp.onFinset
    (Finset.univ.biUnion (fun i : Fin N × F₂ =>
      (rows i).support.image (fun e => (i.1,(e,i.2)))))
    (fun j => rows (j.1,j.2.2) j.2.1) (by
      intro j hj
      exact Finset.mem_biUnion.mpr ⟨(j.1,j.2.2),Finset.mem_univ _,
        Finset.mem_image.mpr ⟨j.2.1,Finsupp.mem_support_iff.mpr hj,rfl⟩⟩)
/- Independent rows, each an independent Poisson number of iid geometric
marks, give all independent signed atom rates 2^(-L-e-2). -/
def spatialTarget (N L : ℕ) : Measure (SpatialConfig N) :=
  (Measure.pi (fun _ : Fin N × F₂ => configurationMeasure (1/2^(L+1)))).map (flattenRows N)
def spatialTargetMass (N L : ℕ) : SpatialConfig N → ℝ := observableLaw (spatialTarget N L) id
def spatialDistance (N L : ℕ) : ℝ :=
  massTV (observableLaw infiniteRademacherMeasure (spatialSource N L)) (spatialTargetMass N L)
def scalarMeanDistance (N L Y : ℕ) : ℝ :=
  ∫ omega, environmentDistance Y (maskedCount L (dyadicBlock N)) (poissonMass (fullRate N L)) omega
    ∂infiniteRademacherMeasure
def spatialMeanDistance (N L Y : ℕ) : ℝ :=
  ∫ omega, environmentDistance Y (spatialSource N L) (spatialTargetMass N L) omega
    ∂infiniteRademacherMeasure
def spatialEventDistance (N L : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTV (conditionalLaw infiniteRademacherMeasure A (spatialSource N L)) (spatialTargetMass N L)
def criticalWindow (C : ℝ) (N L : ℕ) : Prop := |(L : ℝ)-Real.log N/Real.log 2| ≤ C
def criticalScale (N : ℕ) : ℝ := Real.sqrt (Real.log N*Real.log (Real.log N))
def hardRate (N L : ℕ) (epsilon eta : ℝ) : ℝ := (fullRate N L : ℝ)*
  (Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
    (N : ℝ)^(-(1/(3 : ℝ))+epsilon))
def softRate (N L : ℕ) (epsilon eta : ℝ) : ℝ :=
  Real.exp (-(saddleCutoff 2 (Real.log N)-max 0 (Real.log (fullRate N L)))/2+
    eta*saddleNu 2 (Real.log N))+(N : ℝ)^(-(1/(3 : ℝ))+epsilon)
def eventInformation (A : Set InfiniteSample) : ℝ := -Real.log (infiniteRademacherMeasure.real A)
end CriticalField

namespace CriticalField
/- Probability laws of finite point measures use the weak topology and its
Borel sigma-algebra. The limiting PPP is an actual independently marked sum. -/
local instance instTopologicalSign : TopologicalSpace F₂ := ⊥
local instance instDiscreteSign : DiscreteTopology F₂ := ⟨rfl⟩
def PointCloud := FiniteMeasure (ℝ × (ℕ × F₂))
instance instTopologicalPointCloud : TopologicalSpace PointCloud :=
  inferInstanceAs (TopologicalSpace (FiniteMeasure (ℝ × (ℕ × F₂))))
instance instMeasurablePointCloud : MeasurableSpace PointCloud := borel PointCloud
instance instBorelPointCloud : BorelSpace PointCloud := ⟨rfl⟩
instance instAddPointCloud : AddCommMonoid PointCloud :=
  inferInstanceAs (AddCommMonoid (FiniteMeasure (ℝ × (ℕ × F₂))))
def pointDirac (x : ℝ × (ℕ × F₂)) : PointCloud := (diracProba x).toFiniteMeasure
def spatialEmbedding (N : ℕ) (c : SpatialConfig N) : PointCloud :=
  c.sum (fun j n => n • pointDirac (1+(j.1.val : ℝ)/N,j.2))
def uniformPosition : Measure unitInterval := volume.comap ((↑) : unitInterval → ℝ)
instance instProbabilityUniformPosition : IsProbabilityMeasure uniformPosition := by
  constructor
  rw [uniformPosition,comap_subtype_coe_apply measurableSet_Icc,Set.image_univ,Subtype.range_coe]
  norm_num [Real.volume_Icc]
def diffuseMarkMeasure : Measure (unitInterval × (ℕ × F₂)) :=
  uniformPosition.prod ((geometricMeasure halfSuccess).prod coordinateMeasure)
instance instProbabilityDiffuseMark : IsProbabilityMeasure diffuseMarkMeasure := by
  unfold diffuseMarkMeasure; infer_instance
def diffuseSampleCloud (s : ℕ × (ℕ → unitInterval × (ℕ × F₂))) : PointCloud :=
  ∑ i∈Finset.range s.1, pointDirac (1+(s.2 i).1,(s.2 i).2)
def diffuseMeasure (rate : ℝ≥0) : Measure PointCloud :=
  ((poissonMeasure rate).prod (Measure.infinitePi (fun _ : ℕ => diffuseMarkMeasure))).map diffuseSampleCloud
end CriticalField

namespace CriticalField
def measureTV {α : Type*} [MeasurableSpace α] (mu nu : Measure α) : ℝ :=
  sSup {r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r=|mu.real A-nu.real A|}
end CriticalField

namespace CriticalField
open Analysis
local instance instPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance instFinitePrime (M : ℕ) : Fintype (PrimeUpTo M) := Subtype.fintype _
local instance instDecidablePrime (M : ℕ) : DecidableEq (PrimeUpTo M) := Classical.decEq _
def valueLinear (M n : ℕ) : SampleSpace M →ₗ[F₂] F₂ where
  toFun omega := ∑ p : PrimeUpTo M, omega p*parityVec n p.val
  map_add' omega eta := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c omega := by simp [Finset.mul_sum,mul_assoc]
def startRow (M x L : ℕ) (i : Fin L) : SampleSpace M →ₗ[F₂] F₂ :=
  if i.val=0 then valueLinear M (x-1)+valueLinear M x else valueLinear M x+valueLinear M (x+i.val)
def twoStartSystem (M x y L : ℕ) : SampleSpace M →ₗ[F₂] (Sum (Fin L) (Fin L) → F₂) :=
  LinearMap.pi (fun i => match i with | Sum.inl j => startRow M x L j | Sum.inr j => startRow M y L j)
def dotLinear {ι : Type*} [Fintype ι] (w : ι → F₂) : (ι → F₂) →ₗ[F₂] F₂ where
  toFun := dotProduct w
  map_add' y z := dotProduct_add w y z
  map_smul' c y := dotProduct_smul c w y
def relationMap {V ι : Type*} [AddCommGroup V] [Module F₂ V] [Fintype ι]
    (A : V →ₗ[F₂] (ι → F₂)) : (ι → F₂) →ₗ[F₂] (V →ₗ[F₂] F₂) where
  toFun u := (dotLinear u).comp A
  map_add' u v := by ext x; simp [dotLinear,add_dotProduct]
  map_smul' c u := by ext x; simp [dotLinear,smul_dotProduct]
def jointRho (N L : ℕ) (pair : ℕ × ℕ) : ℕ :=
  Module.finrank F₂ (LinearMap.ker (relationMap (twoStartSystem (2*N+L) pair.1 pair.2 L)))
def separatedPairs (mask : Finset ℕ) (L : ℕ) : Finset (ℕ × ℕ) :=
  (mask ×ˢ mask).filter (fun p => L<Nat.dist p.1 p.2)
def jointDefectMass (N L : ℕ) (pairs : Finset (ℕ × ℕ)) : ℕ :=
  ∑ p∈pairs, (2^jointRho N L p-1)
def HDefective (H n : ℕ) : Prop := ∀ p : ℕ, p.Prime → H<p → parityVec n p=0
def defectIndices (H x B : ℕ) : Finset (Fin B) :=
  Finset.univ.filter (fun i => HDefective H (x-1+i.val))
def fullDefectMass (L : ℕ) (mask : Finset ℕ) : ℕ :=
  ∑ x∈mask, (2^(defectIndices (L+1) x (L+1)).card-1)
def treeSupport (x L : ℕ) : Finset ℕ := insert (x-1) ((Finset.range L).image (fun j => x+j))
def fullBadStarts (N L Y : ℕ) : Finset ℕ :=
  (dyadicBlock N).filter (fun x => ∃ n∈treeSupport x L, HDefective Y n)
def retainedRate (N L Y : ℕ) (mask : Finset ℕ) : ℝ≥0 :=
  ⟨((mask \ fullBadStarts N L Y).card : ℝ)/2^L, by positivity⟩
def largeOddSupport (Y n : ℕ) : Finset ℕ :=
  (n.factorization.mapRange (fun e : ℕ => e%2) (by simp)).support.filter (fun p => Y<p)
def primeCoordinates (x L Y : ℕ) : Finset ℕ :=
  (treeSupport x L).biUnion (fun n => largeOddSupport Y n)
def supportEdges (L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  mask.offDiag.filter (fun p => p.1≠p.2 ∧ (primeCoordinates p.1 L Y ∩ primeCoordinates p.2 L Y).Nonempty)
/- These are the actual arithmetic costs: all defective vertices, all removed
sites including the root, and the full two-window relation space. -/
def maskedBudget (N L Y : ℕ) (mask : Finset ℕ) : ℝ :=
  ((fullDefectMass L mask : ℝ)+2*(mask ∩ fullBadStarts N L Y).card)/(2 : ℝ)^L+
    2*firstSteinFactor (retainedRate N L Y mask)*
      (((mask.card : ℝ)+(supportEdges L Y mask).card+
        (jointDefectMass N L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L))
end CriticalField

theorem source_measure_eq : infiniteRademacherMeasure =
    PaperC.InfiniteRademacher.infiniteRademacherMeasure := rfl
theorem value_eq (omega : InfiniteSample) (n : ℕ) : infiniteValueBit omega n =
    PaperC.InfiniteRademacher.infiniteValueBit omega n := rfl
theorem maskedCount_eq (L : ℕ) (mask : Finset ℕ) : maskedCount L mask =
    PaperC.V282.InfiniteMaskedScalarTransfer.infiniteMaskedCount L mask := rfl
theorem exactLengthCount_eq (N L e : ℕ) : infiniteExactLengthCount N L e =
    PaperC.MarkedDetruncation.infiniteExactLengthCount N L e := rfl
theorem fullRate_eq (N L : ℕ) : fullRate N L = PaperC.V282.AllStartSoftPoisson.fullRate N L := rfl
theorem restriction_eq (Y : ℕ) : restrictToFinite Y =
    PaperC.InfiniteCylinderTransfer.restrictToFinite Y := rfl
theorem observedAtom_eq (Y : ℕ) (omega : InfiniteSample) : observedAtom Y omega =
    PaperC.V282.InfiniteConditionalWords.infiniteSmallPrimeAtom Y Y
      (PaperC.V282.InfiniteConditionalWords.smallPrimeRestriction Y Y omega) := by
  symm
  exact PaperC.V282.FinitePrimeEnvironment.observed_atom_eq (le_refl Y) omega
theorem environmentDistance_eq {α : Type*} (Y : ℕ) (f : InfiniteSample → α)
    (q : α → ℝ) : environmentDistance Y f q =
      PaperC.V282.FinitePrimeEnvironment.environmentDistance Y Y f q := by
  funext omega
  unfold environmentDistance PaperC.V282.FinitePrimeEnvironment.environmentDistance
  rw [observedAtom_eq]
  rfl
namespace Process
theorem process_input_to_core (h : ProcessAGGStatement) :
    PaperC.V282.ProcessAGGInput.ProcessAGGStatement := by
  intro Ω ι instOmega instIota instDec mu X G hG
  let mu' : FinitePMF Ω := ⟨mu.prob,mu.nonneg,mu.sum_prob⟩
  exact h Ω ι mu' X G hG
end Process
theorem dyadicBlock_eq (N : ℕ) : dyadicBlock N = PaperC.dyadicBlock N := rfl
theorem massTV_eq {α : Type*} (p q : α → ℝ) : massTV p q =
    PaperC.V282.FiniteFieldTotalVariation.massTotalVariation p q := rfl
theorem conditionalLaw_eq {Ω α : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (A : Set Ω) (f : Ω → α) : conditionalLaw mu A f =
      PaperC.V282.ConditionedCountableLaw.conditionalObservableLaw mu A f := rfl
theorem observableLaw_eq {Ω α : Type*} [MeasurableSpace Ω] (mu : Measure Ω) (f : Ω → α) :
    observableLaw mu f = PaperC.V282.InfiniteMassCoupling.observableLaw mu f := rfl

namespace Analysis
theorem pnt_input_eq : PrimeNumberTheoremRemainder =
    PaperC.V282.PrimeEulerPNT.PrimeNumberTheoremRemainder := rfl
theorem scalar_input_eq : ScalarSteinFactorsStatement =
    PaperC.V282.ScalarSteinInput.ScalarSteinFactorsStatement := rfl
theorem saddleParameter_eq (a H : ℝ) : saddleParameter a H =
    PaperC.V282.SaddleParameters.saddleParameter a H := by
  unfold saddleParameter PaperC.V282.SaddleParameters.saddleParameter
  change (if 0<a ∧ PaperC.V282.SaddleParameters.saddleThreshold a≤H then
    Classical.epsilon (fun u : ℝ => PaperC.V282.SaddleParameters.saddleParameterBase≤u ∧
      PaperC.V282.SaddleParameters.saddleHeight a u=H) else _) = _
  split_ifs with h
  · have he := PaperC.V282.SaddleParameters.existsUnique_saddleHeight h.1 h.2
    exact (Classical.choose_spec he).2 _ (Classical.epsilon_spec he.exists)
  · rfl
theorem saddleCutoff_eq (a H : ℝ) : saddleCutoff a H =
    PaperC.V282.SaddleParameters.saddleCutoff a H := by
  unfold saddleCutoff PaperC.V282.SaddleParameters.saddleCutoff
  rw [saddleParameter_eq]; rfl
theorem saddleNu_eq (a H : ℝ) : saddleNu a H = PaperC.V282.SaddleScales.saddleNu a H := by
  unfold saddleNu PaperC.V282.SaddleScales.saddleNu; rw [saddleCutoff_eq]
theorem hardCutoff_eq (N : ℕ) : hardCutoff N = PaperC.V282.HardPoissonRates.hardCutoff N := by
  unfold hardCutoff PaperC.V282.HardPoissonRates.hardCutoff; rw [saddleCutoff_eq]
theorem softCutoff_eq (N : ℕ) : softCutoff N = PaperC.V282.SoftRateAssembly.softCutoff N := by
  unfold softCutoff PaperC.V282.SoftRateAssembly.softCutoff; rw [saddleCutoff_eq]
end Analysis

namespace CriticalField
theorem poissonMass_eq (rate : ℝ≥0) : Analysis.poissonMass rate =
    PaperC.V282.ScalarSteinInput.poissonMass rate := rfl
theorem spatialSource_eq (N L : ℕ) : spatialSource N L =
    PaperC.V282.SpatialMarkedSource.spatialMarkedSource N L := by
  funext omega
  apply Finsupp.ext
  intro j
  have hc : ∀ j : SpatialIndex N,
      PaperC.V282.SpatialMarkedSource.spatialMarkedSource N L omega j =
        if ExactLengthEvent (infiniteValueBit omega) (N+j.1.val) (L+j.2.1+1) ∧
          infiniteValueBit omega (N+j.1.val)=j.2.2 then 1 else 0 := by
    intro j
    simp only [PaperC.V282.SpatialMarkedSource.spatialMarkedSource_apply,
      PaperC.V282.SpatialMarkedSource.spatialMarkedValue, PaperC.V282.ExactMarkedModel.signedMarkValue]
    split_ifs <;> first | rfl | contradiction
  have hex : ∃ c : SpatialConfig N, ∀ j : SpatialIndex N, c j =
      if ExactLengthEvent (infiniteValueBit omega) (N+j.1.val) (L+j.2.1+1) ∧
        infiniteValueBit omega (N+j.1.val)=j.2.2 then 1 else 0 := ⟨_,hc⟩
  exact (Classical.epsilon_spec hex j).trans (hc j).symm

 theorem spatialTarget_eq (N L : ℕ) : spatialTarget N L =
    PaperC.V282.SpatialMarkedTarget.spatialTargetMeasure N L := rfl
theorem spatialTargetMass_eq (N L : ℕ) : spatialTargetMass N L =
    PaperC.V282.SpatialMarkedFieldComparison.spatialTargetLaw N L := rfl
theorem spatialDistance_eq (N L : ℕ) : spatialDistance N L =
    PaperC.V282.SpatialMarkedFieldComparison.spatialSignedDistance N L := by
  unfold spatialDistance; rw [spatialSource_eq]; rfl
theorem scalarMeanDistance_eq (N L Y : ℕ) (hY : Y ≤ PaperC.dyadicCutoff N L) :
    scalarMeanDistance N L Y = PaperC.V282.DyadicPoissonDistance.conditionalDistance N L Y := by
  unfold scalarMeanDistance
  rw [environmentDistance_eq,source_measure_eq,PaperC.V282.FinitePrimeEnvironment.integral_environmentDistance]
  rw [← PaperC.V282.FinitePrimeEnvironment.meanAtomDistance_eq_canonical hY]
  exact PaperC.V282.MeanScalarBudget.mean_scalar_eq N L Y
end CriticalField

namespace CriticalField
open Analysis Process

/-- Literal coefficients, including every excess and both signs, with no input premise. -/
theorem exact_source_coefficients (N L : ℕ) (omega : InfiniteSample) (j : SpatialIndex N) :
    spatialSource N L omega j =
      if ExactLengthEvent (infiniteValueBit omega) (N+j.1.val) (L+j.2.1+1) ∧
        infiniteValueBit omega (N+j.1.val)=j.2.2 then 1 else 0 := by
  rw [spatialSource_eq]
  simp only [PaperC.V282.SpatialMarkedSource.spatialMarkedSource_apply,
    PaperC.V282.SpatialMarkedSource.spatialMarkedValue,PaperC.V282.ExactMarkedModel.signedMarkValue]
  split_ifs <;> first | rfl | contradiction

/-- The complete signed lattice estimate, uniform before choosing the length. -/
theorem critical_lattice (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (C a : ℝ) (hC : 0 ≤ C) (ha : a < 1/Real.sqrt 2) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, criticalWindow C N L →
      spatialDistance N L ≤ Real.exp (-a*criticalScale N) := by
  simpa only [spatialDistance_eq,criticalWindow,criticalScale,
    PaperC.CriticalRunWindow.InRunLengthWindow,PaperC.V282.SaddleErrorExponent.criticalScale] using
    PaperC.V282.SpatialMarkedCritical.theorem_one_one_lattice
      (process_input_to_core hAGG) hPNT C hC a ha

/-- The actual start count has Poisson parameter N/2^L, not a retained intensity. -/
theorem critical_start_count (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (C a : ℝ) (hC : 0 ≤ C) (ha : a < 1/Real.sqrt 2) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, criticalWindow C N L →
      massTV (observableLaw infiniteRademacherMeasure (maskedCount L (dyadicBlock N)))
        (poissonMass (fullRate N L)) ≤ Real.exp (-a*criticalScale N) := by
  exact PaperC.V282.SpatialMarkedStatistics.theorem_one_one_start_count
    (process_input_to_core hAGG) hPNT C hC a ha

/-- Every deterministic restriction or statistic preserves the same complete-field error. -/
theorem deterministic_statistic (N L : ℕ) {α : Type*} (stat : SpatialConfig N → α) :
    massTV (observableLaw infiniteRademacherMeasure (stat ∘ spatialSource N L))
      (observableLaw (spatialTarget N L) stat) ≤ spatialDistance N L := by
  rw [spatialSource_eq,spatialTarget_eq,spatialDistance_eq]
  exact PaperC.V282.SpatialMarkedStatistics.spatial_statistic_tv_le N L stat

/-- Equation (4.8) for actual conditional laws on the full small-prime atoms. -/
theorem hard_conditional (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (lo hi epsilon eta : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (heps : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      lo*Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ hi*Real.log N →
      scalarMeanDistance N L (hardCutoff N) ≤ 20*min 1 (hardRate N L epsilon eta) := by
  obtain ⟨N0,h0⟩ := PaperC.V282.HardPoissonRates.hard_conditional_rate_eventually
    hStein hPNT lo hi epsilon eta hlo hhi heps heta
  refine ⟨N0,?_⟩
  intro N hN L hL hL'
  obtain ⟨hY,hd⟩ := h0 N hN L hL hL'
  rw [hardCutoff_eq,scalarMeanDistance_eq N L _ hY]
  have hm := PaperC.V282.DyadicPoissonDistance.le_mul_min_one_of_le (by norm_num : (1 : ℝ) ≤ 20)
    (PaperC.V282.DyadicPoissonDistance.conditionalDistance_le_one N L _) hd
  simpa only [hardRate,PaperC.V282.HardPoissonRates.hardRate,saddleCutoff_eq,saddleNu_eq,fullRate_eq] using hm

/-- Equation (4.9); the second saddle and logarithm of the actual intensity are retained. -/
theorem soft_conditional (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (lo hi epsilon eta : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (heps : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      lo*Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ hi*Real.log N →
      scalarMeanDistance N L (softCutoff N) ≤ 6*min 1 (softRate N L epsilon eta) := by
  obtain ⟨N0,h0⟩ := PaperC.V282.SoftRateAssembly.soft_conditional_rate_eventually
    hStein hPNT lo hi epsilon eta hlo hhi heps heta
  refine ⟨N0,?_⟩
  intro N hN L hL hL'
  obtain ⟨hY,hd⟩ := h0 N hN L hL hL'
  rw [softCutoff_eq,scalarMeanDistance_eq N L _ hY]
  simpa only [softRate,PaperC.V282.SoftRateAssembly.softRate,saddleCutoff_eq,saddleNu_eq,fullRate_eq] using hd

/-- The whole spatial law under a positive hard small-prime event, including lambda<1. -/
theorem spatial_hard_conditioning (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (lo hi K c : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (hc : 0 < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      lo*Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ hi*Real.log N →
      (fullRate N L : ℝ) ≤ K → ∀ A : Set InfiniteSample,
      MeasurableSet[primeSigma (hardCutoff N)] A → 0 < infiniteRademacherMeasure.real A →
      eventInformation A ≤ saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      spatialEventDistance N L A ≤ 32*Real.exp (-(c/4)*saddleNu 1 (Real.log N))+
        32*(N : ℝ)^(-(1/(12 : ℝ)))+3*Real.exp (-saddleCutoff 1 (Real.log N)) := by
  obtain ⟨N0,h0⟩ := PaperC.V282.SpatialBoundedInformation.spatial_event_bound
    (process_input_to_core hAGG) hPNT lo hi K c hlo hhi hc
  refine ⟨N0,?_⟩
  intro N hN L hlo' hhi' hK A hA hp hI
  change MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] A at hA
  rw [hardCutoff_eq] at hA
  have hI' := hI
  simp only [saddleCutoff_eq,saddleNu_eq] at hI'
  have h := h0 N hN L hlo' hhi' hK A hA hp hI'
  simpa only [spatialEventDistance,spatialSource_eq,spatialTargetMass_eq,
    PaperC.V282.SpatialMarkedEventComparison.spatialEventDistance,saddleCutoff_eq,saddleNu_eq,
    massTV_eq,conditionalLaw_eq,source_measure_eq] using h

/-- The distinct soft information domain for the complete spatial signed law. -/
theorem spatial_soft_conditioning (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (lo hi c : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (hc : 0 < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      lo*Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ hi*Real.log N →
      1 ≤ (fullRate N L : ℝ) → ∀ A : Set InfiniteSample,
      MeasurableSet[primeSigma (softCutoff N)] A → 0 < infiniteRademacherMeasure.real A →
      eventInformation A+Real.log (fullRate N L) ≤
        saddleCutoff 2 (Real.log N)/2-c*saddleNu 2 (Real.log N) →
      spatialEventDistance N L A ≤ 64*Real.exp (-(c/2)*saddleNu 2 (Real.log N))+
        64*(N : ℝ)^(-(1/(12 : ℝ)))+3*Real.exp (-saddleCutoff 2 (Real.log N)) := by
  obtain ⟨N0,h0⟩ := PaperC.V282.SpatialMarkedMovableBudget.movable_labelled_event_bound
    (process_input_to_core hAGG) hPNT lo hi c hlo hhi hc
  refine ⟨N0,?_⟩
  intro N hN L hlo' hhi' hr A hA hp hI
  change MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance] A at hA
  rw [softCutoff_eq] at hA
  have hI' := hI
  simp only [saddleCutoff_eq,saddleNu_eq] at hI'
  have h := h0 N hN L hlo' hhi' hr A hA hp hI'
  simpa only [spatialEventDistance,spatialSource_eq,spatialTargetMass_eq,
    PaperC.V282.SpatialMarkedEventComparison.spatialEventDistance,saddleCutoff_eq,saddleNu_eq,
    massTV_eq,conditionalLaw_eq,source_measure_eq] using h

/-- One almost-sure event controls all admissible lengths on every geometric lower scale. -/
theorem uniform_quenched_scalar (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes : ℕ → ℕ) (hg : ∃ A : ℝ, 0 < A ∧ ∀ᶠ k : ℕ in atTop, (k : ℝ) ≤ A*Real.log (sizes k))
    (lo hi c beta : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (hb : 0 < beta) (hbc : beta < c) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop, ∀ L : ℕ,
      lo*Real.log (sizes k) ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ hi*Real.log (sizes k) →
      max 0 (Real.log (fullRate (sizes k) L)) ≤
        saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k)) →
      environmentDistance (hardCutoff (sizes k)) (maskedCount L (dyadicBlock (sizes k)))
        (poissonMass (fullRate (sizes k) L)) omega ≤ Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  have h := PaperC.V282.QuenchedScalarBand.corollary_six_four_uniform_scalar
    hStein hPNT sizes hg lo hi c beta hlo hhi hb hbc
  simpa only [environmentDistance_eq,hardCutoff_eq,saddleCutoff_eq,saddleNu_eq,
    PaperC.V282.QuenchedScalarBand.scalarEnvironmentDistance,fullRate_eq,maskedCount_eq,source_measure_eq,
    dyadicBlock_eq,poissonMass_eq] using h
end CriticalField

namespace CriticalField
open Analysis Process
/-- Weak convergence on arbitrary diverging subsequences, retaining positions,
all excesses and signs. The target has uniform [1,2] positions, geometric
excesses and fair signs, independent of its Poisson number of atoms. -/
theorem critical_diffuse (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (C : ℝ) (hC : 0 ≤ C) (sizes lengths : ℕ → ℕ) (rate : ℝ≥0)
    (hsizes : Tendsto sizes atTop atTop)
    (hwindow : ∀ᶠ j in atTop, criticalWindow C (sizes j) (lengths j))
    (hrate : Tendsto (fun j => (fullRate (sizes j) (lengths j) : ℝ)) atTop (𝓝 (rate : ℝ))) :
    ∃ laws : ℕ → ProbabilityMeasure PointCloud, ∃ target : ProbabilityMeasure PointCloud,
      (∀ j, (laws j : Measure PointCloud)=infiniteRademacherMeasure.map
        (spatialEmbedding (sizes j) ∘ spatialSource (sizes j) (lengths j))) ∧
      (target : Measure PointCloud)=diffuseMeasure rate ∧ Tendsto laws atTop (𝓝 target) := by
  refine ⟨fun j => PaperC.V282.SpatialMarkedDiffuse.spatialPointSourceLaw (sizes j) (lengths j),
    PaperC.V282.SpatialPointConvergence.diffusePoissonLaw rate,?_,?_,?_⟩
  · intro j
    rw [spatialSource_eq]
    rfl
  · rfl
  · exact PaperC.V282.SpatialMarkedDiffuse.theorem_one_one_diffuse
      (process_input_to_core hAGG) hPNT C hC sizes lengths rate hsizes hwindow hrate
end CriticalField

namespace CriticalField
/-- Any full-F_Y recorded variable remains in the joint law. The right side
is the actual conditional mean, not a supplied TV conclusion. -/
theorem stable_small_prime_record {β γ : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    [Nonempty β] [Countable β] [MeasurableSingletonClass β] [MeasurableSpace γ]
    (Y : ℕ) (f : InfiniteSample → β) (hf : Measurable f) (nu : Measure β) [IsProbabilityMeasure nu]
    (V : InfiniteSample → γ) (hV : Measurable[primeSigma Y] V)
    (D : Set InfiniteSample) (hD : MeasurableSet[primeSigma Y] D)
    (hpos : 0 < infiniteRademacherMeasure.real D) :
    measureTV ((cond infiniteRademacherMeasure D).map f) nu ≤
      (∫ omega, environmentDistance Y f (observableLaw nu id) omega ∂infiniteRademacherMeasure) /
        infiniteRademacherMeasure.real D ∧
    measureTV ((cond infiniteRademacherMeasure D).map (fun omega => (V omega,f omega)))
      (((cond infiniteRademacherMeasure D).map V).prod nu) ≤
      (∫ omega, environmentDistance Y f (observableLaw nu id) omega ∂infiniteRademacherMeasure) /
        infiniteRademacherMeasure.real D := by
  have h := PaperC.V282.PrimeEnvironmentStableLift.fullFY_conditioned_stable_product_lift
    (C:=Y) (le_refl Y) f hf nu _ (le_refl _) V hV D hD hpos
  simpa only [environmentDistance_eq,source_measure_eq,measureTV,
    PaperC.V282.SharpConditioning.measureTotalVariation,observableLaw_eq,
    PaperC.V282.FinitePrimeEnvironment.integral_environmentDistance] using h
end CriticalField

namespace CriticalField
open Analysis
theorem defectMass_eq (L : ℕ) (mask : Finset ℕ) : fullDefectMass L mask =
    PaperC.V282.MaskedArithmeticGeometry.fullDefectMass L mask := by
  unfold fullDefectMass PaperC.V282.MaskedArithmeticGeometry.fullDefectMass
  apply Finset.sum_congr rfl
  intro x hx
  congr 2
theorem badStarts_eq (N L Y : ℕ) : fullBadStarts N L Y =
    PaperC.V282.MaskedArithmeticGeometry.fullBadStarts N L Y := rfl
theorem edges_eq (L Y : ℕ) (mask : Finset ℕ) : supportEdges L Y mask =
    PaperC.V282.MaskedPairGeometry.maskedSupportEdges L Y mask := by
  unfold supportEdges PaperC.V282.MaskedPairGeometry.maskedSupportEdges
  apply Finset.filter_congr
  intro p hp
  rfl
theorem jointMass_eq (N L : ℕ) (pairs : Finset (ℕ × ℕ)) : jointDefectMass N L pairs =
    PaperC.SectionTwelveMoments.jointDefectMass N L pairs := by
  unfold jointDefectMass PaperC.SectionTwelveMoments.jointDefectMass
  apply Finset.sum_congr rfl
  intro p hp
  congr 2
/-- The full-F_Y masked scalar kernel bound, for every cutoff Y≥2L and
all deterministic masks, with the costs explicitly computed above. -/
theorem masked_conditional_kernel (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2*L ≤ Y) :
    (∫ omega, environmentDistance Y (maskedCount L mask) (poissonMass (maskRate L mask)) omega
      ∂infiniteRademacherMeasure) ≤ maskedBudget N L Y mask := by
  have h := (PaperC.V282.MaskedScalarFullConditioning.theorem_four_one_scalar_full_FY
    hStein mask hmask hN hL hY).2
  rw [environmentDistance_eq,source_measure_eq,
    PaperC.V282.FinitePrimeEnvironment.integral_environmentDistance,
    ← PaperC.V282.FinitePrimeEnvironment.meanAtomDistance_eq_canonical
      (le_max_right (PaperC.dyadicCutoff N L) Y)]
  unfold PaperC.V282.CountablePrimeEventTransfer.meanAtomDistance
  unfold PaperC.V282.FiniteFieldTotalVariation.massTotalVariation
  simp_rw [PaperC.V282.ConditionedCountableLaw.conditionalObservableLaw_eq_ratio _ _
    (PaperC.V282.InfiniteConditionalWords.measurableSet_infiniteSmallPrimeAtom _ _ _) _ _]
  convert h using 1
  · rfl
  · simp only [maskedBudget,defectMass_eq,badStarts_eq,edges_eq,jointMass_eq]
    rfl
end CriticalField

namespace CriticalField
open Analysis Process
/-- Mean conditional TV for the complete signed field, uniformly on the
whole length band with the true two-intensity information cost. -/
theorem spatial_conditional_mean (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (lo hi c c' : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (hc' : 0 < c') (hcc : c' < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      lo*Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ hi*Real.log N →
      1 ≤ (fullRate N L : ℝ) →
      Real.log (fullRate N L)+Real.log (1+(fullRate N L : ℝ)) ≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      spatialMeanDistance N L (hardCutoff N) ≤ 67*Real.exp (-c'*saddleNu 1 (Real.log N)) := by
  have h := PaperC.V282.MeanSpatialBudget.integral_spatial_hard_rate
    (process_input_to_core hAGG) hPNT lo hi c c' hlo hhi hc' hcc
  simpa only [spatialMeanDistance,environmentDistance_eq,spatialSource_eq,spatialTargetMass_eq,
    source_measure_eq,hardCutoff_eq,saddleCutoff_eq,saddleNu_eq,fullRate_eq,
    PaperC.V282.LabelledInformationBudget.labelledLogCost,zero_add] using h
end CriticalField

end PaperCV3Audit
end
