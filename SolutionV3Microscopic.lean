import PaperCV282.MicroscopicBoundaryDominance
import PaperCV282.MesoscopicStability
import PaperCV282.PrefixAlmostSureEnvelopes
import PaperCV282.PrefixCriticalVoid

import PaperCPrel8.MicroscopicNormalization
import PaperCPrel8.EmpiricalPaperTheorem
import PaperCPrel8.EmpiricalSupportTheorem
import PaperCPrel8.DyadicMicroscopicTheorem

namespace PaperCV3Audit
noncomputable section
local instance instDecidableProp (P : Prop) : Decidable P := Classical.propDecidable P
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

namespace Boundary
open Analysis
instance instFintypePrimeUpTo (Y : ℕ) : Fintype (PrimeUpTo Y) := by
  unfold PrimeUpTo; infer_instance
/- Three additional published arithmetic statements, fully displayed. -/
def consecutiveProduct (n k : ℕ) : ℕ := ∏ i ∈ Finset.range k, (n+i)
def UniformPrimeDivisorStatement : Prop :=
  ∀ epsilon : ℝ, 0<epsilon → ∃ kzero : ℕ, ∀ k : ℕ, kzero≤k → 2≤k → ∀ n : ℕ, k<n →
    (2-epsilon)*(Fintype.card (PrimeUpTo k) : ℝ) ≤
      ((consecutiveProduct n k).primeFactors.card : ℝ)
def shoreyMu (k : ℕ) (theta : ℝ) : ℝ := (k : ℝ)*(1-
  Real.log (Real.log k)/Real.log k + Real.log (Real.log (Real.log k))/Real.log k+theta/Real.log k)
def ShoreySquareProductStatement : Prop :=
  ∃ theta : ℝ, ∀ epsilon : ℝ, 0<epsilon → ∃ Kzero : ℕ, ∀ k≥Kzero,
    ∀ z b y : ℕ, ∀ offsets : Finset ℕ,
    2≤offsets.card → offsets⊆Finset.range k → 0<b → 0<y →
    (∀ p∈b.primeFactors, p≤k) → (∏ d∈offsets, (z+d))=b*y^2 →
    Real.exp (1-theta+epsilon)*((k : ℝ)*Real.log k/Real.log (Real.log k))<z →
    (offsets.card : ℝ)<shoreyMu k theta
def DivisorLogBoundStatement : Prop := ∀ n : ℕ, 64≤n →
  Real.log (n.divisors.card : ℝ)*Real.log (Real.log n) ≤ 2*Real.log 2*Real.log n
/- Literal events, source measures and contained-prefix observables. -/
def startEvent (x L : ℕ) : Set InfiniteSample := {omega | StartEvent (infiniteValueBit omega) x L}
def borderEvent (L : ℕ) : Set InfiniteSample :=
  {omega | ∀ n : ℕ, 1≤n → n≤L → infiniteValueBit omega n=0}
def interiorEvent (L : ℕ) : Set InfiniteSample := ⋃ x∈Finset.Icc 2 (2*L^2), startEvent x L
def microscopicEvent (L : ℕ) : Set InfiniteSample := borderEvent L ∪ interiorEvent L
def microscopicProbability (L : ℕ) : ℝ := infiniteRademacherMeasure.real (microscopicEvent L)
def uniqueBorderEvent (L : ℕ) : Set InfiniteSample := borderEvent L \ interiorEvent L
def measureTV {α : Type*} [MeasurableSpace α] (mu nu : Measure α) : ℝ :=
  sSup {r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r=|mu.real A-nu.real A|}
def extraEvent (L T : ℕ) : Set InfiniteSample := ⋃ x∈Finset.Ioc (2*L^2) T, startEvent x L
def enlargedEvent (L T : ℕ) : Set InfiniteSample := microscopicEvent L ∪ extraEvent L T
def microscopicRecord (L T : ℕ) (omega : InfiniteSample) (x : ℕ) : Bool :=
  if x=1 then if omega∈borderEvent L then true else false
  else if x∈Finset.Icc 2 (max (2*L^2) T) then
    if omega∈startEvent x L then true else false else false
def PrefixConstantStretch (g : ℕ → F₂) (M x L : ℕ) : Prop :=
  1≤x ∧ x+L≤M+1 ∧ ∀ j : ℕ, j<L → g (x+j)=g x
def prefixHasConstantStretch (g : ℕ → F₂) (M L : ℕ) : Prop :=
  ∃ x : ℕ, PrefixConstantStretch g M x L
def prefixLengths (g : ℕ → F₂) (M : ℕ) : Finset ℕ :=
  (Finset.range (M+1)).filter (prefixHasConstantStretch g M)
theorem prefixLengths_nonempty (g : ℕ → F₂) (M : ℕ) : (prefixLengths g M).Nonempty := by
  refine ⟨0, ?_⟩
  simp only [prefixLengths, Finset.mem_filter, Finset.mem_range, Nat.zero_lt_succ, true_and]
  exact ⟨1, by simp [PrefixConstantStretch]⟩
def longestRun (M : ℕ) (omega : InfiniteSample) : ℕ :=
  (prefixLengths (infiniteValueBit omega) M).max' (prefixLengths_nonempty _ _)
def prefixCount (M L : ℕ) (omega : InfiniteSample) : ℕ :=
  (if omega∈borderEvent L then 1 else 0)+maskedCount L (Finset.Icc 2 (M-L+1)) omega
def prefixLaw (M L : ℕ) : ℕ → ℝ := observableLaw infiniteRademacherMeasure (prefixCount M L)
def InRunLengthWindow (C : ℝ) (M L : ℕ) : Prop := |(L : ℝ)-Real.log M/Real.log 2|≤C
def hardRate (M L : ℕ) (epsilon eta : ℝ) : ℝ := (fullRate M L : ℝ)*
  (Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M))+
    (M : ℝ)^(-(1/(3 : ℝ))+epsilon))
def upperAdditiveConstant (epsilon : ℝ) : ℝ := 3+epsilon+Real.log (2/Real.log 2)/Real.log 2
end Boundary
/-! # Microscopic signed fields and empirical Poisson laws

The objects below are constructed directly from independent prime signs and
independent Poisson/geometric variables. Literature inputs remain explicit.
The counted runs start at their left boundary and retain all signed excesses.
-/

namespace Analysis
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

end Analysis

/-! The complete microscopic field, retaining integer positions, excesses and both signs. -/
namespace Microscopic
open Analysis Boundary
@[reducible] def MarkIndex (sites : Finset ℕ) := {x : ℕ // x ∈ sites} × (ℕ × F₂)
@[reducible] def Config (sites : Finset ℕ) := MarkIndex sites →₀ ℕ
instance instMeasurableConfig (sites : Finset ℕ) : MeasurableSpace (Config sites) := ⊤
instance instSingletonConfig (sites : Finset ℕ) : MeasurableSingletonClass (Config sites) := by infer_instance
/-- The unique finitely supported array of actual signed exact-run indicators.
Its coefficients are verified by a selected theorem, rather than assumed. -/
def source (sites : Finset ℕ) (L : ℕ) (omega : InfiniteSample) : Config sites :=
  Classical.epsilon (fun c => ∀ j : MarkIndex sites, c j =
    if ExactLengthEvent (infiniteValueBit omega) j.1.val (L+j.2.1+1) ∧
      infiniteValueBit omega j.1.val=j.2.2 then 1 else 0)
instance instMeasurableCluster : MeasurableSpace (ℕ →₀ ℕ) := ⊤
instance instSingletonCluster : MeasurableSingletonClass (ℕ →₀ ℕ) := by infer_instance
def halfSuccess : unitInterval := ⟨1/2, by norm_num, by norm_num⟩
def geometricClusterMeasure : Measure ℕ := (geometricMeasure halfSuccess).map Nat.succ
instance instProbabilityGeometric : IsProbabilityMeasure geometricClusterMeasure := by
  unfold geometricClusterMeasure
  exact ((Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr inferInstance)
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
  exact ((Measure.isProbabilityMeasure_map_iff measurable_clusterConfiguration.aemeasurable).mpr inferInstance)

/-- Assemble the independent geometric-Poisson rows into their finite configuration. -/
def flattenRows (sites : Finset ℕ) (rows : ({x : ℕ // x ∈ sites} × F₂) → (ℕ →₀ ℕ)) : Config sites :=
  Finsupp.onFinset
    (Finset.univ.biUnion (fun i : {x : ℕ // x ∈ sites} × F₂ =>
      (rows i).support.image (fun e => (i.1,(e,i.2)))))
    (fun j => rows (j.1,j.2.2) j.2.1) (by
      intro j hj
      exact Finset.mem_biUnion.mpr ⟨(j.1,j.2.2),Finset.mem_univ _,
        Finset.mem_image.mpr ⟨j.2.1,Finsupp.mem_support_iff.mpr hj,rfl⟩⟩)
/-- Independent Poisson atoms with rates 2^(-L-e-2), for every excess e and sign. -/
def target (sites : Finset ℕ) (L : ℕ) : Measure (Config sites) :=
  (Measure.pi (fun _ : {x : ℕ // x ∈ sites} × F₂ => configurationMeasure (1/2^(L+1)))).map (flattenRows sites)
/-- Actual start positions 2,...,M-L+1; the exceptional left border is excluded. -/
def interior (M L : ℕ) : Finset ℕ := (Finset.Icc 1 (M-L)).image (fun j => j+1)
def distance (M L : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTV (conditionalLaw infiniteRademacherMeasure A (source (interior M L) L))
    (observableLaw (target (interior M L) L) id)
def information (A : Set InfiniteSample) : ℝ := -Real.log (infiniteRademacherMeasure.real A)
def siteRate (M L : ℕ) : ℝ := (M-L:ℕ)/(2:ℝ)^L
/-- Literal moving-depth length; initial degenerate values use natural subtraction. -/
def paperLength (M depth : ℕ) : ℕ := ⌊Real.log M/Real.log 2⌋₊-depth
/-- Literal excess cutoff in the paper's microscopic comparison. -/
def excess (M L : ℕ) (I : ℝ) : ℕ :=
  ⌈(I+saddleCutoff 1 (Real.log M)+Real.log (2+(fullRate M L:ℝ)))/Real.log 2⌉₊
/-- Maximum prime with odd valuation, totalized to 1 when that support is empty. -/
def pivot (n : ℕ) : ℕ := max 1 ((n.factorization.mapRange (fun e : ℕ => e%2) (by simp)).support.sup id)
def goodSites (M L : ℕ) (I : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (M-L)).filter fun j => ⌈Real.sqrt M⌉₊ ≤ j+1 ∧
    ∀ a : Fin (L+excess M L I+2), hardCutoff M < pivot (j+a.val)
/-- Only the literature's analytic solution bounds for this actual finite carrier.
This is an explicit premise, not an arithmetic comparison or assumed conclusion. -/
def markRate (L e : ℕ) : ℝ≥0 := ⟨1/(2:ℝ)^(L+e+2),by positivity⟩
def SteinInput (M L : ℕ) (I : ℝ) : Prop :=
  DirectionalSolutionBounds (fun j : {j // j ∈ goodSites M L I} × (Fin (excess M L I+1) × F₂) =>
    markRate L j.2.1.val)
/-- Exact dyadic scales of the empirical count law. -/
def size (k : ℕ) : ℕ := 2^k
def length (alpha : ℝ) (k : ℕ) : ℕ := k-⌊alpha*saddleCutoff 1 (Real.log (size k))/Real.log 2⌋₊
def windowSize (alpha tau : ℝ) (k : ℕ) : ℕ := ⌊tau*(2:ℝ)^(length alpha k)⌋₊
def origins (alpha tau : ℝ) (k : ℕ) : ℕ := size k-length alpha k-windowSize alpha tau k+1
/-- Relative origin u counts left-maximal starts at u+2,...,u+h+1. -/
def windowCount (M L h u : ℕ) (omega : InfiniteSample) : ℕ :=
  ∑ i ∈ (Finset.univ : Finset (Fin (M-L))).filter (fun i => u ≤ i.val ∧ i.val < u+h),
    if StartEvent (infiniteValueBit omega) (i.val+2) L then 1 else 0
def frequency (alpha tau : ℝ) (k r : ℕ) (omega : InfiniteSample) : ℝ :=
  (∑ u : Fin (origins alpha tau k),
    if windowCount (size k) (length alpha k) (windowSize alpha tau k) u.val omega=r then (1:ℝ) else 0)/
    origins alpha tau k
end Microscopic

open Boundary Analysis
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
end Analysis

namespace Microscopic
open Analysis Boundary

theorem source_eq (sites : Finset ℕ) (L : ℕ) :
    source sites L = PaperC.V282.BulkMarkedSource.spatialMarkedSource sites L := by
  funext omega
  have h : ∃ c : Config sites, ∀ j : MarkIndex sites, c j =
      if ExactLengthEvent (infiniteValueBit omega) j.1.val (L+j.2.1+1) ∧
        infiniteValueBit omega j.1.val=j.2.2 then 1 else 0 :=
    by
      refine ⟨PaperC.V282.BulkMarkedSource.spatialMarkedSource sites L omega, ?_⟩
      intro j
      simp only [PaperC.V282.BulkMarkedSource.spatialMarkedSource_apply,
        PaperC.V282.BulkMarkedSource.spatialMarkedValue,PaperC.V282.ExactMarkedModel.signedMarkValue]
      split_ifs <;> first | rfl | contradiction
  apply Finsupp.ext
  intro j
  have hc := Classical.epsilon_spec h j
  change source sites L omega j = _ at hc
  rw [hc]
  simp only [PaperC.V282.BulkMarkedSource.spatialMarkedSource_apply,
    PaperC.V282.BulkMarkedSource.spatialMarkedValue,PaperC.V282.ExactMarkedModel.signedMarkValue]
  split_ifs <;> first | rfl | contradiction
theorem target_eq (sites : Finset ℕ) (L : ℕ) :
    target sites L = PaperC.V282.BulkMarkedTarget.spatialTargetMeasure sites L := rfl
theorem excess_eq (M L : ℕ) (I : ℝ) :
    excess M L I = PaperC.Prel8.MicroscopicProfileBudget.paperExcess M L I := by
  unfold excess PaperC.Prel8.MicroscopicProfileBudget.paperExcess
    PaperC.Prel8.MicroscopicInformationCutoff.excessCutoff
  rw [saddleCutoff_eq]
  rfl
theorem goodSites_eq (M L : ℕ) (I : ℝ) :
    goodSites M L I = PaperC.Prel8.MicroscopicRetainedTheorem.actualSites M L I := by
  unfold goodSites PaperC.Prel8.MicroscopicRetainedTheorem.actualSites
    PaperC.Prel8.MicroscopicGoodField.goodSites
  rw [excess_eq,hardCutoff_eq]
  rfl
theorem stein_eq (M L : ℕ) (I : ℝ) : SteinInput M L I =
    PaperC.V282.DirectionalSteinInput.DirectionalSolutionBounds
      (PaperC.Prel8.ActualSignedPalm.rate L :
        PaperC.Prel8.ActualSignedPalm.Index (PaperC.Prel8.MicroscopicRetainedTheorem.actualSites M L I)
          (PaperC.Prel8.MicroscopicProfileBudget.paperExcess M L I) → ℝ≥0) := by
  unfold SteinInput
  rw [goodSites_eq,excess_eq]
  rfl
theorem distance_eq (M L : ℕ) (A : Set InfiniteSample) : distance M L A =
    PaperC.V282.FiniteFieldTotalVariation.massTotalVariation
      (PaperC.V282.ConditionedCountableLaw.conditionalObservableLaw infiniteRademacherMeasure A
        (PaperC.V282.BulkMarkedSource.spatialMarkedSource (interior M L) L))
      (PaperC.V282.BulkMarkedComparison.spatialTargetLaw (interior M L) L) := by
  unfold distance
  simp only [source_eq,target_eq]
  rfl
theorem length_eq (alpha : ℝ) (k : ℕ) :
    length alpha k = PaperC.Prel8.EmpiricalPaperScales.length alpha k := by
  unfold length PaperC.Prel8.EmpiricalPaperScales.length PaperC.Prel8.EmpiricalPaperScales.depth
    PaperC.Prel8.EmpiricalPaperScales.cutoff
  rw [saddleCutoff_eq]
  rfl
theorem windowSize_eq (alpha tau : ℝ) (k : ℕ) :
    windowSize alpha tau k = PaperC.Prel8.EmpiricalPaperScales.windowSize alpha tau k := by
  unfold windowSize PaperC.Prel8.EmpiricalPaperScales.windowSize
  rw [length_eq]
theorem origins_eq (alpha tau : ℝ) (k : ℕ) :
    origins alpha tau k = PaperC.Prel8.EmpiricalPaperScales.origins alpha tau k := by
  unfold origins PaperC.Prel8.EmpiricalPaperScales.origins PaperC.Prel8.EmpiricalPaperScales.sites
  rw [length_eq,windowSize_eq]
  rfl
theorem windowCount_eq (M L h u : ℕ) (omega : InfiniteSample) :
    windowCount M L h u omega = PaperC.Prel8.EmpiricalWindowVariance.windowCount h u
      (PaperC.Prel8.EmpiricalStartField.actualStarts M L omega) := by
  unfold windowCount PaperC.Prel8.EmpiricalWindowVariance.windowCount PaperC.Prel8.EmpiricalWindowVariance.window
  apply Finset.sum_congr rfl
  intro i _
  unfold PaperC.Prel8.EmpiricalStartField.actualStarts PaperC.V282.BulkMarkedAggregation.startField
    PaperC.V282.ExactMarkedModel.baseStartValue
  split_ifs <;> first | rfl | contradiction
theorem frequency_eq (alpha tau : ℝ) (k r : ℕ) (omega : InfiniteSample) :
    frequency alpha tau k r omega = PaperC.Prel8.EmpiricalWindowVariance.frequency
      (PaperC.Prel8.EmpiricalPaperScales.origins alpha tau k)
      (PaperC.Prel8.EmpiricalPaperScales.windowSize alpha tau k) r
      (PaperC.Prel8.EmpiricalStartField.actualStarts (size k)
        (PaperC.Prel8.EmpiricalPaperScales.length alpha k) omega) := by
  unfold frequency
  rw [origins_eq,windowSize_eq,length_eq]
  simp only [windowCount_eq]
  unfold PaperC.Prel8.EmpiricalWindowVariance.frequency PaperC.Prel8.EmpiricalWindowVariance.hit
  rfl

end Microscopic

namespace Microscopic
open Analysis Boundary

/-- The source is the literal signed exact-run configuration, for every realization. -/
theorem exact_source_coefficients (sites : Finset ℕ) (L : ℕ) (omega : InfiniteSample) (j : MarkIndex sites) :
    source sites L omega j =
      if ExactLengthEvent (infiniteValueBit omega) j.1.val (L+j.2.1+1) ∧
        infiniteValueBit omega j.1.val=j.2.2 then 1 else 0 := by
  rw [source_eq]
  simp only [PaperC.V282.BulkMarkedSource.spatialMarkedSource_apply,
    PaperC.V282.BulkMarkedSource.spatialMarkedValue,PaperC.V282.ExactMarkedModel.signedMarkValue]
  split_ifs <;> first | rfl | contradiction

/-- Article 7.7: complete position/excess/sign field in the literal moving-depth regime. -/
theorem full_field_comparison
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : DivisorLogBoundStatement)
    (c c' epsilon : ℝ) (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon)
    (depth : ℕ → ℕ) (events : ℕ → Set InfiniteSample)
    (hdepth : Tendsto (fun M : ℕ => (depth M:ℝ)/Real.log M) atTop (𝓝 0))
    (hintensity : Tendsto (fun M : ℕ => siteRate M (paperLength M (depth M))) atTop atTop)
    (hregime : ∀ᶠ M : ℕ in atTop,
      information (events M)+Real.log (siteRate M (paperLength M (depth M))) ≤
        saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) ∧
      MeasurableSet[primeSigma (hardCutoff M)] (events M) ∧
      0 < infiniteRademacherMeasure.real (events M) ∧
      SteinInput M (paperLength M (depth M)) (information (events M))) :
    ∀ᶠ M : ℕ in atTop,
      distance M (paperLength M (depth M)) (events M) ≤
      10*Real.exp (-c'*saddleNu 1 (Real.log M))+4*(M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  have hregime' := hregime.mono (fun M h => by
    rw [hardCutoff_eq] at h
    simpa only [stein_eq,saddleCutoff_eq,saddleNu_eq] using h)
  simp only [distance_eq,saddleNu_eq]
  exact PaperC.Prel8.MicroscopicNormalization.paper_comparison_eventually
    hLS hShorey hPNT hNR c c' epsilon hc' hcc hepsilon depth events hdepth hintensity hregime'

/-- The original dyadic grid and its smaller conditioning field are retained. -/
theorem dyadic_field_comparison
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : DivisorLogBoundStatement)
    (betaMin betaMax c c' epsilon : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax)
    (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon) (hepsMax : epsilon < 1/3) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin*Real.log N ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log N →
      1 ≤ (fullRate N L:ℝ) → ∀ A : Set InfiniteSample,
      MeasurableSet[primeSigma (hardCutoff N)] A →
      0 < infiniteRademacherMeasure.real A →
      information A+Real.log (fullRate N L:ℝ) ≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      SteinInput (4*N) L (information A) →
      massTV (conditionalLaw infiniteRademacherMeasure A (source (Finset.Ico N (2*N)) L))
        (observableLaw (target (Finset.Ico N (2*N)) L) id) ≤
        10*Real.exp (-c'*saddleNu 1 (Real.log N))+4*(N:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  obtain ⟨Nzero,hmain⟩ := PaperC.Prel8.DyadicMicroscopicTheorem.dyadic_comparison_eventually
    hLS hShorey hPNT hNR betaMin betaMax c c' epsilon hmin hband hc' hcc hepsilon hepsMax
  refine ⟨Nzero, ?_⟩
  intro N hN L hlo hhi hr A hm hp hb hs
  rw [hardCutoff_eq] at hm
  simp only [saddleCutoff_eq,saddleNu_eq] at hb
  rw [stein_eq] at hs
  rw [saddleNu_eq,source_eq,target_eq]
  exact hmain N hN L hlo hhi hr A hm hp hb hs

/-- Article 7.8a: almost-sure total-variation convergence of empirical window counts. -/
theorem empirical_poisson
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : DivisorLogBoundStatement)
    (alpha : ℝ) (tau : ℝ≥0) (ha : 0 < alpha) (ha1 : alpha < 1) (ht : 0 < tau)
    (hsol : ∀ᶠ k in atTop, SteinInput (size k) (length alpha k) 0) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, Tendsto (fun k => massTV
      (fun r => frequency alpha tau k r omega) (fun r => (poissonMeasure tau).real {r})) atTop (𝓝 0) := by
  simp only [stein_eq,length_eq] at hsol
  simp only [frequency_eq]
  exact PaperC.Prel8.EmpiricalPaperTheorem.paper_empirical_poisson
    hLS hShorey hPNT hNR alpha tau ha ha1 ht hsol
end Microscopic

namespace Microscopic
/-- Total variation on arbitrary measurable output spaces. -/
def measureTV {α : Type*} [MeasurableSpace α] (mu nu : Measure α) : ℝ :=
  sSup {r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r=|mu.real A-nu.real A|}
/-- The full vector read at one contained relative origin. -/
def localVector (L h u : ℕ) (omega : InfiniteSample) : Fin h → ℕ :=
  fun i => if StartEvent (infiniteValueBit omega) (u+i.val+2) L then 1 else 0
/-- Uniform contained origins, including the manuscript's totalization at small scales. -/
def vectorMeasure (M L h : ℕ) (omega : InfiniteSample) : Measure (Fin h → ℕ) := by
  letI : NeZero (M-L-h+1) := ⟨by omega⟩
  exact (PMF.uniformOfFintype (Fin (M-L-h+1))).toMeasure.map
    (fun u => localVector L h u.val omega)
def vectorDistance (M L h : ℕ) (omega : InfiniteSample) : ℝ :=
  measureTV (vectorMeasure M L h omega)
    (Measure.pi (fun _ : Fin h => poissonMeasure ((1:ℝ≥0)/2^L)))
end Microscopic

namespace Microscopic
open Analysis Boundary
/-- Every common measurable readout contracts the complete-field distance. -/
theorem common_readout {α : Type*} [MeasurableSpace α]
    (M L : ℕ) (A : Set InfiniteSample) (hpos : 0 < infiniteRademacherMeasure.real A)
    (stat : Config (interior M L) → α) (hstat : Measurable stat) :
    measureTV ((cond infiniteRademacherMeasure A).map (stat ∘ source (interior M L) L))
      ((target (interior M L) L).map stat) ≤ distance M L A := by
  rw [source_eq,target_eq,distance_eq]
  exact PaperC.Prel8.MicroscopicReadouts.measurable_readout_le M L A hpos stat hstat

/-- Article 7.8b: the empirical full vector remains separated from the independent target. -/
theorem empirical_vector_obstruction (alpha tau : ℝ) (ha : 0 < alpha)
    (ha1 : alpha < 1) (ht : 0 < tau) (omega : InfiniteSample) :
    (1-Real.exp (-tau)*(1+tau) ≤
      liminf (fun k => vectorDistance (size k) (length alpha k) (windowSize alpha tau k) omega) atTop) ∧
    0 < 1-Real.exp (-tau)*(1+tau) := by
  have he (k : ℕ) : vectorDistance (size k) (length alpha k) (windowSize alpha tau k) omega =
      PaperC.V282.SharpConditioning.measureTotalVariation
        (PaperC.Prel8.EmpiricalSupportTheorem.actualEmpiricalVectorMeasure alpha tau k omega)
        (PaperC.V282.PoissonFieldMeasure.fieldMeasure (fun _ : Fin (PaperC.Prel8.EmpiricalPaperScales.windowSize alpha tau k) =>
          (1:ℝ≥0)/2^(PaperC.Prel8.EmpiricalPaperScales.length alpha k))) := by
    unfold vectorDistance
    rw [length_eq,windowSize_eq]
    unfold vectorMeasure PaperC.Prel8.EmpiricalSupportTheorem.actualEmpiricalVectorMeasure
      PaperC.Prel8.EmpiricalFiniteSupport.empiricalMeasure PaperC.V282.UniformSpatialGrid.uniformGridMeasure
    congr 3
  simp only [he]
  exact PaperC.Prel8.EmpiricalSupportTheorem.paper_empirical_vector_obstruction alpha tau ha ha1 ht omega
end Microscopic

end
end PaperCV3Audit
