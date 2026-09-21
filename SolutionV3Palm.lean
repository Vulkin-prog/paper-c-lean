import PaperCV282.MicroscopicBoundaryDominance
import PaperCV282.MesoscopicStability
import PaperCV282.PrefixAlmostSureEnvelopes
import PaperCV282.PrefixCriticalVoid

import PaperCPrel8.MicroscopicNormalization
import PaperCPrel8.EmpiricalPaperTheorem
import PaperCPrel8.EmpiricalSupportTheorem
import PaperCPrel8.DyadicMicroscopicTheorem
import PaperCPrel8.ArithmeticPalmCompletion
import PaperCPrel8.PrimeCumulantObstruction
import PaperCPrel8.RegularTargetCompletion

/-! # Regular configurations, Palm comparisons and cumulant obstructions

The nine selected declarations below describe the exact signed run field of a
random completely multiplicative Rademacher function. The following notation
is used in their mathematical accounts; the definitions are given in this module.

For a finite set S of run-start positions, Z_S = `source S L` retains each
exact length L+e and sign, for all e >= 0. P_A denotes the original prime-sign
law conditioned on `traceEvent C Y A`: A depends only on prime signs with
p <= C and p <= Y, and this event must have positive probability. Q_S denotes
the independent Poisson target, with intensity 2^(-L-e-2) for each signed atom.
Write p = 2^(-L), mu_S = |S|p, q_S(z) = Q_S({z}), and
Delta_S = (1/2) sum_z |P_A(Z_S=z) - q_S(z)|.

R_S = `RegularPlant S C L E Y` consists of enumerated planted marks (j,e,sign)
with j >= 2, e <= E and j+L+E <= C. Each raw vertex in every support
j-1,...,j+L+E has a prime > Y occurring to odd valuation there and dividing
no other raw vertex occurrence of the plant. Such configurations have distinct
sites. Write |z| = `totalSize S z`; R_{S,K} also requires |z| <= K.
The empty configuration is included. The source and target themselves retain
all excesses; E restricts the regular configurations in the averages.

Occ(z) prescribes presence of every exact signed run in z, without forbidding
other runs. On R_S its conditional probability is positive. The Palm void is
v_S(z) = P_A(Z_S=z | Occ(z)). Set
 r_S(z) = v_S(z)/(1-p)^(|S|-|z|),
 D_S = sum_{z in R_S} q_S(z) max(1-exp(mu_S)v_S(z),0), and
 Dnorm_{S,K} = sum_{z in R_{S,K}} q_S(z) max(1-r_S(z),0).
These are `fullDeficit`, `normalizedVoid` and `voidDeficit` in the statements.
For L >= 1 the denominator is positive; regularity gives |z| <= |S|.

For the asymptotic statements put H = log M, u = `saddleParameter 1 H`,
V = `saddleCutoff 1 H`, nu = `saddleNu 1 H` = H/V, Y = floor(exp V),
n = M-L (natural subtraction), lambda = n/2^L, and
E_M = `excess M L I` = ceil((I+V+log(2+M/2^L))/log 2).
The length/information regime means
 betaMin H <= L+1 <= betaMax H, I >= 0, lambda >= 1,
 I+log(lambda) <= V-c nu.
G0 = `goodSites M L I` uses left-boundary labels j in {1,...,n}:
j+1 >= ceil(sqrt M), and each j+a for 0 <= a <= L+E_M+1 has an
odd-valuation prime above Y. Gtheta = `strongerGood M L I theta` further
requires the product of all odd-valuation primes > Y at each such vertex to
exceed floor(exp(theta H/u)). These labels j correspond to actual starts j+1;
the Palm sets S instead use actual start positions.
-/

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
/-- The complete target is a genuine probability law on the discrete configuration space. -/
theorem measurable_flattenRows (sites : Finset ℕ) : Measurable (flattenRows sites) :=
  measurable_of_countable _
instance instProbabilityTarget (sites : Finset ℕ) (L : ℕ) : IsProbabilityMeasure (target sites L) := by
  unfold target
  exact (Measure.isProbabilityMeasure_map_iff (measurable_flattenRows sites).aemeasurable).mpr inferInstance
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
namespace Palm
open Analysis Boundary Microscopic
/-- Small-prime assignments in a fixed finite cylinder. -/
abbrev SmallSample (C Y : ℕ) := {p : PrimeUpTo C // p.1.1 ≤ Y} → F₂
def traceEvent (C Y : ℕ) (A : SmallSample C Y → Prop) : Set InfiniteSample :=
  {omega | A (fun p => restrictToFinite C omega p.1)}
def roughPrimes (Y n : ℕ) : Finset ℕ :=
  ((n.factorization.mapRange (fun e : ℕ => e%2) (by simp)).support).filter (fun p => Y<p)
/-- Each raw occurrence has a prime private to it among all planted occurrences. -/
def Regular {k : ℕ} (Q Y : ℕ) (J : Fin k → ℕ) : Prop :=
  ∀ i : Fin k, ∀ a : Fin (Q+1), ∃ p ∈ roughPrimes Y (J i+a.val),
    ∀ l : Fin k, ∀ b : Fin (Q+1), l≠i ∨ b≠a → ¬ p ∣ J l+b.val
def enumerated {k : ℕ} (sites : Finset ℕ) (labels : Fin k → MarkIndex sites) : Config sites :=
  ∑ i, Finsupp.single (labels i) 1
/-- Private-prime regularity includes the cylinder, excess and endpoint conditions. -/
def RegularPlant (sites : Finset ℕ) (C L E Y : ℕ) (z : Config sites) : Prop :=
  ∃ k, ∃ labels : Fin k → MarkIndex sites,
    z=enumerated sites labels ∧
    (∀ i, 2≤(labels i).1.val) ∧ (∀ i, (labels i).2.1≤E) ∧
    (∀ i, (labels i).1.val-1+(L+E+1)≤C) ∧
    Regular (L+E+1) Y (fun i => (labels i).1.val-1)
def presence (sites : Finset ℕ) (L : ℕ) (z : Config sites) : Set InfiniteSample :=
  {omega | ∀ j, z j≠0 → ExactLengthEvent (infiniteValueBit omega) j.1.val (L+j.2.1+1) ∧
    infiniteValueBit omega j.1.val=j.2.2}
def totalRate (sites : Finset ℕ) (L : ℕ) : ℝ≥0 := ⟨(sites.card:ℝ)/2^L,by positivity⟩
def sourceMass {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) : Config sites → ℝ :=
  conditionalLaw infiniteRademacherMeasure (traceEvent C Y A) (source sites L)
def targetMass (sites : Finset ℕ) (L : ℕ) (z : Config sites) : ℝ := (target sites L).real {z}
def palmVoid {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) (z : Config sites) : ℝ :=
  (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence sites L z)).real
    {omega | source sites L omega=z}
def voidDeficit {α : Type*} (nu : α → ℝ) (R : α → Prop) (v : α → ℝ) : ℝ :=
  ∑' z, if R z then nu z*max (1-v z) 0 else 0
def fullDeficit {C Y : ℕ} (sites : Finset ℕ) (L E : ℕ) (A : SmallSample C Y → Prop) : ℝ :=
  voidDeficit (targetMass sites L) (RegularPlant sites C L E Y)
    (fun z => Real.exp (totalRate sites L:ℝ)*palmVoid sites L A z)
def totalSize (sites : Finset ℕ) (z : Config sites) : ℕ := z.sum (fun _ n => n)
def boundedRegular (sites : Finset ℕ) (C L E Y K : ℕ) (z : Config sites) : Prop :=
  RegularPlant sites C L E Y z ∧ totalSize sites z≤K
def normalizedVoid {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) (z : Config sites) : ℝ :=
  palmVoid sites L A z/(1-1/(2:ℝ)^L)^(sites.card-totalSize sites z)
def penalty (sites : Finset ℕ) (L K : ℕ) : ℝ :=
  (K:ℝ)*(1/(2:ℝ)^L)+(sites.card:ℝ)*(1/(2:ℝ)^L)^2/(1-1/(2:ℝ)^L)
def exceptionalMass {α : Type*} (nu : α → ℝ) (R : α → Prop) : ℝ :=
  ∑' z, if R z then 0 else nu z
def hitEvent (L : ℕ) (sites : Finset ℕ) : Set InfiniteSample :=
  {omega | maskedCount L sites omega ≠ 0}
def sourceCylinder (M L : ℕ) (I : ℝ) : ℕ := 2*M+(L+excess M L I+2)
end Palm

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

end Microscopic

namespace Palm
open Analysis Boundary Microscopic
 theorem presence_eq (sites : Finset ℕ) (L : ℕ) :
    presence sites L = PaperC.Prel8.ArithmeticPalmMass.presence sites L := rfl
 theorem regular_eq (sites : Finset ℕ) (C L E Y : ℕ) :
    RegularPlant sites C L E Y = PaperC.Prel8.ArithmeticPalmMass.RegularPlant sites C L E Y := rfl
 theorem sourceMass_eq {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) :
    sourceMass sites L A = PaperC.Prel8.ArithmeticPalmDeficit.sourceMass sites L A := by
  unfold sourceMass; rw [source_eq]; rfl
 theorem targetMass_eq (sites : Finset ℕ) (L : ℕ) :
    targetMass sites L = PaperC.Prel8.ArithmeticPalmDeficit.targetMass sites L := by
  unfold targetMass; rw [target_eq]; rfl
 theorem palmVoid_eq {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) :
    palmVoid sites L A = PaperC.Prel8.ArithmeticPalmDeficit.palmVoid sites L A := by
  unfold palmVoid; rw [source_eq]; rfl
 theorem fullDeficit_eq {C Y : ℕ} (sites : Finset ℕ) (L E : ℕ) (A : SmallSample C Y → Prop) :
    fullDeficit sites L E A = PaperC.Prel8.ArithmeticPalmDeficit.fullDeficit sites L E A := by
  unfold fullDeficit; rw [targetMass_eq,regular_eq,palmVoid_eq]; rfl
 theorem normalizedVoid_eq {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) :
    normalizedVoid sites L A = PaperC.Prel8.ArithmeticPalmNormalization.normalizedVoid sites L A := by
  unfold normalizedVoid; rw [palmVoid_eq]; rfl
 theorem sourceCylinder_eq (M L : ℕ) (I : ℝ) :
    sourceCylinder M L I = PaperC.Prel8.MicroscopicActualGeometry.sourceCylinder M L I := by
  unfold sourceCylinder PaperC.Prel8.MicroscopicActualGeometry.sourceCylinder; rw [excess_eq]
end Palm


namespace Palm
open Analysis Boundary Microscopic
/-- Exact conditional arithmetic-to-Poisson Palm mass identity.

Use Z_S, P_A, Q_S, mu_S, R_S and Occ(z) from the module account. For any
finite S, natural C,E,Y, L >= 1, any positive-probability small-prime event A,
and every z in R_S, the theorem proves
 P_A(Z_S=z) = q_S(z) exp(mu_S) P_A(Z_S=z | Occ(z)).
There is no bound on |z| beyond regularity and no literature premise.
It also proves that each coefficient of Z_S is the indicator of the actual
exact signed run, that Z_S and Occ(z) are measurable, that Q_S and both
conditional measures are probability measures, and that P_A(Occ(z)) > 0.
Thus the displayed Palm probability is conditioning on an event of positive
mass. The factorization uses the private primes of the regular plant.
-/
theorem source_target_palm_mass {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A))
    (z : Config sites) (hz : RegularPlant sites C L E Y z) :
    (∀ omega : InfiniteSample, ∀ j : MarkIndex sites, source sites L omega j =
      if ExactLengthEvent (infiniteValueBit omega) j.1.val (L+j.2.1+1) ∧
        infiniteValueBit omega j.1.val=j.2.2 then 1 else 0) ∧
    MeasurableSet (presence sites L z) ∧ Measurable (source sites L) ∧
    IsProbabilityMeasure (target sites L) ∧
    IsProbabilityMeasure (cond infiniteRademacherMeasure (traceEvent C Y A)) ∧
    0 < (cond infiniteRademacherMeasure (traceEvent C Y A)).real (presence sites L z) ∧
    IsProbabilityMeasure (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence sites L z)) ∧
    (cond infiniteRademacherMeasure (traceEvent C Y A)).real {w | source sites L w=z} =
    (target sites L).real {z} * (Real.exp (totalRate sites L:ℝ)*
      (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence sites L z)).real
        {w | source sites L w=z}) := by
  refine ⟨?_, PaperC.Prel8.ArithmeticPalmMass.measurableSet_presence sites L z, ?_⟩
  · intro omega j
    rw [source_eq]
    simp only [PaperC.V282.BulkMarkedSource.spatialMarkedSource_apply,
      PaperC.V282.BulkMarkedSource.spatialMarkedValue, PaperC.V282.ExactMarkedModel.signedMarkValue]
    split_ifs <;> first | rfl | contradiction
  ·
    have hm : Measurable (source sites L) := by
      rw [source_eq]
      exact PaperC.V282.BulkMarkedSource.measurable_spatialMarkedSource _ _
    letI : IsProbabilityMeasure (cond infiniteRademacherMeasure (traceEvent C Y A)) :=
      cond_isProbabilityMeasure (PaperC.V282.ConditionedCountableLaw.measure_ne_zero_of_real_pos _ hA)
    have hp : 0 < (cond infiniteRademacherMeasure (traceEvent C Y A)).real (presence sites L z) :=
      PaperC.Prel8.ArithmeticPalmMass.presence_pos sites hL A hA z hz
    refine ⟨hm, inferInstance, inferInstance, hp,
      cond_isProbabilityMeasure (PaperC.V282.ConditionedCountableLaw.measure_ne_zero_of_real_pos _ hp), ?_⟩
    rw [source_eq,target_eq]
    exact PaperC.Prel8.ArithmeticPalmMass.source_target_palm_mass sites hL A hA z hz

/-- TV-minus-deficit sandwich on the full countable marked target.

For any finite S, natural C,E,Y, L >= 1 and positive-probability small-prime
event A, use the module notation Delta_S, R_S and
 D_S = sum_{z in R_S} q_S(z) max(1-exp(mu_S)v_S(z),0).
The two conclusions about total mass are sum_z P_A(Z_S=z)=1 and sum_z q_S(z)=1
(the `HasSum` assertions). The principal inequalities are exactly
 0 <= Delta_S - D_S <= Q_S(z not in R_S).
The comparison concerns the full source and full target, with all excesses;
only the deficit average is restricted to private-prime regular plants with
excess <= E and their supports in the cylinder C. There is no K cutoff here.
No literature, large-M, or target-regularity-in-probability assumption is used.
The right-hand side is the target exceptional probability, with no exp(mu_S)
multiplier. In particular, target regularity alone does not show Delta_S tends
to zero: the remaining quantity D_S must also be controlled.
-/
theorem full_deficit_comparison {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    HasSum (sourceMass sites L A) 1 ∧ HasSum (targetMass sites L) 1 ∧
    0 ≤ massTV (sourceMass sites L A) (targetMass sites L)-fullDeficit sites L E A ∧
    massTV (sourceMass sites L A) (targetMass sites L)-fullDeficit sites L E A ≤
      (target sites L).real {z | ¬RegularPlant sites C L E Y z} := by
  have hm : Measurable (source sites L) := by
    rw [source_eq]
    exact PaperC.V282.BulkMarkedSource.measurable_spatialMarkedSource _ _
  letI : IsProbabilityMeasure (cond infiniteRademacherMeasure (traceEvent C Y A)) :=
    cond_isProbabilityMeasure (PaperC.V282.ConditionedCountableLaw.measure_ne_zero_of_real_pos _ hA)
  refine ⟨PaperC.V282.InfiniteMassCoupling.hasSum_observableLaw _ hm,
    PaperC.V282.InfiniteMassCoupling.hasSum_observableLaw (target sites L) measurable_id, ?_⟩
  rw [sourceMass_eq,targetMass_eq,fullDeficit_eq,target_eq]
  exact PaperC.Prel8.ArithmeticPalmDeficit.fullDeficit_comparison sites hL A hA

/-- Ordinary deletion identity for the exact signed run field (companion Appendix G,
Proposition `supp:palm:prop:palm`, equation `supp:palm:eq:averaged-deletion`).

Let S be the finite set `sites` of retained run-start positions and let
Z = `source sites L` record all exact runs on S, including their excess e >= 0
(actual length L+e) and sign. Let P_A be the original Rademacher law conditioned
on `traceEvent C Y A`. Here A is any predicate on the signs of primes at most Y
in the finite cylinder of primes at most C; `hA` requires this event to have
strictly positive probability. Assume L >= 1. No literature or asymptotic
hypothesis is needed for this exact identity.

The sum is restricted to R = `RegularPlant sites C L E Y`: a configuration z
must have an enumeration of planted marks (j,e,sign) with j >= 2, e <= E,
and j-1+(L+E+1) <= C. Each raw vertex in each maximal support
j-1,...,j+L+E must have a prime greater than Y occurring to odd valuation
there and dividing no other raw vertex occurrence in the whole plant.
There is no additional bound K on the number of planted marks in this theorem.

Write Occ(z) = `presence sites L z` for the event that every planted exact
signed run occurs, without excluding additional runs. For regular z its P_A
probability is proved positive. Write P_A^z for P_A conditioned on Occ(z),
q(z) = `targetMass sites L z` for the independent Poisson target mass, and
mu = |S|/2^L = `totalRate sites L`. Define
v_S(z) = P_A^z(Z=z) and v_no_O(z) = P_A^z({Z=z} \ O), where
O = `outside` is any measurable event in the original sample space.
No independence from A, Occ(z), or Z is required. The assertion is exactly

  sum_{z in R} q(z) exp(mu) (v_S(z) - v_no_O(z)) = P_A(Z in R and O).

For deletion of sites outside S in a larger finite observation window, take O
to be the measurable event that a run of length at least L starts at one of
those deleted sites. Deleting those coordinates removes the requirement that
no run occur there: v_S allows outside occurrences, while v_no_O also requires
absence outside S. Thus their weighted difference is the ordinary conditional
probability of an outside occurrence together with regularity of the retained
configuration. It is consequently at most P_A(O); this upper bound is an
immediate consequence of the displayed equality and event inclusion.

The cancellation uses the proved identity q(z) exp(mu) = P_A(Occ(z)) on R.
Each summand becomes P_A(Z=z and O); summing the disjoint configuration events
gives the right-hand side. The error is therefore not multiplied by exp(mu).
-/
theorem ordinary_deletion {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A))
    (outside : Set InfiniteSample) (houtside : MeasurableSet outside) :
    (∑' z, if RegularPlant sites C L E Y z then targetMass sites L z*Real.exp (totalRate sites L:ℝ)*
      (palmVoid sites L A z-
        (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence sites L z)).real
          ({w | source sites L w=z} \ outside)) else 0) =
      (cond infiniteRademacherMeasure (traceEvent C Y A)).real
        ({w | RegularPlant sites C L E Y (source sites L w)} ∩ outside) := by
  simp only [targetMass_eq,palmVoid_eq,source_eq]
  exact PaperC.Prel8.ArithmeticPalmDeficit.ordinary_deletion sites hL A hA outside houtside

/-- Full-to-retained TV comparison with four explicit error terms.

Let s be a subset of a finite set t of actual run-start positions. For natural
C,E,Y,K, L >= 1 and any positive-probability small-prime event A, use the
module notation Delta_t and Dnorm_{s,K}. The theorem states exactly
 |Delta_t - Dnorm_{s,K}| <= d_A + delta + epsilon_reg + eta,
where the four nonnegative error terms are
 d_A = P_A(a run of length at least L starts at some position in t minus s),
 delta = |t minus s|p,
 epsilon_reg = Q_s(z not in R_{s,K}),
 eta = Kp + |s|p^2/(1-p), with p=2^(-L).
The first is `hitEvent`'s ordinary conditional probability, the second is
`maskRate`, the third is `exceptionalMass`, and the last is `penalty`.
R_{s,K} imposes the private-prime, cylinder and excess conditions of RegularPlant
as well as |z| <= K. The normalized void r_s divides the Palm void by the
independent Bernoulli empty-site factor (1-p)^(|s|-|z|); it is not exp(mu_s)v_s.
L >= 1 makes 0 < p < 1, and regularity ensures |z| <= |s|. There is no
assumption that s itself is a particular good set, or that K <= |s|.
Empty finite sets are allowed. This finite inequality needs no literature or
asymptotic premise; it neither assumes nor asserts that its errors are small.
-/
theorem full_retained_normalized_comparison {C L E Y K : ℕ} {s t : Finset ℕ}
    (hst : s⊆t) (hL : 1≤L) (A : SmallSample C Y → Prop)
    (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    |massTV (sourceMass t L A) (targetMass t L)-
      voidDeficit (targetMass s L) (boundedRegular s C L E Y K) (normalizedVoid s L A)|≤
      (cond infiniteRademacherMeasure (traceEvent C Y A)).real
        (hitEvent L (t\s))+
      (maskRate L (t\s):ℝ)+
      exceptionalMass (targetMass s L) (boundedRegular s C L E Y K)+penalty s L K := by
  simp only [sourceMass_eq,targetMass_eq,normalizedVoid_eq]
  exact PaperC.Prel8.ArithmeticPalmCompletion.full_retained_normalized_comparison (E := E) (K := K) hst hL A hA

/-- Uniform eventual upper bound for the normalized Palm deficit.

Assume the displayed literature propositions for Laishram-Shorey's uniform
prime-divisor estimate, Shorey's square-product exclusion, the prime number
theorem remainder and the Nicolas-Robin divisor bound. Fix
0 < betaMin < betaMax, 0 < c' < c and epsilon > 0. There exists one Mzero
such that for every M >= Mzero, every natural L >= 1 and real I satisfying
the length/information regime in the module account, the following holds.

Set C = `sourceCylinder M L I` = 2M+L+E_M+2 and Y = floor(exp V).
Choose any small-prime event A with positive probability, with I equal to
minus the logarithm of that probability. Require `SteinInput M L I`: existence
of solutions to the multivariate Poisson Stein equation for every indicator
test on the finite carrier G0 x {0,...,E_M} x F2, with rates 2^(-L-e-2),
entrywise second differences bounded by one and the weighted quadratic Hessian
bound in `DirectionalSolutionBounds`. This is an analytic solution premise,
not an assumed arithmetic Poisson comparison.

For EVERY subset S of the actual start positions {2,...,M-L+1} and EVERY
natural E, put K=ceil(2 lambda) and form Dnorm_{S,K} using C,L,E,Y. Then
 Dnorm_{S,K} <= 10 exp(-c' nu) + 4 M^(-1/3+epsilon) + M^(-1/2).
The threshold Mzero is chosen before L,I,A,S,E; in particular this is uniform
in the conditioning event and the retained set. S need not equal G0 or Gtheta
and E need not equal E_M (which is the cutoff in the Stein premise).
The conclusion is a one-sided bound on the averaged positive deficit, not a
uniform two-sided relative Palm estimate for every plant. The stated bound
holds for every epsilon > 0; its power term tends to zero when epsilon < 1/3.
-/
theorem normalized_deficit_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : DivisorLogBoundStatement)
    (betaMin betaMax c c' epsilon : ℝ) (hmin : 0<betaMin)
    (hband : betaMin<betaMax) (hc' : 0<c') (hcc : c'<c) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, ∀ I : ℝ,
      1≤L → betaMin*Real.log M≤(L+1:ℝ) → (L+1:ℝ)≤betaMax*Real.log M →
      0≤I → 1≤siteRate M L →
      I+Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      ∀ A : SmallSample (sourceCylinder M L I) (hardCutoff M) → Prop,
      0 < infiniteRademacherMeasure.real (traceEvent (sourceCylinder M L I) (hardCutoff M) A) →
      I = -Real.log (infiniteRademacherMeasure.real
        (traceEvent (sourceCylinder M L I) (hardCutoff M) A)) →
      SteinInput M L I →
      ∀ sites : Finset ℕ, sites⊆interior M L → ∀ E : ℕ,
      voidDeficit (targetMass sites L)
        (boundedRegular sites (sourceCylinder M L I) L E (hardCutoff M) ⌈2*siteRate M L⌉₊)
        (normalizedVoid sites L A)≤
      10*Real.exp (-c'*saddleNu 1 (Real.log M))+4*(M:ℝ)^(-(1/(3:ℝ))+epsilon)+(M:ℝ)^(-(1/(2:ℝ))) := by
  rw [show sourceCylinder = PaperC.Prel8.MicroscopicActualGeometry.sourceCylinder from
    funext fun M => funext fun L => funext fun I => sourceCylinder_eq M L I]
  rw [show Analysis.hardCutoff = PaperC.Prel8.MicroscopicActualGeometry.primeCutoff from
    funext fun M => Analysis.hardCutoff_eq M]
  simp only [stein_eq,targetMass_eq,normalizedVoid_eq,Analysis.saddleCutoff_eq,Analysis.saddleNu_eq]
  exact PaperC.Prel8.ArithmeticPalmCompletion.normalized_deficit_eventually hLS hShorey hPNT hNR betaMin betaMax c c' epsilon hmin hband hc' hcc hepsilon

end Palm

namespace Palm
open Analysis Boundary Microscopic
namespace Cumulants
open Finset
variable {ι : Type*} [DecidableEq ι]
def partitions (S : Finset ι) : Finset (Finset (Finset ι)) :=
  S.powerset.powerset.filter (fun p ↦ (p:Set (Finset ι)).PairwiseDisjoint id ∧
    ∅∉p ∧ p.biUnion id=S)

def properPartitions (S : Finset ι) : Finset (Finset (Finset ι)) :=
  (partitions S).erase {S}

theorem block_subset {S B : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈partitions S) (hB : B∈p) : B⊆S :=
  mem_powerset.mp (mem_powerset.mp (mem_filter.mp hp).1 hB)

theorem block_nonempty {S B : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈partitions S) (hB : B∈p) : B.Nonempty := by
  apply nonempty_iff_ne_empty.mpr
  intro he
  exact (mem_filter.mp hp).2.2.1 (he ▸ hB)

theorem partition_with_full_block {S : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈partitions S) (hS : S∈p) : p={S} := by
  apply eq_singleton_iff_unique_mem.mpr
  refine ⟨hS,?_⟩
  intro B hB
  by_contra hne
  have hd := (mem_filter.mp hp).2.1 hB hS hne
  obtain ⟨x,hx⟩ := block_nonempty hp hB
  exact disjoint_left.mp hd hx (block_subset hp hB hx)

theorem proper_block_ssubset {S B : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈properPartitions S) (hB : B∈p) : B⊂S := by
  obtain ⟨hne,hp⟩ := mem_erase.mp hp
  apply ssubset_iff_subset_ne.mpr
  refine ⟨block_subset hp hB,?_⟩
  intro he
  exact hne (partition_with_full_block hp (he ▸ hB))

theorem singleton_partition {S : Finset ι} (hS : S.Nonempty) : {S}∈partitions S := by
  simp [partitions,Ne.symm hS.ne_empty]

theorem partitions_empty : partitions (∅:Finset ι)={∅} := by
  ext p
  simp only [partitions,mem_filter,mem_powerset,powerset_empty,subset_singleton_iff,mem_singleton]
  constructor
  · rintro ⟨h,hd,he,hu⟩
    rcases h with h|h
    · exact h
    · simp [h] at he
  · rintro rfl
    simp

/-- Triangular finite definition of joint cumulants from a prescribed moment table. -/
def cumulant (moment : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  if S=∅ then 0 else moment S-
    ∑ p : properPartitions S, ∏ B : p.val, cumulant moment B.val
termination_by S.card
decreasing_by exact card_lt_card (proper_block_ssubset p.property B.property)

end Cumulants
/-- The actual finite prime-sign assignment on the witness cylinder. -/
def finiteValue {C : ℕ} (omega : SampleSpace C) (n : ℕ) : F₂ :=
  ∑ p : PrimeUpTo C, omega p * parityVec n p.1
/-- Low exact categories; the unique realized signed excess is selected if present. -/
def lowCategory (C L E j : ℕ) (omega : SampleSpace C) : Option (Fin (E+1)×F₂) :=
  if h : ∃ a : Fin (E+1)×F₂,
    ExactLengthEvent (finiteValue omega) (j+1) (L+a.1.val+1) ∧ finiteValue omega (j+1)=a.2
  then some (Classical.choose h) else none
def categoryIndicator (C L E : ℕ) (G : Finset ℕ)
    (a : G×(Fin (E+1)×F₂)) (omega : SampleSpace C) : ℝ :=
  if lowCategory C L E a.1.val omega=some a.2 then 1 else 0
def uniformMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  ∑ omega, (Fintype.card Ω:ℝ)⁻¹*f omega
def centeredMoment {ι Ω : Type*} [Fintype Ω] (X : ι → Ω → ℝ) (S : Finset ι) : ℝ :=
  uniformMean (fun omega => ∏ i∈S, (X i omega-uniformMean (X i)))
def transversals {ι α : Type*} [Fintype ι] [Fintype α] : Finset (Finset (ι×α)) :=
  Finset.univ.powerset.filter (fun S => ∀ i a b, (i,a)∈S → (i,b)∈S → a=b)
/-- G.9 retains all cumulant orders of the actual low-category indicators. -/
def activity (C L E : ℕ) (G : Finset ℕ) : ℝ :=
  ∑ S∈(transversals (ι := G) (α := Fin (E+1)×F₂)).filter (fun S => 2≤S.card),
    (2:ℝ)^(S.card-1)*|Cumulants.cumulant (centeredMoment (categoryIndicator C L E G)) S|
def primeWindow (q : ℕ) : ℕ := 2^(q-1+Nat.log 2 q)
def primeExcess (q : ℕ) : ℕ := excess (primeWindow q) (q-1) 0
def primeCylinder (q : ℕ) : ℕ := primeWindow q+(q-1+primeExcess q+1)
def original (q : ℕ) : Finset ℕ := goodSites (primeWindow q) (q-1) 0
/-- Stronger retention requires every raw vertex to have a sufficiently large rough kernel. -/
def strongerGood (M L : ℕ) (I theta : ℝ) : Finset ℕ :=
  (goodSites M L I).filter (fun j => ∀ a : Fin (L+excess M L I+1+1),
    ⌊Real.exp (theta*Real.log M/saddleParameter 1 (Real.log M))⌋₊ <
      (roughPrimes (hardCutoff M) (j+a.val)).prod id)
def retained (q : ℕ) (theta : ℝ) : Finset ℕ := strongerGood (primeWindow q) (q-1) 0 theta
def obstructionConstant : ℝ := Real.log 2/2*(Real.log 3-1)
end Palm

namespace Palm
open Analysis Boundary Microscopic
 theorem cumulant_eq {ι : Type*} [DecidableEq ι] (m : Finset ι → ℝ) (S : Finset ι) :
    Cumulants.cumulant m S = PaperC.Prel8.FiniteCumulantPartitions.cumulant m S := by
  induction S using Finset.strongInductionOn
  rename_i S ih
  ·
    rw [Cumulants.cumulant,PaperC.Prel8.FiniteCumulantPartitions.cumulant]
    split_ifs
    · rfl
    · congr 1
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.prod_congr rfl
      intro B _
      exact ih B.val (Cumulants.proper_block_ssubset p.property B.property)
 theorem lowCategory_eq (C L E j : ℕ) : lowCategory C L E j =
    PaperC.Prel8.ArithmeticLowCategory.lowCategory C L E j := by
  funext omega
  unfold lowCategory PaperC.Prel8.ArithmeticLowCategory.lowCategory
  split_ifs <;> first | rfl | contradiction
 theorem activity_eq (C L E : ℕ) (G : Finset ℕ) : activity C L E G =
    PaperC.Prel8.CategoricalCumulantBound.activity (PaperC.FinitePMF.uniform (PaperC.SampleSpace C))
      (PaperC.Prel8.ArithmeticLowCategory.retainedCategory C L E G) := by
  unfold activity PaperC.Prel8.CategoricalCumulantBound.activity
  simp only [cumulant_eq]
  have he : categoryIndicator C L E G = PaperC.Prel8.CategoricalMomentExpansion.indicator
      (PaperC.Prel8.ArithmeticLowCategory.retainedCategory C L E G) := by
    funext a omega
    unfold categoryIndicator
    rw [lowCategory_eq]
    rfl
  rw [he]
  unfold PaperC.Prel8.FiniteCumulantEnvelope.jointCumulant
    PaperC.Prel8.FiniteCumulantEnvelope.centeredMoment centeredMoment uniformMean
    PaperC.IndependentThinning.finitePMFExpectation PaperC.FinitePMF.uniform
    transversals PaperC.Prel8.CategoricalTransversals.transversals PaperC.Prel8.CategoricalTransversals.Transversal
  congr 1
  ext S
  simp
 theorem primeExcess_eq (q : ℕ) : primeExcess q = PaperC.Prel8.PrimeWindowGeometry.excess q := by
  unfold primeExcess PaperC.Prel8.PrimeWindowGeometry.excess; rw [excess_eq]; rfl
 theorem primeCylinder_eq (q : ℕ) : primeCylinder q = PaperC.Prel8.PrimeWindowGeometry.cylinder q := by
  unfold primeCylinder PaperC.Prel8.PrimeWindowGeometry.cylinder PaperC.Prel8.PrimeWindowGeometry.support
  rw [primeExcess_eq]; rfl
 theorem original_eq (q : ℕ) : original q = PaperC.Prel8.PrimeRetainedDensity.original q := by
  unfold original PaperC.Prel8.PrimeRetainedDensity.original PaperC.Prel8.StrongerDeletionTheorem.originalGood
  rw [goodSites_eq]; rfl
 theorem strongerGood_eq (M L : ℕ) (I theta : ℝ) : strongerGood M L I theta =
    PaperC.Prel8.StrongerDeletionTheorem.strongerGood M L I theta := by
  unfold strongerGood PaperC.Prel8.StrongerDeletionTheorem.strongerGood
    PaperC.Prel8.RoughKernelGoodSet.paperGood PaperC.Prel8.RoughKernelDeletion.strongGood
    PaperC.Prel8.RoughKernelThreshold.threshold
  rw [goodSites_eq,excess_eq,Analysis.hardCutoff_eq,Analysis.saddleParameter_eq]
  rfl
 theorem retained_eq (q : ℕ) (theta : ℝ) : retained q theta = PaperC.Prel8.PrimeRetainedDensity.retained q theta := by
  unfold retained PaperC.Prel8.PrimeRetainedDensity.retained
  rw [strongerGood_eq]; rfl
end Palm
namespace Palm
open Analysis Boundary Microscopic
/-- G.9: normalized absolute cumulant activity on prime scales.

Assume the prime number theorem remainder. For every epsilon > 0, for all
sufficiently large natural q that are prime, set
 M_q=2^(q-1+floor(log_2 q)), L_q=q-1, E_q=excess(M_q,L_q,0),
 C_q=M_q+(L_q+E_q+1), and G=goodSites(M_q,L_q,0). The assertion is
 (log M_q)/M_q * activity(C_q,L_q,E_q,G) >= c_star-epsilon,
where c_star=(log 2)/2*(log 3-1) > 0.
Activity is the finite sum over all distinct-site sets of signed low-category
indices of size at least two of 2^(size-1) times the absolute joint cumulant.
Cumulants are defined by the finite partition recursion from centered moments
under uniform independent prime signs up to C_q; the exact categories have
excess <= E_q and use run starts j+1 for left-boundary labels j in G.
All orders, not only pairs, are included. The conclusion is along prime q,
not every integer q; it obstructs small normalized absolute cumulant activity
and is not a lower bound on total variation. There is no Stein premise.
-/
theorem original_cumulant_obstruction (hPNT : PrimeNumberTheoremRemainder)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, q.Prime → obstructionConstant-epsilon ≤
      Real.log (primeWindow q)/(primeWindow q:ℝ)*activity (primeCylinder q) (q-1) (primeExcess q) (original q) := by
  simp only [activity_eq,primeCylinder_eq,primeExcess_eq,original_eq]
  exact PaperC.Prel8.PrimeCumulantObstruction.original_obstruction hPNT hepsilon
/-- G.9: the same cumulant lower bound after stronger retention.

With the prime-scale definitions, centered cumulant activity and positive
constant c_star in `original_cumulant_obstruction`, replace G by
Gtheta=strongerGood(M_q,q-1,0,theta). Assume the prime number theorem remainder,
fix any theta >= 0 and epsilon > 0. For every sufficiently large prime q,
 (log M_q)/M_q * activity(C_q,q-1,E_q,Gtheta) >= c_star-epsilon.
The threshold may depend on the fixed theta and epsilon. No upper restriction
theta < c is imposed in this theorem, and no small-prime conditioning event
or Stein premise is required. The retained indicators and their centered
moments are the actual finite prime-sign objects, with every cumulant order
at least two included. This remains a cumulant-activity obstruction, not a
failure of the separately established Poisson approximation.
-/
theorem retained_cumulant_obstruction (hPNT : PrimeNumberTheoremRemainder)
    {theta : ℝ} (htheta : 0≤theta) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, q.Prime → obstructionConstant-epsilon ≤
      Real.log (primeWindow q)/(primeWindow q:ℝ)*activity (primeCylinder q) (q-1) (primeExcess q) (retained q theta) := by
  simp only [activity_eq,primeCylinder_eq,primeExcess_eq,retained_eq]
  exact PaperC.Prel8.PrimeCumulantObstruction.retained_obstruction hPNT htheta hepsilon
end Palm

namespace Palm
open Analysis Boundary Microscopic
/-- G.3 target regularity uses left-boundary labels, before shifting them to run starts. -/
def regularConfiguration (M L : ℕ) (I theta : ℝ) (z : Config (Finset.Icc 1 (M-L))) : Prop :=
  ∃ k≤⌈2*siteRate M L⌉₊, ∃ labels : Fin k → MarkIndex (Finset.Icc 1 (M-L)),
    z=∑ i, Finsupp.single (labels i) 1 ∧
    (∀ i, (labels i).1.val∈strongerGood M L I theta) ∧
    Regular (L+excess M L I+1) (hardCutoff M) (fun i => (labels i).1.val) ∧
    (∀ i, (labels i).2.1≤excess M L I)
end Palm
namespace Palm
open Analysis Boundary Microscopic
 theorem regularConfiguration_eq (M L : ℕ) (I theta : ℝ) : regularConfiguration M L I theta =
    PaperC.Prel8.RegularTargetSaddle.paperRegular M L I theta := by
  unfold regularConfiguration PaperC.Prel8.RegularTargetSaddle.paperRegular
    PaperC.Prel8.RegularTargetCloud.RegularConfiguration
  rw [excess_eq,Analysis.hardCutoff_eq,strongerGood_eq]
  rfl
end Palm

namespace Palm
open Analysis Boundary Microscopic
/-- G.1: weighted additional deletions and total omitted-site count.

Assume the prime number theorem remainder. Fix 0 < betaMin < betaMax and
0 <= theta < c. There is one Mzero such that, for every M >= Mzero and all
L,I in the length/information regime in the module account, both bounds hold:
 p * |G0 minus Gtheta| <= exp(-((c-theta)/2) nu),
 |{1,...,M-L} minus Gtheta| <= ceil(sqrt M) + M exp(-V+(theta+1)nu).
Here p=2^(-L), G0 is `goodSites M L I` and Gtheta is
`strongerGood M L I theta`, with the literal Y and E_M specified in the module
account. In particular, retention compares the product of odd-valuation primes
above Y at every raw vertex with floor(exp(theta H/u)); it does not change Y.
The first bound weights only the additionally omitted sites by the base rate;
the second counts all omitted left-boundary labels, including the initial
short segment and sites already absent from G0. Natural subtraction is used
in M-L. No separate L >= 1 hypothesis occurs; the positive logarithmic lower
band ensures it eventually. The threshold precedes L and I. I is a nonnegative
budget parameter here: there is no event A or equality I=-log P(A) in this
counting statement, and no Stein or other literature premise beyond PNT.
-/
theorem stronger_retention_counts (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax theta c : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax)
    (htheta : 0 ≤ theta) (htc : theta < c) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      (1/(2:ℝ)^L) * ((goodSites M L I \ strongerGood M L I theta).card : ℝ) ≤
        Real.exp (-((c-theta)/2)*saddleNu 1 (Real.log M)) ∧
      (((Finset.Icc 1 (M-L)) \ strongerGood M L I theta).card : ℝ) ≤
        (⌈Real.sqrt M⌉₊ : ℝ) + M * Real.exp
          (-saddleCutoff 1 (Real.log M)+(theta+1)*saddleNu 1 (Real.log M)) := by
  simp only [saddleCutoff_eq,saddleNu_eq,strongerGood_eq,goodSites_eq]
  exact PaperC.Prel8.StrongerDeletionTheorem.paper_counts hPNT betaMin betaMax theta c hmin hband htheta htc

/-- G.3: the full target is regular with probability tending to one.

Assume the prime number theorem remainder and fix 0 < betaMin < betaMax and
0 < theta < c. Let L(M) and I(M) eventually satisfy the length/information
regime in the module account, and require lambda(M)=(M-L(M))/2^L(M) to tend
to infinity. Under the full target Q on the left-boundary grid {1,...,M-L(M)},
 Q(z is not regularConfiguration(M,L(M),I(M),theta)) tends to zero.
In this predicate z is a sum of k planted atoms, k <= ceil(2 lambda); every
label belongs to Gtheta, every excess is <= E_M, and the raw supports
j,...,j+L+E_M+1 have private odd-valuation primes above Y. The target retains
all excesses, so excessive marks contribute to the exceptional probability.
This is the left-boundary convention j, before conversion to run starts j+1;
it is distinct from the shifted RegularPlant predicate used in the Palm sums.
There is no source conditioning event or Stein premise. This assertion about
the target alone neither asserts source regularity nor proves small source-to-
target total variation; the Palm comparisons retain their deficit term.
-/
theorem regular_target_probability (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c theta : ℝ) (hmin : 0<betaMin) (hband : betaMin<betaMax)
    (htheta : 0<theta) (htc : theta<c) (L : ℕ → ℕ) (I : ℕ → ℝ)
    (hrate : Tendsto (fun M ↦ siteRate M (L M)) atTop atTop)
    (hregime : ∀ᶠ M : ℕ in atTop, betaMin*Real.log M≤(L M+1:ℝ) ∧
      (L M+1:ℝ)≤betaMax*Real.log M ∧ 0≤I M ∧ 1≤siteRate M (L M) ∧
      I M+Real.log (siteRate M (L M))≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) :
    Tendsto (fun M ↦ (target (Finset.Icc 1 (M-L M)) (L M)).real
      {z | ¬regularConfiguration M (L M) (I M) theta z}) atTop (𝓝 0) := by
  simp only [saddleCutoff_eq,saddleNu_eq] at hregime
  simp only [regularConfiguration_eq,target_eq]
  exact PaperC.Prel8.RegularTargetCompletion.target_failure_tendsto hPNT betaMin betaMax c theta hmin hband htheta htc L I hrate hregime

end Palm

end
end PaperCV3Audit
