import PaperCV282.AffineCrossoverUncappingTheorem
import PaperCV282.AffineCrossoverSign
import PaperCV282.CrossoverResolvedLocationTheorem
import PaperCV282.CrossoverLocationTheorem
import PaperCV282.CrossoverSignTheorem

set_option maxHeartbeats 1000000
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

namespace Crossover
open Boundary Analysis
open scoped BoundedContinuousFunction
abbrev Record := Option (Sum ℕ (ℕ × (ℕ × F₂)))
instance instMeasurableRecord : MeasurableSpace Record := ⊤
instance instMeasurableSingletonRecord : MeasurableSingletonClass Record := by infer_instance
abbrev MarkIndex (sites : Finset ℕ) := {x : ℕ // x∈sites} × (ℕ × F₂)
def hitEvent (M L : ℕ) : Set InfiniteSample := {omega | L≤longestRun M omega}
def siteStartEvent (L x : ℕ) : Set InfiniteSample :=
  if x=1 then borderEvent L else if 2≤x then startEvent x L else ∅
def containedStarts (M L : ℕ) (omega : InfiniteSample) : Finset ℕ :=
  (Finset.Icc 1 (M-L+1)).filter (fun x => L≤M ∧ omega∈siteStartEvent L x)
def firstStart (M L : ℕ) (omega : InfiniteSample) : ℕ :=
  if h : (containedStarts M L omega).Nonempty then Nat.find h else 0
def bulkStarts (M L : ℕ) (delta : ℝ) : Finset ℕ := Finset.Icc ⌈(M : ℝ)^delta⌉₊ (M-L+1)
def firstNegativeIndex (omega : InfiniteSample) : ℕ :=
  if h : ∃ j,omega j≠0 then Nat.find h else 0
def primeOvershoot (L : ℕ) (omega : InfiniteSample) : ℕ :=
  if omega∈borderEvent L then firstNegativeIndex omega-Nat.primeCounting L else 0
def signedMarkValue (g : ℕ→F₂) (x L e : ℕ) (s : F₂) : ℕ :=
  if ExactLengthEvent g x (L+e+1) ∧ g x=s then 1 else 0
/- A direct reading of the unique exact mark; it does not encode a law. -/
def gamma (M L : ℕ) (delta : ℝ) (omega : InfiniteSample) : Record :=
  let sites := bulkStarts M L delta
  let x := firstStart M L omega
  if x=1 then some (Sum.inl (primeOvershoot L omega)) else
    (if h : ∃ j : MarkIndex sites, j.1.val=x ∧
      signedMarkValue (infiniteValueBit omega) j.1.val L j.2.1 j.2.2≠0 then some h.choose else none).map
        (fun j => Sum.inr (j.1.val,j.2))
def sourceLaw (M L : ℕ) (delta : ℝ) (A : Set InfiniteSample) : Measure Record :=
  (cond infiniteRademacherMeasure (A∩hitEvent M L)).map (gamma M L delta)
def halfSuccess : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
def borderLabel (G : ℕ) : Record := some (Sum.inl G)
def bulkLabel (sites : Finset ℕ) (j : MarkIndex sites) : Record := some (Sum.inr (j.1.val,j.2))
def uniformSiteMeasure (sites : Finset ℕ) (hs : sites.Nonempty) : Measure {x // x∈sites} := by
  letI instNonemptySites : Nonempty {x // x∈sites} := ⟨⟨hs.choose,hs.choose_spec⟩⟩
  exact (PMF.uniformOfFintype {x // x∈sites}).toMeasure
def labelMeasure (sites : Finset ℕ) (hs : sites.Nonempty) : Measure (MarkIndex sites) :=
  (uniformSiteMeasure sites hs).prod ((geometricMeasure halfSuccess).prod coordinateMeasure)
def borderLaw : Measure Record := (geometricMeasure halfSuccess).map borderLabel
def bulkLaw (sites : Finset ℕ) (hs : sites.Nonempty) : Measure Record :=
  (labelMeasure sites hs).map (bulkLabel sites)
def totalRate (sites : Finset ℕ) (L : ℕ) : ℝ≥0 := sites.card/(2 : ℝ≥0)^L
def borderWeight (sites : Finset ℕ) (L : ℕ) (alpha : ℝ≥0) : ℝ≥0 := alpha/(alpha+totalRate sites L)
def bulkWeight (sites : Finset ℕ) (L : ℕ) (alpha : ℝ≥0) : ℝ≥0 := totalRate sites L/(alpha+totalRate sites L)
def mixedLaw (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) (alpha : ℝ≥0) : Measure Record :=
  (borderWeight sites L alpha : ℝ≥0∞) • borderLaw + (bulkWeight sites L alpha : ℝ≥0∞) • bulkLaw sites hs
def targetLaw (M L : ℕ) (delta : ℝ) (alpha : ℝ≥0) : Measure Record :=
  if hs : (bulkStarts M L delta).Nonempty then mixedLaw (bulkStarts M L delta) hs L alpha else borderLaw
def distance (M L : ℕ) (delta : ℝ) (A : Set InfiniteSample) (alpha : ℝ≥0) : ℝ :=
  measureTV (sourceLaw M L delta A) (targetLaw M L delta alpha)
def borderRate (L : ℕ) : ℝ≥0 := 1/2^Nat.primeCounting L
def locationLaw (M L : ℕ) (A : Set InfiniteSample) : Measure ℝ :=
  (cond infiniteRademacherMeasure (A∩hitEvent M L)).map (fun omega => (firstStart M L omega : ℝ)/M)
def resolvedInteger (L x : ℕ) : Bool×ℕ := if x≤2*L^2 then (false,x) else (true,x)
def resolvedPosition (M L : ℕ) (z : Bool×ℕ) : Bool×ℝ :=
  (z.1,(z.2 : ℝ)/(if z.1 then (M : ℝ) else (L : ℝ)^2))
def resolvedLaw (M L : ℕ) (A : Set InfiniteSample) : Measure (Bool×ℝ) :=
  (cond infiniteRademacherMeasure (A∩hitEvent M L)).map
    (fun omega => resolvedPosition M L (resolvedInteger L (firstStart M L omega)))
def phaseBorderWeight (s : ℝ) : ℝ≥0 := ⟨1/(1+(2 : ℝ)^(-s)),by positivity⟩
def phaseBulkWeight (s : ℝ) : ℝ≥0 := ⟨(2 : ℝ)^(-s)/(1+(2 : ℝ)^(-s)),by positivity⟩
def zeroLaw : Measure ℝ := Measure.dirac 0
def uniformLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
def labelledLaw (b : Bool) (mu : Measure ℝ) : Measure (Bool×ℝ) := mu.map (fun x => (b,x))
def limitLaw (s : ℝ) : Measure ℝ :=
  (phaseBorderWeight s : ℝ≥0∞) • zeroLaw+(phaseBulkWeight s : ℝ≥0∞) • uniformLaw
def resolvedLimitLaw (s : ℝ) : Measure (Bool×ℝ) :=
  (phaseBorderWeight s : ℝ≥0∞) • labelledLaw false zeroLaw+
    (phaseBulkWeight s : ℝ≥0∞) • labelledLaw true uniformLaw
def Weakly {α : Type*} [MeasurableSpace α] [TopologicalSpace α] (mu : ℕ→Measure α) (nu : Measure α) : Prop :=
  ∀ F : α→ᵇℝ, Tendsto (fun n => ∫ x,F x ∂mu n) atTop (𝓝 (∫ x,F x ∂nu))
def phase (M L d : ℕ) : ℝ := (L : ℝ)-Real.log M/Real.log 2-d
/- The affine system is literal on the first pi(Y) prime bits. -/
variable {Y : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]
def borderPrimeEmbedding {L : ℕ} (hLY : L≤Y) : PrimeUpTo L ↪ PrimeUpTo Y where
  toFun p := ⟨⟨p.val.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ p.val.isLt).trans hLY)⟩,p.property⟩
  inj' p q hpq := by
    apply Subtype.ext; apply Fin.ext
    exact congrArg (fun p : PrimeUpTo Y => p.val.val) hpq
def borderProjection {L : ℕ} (hLY : L≤Y) : SampleSpace Y→ₗ[F₂]SampleSpace L where
  toFun sigma p := sigma (borderPrimeEmbedding hLY p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def affineCylinder (G : SampleSpace Y→ₗ[F₂]W) (b : W) : Set InfiniteSample :=
  {omega | G (restrictToFinite Y omega)=b}
def Compatible {V W : Type*} [AddCommGroup V] [Module F₂ V] [AddCommGroup W] [Module F₂ W]
    (G : V→ₗ[F₂]W) (b : W) : Prop := ∃ v,G v=b
def rowSpace (G : SampleSpace Y→ₗ[F₂]W) : Submodule F₂ (Module.Dual F₂ (SampleSpace Y)) :=
  LinearMap.range G.dualMap
def cylinderInformation (G : SampleSpace Y→ₗ[F₂]W) : ℝ :=
  (Module.finrank F₂ (LinearMap.range G) : ℝ)*Real.log 2
def borderDeficitAt (G : SampleSpace Y→ₗ[F₂]W) (L : ℕ) : ℕ :=
  Nat.primeCounting (min L Y)-Module.finrank F₂ ↥(rowSpace G ⊓ rowSpace (borderProjection (Nat.min_le_right L Y)))
def futurePrimeEmbedding {L K : ℕ} (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤Y) :
    Fin K ↪ PrimeUpTo Y where
  toFun i := ⟨⟨Nat.nth Nat.Prime (Nat.primeCounting L+i.val),Nat.lt_succ_of_le
    ((Nat.nth_monotone Nat.infinite_setOf_prime (by omega : Nat.primeCounting L+i.val≤Nat.primeCounting L+K)).trans hcut)⟩,
      Nat.prime_nth_prime _⟩
  inj' i j hij := by
    have hp := congrArg (fun p : PrimeUpTo Y => p.val.val) hij
    have heq := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hp
    exact Fin.ext (by omega)
def futurePrimeProjection {L K : ℕ} (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤Y) :
    SampleSpace Y→ₗ[F₂](Fin K→F₂) where
  toFun sigma i := sigma (futurePrimeEmbedding hcut i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def FutureNeutralAt (G : SampleSpace Y→ₗ[F₂]W) (L K : ℕ) : Prop :=
  ∃ hLY : L≤Y, ∃ hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤Y,
    (rowSpace G ⊔ rowSpace (borderProjection hLY)) ⊓ rowSpace (futurePrimeProjection hcut)=⊥
def positiveProbability (M L : ℕ) (A : Set InfiniteSample) : ℝ :=
  (cond infiniteRademacherMeasure (A∩hitEvent M L)).real
    {omega | (if infiniteValueBit omega (firstStart M L omega)=0 then true else false)=true}
end Crossover

open Boundary Analysis Crossover Process
namespace Analysis
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
private theorem borderDeficit_eq_core {Y : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]
    (G : SampleSpace Y→ₗ[F₂]W) (L : ℕ) : borderDeficitAt G L =
      PaperC.V282.AffineCrossoverDeficit.borderDeficitAt G L := by
  unfold borderDeficitAt PaperC.V282.AffineCrossoverDeficit.borderDeficitAt
    PaperC.V282.AffineCrossoverCylinder.borderDeficit PaperC.V282.AffineCrossoverCylinder.borderOverlap
    PaperC.V282.AffineBorderLinear.rowOverlap
  rfl
private theorem firstStart_eq_core (M L : ℕ) : firstStart M L = PaperC.V282.RarePrefixGeometry.firstStart M L := rfl
private theorem signedMark_eq_core (g : ℕ→F₂) (x L e : ℕ) (a : F₂) : signedMarkValue g x L e a =
    PaperC.V282.ExactMarkedModel.signedMarkValue g x L e a := by
  unfold signedMarkValue PaperC.V282.ExactMarkedModel.signedMarkValue
    PaperC.V282.ExactMarkedModel.SignedExactMark PaperC.MixedLengthAffine.excessRowCount
    PaperCV3Audit.ExactLengthEvent PaperC.MixedLengthAffine.ExactLengthEvent
  split_ifs <;> rfl
private theorem primeOvershoot_eq_core (L : ℕ) : primeOvershoot L = PaperC.V282.PrimeClockDistribution.primeOvershoot L := rfl
private theorem gamma_eq (M L : ℕ) (delta : ℝ) : Crossover.gamma M L delta =
    PaperC.V282.CrossoverMarkedModel.gamma M L delta := by
  funext omega
  unfold Crossover.gamma PaperC.V282.CrossoverMarkedModel.gamma PaperC.V282.CrossoverMarkedModel.recordFromValues
  simp only [PaperC.V282.CrossoverMarkedModel.pointAtSite,
    PaperC.V282.BulkMarkedSource.spatialMarkedSource_apply,PaperC.V282.BulkMarkedSource.spatialMarkedValue]
  simp_rw [signedMark_eq_core,firstStart_eq_core,primeOvershoot_eq_core]
  rfl
private theorem target_eq (M L : ℕ) (delta : ℝ) (alpha : ℝ≥0) : targetLaw M L delta alpha =
    PaperC.V282.AffineCrossoverTarget.targetLaw M L delta alpha := rfl
private theorem unconditioned_distance_eq (M L : ℕ) (delta : ℝ) :
    distance M L delta Set.univ (borderRate L) = PaperC.V282.CrossoverMovingTarget.actualDistance M L delta := by
  unfold distance sourceLaw
  rw [Set.univ_inter,gamma_eq]
  rfl
private theorem conditioned_distance_eq {Y : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]
    (G : SampleSpace Y→ₗ[F₂]W) (b : W) (M L : ℕ) (delta : ℝ) (alpha : ℝ≥0) :
    distance M L delta (affineCylinder G b) alpha =
      PaperC.V282.AffineCrossoverModel.actualDistance
        (PaperC.V282.AffineCrossoverModel.conditionedMeasure (PaperC.V282.AffineBorderCylinders.affineCylinder G b))
        M L delta alpha := by
  unfold distance PaperC.V282.AffineCrossoverModel.actualDistance
  rw [PaperC.V282.AffineCrossoverModel.sourceLaw_conditioned _
    (PaperC.V282.AffineBorderCylinders.measurableSet_affineCylinder G b)]
  unfold sourceLaw
  rw [gamma_eq]
  rfl
private theorem limitLaw_eq (s : ℝ) : limitLaw s =
    (PaperC.V282.CrossoverLocationMixture.crossoverLimitLaw s : Measure ℝ) := by
  unfold limitLaw PaperC.V282.CrossoverLocationMixture.crossoverLimitLaw PaperC.V282.CrossoverLocationMixture.mixtureLaw
  simp only [ProbabilityMeasure.coe_mk]
  rw [PaperC.V282.CrossoverLocationGrid.unitIntervalLaw_eq_volume_restrict]
  rfl
private theorem resolvedLimitLaw_eq (s : ℝ) : resolvedLimitLaw s =
    (PaperC.V282.CrossoverResolvedLocationTarget.resolvedLimitLaw s : Measure (Bool×ℝ)) := by
  unfold resolvedLimitLaw PaperC.V282.CrossoverResolvedLocationTarget.resolvedLimitLaw
    PaperC.V282.CrossoverResolvedLocationTarget.resolvedMixture
  simp only [ProbabilityMeasure.coe_mk]
  unfold labelledLaw PaperC.V282.CrossoverResolvedLocationTarget.labelledLaw PaperC.V282.CountableWeakTransfer.imageProbabilityLaw
  simp only [ProbabilityMeasure.coe_mk]
  rw [PaperC.V282.CrossoverLocationGrid.unitIntervalLaw_eq_volume_restrict]
  rfl
private theorem weakly_of_probability {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α]
    (p : ℕ→ProbabilityMeasure α) (q : ProbabilityMeasure α)
    (mu : ℕ→Measure α) (nu : Measure α) (ht : Tendsto p atTop (𝓝 q))
    (he : ∀ᶠ n in atTop,(p n : Measure α)=mu n) (hq : (q : Measure α)=nu) : Weakly mu nu := by
  intro F
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht) F
  rw [hq] at h
  apply h.congr'
  filter_upwards [he] with n hn
  rw [hn]
private theorem ordinary_location_eq {M L : ℕ} (hLM : L≤M) :
    locationLaw M L Set.univ=(PaperC.V282.CrossoverLocationTransfer.firstLocationLaw M L : Measure ℝ) := by
  unfold locationLaw
  rw [Set.univ_inter]
  symm
  change (PaperC.V282.CrossoverLocationTransfer.firstStartLaw M L : Measure ℕ).map _ = _
  rw [PaperC.V282.CrossoverLocationTransfer.firstStartLaw_eq hLM,
    Measure.map_map (measurable_of_countable _) (PaperC.V282.RarePrefixGeometry.measurable_firstStart M L)]
  rfl
private theorem ordinary_resolved_eq {M L : ℕ} (hLM : L≤M) :
    resolvedLaw M L Set.univ=(PaperC.V282.CrossoverResolvedLocationSource.resolvedSourceLaw M L : Measure (Bool×ℝ)) := by
  unfold resolvedLaw
  rw [Set.univ_inter]
  symm
  exact PaperC.V282.CrossoverResolvedLocationSource.resolvedSourceLaw_eq hLM
private theorem affine_location_eq {M L : ℕ} {A : Set InfiniteSample}
    (hp : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) :
    locationLaw M L A=(PaperC.V282.AffineCrossoverLocationSource.firstLocationLaw M L A : Measure ℝ) :=
  (PaperC.V282.AffineCrossoverLocationSource.firstLocationLaw_eq hp).symm
private theorem affine_resolved_eq {M L : ℕ} {A : Set InfiniteSample}
    (hp : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) :
    resolvedLaw M L A=(PaperC.V282.AffineCrossoverLocationSource.resolvedSourceLaw M L A : Measure (Bool×ℝ)) :=
  (PaperC.V282.AffineCrossoverLocationSource.resolvedSourceLaw_eq hp).symm

private theorem positiveProbability_eq_core (M L : ℕ) : positiveProbability M L Set.univ =
    PaperC.V282.CrossoverSignTheorem.positiveProbability M L := by
  unfold positiveProbability PaperC.V282.CrossoverSignTheorem.positiveProbability
  rw [Set.univ_inter]
  congr 1

private theorem borderRate_eq_core (L : ℕ) : borderRate L =
    PaperC.V282.CrossoverMarkedTarget.borderRate L := rfl
private theorem totalRate_eq_core (sites : Finset ℕ) (L : ℕ) : totalRate sites L =
    PaperC.V282.CrossoverBulkAtoms.totalRate sites L := rfl
private theorem bulkStarts_eq_core (M L : ℕ) (delta : ℝ) : bulkStarts M L delta =
    PaperC.V282.BulkMarkedGeometry.bulkStarts M L delta := rfl

theorem v3_crossover_affine_border_mass {Y L : ℕ} (hLY : L≤Y)
    {W : Type*} [AddCommGroup W] [Module F₂ W] (G : SampleSpace Y→ₗ[F₂]W) (b : W)
    (hstack : Compatible (G.prod (borderProjection hLY)) (b,0)) :
    (cond infiniteRademacherMeasure (affineCylinder G b)).real (Boundary.borderEvent L)=
      1/(2 : ℝ)^borderDeficitAt G L := by
  rw [borderDeficit_eq_core,PaperC.V282.AffineCrossoverDeficit.borderDeficitAt_eq G hLY]
  exact PaperC.V282.AffineBorderCylinders.theorem_seven_ten_exact_border_mass hLY G b hstack

section Unconditioned
variable (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : DivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
include hAGG hPNT hLS hShorey hNR hsizes hlengths hbeta hdelta hdeltaOne hupper hrare

theorem v3_crossover_complete_moving_mixture  :
    Tendsto (fun n => distance (sizes n) (lengths n) delta Set.univ (borderRate (lengths n))) atTop (𝓝 0) := by
  simpa only [unconditioned_distance_eq] using
    PaperC.V282.CrossoverMarkedConvergence.theorem_seven_nine (process_input_to_core hAGG) hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta hdeltaOne hupper hrare

theorem v3_crossover_locations (s : ℝ) (hphase : Tendsto (fun n => phase (sizes n) (lengths n) (Nat.primeCounting (lengths n))) atTop (𝓝 s)) :
    Weakly (fun n => locationLaw (sizes n) (lengths n) Set.univ) (limitLaw s) ∧
    Weakly (fun n => resolvedLaw (sizes n) (lengths n) Set.univ) (resolvedLimitLaw s) := by
  have h1 := PaperC.V282.CrossoverLocationTheorem.equation_seven_nineteen (process_input_to_core hAGG) hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta hdeltaOne hupper hrare s hphase
  have h2 := PaperC.V282.CrossoverResolvedLocationTheorem.equation_seven_nineteen_resolved (process_input_to_core hAGG) hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta hdeltaOne hupper hrare s hphase
  have hc := PaperC.V282.RarePrefixMass.logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper
  constructor
  · exact weakly_of_probability _ _ _ _ h1
      (hc.mono fun n hn => (ordinary_location_eq hn).symm) ((limitLaw_eq s).symm)
  · exact weakly_of_probability _ _ _ _ h2
      (hc.mono fun n hn => (ordinary_resolved_eq hn).symm) ((resolvedLimitLaw_eq s).symm)

theorem v3_crossover_locations_atTop (hphase : Tendsto (fun n => phase (sizes n) (lengths n) (Nat.primeCounting (lengths n))) atTop atTop) :
    Weakly (fun n => locationLaw (sizes n) (lengths n) Set.univ) (zeroLaw) ∧
    Weakly (fun n => resolvedLaw (sizes n) (lengths n) Set.univ) (labelledLaw false zeroLaw) := by
  have h1 := PaperC.V282.CrossoverLocationTheorem.equation_seven_nineteen_phase_atTop (process_input_to_core hAGG) hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta hdeltaOne hupper hrare hphase
  have h2 := PaperC.V282.CrossoverResolvedLocationTheorem.equation_seven_nineteen_resolved_phase_atTop (process_input_to_core hAGG) hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta hdeltaOne hupper hrare hphase
  have hc := PaperC.V282.RarePrefixMass.logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper
  constructor
  · exact weakly_of_probability _ _ _ _ h1
      (hc.mono fun n hn => (ordinary_location_eq hn).symm) (rfl)
  · exact weakly_of_probability _ _ _ _ h2
      (hc.mono fun n hn => (ordinary_resolved_eq hn).symm) (rfl)

theorem v3_crossover_locations_atBot (hphase : Tendsto (fun n => phase (sizes n) (lengths n) (Nat.primeCounting (lengths n))) atTop atBot) :
    Weakly (fun n => locationLaw (sizes n) (lengths n) Set.univ) (uniformLaw) ∧
    Weakly (fun n => resolvedLaw (sizes n) (lengths n) Set.univ) (labelledLaw true uniformLaw) := by
  have h1 := PaperC.V282.CrossoverLocationTheorem.equation_seven_nineteen_phase_atBot (process_input_to_core hAGG) hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta hdeltaOne hupper hrare hphase
  have h2 := PaperC.V282.CrossoverResolvedLocationTheorem.equation_seven_nineteen_resolved_phase_atBot (process_input_to_core hAGG) hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta hdeltaOne hupper hrare hphase
  have hc := PaperC.V282.RarePrefixMass.logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper
  constructor
  · exact weakly_of_probability _ _ _ _ h1
      (hc.mono fun n hn => (ordinary_location_eq hn).symm) (PaperC.V282.CrossoverLocationGrid.unitIntervalLaw_eq_volume_restrict)
  · exact weakly_of_probability _ _ _ _ h2
      (hc.mono fun n hn => (ordinary_resolved_eq hn).symm) (by change (PaperC.V282.CrossoverLocationGrid.unitIntervalLaw : Measure ℝ).map _ = _; rw [PaperC.V282.CrossoverLocationGrid.unitIntervalLaw_eq_volume_restrict]; rfl)

theorem v3_crossover_sign  :
    Tendsto (fun n => positiveProbability (sizes n) (lengths n) Set.univ-
      ((borderRate (lengths n) : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)/2)/
        ((borderRate (lengths n) : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)))
      atTop (𝓝 0) := by
  have ht := PaperC.V282.CrossoverSignTheorem.theorem_seven_nine_sign (process_input_to_core hAGG) hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta hdeltaOne hupper hrare
  simpa only [positiveProbability_eq_core,borderRate_eq_core,totalRate_eq_core,bulkStarts_eq_core] using ht

end Unconditioned

section Affine
variable (hAGG : ProcessAGGStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : DivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta c : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1) (hc : 0<c)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (W : ℕ→Type*) [∀ n,AddCommGroup (W n)] [∀ n,Module F₂ (W n)]
    (G : ∀ n,SampleSpace (hardCutoff (sizes n))→ₗ[F₂]W n) (b : ∀ n,W n)
    (hstack : ∀ᶠ n in atTop,∃ hLY : lengths n≤hardCutoff (sizes n),
      Compatible ((G n).prod (borderProjection hLY)) (b n,0))
    (hbudget : ∀ᶠ n in atTop,cylinderInformation (G n)≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n)))
include hAGG hLS hShorey hPNT hNR hsizes hlengths hbeta hdelta hdeltaOne hc hupper hrare hstack hbudget

theorem v3_crossover_affine_complete_clock (hneutral : ∀ K,∀ᶠ n in atTop,FutureNeutralAt (G n) (lengths n) K) :
    Tendsto (fun n => distance (sizes n) (lengths n) delta (affineCylinder (G n) (b n))
      (((2 : ℝ≥0)⁻¹)^borderDeficitAt (G n) (lengths n))) atTop (𝓝 0) := by
  revert hneutral hbudget hstack b G
  rw [show Analysis.hardCutoff=PaperC.V282.HardPoissonRates.hardCutoff from funext Analysis.hardCutoff_eq]
  simp_rw [Analysis.saddleCutoff_eq,Analysis.saddleNu_eq]
  intro G b hstack hbudget hneutral
  simpa only [conditioned_distance_eq,borderDeficit_eq_core] using
    PaperC.V282.AffineCrossoverUncappingTheorem.theorem_seven_ten_complete_clock_deficit (process_input_to_core hAGG) hLS hShorey hPNT hNR sizes lengths hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget hneutral

theorem v3_crossover_affine_locations (s : ℝ) (hphase : Tendsto (fun n => phase (sizes n) (lengths n) (borderDeficitAt (G n) (lengths n))) atTop (𝓝 s)) :
    Weakly (fun n => locationLaw (sizes n) (lengths n) (affineCylinder (G n) (b n))) (limitLaw s) ∧
    Weakly (fun n => resolvedLaw (sizes n) (lengths n) (affineCylinder (G n) (b n))) (resolvedLimitLaw s) := by
  revert hphase hbudget hstack b G
  rw [show Analysis.hardCutoff=PaperC.V282.HardPoissonRates.hardCutoff from funext Analysis.hardCutoff_eq]
  simp_rw [Analysis.saddleCutoff_eq,Analysis.saddleNu_eq]
  intro G b hstack hbudget hphase
  simp_rw [borderDeficit_eq_core] at hphase
  have ht := PaperC.V282.AffineCrossoverLocationTheorem.theorem_seven_ten_location (process_input_to_core hAGG) hLS hShorey hPNT hNR sizes lengths hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget s hphase
  obtain ⟨hp,_,_⟩ := PaperC.V282.AffineCrossoverLocationTheorem.location_inputs_under_rank_budget (process_input_to_core hAGG) hLS hShorey hPNT hNR sizes lengths hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  constructor
  · exact weakly_of_probability _ _ _ _ ht.1
      (hp.mono fun n hn => (affine_location_eq hn).symm) ((limitLaw_eq s).symm)
  · exact weakly_of_probability _ _ _ _ ht.2
      (hp.mono fun n hn => (affine_resolved_eq hn).symm) ((resolvedLimitLaw_eq s).symm)

theorem v3_crossover_affine_locations_atTop (hphase : Tendsto (fun n => phase (sizes n) (lengths n) (borderDeficitAt (G n) (lengths n))) atTop atTop) :
    Weakly (fun n => locationLaw (sizes n) (lengths n) (affineCylinder (G n) (b n))) (zeroLaw) ∧
    Weakly (fun n => resolvedLaw (sizes n) (lengths n) (affineCylinder (G n) (b n))) (labelledLaw false zeroLaw) := by
  revert hphase hbudget hstack b G
  rw [show Analysis.hardCutoff=PaperC.V282.HardPoissonRates.hardCutoff from funext Analysis.hardCutoff_eq]
  simp_rw [Analysis.saddleCutoff_eq,Analysis.saddleNu_eq]
  intro G b hstack hbudget hphase
  simp_rw [borderDeficit_eq_core] at hphase
  have ht := PaperC.V282.AffineCrossoverLocationTheorem.theorem_seven_ten_location_phase_atTop (process_input_to_core hAGG) hLS hShorey hPNT hNR sizes lengths hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget hphase
  obtain ⟨hp,_,_⟩ := PaperC.V282.AffineCrossoverLocationTheorem.location_inputs_under_rank_budget (process_input_to_core hAGG) hLS hShorey hPNT hNR sizes lengths hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  constructor
  · exact weakly_of_probability _ _ _ _ ht.1
      (hp.mono fun n hn => (affine_location_eq hn).symm) (rfl)
  · exact weakly_of_probability _ _ _ _ ht.2
      (hp.mono fun n hn => (affine_resolved_eq hn).symm) (rfl)

theorem v3_crossover_affine_locations_atBot (hphase : Tendsto (fun n => phase (sizes n) (lengths n) (borderDeficitAt (G n) (lengths n))) atTop atBot) :
    Weakly (fun n => locationLaw (sizes n) (lengths n) (affineCylinder (G n) (b n))) (uniformLaw) ∧
    Weakly (fun n => resolvedLaw (sizes n) (lengths n) (affineCylinder (G n) (b n))) (labelledLaw true uniformLaw) := by
  revert hphase hbudget hstack b G
  rw [show Analysis.hardCutoff=PaperC.V282.HardPoissonRates.hardCutoff from funext Analysis.hardCutoff_eq]
  simp_rw [Analysis.saddleCutoff_eq,Analysis.saddleNu_eq]
  intro G b hstack hbudget hphase
  simp_rw [borderDeficit_eq_core] at hphase
  have ht := PaperC.V282.AffineCrossoverLocationTheorem.theorem_seven_ten_location_phase_atBot (process_input_to_core hAGG) hLS hShorey hPNT hNR sizes lengths hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget hphase
  obtain ⟨hp,_,_⟩ := PaperC.V282.AffineCrossoverLocationTheorem.location_inputs_under_rank_budget (process_input_to_core hAGG) hLS hShorey hPNT hNR sizes lengths hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  constructor
  · exact weakly_of_probability _ _ _ _ ht.1
      (hp.mono fun n hn => (affine_location_eq hn).symm) (PaperC.V282.CrossoverLocationGrid.unitIntervalLaw_eq_volume_restrict)
  · exact weakly_of_probability _ _ _ _ ht.2
      (hp.mono fun n hn => (affine_resolved_eq hn).symm) (by change (PaperC.V282.CrossoverLocationGrid.unitIntervalLaw : Measure ℝ).map _ = _; rw [PaperC.V282.CrossoverLocationGrid.unitIntervalLaw_eq_volume_restrict]; rfl)

theorem v3_crossover_affine_sign  :
    Tendsto (fun n => positiveProbability (sizes n) (lengths n) (affineCylinder (G n) (b n))-
      ((((2 : ℝ≥0)⁻¹)^borderDeficitAt (G n) (lengths n) : ℝ)+
          (totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)/2)/
        ((((2 : ℝ≥0)⁻¹)^borderDeficitAt (G n) (lengths n) : ℝ)+
          (totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)))
      atTop (𝓝 0) := by
  revert hbudget hstack b G
  rw [show Analysis.hardCutoff=PaperC.V282.HardPoissonRates.hardCutoff from funext Analysis.hardCutoff_eq]
  simp_rw [Analysis.saddleCutoff_eq,Analysis.saddleNu_eq]
  intro G b hstack hbudget
  have ht := PaperC.V282.AffineCrossoverSign.theorem_seven_ten_sign (process_input_to_core hAGG) hLS hShorey hPNT hNR sizes lengths hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  apply ht.congr'
  filter_upwards [hstack] with n hn
  obtain ⟨hLY,hs⟩ := hn
  rw [PaperC.V282.AffineCrossoverDeficit.conditionalBorderRate_eq_deficit (G n) (b n) hLY hs]
  simp only [borderDeficit_eq_core]
  rfl

end Affine
end
end PaperCV3Audit
