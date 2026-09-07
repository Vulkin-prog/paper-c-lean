import Mathlib

/-! V3PREL patterns candidate: autonomous transparent interface, followed by proved bridges. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PaperCV3Audit
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
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

def poissonMass (rate : ℝ≥0) (k : ℕ) : ℝ := (poissonMeasure rate).real {k}

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
def massTV {α : Type*} (p q : α → ℝ) : ℝ := (2 : ℝ)⁻¹ * ∑' k, |p k-q k|
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
namespace Patterns
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology

/- Actual independent prime bits; all observations below are functions of this source. -/
@[reducible] def Bit := ZMod 2
local instance instMeasurableBit : MeasurableSpace Bit := ⊤
@[reducible] def Sample := ℕ → Bit
@[reducible] def PrimeUpTo (Y : ℕ) := {p : Fin (Y+1) // Nat.Prime p.val}
def parity (n : ℕ) : ℕ →₀ Bit :=
  n.factorization.mapRange (fun e : ℕ => (e : Bit)) (by simp)
def coordinateMeasure : Measure Bit := (PMF.uniformOfFintype Bit).toMeasure
def sourceMeasure : Measure Sample := Measure.infinitePi (fun _ : ℕ => coordinateMeasure)
def value (omega : Sample) (n : ℕ) : Bit :=
  (parity n).sum fun p e => omega (Nat.primeCounting' p) * e
def restrict (Y : ℕ) (omega : Sample) : PrimeUpTo Y → Bit :=
  fun p => omega (Nat.primeCounting' p.val.val)
@[reducible] def fullFY (Y : ℕ) : MeasurableSpace Sample :=
  MeasurableSpace.comap (restrict Y) inferInstance
def block (N : ℕ) : Finset ℕ := Finset.Ico N (2*N)
def fullRate (N L : ℕ) : ℝ≥0 := ⟨(N : ℝ)/2^L, by positivity⟩
def information (A : Set Sample) : ℝ := -Real.log (sourceMeasure.real A)

def massTV {α : Type*} (p q : α → ℝ) : ℝ := (2 : ℝ)⁻¹ * ∑' a, |p a-q a|
def law {Ω α : Type*} [MeasurableSpace Ω] (mu : Measure Ω) (f : Ω → α) (a : α) : ℝ :=
  mu.real {omega | f omega=a}
def poissonMass (rate : ℝ≥0) (k : ℕ) : ℝ := (poissonMeasure rate).real {k}
def poissonFieldMass {I : Type*} [Fintype I] (rates : I → ℝ≥0) (k : I → ℕ) : ℝ :=
  ∏ i, poissonMass (rates i) (k i)
def fieldMeasure {I : Type*} [Fintype I] (rates : I → ℝ≥0) : Measure (I → ℕ) :=
  Measure.pi (fun i => poissonMeasure (rates i))

/- Full prescribed words include the left root x-1. Ω keeps all directed self-overlaps. -/
def occurs {B : ℕ} (f : ℕ → Bit) (x : ℕ) (w : Fin B → Bit) : Prop :=
  ∀ i, f (x-1+i.val)=w i
def compatible {B : ℕ} (d : ℕ) (w v : Fin B → Bit) : Prop :=
  ∀ j : Fin B, ∀ h : d+j.val<B, w ⟨d+j.val,h⟩=v j
def overlapWeight {B : ℕ} (W : Finset (Fin B → Bit)) : ℝ :=
  (∑ w ∈ W, ∑ v ∈ W, ∑ d ∈ Finset.Icc 1 (B-1),
    if compatible d w v then 1/(2 : ℝ)^d else 0)/(W.card : ℝ)
@[reducible] def DictionaryIndex (N L : ℕ) (W : Finset (Fin (L+1) → Bit)) :=
  {x : ℕ // x ∈ block N} × {w : Fin (L+1) → Bit // w ∈ W}
def wordRate (L : ℕ) : ℝ≥0 := ⟨1/(2 : ℝ)^(L+1), by positivity⟩
def wordField (N L : ℕ) (W : Finset (Fin (L+1) → Bit))
    (omega : Sample) (i : DictionaryIndex N L W) : ℕ :=
  if occurs (value omega) i.1.val i.2.val then 1 else 0
def dictionaryDistance (N L : ℕ) (W : Finset (Fin (L+1) → Bit)) : ℝ :=
  massTV (law sourceMeasure (wordField N L W)) (poissonFieldMass (fun _ => wordRate L))
def wordCounts {N L : ℕ} (W : Finset (Fin (L+1) → Bit))
    (k : DictionaryIndex N L W → ℕ) : {w // w ∈ W} → ℕ := fun w => ∑ x, k (x,w)
def wordCountDistance (N L : ℕ) (W : Finset (Fin (L+1) → Bit)) : ℝ :=
  massTV (law sourceMeasure (fun omega => wordCounts W (wordField N L W omega)))
    (poissonFieldMass (fun _ : {w // w ∈ W} => N * wordRate L))
def iidSequence (C : ℕ) (omega : Fin C → Bit) (n : ℕ) : Bit :=
  if h : n<C then omega ⟨n,h⟩ else 0

/- The exact excess e denotes a run of length L+e, with both boundaries pinned. -/
def start (g : ℕ → Bit) (x L : ℕ) : Prop :=
  g (x-1)+g x=1 ∧ ∀ j : ℕ, j<L → g (x+j)=g x
def exact (g : ℕ → Bit) (x L e : ℕ) : Prop :=
  g (x-1)+g x=1 ∧
    (∀ j : ℕ, 0<j → j+1<L+e+1 → g x=g (x+j)) ∧
    g x+g (x+(L+e+1-1))=1
def signedExact (g : ℕ → Bit) (x L e : ℕ) (s : Bit) : Prop :=
  exact g x L e ∧ g x=s
@[reducible] def ExactIndex (N E : ℕ) := {x : ℕ // x ∈ block N} × Fin (E+1)
@[reducible] def SignedIndex (N E : ℕ) := {x : ℕ // x ∈ block N} × (Fin (E+1) × Bit)
def exactField (N L E : ℕ) (omega : Sample) (i : ExactIndex N E) : ℕ :=
  if i.1.val ∈ block N ∧ exact (value omega) i.1.val L i.2.val then 1 else 0
def signedField (N L E : ℕ) (omega : Sample) (i : SignedIndex N E) : ℕ :=
  if i.1.val ∈ block N ∧ signedExact (value omega) i.1.val L i.2.1.val i.2.2 then 1 else 0
def exactRate (L e : ℕ) : ℝ≥0 := ⟨1/(2 : ℝ)^(L+e+1), by positivity⟩
def signedRate (L e : ℕ) : ℝ≥0 := ⟨1/(2 : ℝ)^(L+e+2), by positivity⟩
def exactDistance (N L E : ℕ) : ℝ :=
  massTV (law sourceMeasure (exactField N L E))
    (poissonFieldMass (fun i : ExactIndex N E => exactRate L i.2.val))
def signedDistance (N L E : ℕ) : ℝ :=
  massTV (law sourceMeasure (signedField N L E))
    (poissonFieldMass (fun i : SignedIndex N E => signedRate L i.2.1.val))
def exactError (N L : ℕ) (epsilon eta : ℝ) : ℝ :=
  (fullRate N L : ℝ)*(1+(fullRate N L : ℝ))*
    (Real.exp (-Analysis.saddleCutoff 1 (Real.log N)+eta*Analysis.saddleNu 1 (Real.log N))+
      (N : ℝ)^(-(1/(3 : ℝ))+epsilon))

/- A genuine Poisson count independent of an infinite iid sequence of positive geometric marks. -/
def halfSuccess : unitInterval := ⟨1/2, by norm_num, by norm_num⟩
def geometricMeasurePositive : Measure ℕ := (geometricMeasure halfSuccess).map Nat.succ
instance instProbabilityGeometric : IsProbabilityMeasure geometricMeasurePositive :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
def markSequenceMeasure (mu : Measure ℕ) [IsProbabilityMeasure mu] : Measure (ℕ → ℕ) :=
  Measure.infinitePi (fun _ : ℕ => mu)
def compoundSample (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu] :
    Measure (ℕ × (ℕ → ℕ)) := (poissonMeasure rate).prod (markSequenceMeasure mu)
def stoppedSum (sample : ℕ × (ℕ → ℕ)) : ℕ := ∑ j ∈ Finset.range sample.1, sample.2 j
def compoundMeasure (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu] : Measure ℕ :=
  (compoundSample rate mu).map stoppedSum
instance instMeasurableConfiguration : MeasurableSpace (ℕ →₀ ℕ) := ⊤
def configuration (sample : ℕ × (ℕ → ℕ)) : ℕ →₀ ℕ :=
  ∑ j ∈ Finset.range sample.1,
    if 0<sample.2 j then Finsupp.single (sample.2 j-1) 1 else 0
def configurationMeasure (rate : ℝ≥0) : Measure (ℕ →₀ ℕ) :=
  (compoundSample rate geometricMeasurePositive).map configuration
def configurationWeight (k : ℕ →₀ ℕ) : ℕ := k.sum (fun e n => (e+1)*n)
def coordinateRates (rate : ℝ≥0) (E : ℕ) (e : Fin (E+1)) : ℝ≥0 := rate/2^(e.val+1)
def tailCount (k : ℕ →₀ ℕ) (m : ℕ) : ℕ :=
  ∑ e ∈ k.support, if m≤e then k e else 0

def thresholdSource (N L : ℕ) (omega : Sample) (m : ℕ) : ℕ :=
  ∑ x ∈ block N, if start (value omega) x (L+m) then 1 else 0
def thresholdDistance (N L : ℕ) (A : Set Sample) : ℝ :=
  massTV (law (cond sourceMeasure A) (thresholdSource N L))
    (law (configurationMeasure (fullRate N L)) tailCount)

/- Every constant window is counted; no left-maximality restriction is hidden here. -/
def constantWindowCount (N L : ℕ) (omega : Sample) : ℕ :=
  ∑ x ∈ block N, if (∀ j : ℕ, j<L → value omega (x+j)=value omega x) then 1 else 0
def constantWindowDistance (N L : ℕ) : ℝ :=
  massTV (law sourceMeasure (constantWindowCount N L))
    (fun n => (compoundMeasure (fullRate N L) geometricMeasurePositive).real {n})
end Patterns

namespace Patterns
local instance instMeasurableBitTheorems : MeasurableSpace Bit := ⊤

theorem word_overlap_probability {C x B d : ℕ} (hx : 1≤x) (hd : d≤B)
    (hcut : x-1+(B+d)≤C) (w v : Fin B → Bit) :
    ((PMF.uniformOfFintype (Fin C → Bit)).toMeasure).real
      {omega | occurs (iidSequence C omega) x w ∧ occurs (iidSequence C omega) (x+d) v} =
      if compatible d w v then 1/(2 : ℝ)^(B+d) else 0  := by sorry

theorem dictionary_critical (hAGG : Process.ProcessAGGStatement)
    (hPNT : Analysis.PrimeNumberTheoremRemainder) (C delta : ℝ) (hdelta : 0<delta)
    (L : ℕ → ℕ) (W : ∀ N, Finset (Fin (L N+1) → Bit))
    (hcritical : ∀ᶠ N in atTop,
      (W N).Nonempty ∧ ((W N).card : ℝ)≤(N : ℝ)^(1/2-delta) ∧
      |(L N+1 : ℝ)-Real.log ((N : ℝ)*(W N).card)/Real.log 2|≤C)
    (hoverlap : Tendsto (fun N => overlapWeight (W N)) atTop (𝓝 0)) :
    Tendsto (fun N => dictionaryDistance N (L N) (W N)) atTop (𝓝 0) ∧
    Tendsto (fun N => wordCountDistance N (L N) (W N)) atTop (𝓝 0)  := by sorry

theorem exact_marked_quantitative (hAGG : Process.ProcessAGGStatement)
    (hPNT : Analysis.PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L E : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+E+2 : ℝ)≤betaMax*Real.log N →
      exactDistance N L E≤32*exactError N L epsilon eta ∧
      signedDistance N L E≤32*exactError N L epsilon eta  := by sorry

theorem exact_sign_partition (g : ℕ → Bit) (x L E e : ℕ) (hL : 1≤L) :
    (∑ s : Bit, if signedExact g x L e s then (1 : ℕ) else 0)=
      (if exact g x L e then 1 else 0) ∧
    (∑ f : Fin (E+1), ∑ s : Bit, if signedExact g x L f.val s then (1 : ℕ) else 0)≤
      (if start g x L then 1 else 0)  := by sorry

theorem aggregate_hard_budget (hStein : Analysis.DirectionalSteinFactorsStatement)
    (hPNT : Analysis.PrimeNumberTheoremRemainder) (betaMin betaMax c c' epsilon : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc' : 0<c') (hcc : c'<c)
    (hepsilon : 0<epsilon) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      ∀ A : Set Sample, MeasurableSet[fullFY (Analysis.hardCutoff N)] A →
      0<sourceMeasure.real A → 1≤(fullRate N L : ℝ) →
      information A+Real.log (fullRate N L : ℝ)≤
        Analysis.saddleCutoff 1 (Real.log N)-c*Analysis.saddleNu 1 (Real.log N) →
      thresholdDistance N L A≤2*Real.exp (-c'*Analysis.saddleNu 1 (Real.log N))+
        (N : ℝ)^(-(1/3 : ℝ)+epsilon)  := by sorry

theorem geometric_joint_configuration (rate : ℝ≥0) (E : ℕ) :
    HasLaw (fun k : ℕ →₀ ℕ => fun e : Fin (E+1) => k e.val)
      (fieldMeasure (coordinateRates rate E)) (configurationMeasure rate)  := by sorry

theorem geometric_compound_weight (rate : ℝ≥0) :
    HasLaw configurationWeight (compoundMeasure rate geometricMeasurePositive) (configurationMeasure rate)  := by sorry

theorem geometric_compound_pgf (rate : ℝ≥0) {z : ℝ} (hz : 0≤z) (hzOne : z≤1) :
    (∫ n, z^n ∂compoundMeasure rate geometricMeasurePositive)=
      Real.exp ((rate : ℝ)*(z/(2-z)-1))  := by sorry

theorem constant_windows_compound (hAGG : Process.ProcessAGGStatement)
    (hPNT : Analysis.PrimeNumberTheoremRemainder) (C : ℝ) (hC : 0≤C)
    (L : ℕ → ℕ)
    (hwindow : ∀ᶠ N in atTop, |(L N : ℝ)-Real.log N/Real.log 2|≤C) :
    Tendsto (fun N => constantWindowDistance N (L N)) atTop (𝓝 0)  := by sorry

end Patterns
end PaperCV3Audit
end
