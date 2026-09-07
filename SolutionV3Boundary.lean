import PaperCV282.MicroscopicBoundaryDominance
import PaperCV282.MesoscopicStability
import PaperCV282.PrefixAlmostSureEnvelopes
import PaperCV282.PrefixCriticalVoid

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

private theorem ls_input_eq : UniformPrimeDivisorStatement =
    PaperC.V282.LaishramUniformInput.UniformPrimeDivisorStatement := rfl
private theorem shorey_input_eq : ShoreySquareProductStatement =
    PaperC.V282.PostQuadraticLiterature.ShoreySquareProductStatement := rfl
private theorem divisor_input_eq : DivisorLogBoundStatement =
    PaperC.PellInput.NicolasRobinDivisorLogBoundStatement := rfl
private theorem longestRun_eq (M : ℕ) (omega : InfiniteSample) : longestRun M omega =
    PaperC.CorollaryPrefixLaw.infinitePrefixLongestConstantStretch M omega := rfl
private theorem prefixCount_eq (M L : ℕ) : prefixCount M L =
    PaperC.CorollaryPrefixLaw.infinitePrefixStartCount M L := by
  funext omega
  symm
  exact PaperC.V282.PrefixLongestGeometry.infinitePrefixStartCount_eq_border_add M L omega
private theorem prefixLaw_eq (M L : ℕ) : prefixLaw M L =
    PaperC.CorollaryPrefixLaw.infinitePrefixStartLaw M L := by
  unfold prefixLaw observableLaw
  rw [prefixCount_eq]
  rfl
private theorem hardRate_eq (M L : ℕ) (epsilon eta : ℝ) : hardRate M L epsilon eta =
    PaperC.V282.HardPoissonRates.hardRate M L epsilon eta := by
  unfold hardRate PaperC.V282.HardPoissonRates.hardRate
  rw [Analysis.saddleCutoff_eq,Analysis.saddleNu_eq]
  rfl

theorem v3_boundary_exact (L : ℕ) :
    infiniteRademacherMeasure.real (borderEvent L)=((2 : ℝ)⁻¹)^Nat.primeCounting L := by
  exact PaperC.V282.MicroscopicBorderEvents.equation_seven_one L

theorem v3_boundary_microscopic (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) :
    ∃ Lzero : ℕ, ∀ L≥Lzero,
      0≤microscopicProbability L/((2 : ℝ)⁻¹)^Nat.primeCounting L-1 ∧
      microscopicProbability L/((2 : ℝ)⁻¹)^Nat.primeCounting L-1 ≤
        (2 : ℝ)^(-(1/(256 : ℝ))*Nat.primeCounting L) ∧
      1-(2 : ℝ)^(-(1/(256 : ℝ))*Nat.primeCounting L) ≤
        (cond infiniteRademacherMeasure (microscopicEvent L)).real (uniqueBorderEvent L) ∧
      measureTV (cond infiniteRademacherMeasure (microscopicEvent L))
        (cond infiniteRademacherMeasure (borderEvent L)) ≤
          (2 : ℝ)^(-(1/(256 : ℝ))*Nat.primeCounting L) := by
  have hstar : (1/(256 : ℝ)) < (PaperC.V282.HarmonicIncidenceSurplus.surplus 11 : ℝ) := by
    rw [PaperC.V282.HarmonicIncidenceSurplus.surplus_eleven_eq]
    norm_num
  obtain ⟨N,hN⟩ := PaperC.V282.MicroscopicBoundaryDominance.theorem_seven_one hLS hShorey hPNT
    (by norm_num : (0 : ℝ)<1/256) hstar
  exact ⟨N,fun L hL => (hN L hL).2⟩

theorem v3_boundary_mesoscopic (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : DivisorLogBoundStatement) (T : ℕ → ℕ)
    (hsmall : Tendsto (fun L : ℕ => (T L : ℝ)/(2 : ℝ)^((L : ℝ)-Nat.primeCounting L)) atTop (𝓝 0)) :
    Tendsto (fun L : ℕ => measureTV
      ((cond infiniteRademacherMeasure (enlargedEvent L (T L))).map (microscopicRecord L (T L)))
      ((cond infiniteRademacherMeasure (microscopicEvent L)).map (microscopicRecord L 0)))
      atTop (𝓝 0) := by
  exact PaperC.V282.MesoscopicStability.cutoff_conditioned_stability_of_littleO hShorey hPNT hNR T hsmall

theorem v3_boundary_prefix_quantitative (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : DivisorLogBoundStatement)
    (betaMin betaMax epsilon eta : ℝ) (hb : 0<betaMin) (hbb : betaMin<betaMax)
    (he : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      massTV (prefixLaw M L) (poissonMass (fullRate M L)) ≤
        43*min 1 (hardRate M L epsilon eta)+
        4*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M)))+
        ((2 : ℝ)⁻¹)^Nat.primeCounting L+(L : ℝ)/(2 : ℝ)^L := by
  obtain ⟨N,hN⟩ := PaperC.V282.PrefixContainedBounds.theorem_seven_four_contained_prefix
    hStein hLS hShorey hPNT hNR betaMin betaMax epsilon eta hb hbb he heta
  refine ⟨N,fun M hM L hlo hhi => ?_⟩
  rw [prefixLaw_eq,hardRate_eq]
  exact hN M hM L hlo hhi

theorem v3_boundary_prefix_critical (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : DivisorLogBoundStatement)
    (C delta : ℝ) (hC : 0≤C) (hd : 0<delta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, InRunLengthWindow C M L →
      massTV (prefixLaw M L) (poissonMass (fullRate M L))≤delta ∧
      |infiniteRademacherMeasure.real {omega | longestRun M omega<L}-
        Real.exp (-((M : ℝ)/(2 : ℝ)^L))|≤delta := by
  obtain ⟨Nt,ht⟩ := PaperC.V282.PrefixScalarConvergence.critical_prefix_tv_le_eventually
    hStein hLS hShorey hPNT hNR C delta hC hd
  obtain ⟨Nv,hv⟩ := PaperC.V282.PrefixCriticalVoid.critical_prefix_void_le_eventually
    hStein hLS hShorey hPNT hNR C delta hC hd
  refine ⟨max Nt Nv,fun M hM L hw => ?_⟩
  constructor
  · rw [prefixLaw_eq]
    exact ht M (by omega) L hw
  · exact hv M (by omega) L hw

theorem v3_boundary_asymmetric_envelopes (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : DivisorLogBoundStatement)
    (epsilon : ℝ) (he : 0<epsilon) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ M : ℕ in atTop,
      -Real.log (Real.log (Real.log M))/Real.log 2-4 ≤
        (longestRun M omega : ℝ)-Real.log M/Real.log 2 ∧
      (longestRun M omega : ℝ)-Real.log M/Real.log 2 ≤
        Real.log (Real.log M)/Real.log 2+
        (1+epsilon)*Real.log (Real.log (Real.log M))/Real.log 2+upperAdditiveConstant epsilon := by
  exact PaperC.V282.PrefixAlmostSureEnvelopes.theorem_seven_five
    hStein hLS hShorey hPNT hNR epsilon he

theorem v3_boundary_longest_loglog (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : DivisorLogBoundStatement) :
    ∀ᵐ omega ∂infiniteRademacherMeasure,
      (fun M : ℕ => (longestRun M omega : ℝ)-Real.log M/Real.log 2)
        =O[atTop] (fun M : ℕ => Real.log (Real.log M)) := by
  exact PaperC.V282.PrefixAlmostSureEnvelopes.theorem_seven_five_loglog hStein hLS hShorey hPNT hNR

end
end PaperCV3Audit
