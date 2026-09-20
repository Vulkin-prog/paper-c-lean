import SolutionV3Boundary
import PaperCPrel8.MicroscopicNormalization
import PaperCPrel8.EmpiricalPaperTheorem
import PaperCPrel8.EmpiricalSupportTheorem
import PaperCPrel8.DyadicMicroscopicTheorem

namespace PaperCV3Audit
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators NNReal ENNReal
local instance (P : Prop) : Decidable P := Classical.propDecidable P
local instance : MeasurableSpace F₂ := ⊤

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
