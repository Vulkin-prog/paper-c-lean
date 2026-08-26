import Solution

noncomputable section

/-!
# Paper C external-audit solution: Theorem 16.2 and Corollary 16.4

This file independently reproduces the additional declaration surface of
`ChallengeTheoremSixteenTwo.lean` and closes its four audited declarations
with the canonical endpoints in the frozen Paper C development.
-/

open scoped BigOperators ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory Set

namespace PaperCAudit

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

/-! ## Explicit translation of the one record-valued premise -/

private theorem auditAGG_to_paperC
    (h : PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement) :
    PaperC.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement := by
  classical
  letI (p : Prop) : Decidable p := Classical.propDecidable p
  unfold PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement at h
  unfold PaperC.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement
  intro Ω ι instΩ instι instDec μ X G hdep
  let μAudit : PaperCAudit.FinitePMF Ω :=
    { prob := μ.prob
      nonneg := μ.nonneg
      sum_prob := μ.sum_prob }
  have hdepAudit :
      PaperCAudit.ArratiaGoldsteinGordonInput.HasExactDependencyGraph μAudit X G := by
    simpa [
      PaperCAudit.ArratiaGoldsteinGordonInput.HasExactDependencyGraph,
      PaperC.ArratiaGoldsteinGordonInput.HasExactDependencyGraph,
      PaperCAudit.ArratiaGoldsteinGordonInput.HasOutsidePattern,
      PaperC.ArratiaGoldsteinGordonInput.HasOutsidePattern,
      PaperCAudit.ArratiaGoldsteinGordonInput.OutsideIndex,
      PaperC.ArratiaGoldsteinGordonInput.OutsideIndex,
      PaperCAudit.ArratiaGoldsteinGordonInput.closedNeighborhood,
      PaperC.ArratiaGoldsteinGordonInput.closedNeighborhood,
      PaperCAudit.ArratiaGoldsteinGordonInput.eventProbability,
      PaperC.ArratiaGoldsteinGordonInput.eventProbability,
      μAudit] using hdep
  have hRate :
      PaperCAudit.ArratiaGoldsteinGordonInput.poissonRate μAudit X =
        PaperC.ArratiaGoldsteinGordonInput.poissonRate μ X := by
    apply Subtype.ext
    rfl
  have bound := h Ω ι μAudit X G hdepAudit
  simp only [
    PaperCAudit.ArratiaGoldsteinGordonInput.totalVariationToPoisson,
    PaperC.ArratiaGoldsteinGordonInput.totalVariationToPoisson,
    PaperCAudit.ArratiaGoldsteinGordonInput.indicatorSumLaw,
    PaperC.ArratiaGoldsteinGordonInput.indicatorSumLaw,
    PaperCAudit.ArratiaGoldsteinGordonInput.matchingPoissonLaw,
    PaperC.ArratiaGoldsteinGordonInput.matchingPoissonLaw,
    PaperCAudit.ArratiaGoldsteinGordonInput.bOne,
    PaperC.ArratiaGoldsteinGordonInput.bOne,
    PaperCAudit.ArratiaGoldsteinGordonInput.bTwo,
    PaperC.ArratiaGoldsteinGordonInput.bTwo,
    PaperCAudit.ArratiaGoldsteinGordonInput.marginal,
    PaperC.ArratiaGoldsteinGordonInput.marginal,
    PaperCAudit.ArratiaGoldsteinGordonInput.jointMarginal,
    PaperC.ArratiaGoldsteinGordonInput.jointMarginal,
    PaperCAudit.ArratiaGoldsteinGordonInput.eventProbability,
    PaperC.ArratiaGoldsteinGordonInput.eventProbability,
    PaperCAudit.ArratiaGoldsteinGordonInput.indicatorSum,
    PaperC.ArratiaGoldsteinGordonInput.indicatorSum,
    PaperCAudit.ArratiaGoldsteinGordonInput.closedNeighborhood,
    PaperC.ArratiaGoldsteinGordonInput.closedNeighborhood,
    μAudit, hRate] at bound ⊢
  exact bound

theorem paper_c_theorem_sixteen_two_finite_cylinder
    {C : ℝ} (hC : 0 < C)
    (hPNT : PaperCAudit.PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS : PaperCAudit.LaishramShoreyInput.LaishramShoreyStatement)
    (hDivisor : PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (hBS : PaperCAudit.BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG : PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES : PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    PaperCAudit.TheoremSixteenTwo.TheoremSixteenTwoStatement C := by
  exact PaperC.TheoremSixteenTwo.theorem_sixteen_two_canonical
    hC hPNT hLS hDivisor hBS (auditAGG_to_paperC hAGG) hES

theorem paper_c_theorem_sixteen_two_finite_cylinder_recentered
    {C : ℝ} (hC : 0 < C)
    (hPNT : PaperCAudit.PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS : PaperCAudit.LaishramShoreyInput.LaishramShoreyStatement)
    (hDivisor : PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (hBS : PaperCAudit.BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG : PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES : PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    PaperCAudit.TheoremSixteenTwoRecentered.RecenteredTheoremSixteenTwoStatement C := by
  exact PaperC.TheoremSixteenTwoRecentered.theorem_sixteen_two_recentered_canonical
    hC hPNT hLS hDivisor hBS (auditAGG_to_paperC hAGG) hES

theorem paper_c_theorem_sixteen_two_infinite_model
    {C : ℝ} (hC : 0 < C)
    (hPNT : PaperCAudit.PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS : PaperCAudit.LaishramShoreyInput.LaishramShoreyStatement)
    (hDivisor : PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (hBS : PaperCAudit.BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG : PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES : PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    PaperCAudit.TheoremSixteenTwo.TheoremSixteenTwoInfiniteModelStatement C := by
  exact PaperC.TheoremSixteenTwo.theorem_sixteen_two_infinite_model
    hC hPNT hLS hDivisor hBS (auditAGG_to_paperC hAGG) hES

theorem paper_c_corollary_sixteen_four_prefix_law
    {C : ℝ} (hC : 0 < C)
    (hPNT : PaperCAudit.PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS : PaperCAudit.LaishramShoreyInput.LaishramShoreyStatement)
    (hDivisor : PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement)
    (hBS : PaperCAudit.BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG : PaperCAudit.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES : PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    PaperCAudit.CorollaryPrefixLawCanonical.CorollaryPrefixLawStatement C := by
  exact PaperC.CorollaryPrefixLawCanonical.corollary_prefix_law_canonical
    hC hPNT hLS hDivisor hBS (auditAGG_to_paperC hAGG) hES

#print axioms paper_c_theorem_sixteen_two_finite_cylinder
#print axioms paper_c_theorem_sixteen_two_finite_cylinder_recentered
#print axioms paper_c_theorem_sixteen_two_infinite_model
#print axioms paper_c_corollary_sixteen_four_prefix_law

end
