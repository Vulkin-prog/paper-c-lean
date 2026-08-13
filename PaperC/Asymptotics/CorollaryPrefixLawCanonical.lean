import PaperC.Asymptotics.CorollaryPrefixLaw
import PaperC.Asymptotics.PrefixBoundaryProbability
import PaperC.Asymptotics.PrefixOverflowCoupling
import PaperC.Asymptotics.TheoremSixteenTwoRecentered

/-!
# Canonical finite-prefix Poisson law

This module assembles `cor:prefix-law`.  The prefix count is coupled to the
global interior count on their common finite cylinder.  Its two exceptional
pieces are the zero prime assignment at the left boundary and the masked
first moment of starts whose stretch crosses the right boundary.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace PaperC
namespace CorollaryPrefixLawCanonical

open ArratiaGoldsteinGordonInput
open CorollaryPrefixLaw
open InfiniteRademacher
open PellInput
open ProbabilityTheory
open SectionThirteenFiniteBound
open TheoremSixteenTwo
open TheoremSixteenTwoRecentered

noncomputable section

/-- The left-boundary probability on the common finite cylinder is exactly
the corresponding probability under the source product law. -/
theorem finitePrefixBoundaryProbability_eq_infinite
    (M L : ℕ) :
    PrefixOverflowCoupling.finitePrefixBoundaryProbability M L =
      PrefixBoundaryProbability.infinitePrefixBoundaryProbability L := by
  change CorollaryPrefixLaw.prefixBoundaryProbability M L =
    (infiniteRademacherMeasure
      (PrefixBoundaryProbability.infinitePrefixBoundaryEvent L)).toReal
  rw [CorollaryPrefixLaw.prefixBoundaryProbability_eq_measure]
  rfl

/-- Uniform decay of the finite-cylinder left-boundary term. -/
theorem finitePrefixBoundaryProbability_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      PrefixOverflowCoupling.finitePrefixBoundaryProbability
      (fun _ _ ↦ 1) := by
  intro ε hε
  obtain ⟨M₀, hM₀⟩ :=
    PrefixBoundaryProbability.infinitePrefixBoundaryProbability_uniformLittleOOne
      hC ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L hrun
  rw [finitePrefixBoundaryProbability_eq_infinite]
  exact hM₀ M hM L hrun

/-- Eventually, every length in the manuscript window is at least two and
is shorter than its prefix. -/
theorem prefixRange_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C M L →
        2 ≤ L ∧ L ≤ M := by
  obtain ⟨Mwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Madm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Mheight, hheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := CriticalRunWindow.upperConstant)
      CriticalRunWindow.lowerConstant_pos 3
  refine ⟨max Mwindow (max Madm Mheight), ?_⟩
  intro M hM L hrun
  have hMwindow : Mwindow ≤ M := (le_max_left _ _).trans hM
  have htail : max Madm Mheight ≤ M := (le_max_right _ _).trans hM
  have hMadm : Madm ≤ M := (le_max_left _ _).trans htail
  have hMheight : Mheight ≤ M := (le_max_right _ _).trans htail
  have hw := hwindow M hMwindow L hrun
  have hAdm :
      CriticalWeightedDefect.Admissible
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant M (L + 1) :=
    hadm M hMadm (L + 1) hw.1
  have hthree : 3 ≤ L + 1 :=
    hheight M hMheight (L + 1) hAdm
  have htwo : 2 * (L + 1) ≤ M :=
    CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
      hAdm.1 hAdm.2.2.2.1
  exact ⟨by omega, by omega⟩

/-! ## Assembly of the prefix Poisson law -/

/-- Coupling to the global count followed by the recentered global theorem. -/
theorem prefixStartLaw_poisson_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C)
    (h16 : RecenteredTheoremSixteenTwoStatement C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (prefixStartLaw M L)
          (poissonPMFReal (criticalScaleRate M L)))
      (fun _ _ ↦ 1) := by
  have hcoupling :=
    PrefixOverflowCoupling.natTotalVariation_prefixStartLaw_global_uniformLittleOOne
      hC
  intro ε hε
  obtain ⟨Mcouple, hMcouple⟩ := hcoupling (ε / 2) (by positivity)
  obtain ⟨Mglobal, hMglobal⟩ := h16.1 (ε / 2) (by positivity)
  refine ⟨max Mcouple Mglobal, ?_⟩
  intro M hM L hrun
  have hcouplePoint :
      natTotalVariation (prefixStartLaw M L) (globalStartLaw M L) ≤
        ε / 2 := by
    have h := hMcouple M ((le_max_left _ _).trans hM) L hrun
    rw [abs_of_nonneg (natTotalVariation_nonneg _ _), abs_one,
      mul_one] at h
    exact h
  have hglobalPoint :
      natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (criticalScaleRate M L)) ≤
        ε / 2 := by
    have h := hMglobal M ((le_max_right _ _).trans hM) L hrun
    rw [abs_of_nonneg (natTotalVariation_nonneg _ _), abs_one,
      mul_one] at h
    exact h
  have hprefixSummable : Summable (prefixStartLaw M L) := by
    unfold prefixStartLaw
    exact summable_finiteNatLaw (globalUniformPMF M L)
      (finitePrefixStartCount M L)
  have hpoissonSummable :
      Summable (poissonPMFReal (criticalScaleRate M L)) :=
    (poissonPMFRealSum (criticalScaleRate M L)).summable
  have htriangle :
      natTotalVariation
          (prefixStartLaw M L)
          (poissonPMFReal (criticalScaleRate M L)) ≤
        natTotalVariation (prefixStartLaw M L) (globalStartLaw M L) +
          natTotalVariation
            (globalStartLaw M L)
            (poissonPMFReal (criticalScaleRate M L)) :=
    natTotalVariation_triangle
      hprefixSummable
      (summable_globalStartLaw M L)
      hpoissonSummable
      (fun k ↦ by
        unfold prefixStartLaw
        exact finiteNatLaw_nonneg _ _ k)
      (globalStartLaw_nonneg M L)
      (fun _ ↦ poissonPMFReal_nonneg)
  rw [abs_of_nonneg (natTotalVariation_nonneg _ _), abs_one, mul_one]
  calc
    natTotalVariation
        (prefixStartLaw M L)
        (poissonPMFReal (criticalScaleRate M L)) ≤
      natTotalVariation (prefixStartLaw M L) (globalStartLaw M L) +
        natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (criticalScaleRate M L)) := by
      exact htriangle
    _ ≤ ε / 2 + ε / 2 := add_le_add hcouplePoint hglobalPoint
    _ = ε := by ring

/-- The prefix Poisson law stated directly for `W_{M,L}` on the infinite
Rademacher product space. -/
theorem infinitePrefixStartLaw_poisson_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C)
    (h16 : RecenteredTheoremSixteenTwoStatement C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (infinitePrefixStartLaw M L)
          (poissonPMFReal (criticalScaleRate M L)))
      (fun _ _ ↦ 1) := by
  simpa only [infinitePrefixStartCount_law_eq_prefixStartLaw] using
    prefixStartLaw_poisson_uniformLittleOOne hC h16

/-- Probability that `W_{M,L}` is zero in the source product model. -/
def infinitePrefixEmptyProbability (M L : ℕ) : ℝ :=
  infinitePrefixStartLaw M L 0

/-- The zero atom of the prefix Poisson law. -/
theorem infinitePrefixEmptyProbability_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C)
    (h16 : RecenteredTheoremSixteenTwoStatement C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        infinitePrefixEmptyProbability M L -
          Real.exp (-criticalScale M L))
      (fun _ _ ↦ 1) := by
  have htv := infinitePrefixStartLaw_poisson_uniformLittleOOne hC h16
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := htv (ε / 2) (by positivity)
  refine ⟨M₀, ?_⟩
  intro M hM L hrun
  have htvPoint :
      natTotalVariation
          (infinitePrefixStartLaw M L)
          (poissonPMFReal (criticalScaleRate M L)) ≤ ε / 2 := by
    have h := hM₀ M hM L hrun
    rw [abs_of_nonneg (natTotalVariation_nonneg _ _), abs_one,
      mul_one] at h
    exact h
  have hprefixSummable : Summable (infinitePrefixStartLaw M L) := by
    rw [infinitePrefixStartCount_law_eq_prefixStartLaw]
    unfold prefixStartLaw
    exact summable_finiteNatLaw (globalUniformPMF M L)
      (finitePrefixStartCount M L)
  have hprefixNonneg : ∀ k, 0 ≤ infinitePrefixStartLaw M L k := by
    intro k
    rw [infinitePrefixStartCount_law_eq_prefixStartLaw]
    unfold prefixStartLaw
    exact finiteNatLaw_nonneg _ _ k
  have hpoissonSummable :
      Summable (poissonPMFReal (criticalScaleRate M L)) :=
    (poissonPMFRealSum (criticalScaleRate M L)).summable
  have hpoissonNonneg :
      ∀ k, 0 ≤ poissonPMFReal (criticalScaleRate M L) k :=
    fun _ ↦ poissonPMFReal_nonneg
  have hatom :
      |infinitePrefixStartLaw M L 0 -
          poissonPMFReal (criticalScaleRate M L) 0| ≤
        2 * natTotalVariation
          (infinitePrefixStartLaw M L)
          (poissonPMFReal (criticalScaleRate M L)) :=
    abs_mass_zero_sub_le_two_mul_natTotalVariation
      hprefixSummable
      hpoissonSummable
      hprefixNonneg
      hpoissonNonneg
  have hzero :
      poissonPMFReal (criticalScaleRate M L) 0 =
        Real.exp (-criticalScale M L) := by
    simpa only [coe_criticalScaleRate] using
      poissonPMFReal_zero_eq_exp_neg (criticalScaleRate M L)
  simp only [abs_one, mul_one]
  change
    |infinitePrefixEmptyProbability M L -
      Real.exp (-criticalScale M L)| ≤ ε
  unfold infinitePrefixEmptyProbability
  rw [← hzero]
  calc
    |infinitePrefixStartLaw M L 0 -
        poissonPMFReal (criticalScaleRate M L) 0| ≤
      2 * natTotalVariation
        (infinitePrefixStartLaw M L)
        (poissonPMFReal (criticalScaleRate M L)) := hatom
    _ ≤ 2 * (ε / 2) :=
      mul_le_mul_of_nonneg_left htvPoint (by norm_num)
    _ = ε := by ring

/-- Literal source probability of `R_M < L`. -/
def infinitePrefixLongestStretchBelowProbability (M L : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    {ω | infinitePrefixLongestConstantStretch M ω < L}).toReal

/-- For a genuine prefix length, the longest-stretch event is the zero atom
of `W_{M,L}`. -/
theorem infinitePrefixLongestStretchBelowProbability_eq_empty
    {M L : ℕ} (hLM : L ≤ M) :
    infinitePrefixLongestStretchBelowProbability M L =
      infinitePrefixEmptyProbability M L := by
  rw [infinitePrefixLongestStretchBelowProbability,
    infinitePrefixEmptyProbability,
    infinitePrefixStartCount_law_eq_prefixStartLaw,
    ← prefixLongestStretchBelowProbability_eq_measure hLM]
  rfl

/-- Printed void formula `P(R_M < L) = exp(-M 2⁻ᴸ) + o_C(1)`. -/
theorem infinitePrefixLongestStretchBelowProbability_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C)
    (h16 : RecenteredTheoremSixteenTwoStatement C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        infinitePrefixLongestStretchBelowProbability M L -
          Real.exp (-criticalScale M L))
      (fun _ _ ↦ 1) := by
  have hempty := infinitePrefixEmptyProbability_uniformLittleOOne hC h16
  obtain ⟨Mrange, hrange⟩ := prefixRange_eventually hC
  intro ε hε
  obtain ⟨Mempty, hMempty⟩ := hempty ε hε
  refine ⟨max Mrange Mempty, ?_⟩
  intro M hM L hrun
  have hLM := (hrange M ((le_max_left _ _).trans hM) L hrun).2
  simp only [abs_one, mul_one]
  change
    |infinitePrefixLongestStretchBelowProbability M L -
      Real.exp (-criticalScale M L)| ≤ ε
  rw [infinitePrefixLongestStretchBelowProbability_eq_empty hLM]
  simpa using hMempty M ((le_max_right _ _).trans hM) L hrun

/-- Full statement of the finite-prefix corollary on the infinite product
law. -/
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

/-- Canonical `cor:prefix-law`, conditional on exactly the same six
registered external propositions as Theorem 16.2. -/
theorem corollary_prefix_law_canonical
    {C : ℝ} (hC : 0 < C)
    (hpnt : PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS : LaishramShoreyInput.LaishramShoreyStatement)
    (hDivisor : NicolasRobinDivisorLogBoundStatement)
    (hBS : BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG : ArratiaGoldsteinGordonStatement)
    (hES : EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    CorollaryPrefixLawStatement C := by
  have h16 := theorem_sixteen_two_recentered_canonical
    hC hpnt hLS hDivisor hBS hAGG hES
  exact
    ⟨infinitePrefixStartLaw_poisson_uniformLittleOOne hC.le h16,
      infinitePrefixLongestStretchBelowProbability_uniformLittleOOne
        hC.le h16⟩

end

end CorollaryPrefixLawCanonical
end PaperC
