import PaperC.Asymptotics.TheoremSixteenTwo

/-!
# Recentring the global Poisson law

Theorem 16.2 is first proved with the exact mean `Λ_M` as Poisson parameter.
The same theorem also proves `Λ_M - M 2⁻ᴸ = o_C(1)` (its relative form is
equivalent because the critical scale is uniformly bounded).  The standard
Poisson coupling

`d_TV(Pois(λ), Pois(μ)) ≤ |λ-μ|`

therefore replaces the exact mean by the printed parameter `M 2⁻ᴸ`.  This
module makes that final recentering, and the corresponding void formula,
explicit.
-/

namespace PaperC
namespace TheoremSixteenTwoRecentered

open scoped NNReal
open Filter
open ProbabilityTheory
open SectionThirteenCouplings
open SectionThirteenFiniteBound
open TheoremSixteenTwo

noncomputable section

/-- The printed critical scale packaged as a nonnegative Poisson rate. -/
noncomputable def criticalScaleRate (M L : ℕ) : ℝ≥0 :=
  ⟨criticalScale M L, criticalScale_nonneg M L⟩

@[simp]
theorem coe_criticalScaleRate (M L : ℕ) :
    ((criticalScaleRate M L : ℝ≥0) : ℝ) = criticalScale M L :=
  rfl

/-- Recentring from the exact mean to `M 2⁻ᴸ`, uniformly in the manuscript
critical window. -/
theorem globalStartLaw_recentered_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C)
    (h16 : TheoremSixteenTwoStatement C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (criticalScaleRate M L)))
      (fun _ _ ↦ 1) := by
  intro ε hε
  let B : ℝ := max 1 (CriticalRunWindow.balanceConstant C)
  have hBpos : 0 < B :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨Mtv, htv⟩ := h16.1 (ε / 2) (by positivity)
  obtain ⟨Mmean, hmean⟩ :=
    h16.2.1 (ε / (2 * B)) (by positivity)
  obtain ⟨Mscale, hscale⟩ :=
    criticalScale_le_balanceConstant hC
  refine ⟨max Mtv (max Mmean Mscale), ?_⟩
  intro M hM L hrun
  have hMtv : Mtv ≤ M :=
    (le_max_left Mtv (max Mmean Mscale)).trans hM
  have htail : max Mmean Mscale ≤ M :=
    (le_max_right Mtv (max Mmean Mscale)).trans hM
  have hMmean : Mmean ≤ M :=
    (le_max_left Mmean Mscale).trans htail
  have hMscale : Mscale ≤ M :=
    (le_max_right Mmean Mscale).trans htail
  have htvPoint :
      natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (globalStartRate M L)) ≤ ε / 2 := by
    have h := htv M hMtv L hrun
    rw [abs_of_nonneg (natTotalVariation_nonneg _ _), abs_one,
      mul_one] at h
    exact h
  have hscaleBound : criticalScale M L ≤ B :=
    (hscale M hMscale L hrun).trans (le_max_right _ _)
  have hmeanPoint :
      |globalStartMean M L - criticalScale M L| ≤ ε / 2 := by
    have h := hmean M hMmean L hrun
    have hscaleAbs : |criticalScale M L| = criticalScale M L :=
      abs_of_nonneg (criticalScale_nonneg M L)
    rw [hscaleAbs] at h
    calc
      |globalStartMean M L - criticalScale M L| ≤
          (ε / (2 * B)) * criticalScale M L := h
      _ ≤ (ε / (2 * B)) * B := by
        exact mul_le_mul_of_nonneg_left hscaleBound (by positivity)
      _ = ε / 2 := by field_simp
  have hpoisson :
      natTotalVariation
          (poissonPMFReal (globalStartRate M L))
          (poissonPMFReal (criticalScaleRate M L)) ≤ ε / 2 :=
    (natTotalVariation_poisson_le_abs_rate_sub
      (globalStartRate M L) (criticalScaleRate M L)).trans
      hmeanPoint
  have htriangle :=
    natTotalVariation_triangle
      (summable_globalStartLaw M L)
      ((poissonPMFRealSum (globalStartRate M L)).summable)
      ((poissonPMFRealSum (criticalScaleRate M L)).summable)
      (globalStartLaw_nonneg M L)
      (fun _ ↦ poissonPMFReal_nonneg)
      (fun _ ↦ poissonPMFReal_nonneg)
  rw [abs_of_nonneg (natTotalVariation_nonneg _ _), abs_one, mul_one]
  calc
    natTotalVariation
        (globalStartLaw M L)
        (poissonPMFReal (criticalScaleRate M L)) ≤
      natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (globalStartRate M L)) +
        natTotalVariation
          (poissonPMFReal (globalStartRate M L))
          (poissonPMFReal (criticalScaleRate M L)) := htriangle
    _ ≤ ε / 2 + ε / 2 := add_le_add htvPoint hpoisson
    _ = ε := by ring

/-- The recentered zero-count formula
`P(Z_M=0) = exp(-M 2⁻ᴸ) + o_C(1)`. -/
theorem globalEmptyProbability_recentered_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C)
    (h16 : TheoremSixteenTwoStatement C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        globalEmptyProbability M L -
          Real.exp (-criticalScale M L))
      (fun _ _ ↦ 1) := by
  have htv :=
    globalStartLaw_recentered_uniformLittleOOne hC h16
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := htv (ε / 2) (by positivity)
  refine ⟨M₀, ?_⟩
  intro M hM L hrun
  have htvPoint :
      natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (criticalScaleRate M L)) ≤ ε / 2 := by
    have h := hM₀ M hM L hrun
    rw [abs_of_nonneg (natTotalVariation_nonneg _ _), abs_one,
      mul_one] at h
    exact h
  have hatom :=
    abs_mass_zero_sub_le_two_mul_natTotalVariation
      (summable_globalStartLaw M L)
      ((poissonPMFRealSum (criticalScaleRate M L)).summable)
      (globalStartLaw_nonneg M L)
      (fun _ ↦ poissonPMFReal_nonneg)
  have hzero :
      poissonPMFReal (criticalScaleRate M L) 0 =
        Real.exp (-criticalScale M L) := by
    simpa only [coe_criticalScaleRate] using
      poissonPMFReal_zero_eq_exp_neg (criticalScaleRate M L)
  rw [abs_one, mul_one]
  change
    |globalStartLaw M L 0 - Real.exp (-criticalScale M L)| ≤ ε
  rw [← hzero]
  calc
    |globalStartLaw M L 0 -
        poissonPMFReal (criticalScaleRate M L) 0| ≤
      2 * natTotalVariation
        (globalStartLaw M L)
        (poissonPMFReal (criticalScaleRate M L)) := hatom
    _ ≤ 2 * (ε / 2) :=
      mul_le_mul_of_nonneg_left htvPoint (by norm_num)
    _ = ε := by ring

/-- Recentered form of Theorem 16.2 used by the finite-prefix corollary. -/
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
        globalEmptyProbability M L -
          Real.exp (-criticalScale M L))
      (fun _ _ ↦ 1)

/-- Canonical recentered Theorem 16.2, conditional on exactly the seven
registered external propositions. -/
theorem theorem_sixteen_two_recentered_canonical
    {C : ℝ} (hC : 0 < C)
    (hpnt :
      PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS :
      LaishramShoreyInput.LaishramShoreyStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement)
    (hBS :
      BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    RecenteredTheoremSixteenTwoStatement C := by
  have h16 :=
    theorem_sixteen_two_canonical
      hC hpnt hLS hConductor hDivisor hBS hAGG hES
  exact
    ⟨globalStartLaw_recentered_uniformLittleOOne hC.le h16,
      globalEmptyProbability_recentered_uniformLittleOOne hC.le h16⟩

end

end TheoremSixteenTwoRecentered
end PaperC
