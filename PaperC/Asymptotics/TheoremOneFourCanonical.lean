import PaperC.Asymptotics.DyadicKappaQuantitative
import PaperC.Asymptotics.NonterminalSectorSaving
import PaperC.Probability.SectionTwelveMoments

set_option maxHeartbeats 3600000

/-!
# Canonical asymptotic closure of Theorem 1.4

This module connects the finite moment identities of Section 12 directly to
the quantitative dyadic mother mass.  Its only non-formal inputs are the
three source-shaped arithmetic references already used by the canonical
mother-mass theorem.
-/

namespace PaperC
namespace SectionTwelveMoments

noncomputable section

/--
Canonical source-facing form of Theorem 1.4.  It simultaneously gives the
first-moment rate, the second factorial moment, the homogeneous two-start
mass, and the variance conclusion in the literal critical window.
-/
theorem theorem_one_four_canonical
    {C : ℝ} (hC : 0 ≤ C)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    UniformNegativeHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        dyadicFirstMomentPoissonError ∧
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        dyadicSecondFactorialPoissonError
        (fun _ _ => 1) ∧
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass 3)
        (fun N _ => (N : ℝ) ^ 2) ∧
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        dyadicVariancePoissonError
        (fun _ _ => 1) := by
  have hmotherBigO :=
    DyadicKappaQuantitative.homogeneousMass_uniformBigO
      hC hES hConductor hDivisor
  have hmotherLittleO :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass 3)
        (fun N _ => (N : ℝ) ^ 2) :=
    NonterminalSectorSaving.uniformBigOOn_trans_uniformLittleOOn
      hmotherBigO
      (NonterminalSectorSaving.quadraticDivLogLogSquaredScale_uniformLittleO_quadratic
        (CriticalRunWindow.InRunLengthWindow C))
  have hfirstMomentRate :
      UniformNegativeHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        dyadicFirstMomentPoissonError := by
    simpa only [dyadicFirstMomentPoissonError, criticalMean] using
      CriticalRunWindow.firstMoment_error_uniformNegativeHalfPower hC
  have hseparated :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          (jointDefectMass N L
            (separatedOffDiagPairs N L) : ℝ))
        (fun N _ => (N : ℝ) ^ 2) := by
    intro ε hε
    obtain ⟨Nmother, hNmother⟩ := hmotherLittleO ε hε
    refine ⟨max 2 Nmother, ?_⟩
    intro N hN L hwindow
    have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
    change
      |(jointDefectMass N L
          (separatedOffDiagPairs N L) : ℝ)| ≤
        ε * |(N : ℝ) ^ 2|
    rw [jointDefectMass_separated_cast_eq_homogeneousMass
      (A := 3) hNtwo]
    exact hNmother N ((le_max_right _ _).trans hN) L hwindow
  have hnumerator :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        factorialErrorNumerator
        (fun N _ => (N : ℝ) ^ 2) := by
    have hoverlap := overlappingPairs_uniformLittleOQuadratic hC
    have htouch := touchingMass_uniformLittleOQuadratic hC
    have hlocal :=
      PropositionElevenTwo.uniformLittleOOn_add hoverlap htouch
    have hall :=
      PropositionElevenTwo.uniformLittleOOn_add hlocal hseparated
    simpa only [factorialErrorNumerator] using hall
  have hfiniteMoment :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        factorialMomentError
        (fun _ _ => 1) := by
    obtain ⟨Nwindow, hNwindow⟩ :=
      CriticalRunWindow.firstMomentWindow_eventually hC
    let B := CriticalRunWindow.balanceConstant C
    have hBpos : 0 < B := by
      unfold B CriticalRunWindow.balanceConstant
      positivity
    intro ε hε
    let δ : ℝ := ε / B ^ 2
    have hδ : 0 < δ := by
      dsimp only [δ]
      positivity
    obtain ⟨Nnum, hNnum⟩ := hnumerator δ hδ
    refine ⟨max 2 (max Nwindow Nnum), ?_⟩
    intro N hN L hrun
    have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
    have hNtail : max Nwindow Nnum ≤ N :=
      (le_max_right _ _).trans hN
    have hwin :=
      hNwindow N ((le_max_left _ _).trans hNtail) L hrun
    have hLpos : 0 < L := hwin.2.1
    have hbalance : (N : ℝ) / (2 : ℝ) ^ L ≤ B := by
      simpa only [B] using hwin.2.2
    have hfinite := abs_factorialMomentError_le hNtwo hLpos
    have hnumBound :=
      hNnum N ((le_max_right _ _).trans hNtail) L hrun
    have hnumNonneg : 0 ≤ factorialErrorNumerator N L := by
      unfold factorialErrorNumerator
      positivity
    have hnumLe :
        factorialErrorNumerator N L ≤ δ * (N : ℝ) ^ 2 := by
      simpa only [abs_of_nonneg hnumNonneg,
        abs_of_nonneg (sq_nonneg (N : ℝ))] using hnumBound
    have hratioNonneg : 0 ≤ (N : ℝ) / (2 : ℝ) ^ L := by
      positivity
    have hbalanceSq :
        ((N : ℝ) / (2 : ℝ) ^ L) ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ hratioNonneg hbalance 2
    simp only [abs_one, mul_one]
    calc
      |factorialMomentError N L| ≤
          factorialErrorNumerator N L / (2 : ℝ) ^ (2 * L) :=
        hfinite
      _ ≤ (δ * (N : ℝ) ^ 2) / (2 : ℝ) ^ (2 * L) :=
        div_le_div_of_nonneg_right hnumLe (by positivity)
      _ = δ * ((N : ℝ) / (2 : ℝ) ^ L) ^ 2 := by
        rw [show 2 * L = L * 2 by omega, pow_mul]
        ring
      _ ≤ δ * B ^ 2 :=
        mul_le_mul_of_nonneg_left hbalanceSq hδ.le
      _ = ε := by
        dsimp only [δ]
        field_simp [ne_of_gt hBpos]
  have hbaseline := factorialBaselinePoissonError_uniformLittleOOne hC
  have hfactorialSum :=
    PropositionElevenTwo.uniformLittleOOn_add hfiniteMoment hbaseline
  have hfactorial :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        dyadicSecondFactorialPoissonError
        (fun _ _ => 1) := by
    have heq :
        dyadicSecondFactorialPoissonError =
          fun N L =>
            factorialMomentError N L +
              factorialBaselinePoissonError N L := by
      funext N L
      exact dyadicSecondFactorialPoissonError_eq N L
    rw [heq]
    exact hfactorialSum
  have hmean := dyadicFirstMomentPoissonError_uniformLittleOOne hC
  have hvariance :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        dyadicVariancePoissonError
        (fun _ _ => 1) := by
    obtain ⟨Nwindow, hNwindow⟩ :=
      CriticalRunWindow.firstMomentWindow_eventually hC
    let B := CriticalRunWindow.balanceConstant C
    have hBnonneg : 0 ≤ B := by
      dsimp only [B]
      exact CriticalRunWindow.balanceConstant_nonneg C
    intro ε hε
    let D : ℝ := 2 * B + 3
    have hDpos : 0 < D := by
      dsimp only [D]
      linarith
    let δ : ℝ := ε / D
    have hδ : 0 < δ := by
      dsimp only [δ]
      positivity
    obtain ⟨Nfactorial, hNfactorial⟩ := hfactorial δ hδ
    obtain ⟨Nmean, hNmean⟩ := hmean δ hδ
    obtain ⟨NmeanOne, hNmeanOne⟩ := hmean 1 (by norm_num)
    refine
      ⟨max Nwindow
        (max Nfactorial (max Nmean NmeanOne)), ?_⟩
    intro N hN L hrun
    have hNtail :
        max Nfactorial (max Nmean NmeanOne) ≤ N :=
      (le_max_right _ _).trans hN
    have hwindow :=
      hNwindow N ((le_max_left _ _).trans hN) L hrun
    have hbalance : criticalMean N L ≤ B := by
      simpa only [criticalMean, B] using hwindow.2.2
    have hlambdaNonneg : 0 ≤ criticalMean N L := by
      unfold criticalMean
      positivity
    have hfactorialBound :
        |dyadicSecondFactorialPoissonError N L| ≤ δ := by
      simpa only [abs_one, mul_one] using
        hNfactorial N ((le_max_left _ _).trans hNtail) L hrun
    have hmeanTail : max Nmean NmeanOne ≤ N :=
      (le_max_right _ _).trans hNtail
    have hmeanBound : |dyadicFirstMomentPoissonError N L| ≤ δ := by
      simpa only [abs_one, mul_one] using
        hNmean N ((le_max_left _ _).trans hmeanTail) L hrun
    have hmeanOne : |dyadicFirstMomentPoissonError N L| ≤ 1 := by
      simpa only [abs_one, mul_one] using
        hNmeanOne N ((le_max_right _ _).trans hmeanTail) L hrun
    have hsumMean :
        |(dyadicExpectation N L : ℝ) + criticalMean N L| ≤
          2 * B + 1 := by
      calc
        |(dyadicExpectation N L : ℝ) + criticalMean N L| =
            |dyadicFirstMomentPoissonError N L +
              criticalMean N L + criticalMean N L| := by
          congr 1
          unfold dyadicFirstMomentPoissonError
          ring
        _ ≤
            |dyadicFirstMomentPoissonError N L + criticalMean N L| +
              |criticalMean N L| :=
          abs_add _ _
        _ ≤
            (|dyadicFirstMomentPoissonError N L| +
              |criticalMean N L|) + |criticalMean N L| := by
          exact add_le_add_right
            (abs_add
              (dyadicFirstMomentPoissonError N L)
              (criticalMean N L)) _
        _ ≤ (1 + B) + B := by
          rw [abs_of_nonneg hlambdaNonneg]
          gcongr
        _ = 2 * B + 1 := by ring
    have hsquareIdentity :
        (dyadicExpectation N L : ℝ) ^ 2 -
            (criticalMean N L) ^ 2 =
          dyadicFirstMomentPoissonError N L *
            ((dyadicExpectation N L : ℝ) + criticalMean N L) := by
      unfold dyadicFirstMomentPoissonError
      ring
    have hsquareBound :
        |(dyadicExpectation N L : ℝ) ^ 2 -
            (criticalMean N L) ^ 2| ≤
          δ * (2 * B + 1) := by
      rw [hsquareIdentity, abs_mul]
      exact
        mul_le_mul hmeanBound hsumMean
          (abs_nonneg _) hδ.le
    simp only [abs_one, mul_one]
    rw [dyadicVariancePoissonError_eq]
    calc
      |dyadicSecondFactorialPoissonError N L +
            dyadicFirstMomentPoissonError N L -
          ((dyadicExpectation N L : ℝ) ^ 2 -
            (criticalMean N L) ^ 2)| ≤
          |dyadicSecondFactorialPoissonError N L| +
            |dyadicFirstMomentPoissonError N L| +
              |(dyadicExpectation N L : ℝ) ^ 2 -
                (criticalMean N L) ^ 2| := by
        calc
          |dyadicSecondFactorialPoissonError N L +
                dyadicFirstMomentPoissonError N L -
              ((dyadicExpectation N L : ℝ) ^ 2 -
                (criticalMean N L) ^ 2)| ≤
              |dyadicSecondFactorialPoissonError N L +
                dyadicFirstMomentPoissonError N L| +
                  |(dyadicExpectation N L : ℝ) ^ 2 -
                    (criticalMean N L) ^ 2| :=
            abs_sub _ _
          _ ≤
              (|dyadicSecondFactorialPoissonError N L| +
                |dyadicFirstMomentPoissonError N L|) +
                  |(dyadicExpectation N L : ℝ) ^ 2 -
                    (criticalMean N L) ^ 2| := by
            exact add_le_add_right
              (abs_add
                (dyadicSecondFactorialPoissonError N L)
                (dyadicFirstMomentPoissonError N L)) _
      _ ≤ δ + δ + δ * (2 * B + 1) := by
        gcongr
      _ = ε := by
        dsimp only [δ, D]
        field_simp [ne_of_gt hDpos]
        ring
  exact ⟨hfirstMomentRate, hfactorial, hmotherLittleO, hvariance⟩

end

end SectionTwelveMoments
end PaperC
