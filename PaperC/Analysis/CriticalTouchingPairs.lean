import PaperC.Affine.TouchingDefectRank
import PaperC.Analysis.TouchingMass
import PaperC.Analysis.TouchingWindow
import PaperC.Asymptotics.LinearPower

/-!
# Lemma 3.4(ii): the mass of touching pairs

For an ordered pair of starts at distance `L`, the union of the two start
trees is represented by `Affine.touchingSystem`.  Its relation defect is
bounded by the number of `2L`-defective vertices in the interval beginning
at the lower start.  Proposition 3.2 makes this defect logarithmic over
log-logarithmic, so its power of two is subpolynomial.  Finally, there are at
most `2N` ordered touching pairs in the dyadic block.
-/

namespace PaperC
namespace CriticalTouchingPairs

open Affine

/-- Structural rank bound for the canonically oriented form of any ordered
touching pair. -/
theorem touchingRho_le_card_defectsInInterval
    {N L : ℕ} {pair : ℕ × ℕ}
    (hN : 2 ≤ N) (hL : 0 < L)
    (hpair : pair ∈ TouchingPairs.touchingPairs N L) :
    TouchingMass.touchingRho N L pair ≤
      (IntervalDefectBound.defectsInInterval
        (2 * L) (TouchingMass.touchingLower pair)).card := by
  unfold TouchingMass.touchingRho
  exact
    TouchingDefectRank.relationRho_touchingSystem_le_card_defectsInInterval
      hN (TouchingMass.touchingLower_mem_dyadicBlock hpair) hL

/--
Uniform logarithm-over-logarithm bound for the largest joint relation defect
among touching pairs.
-/
theorem maxTouchingRho_log_bound_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
        CriticalRunWindow.InRunLengthWindow C N L →
        (TouchingMass.maxTouchingRho N L : ℝ) ≤
          K * (Real.log N / Real.log (Real.log N)) := by
  obtain ⟨K, hK, Npoint, hpoint⟩ :=
    TouchingWindow.pointwise_defects_uniform hC
  obtain ⟨Nrun, hrun⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nlog, hNlog⟩ :=
    exists_nat_gt (Real.exp 4)
  let N₀ := max Npoint (max Nrun (max Nlog 2))
  refine ⟨K, hK, N₀, ?_⟩
  intro N hN L hwindow
  have hNpoint : Npoint ≤ N :=
    (le_max_left Npoint (max Nrun (max Nlog 2))).trans hN
  have hNrun : Nrun ≤ N :=
    (le_trans (le_max_left Nrun (max Nlog 2))
      (le_max_right Npoint (max Nrun (max Nlog 2)))).trans hN
  have hNlogN : Nlog ≤ N :=
    (le_trans
      (le_trans (le_max_left Nlog 2)
        (le_max_right Nrun (max Nlog 2)))
      (le_max_right Npoint (max Nrun (max Nlog 2)))).trans hN
  have hNtwo : 2 ≤ N :=
    (le_trans
      (le_trans (le_max_right Nlog 2)
        (le_max_right Nrun (max Nlog 2)))
      (le_max_right Npoint (max Nrun (max Nlog 2)))).trans hN
  have hL : 0 < L :=
    (hrun N hNrun L hwindow).2.1
  have hthreshold :
      Real.exp 4 < (N : ℝ) :=
    hNlog.trans_le (by exact_mod_cast hNlogN)
  have hlogN : 4 < Real.log N := by
    have hmono :=
      Real.log_lt_log (Real.exp_pos 4) hthreshold
    simpa only [Real.log_exp] using hmono
  have hlogNpos : 0 < Real.log N := by linarith
  have hloglogNpos : 0 < Real.log (Real.log N) := by
    apply Real.log_pos
    linarith
  have hscaleNonneg :
      0 ≤ Real.log N / Real.log (Real.log N) :=
    div_nonneg hlogNpos.le hloglogNpos.le
  apply TouchingMass.maxTouchingRho_cast_le
    (mul_nonneg hK hscaleNonneg)
  intro pair hpair
  have hrho :=
    touchingRho_le_card_defectsInInterval hNtwo hL hpair
  have hrhoCast :
      (TouchingMass.touchingRho N L pair : ℝ) ≤
        ((IntervalDefectBound.defectsInInterval
          (2 * L) (TouchingMass.touchingLower pair)).card : ℝ) := by
    exact_mod_cast hrho
  exact hrhoCast.trans
    (hpoint N hNpoint L hwindow
      (TouchingMass.touchingLower pair)
      (TouchingMass.touchingLower_mem_dyadicBlock hpair))

/-- The maximal dyadic loss `2^ρ` over touching pairs is uniformly
subpolynomial in the literal run-length window. -/
theorem two_pow_maxTouchingRho_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (((2 ^ TouchingMass.maxTouchingRho N L : ℕ) : ℝ))) := by
  obtain ⟨K, hK, Nbound, hbound⟩ :=
    maxTouchingRho_log_bound_eventually hC
  apply
    ExpSqrtLog.uniformSubpolynomialOn_two_pow_log_div_loglog_eventually
      (CriticalRunWindow.InRunLengthWindow C)
      TouchingMass.maxTouchingRho K hK
  refine ⟨Nbound, ?_⟩
  intro N hN L hwindow
  simpa only [mul_div_assoc] using hbound N hN L hwindow

/--
Fully quantified form of Lemma 3.4(ii):

`∑_{(x,y) ∈ I_N², |x-y|=L} (2^ρ(x,y)-1) = N^(1+o_C(1))`

as an upper bound, uniformly under `|L-log₂ N| ≤ C`.
-/
theorem touchingMass_uniformLinearSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLinearSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L => (TouchingMass.touchingMass N L : ℝ)) := by
  have hpow :=
    two_pow_maxTouchingRho_uniformSubpolynomial hC
  have hfactor :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          (2 : ℝ) *
            (((2 ^ TouchingMass.maxTouchingRho N L : ℕ) : ℝ))) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul 2 hpow
  apply UniformLinear.of_linear_mul_subpolynomial hfactor
  refine ⟨0, ?_⟩
  intro N _hN L _hwindow
  have hmass :=
    TouchingMass.touchingMass_cast_le_two_mul_two_pow_maxTouchingRho
      N L
  have hmassNonneg :
      0 ≤ (TouchingMass.touchingMass N L : ℝ) := by positivity
  have hfactorNonneg :
      0 ≤
        (2 : ℝ) *
          (((2 ^ TouchingMass.maxTouchingRho N L : ℕ) : ℝ)) := by
    positivity
  rw [abs_of_nonneg hmassNonneg, abs_of_nonneg hfactorNonneg]
  calc
    (TouchingMass.touchingMass N L : ℝ) ≤
        (2 * N : ℝ) *
          (2 : ℝ) ^ TouchingMass.maxTouchingRho N L :=
      hmass
    _ = (N : ℝ) *
        ((2 : ℝ) *
          (((2 ^ TouchingMass.maxTouchingRho N L : ℕ) : ℝ))) := by
      norm_num
      ring

end CriticalTouchingPairs
end PaperC
