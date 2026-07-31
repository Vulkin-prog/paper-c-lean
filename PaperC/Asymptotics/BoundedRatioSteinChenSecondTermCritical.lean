import PaperC.Asymptotics.BoundedRatioSteinChenSecondTerm
import PaperC.Asymptotics.BoundedRatioBadStarts

set_option maxHeartbeats 1800000

/-!
# The averaged second Stein--Chen term in the critical window

This module normalizes the finite majorant from
`BoundedRatioSteinChenSecondTerm` at the literal terminal prime cutoff.
The three numerator contributions are:

* the linear touching population `2M`;
* the bounded ordered dependency-edge population;
* the homogeneous separated excess `R2κ`.

The first is elementary, the second is already proved to be uniformly
`o(N²)`, and the third is precisely Proposition 16.1.  The first-moment
window then converts division by `2^(2L)` into a bounded multiple of
division by `N²`.
-/

namespace PaperC
namespace BoundedRatioSteinChenSecondTermCritical

open scoped BigOperators NNReal

open BoundedRatioSteinChen
open BoundedRatioSteinChenSecondTerm
open BoundedRatioBadStarts
open PropositionSixteenOne
open TerminalPrimeCutoff

noncomputable section

/-! ## Terminal quantities -/

/-- The averaged conditional second AGG term at the literal terminal cutoff. -/
noncomputable def terminalBoundedConditionalBTwoAverage
    (N M L : ℕ) : ℝ :=
  boundedConditionalBTwoAverage N M L
    (terminalPrimeCutoff (L + 1))

/-- The numerator in the manuscript-strength finite majorant. -/
noncomputable def terminalBTwoMajorantNumerator
    (N M L : ℕ) : ℝ :=
  (2 : ℝ) * M +
    ((boundedOrderedDependencyEdges N M L
      (terminalPrimeCutoff (L + 1))).card : ℝ) +
    R2κ N M L

theorem terminalBTwoMajorantNumerator_nonneg
    (N M L : ℕ) :
    0 ≤ terminalBTwoMajorantNumerator N M L := by
  unfold terminalBTwoMajorantNumerator R2κ
  positivity

theorem boundedConditionalBTwoAverage_nonneg
    (N M L Y : ℕ) :
    0 ≤ boundedConditionalBTwoAverage N M L Y := by
  rw [boundedConditionalBTwoAverage_eq_boundedSteinBTwoAverage]
  have hmass :
      (0 : ℚ) ≤ boundedSteinBTwoAverage N M L Y := by
    unfold boundedSteinBTwoAverage boundedJointPairMass
    exact Finset.sum_nonneg fun pair _hpair ↦
      boundedJointStartProbability_nonneg
        M L pair.1 pair.2
  exact_mod_cast hmass

theorem terminalBoundedConditionalBTwoAverage_nonneg
    (N M L : ℕ) :
    0 ≤ terminalBoundedConditionalBTwoAverage N M L :=
  boundedConditionalBTwoAverage_nonneg N M L
    (terminalPrimeCutoff (L + 1))

/-! ## The numerator is uniformly `o(N²)` -/

/-- The linear touching numerator is uniformly negligible on bounded ratios. -/
theorem terminalBTwoTouchingNumerator_uniformLittleOInBoundedRatioWindow
    (C : ℝ) (κ₀ : ℕ) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (fun _N M _L ↦ (2 : ℝ) * M) := by
  intro ε hε
  obtain ⟨Nsize, hNsize⟩ :=
    exists_nat_gt (2 * (κ₀ : ℝ) / ε)
  refine ⟨max 1 Nsize, ?_⟩
  intro N hN M L _hNM hMκ _hrun
  have hNposNat : 0 < N :=
    (le_max_left 1 Nsize).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hNposNat
  have hNsizeReal :
      2 * (κ₀ : ℝ) / ε < (N : ℝ) :=
    hNsize.trans_le (by
      exact_mod_cast (le_max_right 1 Nsize).trans hN)
  have hcoefficient :
      2 * (κ₀ : ℝ) < ε * (N : ℝ) := by
    have hcross := (div_lt_iff₀ hε).mp hNsizeReal
    simpa only [mul_comm] using hcross
  have hMκReal :
      (M : ℝ) ≤ (κ₀ : ℝ) * (N : ℝ) := by
    exact_mod_cast hMκ
  rw [abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * M)]
  rw [abs_of_nonneg (sq_nonneg (N : ℝ))]
  calc
    (2 : ℝ) * M ≤
        (2 * (κ₀ : ℝ)) * (N : ℝ) := by
      nlinarith
    _ ≤ (ε * (N : ℝ)) * (N : ℝ) := by
      exact
        mul_le_mul_of_nonneg_right hcoefficient.le hNpos.le
    _ = ε * (N : ℝ) ^ 2 := by ring

/-- All three finite-majorant numerators are uniformly `o(N²)`. -/
theorem terminalBTwoMajorantNumerator_uniformLittleOInBoundedRatioWindow
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ)
    (hR2 : PropositionSixteenOneStatement C κ₀) :
    UniformLittleOInBoundedRatioWindow C κ₀
      terminalBTwoMajorantNumerator := by
  have htouch :=
    terminalBTwoTouchingNumerator_uniformLittleOInBoundedRatioWindow C κ₀
  have hedge :=
    boundedOrderedDependencyEdges_terminalCutoff_uniformLittleOInBoundedRatioWindow
      hC κ₀
  have htouchEdge :=
    uniformLittleOInBoundedRatioWindow_add htouch hedge
  change UniformLittleOInBoundedRatioWindow C κ₀
    (fun N M L =>
      (2 : ℝ) * M +
        ((boundedOrderedDependencyEdges N M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) +
        R2κ N M L)
  exact uniformLittleOInBoundedRatioWindow_add htouchEdge hR2

/-! ## Adequacy of the terminal cutoff -/

/--
Uniformly in the critical window, the terminal cutoff eventually contains
two complete run lengths.  This is the sole extra finite hypothesis needed
by the manuscript-strength touching estimate.
-/
theorem two_mul_runLength_le_terminalPrimeCutoff_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
        2 * L ≤ terminalPrimeCutoff (L + 1) := by
  let H : ℕ := ⌈Real.exp (1 : ℝ)⌉₊
  obtain ⟨Nheight, hheight⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity hC H
  refine ⟨Nheight, ?_⟩
  intro N hN L hrun
  have hHL : H ≤ L + 1 :=
    hheight N hN L hrun
  have hexp :
      Real.exp (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
    calc
      Real.exp (1 : ℝ) ≤ (H : ℝ) := by
        exact Nat.le_ceil _
      _ ≤ ((L + 1 : ℕ) : ℝ) := by
        exact_mod_cast hHL
  have hlog :
      (1 : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ) := by
    have hmono :=
      Real.log_le_log (Real.exp_pos (1 : ℝ)) hexp
    simpa only [Real.log_exp] using hmono
  have hsquareCutoff :
      (L + 1) ^ 2 ≤ terminalPrimeCutoff (L + 1) := by
    simpa using
      (DependencyEdgesCritical.mul_sq_le_terminalPrimeCutoff
        (m := 1) (B := L + 1)
        (by simpa only [Nat.cast_one] using hlog))
  have htwoSquare : 2 * L ≤ (L + 1) ^ 2 := by
    nlinarith
  exact htwoSquare.trans hsquareCutoff

/-! ## Critical normalization -/

/--
At the terminal cutoff, the averaged conditional second Stein--Chen term is
uniformly `o(1)` on every bounded-ratio critical window.  Proposition 16.1
is the only arithmetic hypothesis.
-/
theorem terminalBoundedConditionalBTwoAverage_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ)
    (hR2 : PropositionSixteenOneStatement C κ₀) :
    UniformLittleOOneInBoundedRatioWindow C κ₀
      terminalBoundedConditionalBTwoAverage := by
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Ncutoff, hcutoff⟩ :=
    two_mul_runLength_le_terminalPrimeCutoff_eventually hC
  let B := CriticalRunWindow.balanceConstant C
  have hBpos : 0 < B := by
    unfold B CriticalRunWindow.balanceConstant
    positivity
  intro ε hε
  let δ : ℝ := ε / B ^ 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  obtain ⟨Nnumerator, hnumerator⟩ :=
    (terminalBTwoMajorantNumerator_uniformLittleOInBoundedRatioWindow
      hC κ₀ hR2) δ hδ
  refine
    ⟨max 2 (max Nwindow (max Ncutoff Nnumerator)), ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2
      (max Nwindow (max Ncutoff Nnumerator))).trans hN
  have htail :
      max Nwindow (max Ncutoff Nnumerator) ≤ N :=
    (le_max_right 2
      (max Nwindow (max Ncutoff Nnumerator))).trans hN
  have hw :=
    hwindow N ((le_max_left _ _).trans htail) L hrun
  have hcutoffN :
      Ncutoff ≤ N :=
    (le_max_left Ncutoff Nnumerator).trans
      ((le_max_right Nwindow
        (max Ncutoff Nnumerator)).trans htail)
  have htwoLY :
      2 * L ≤ terminalPrimeCutoff (L + 1) :=
    hcutoff N hcutoffN L hrun
  have hnumeratorN :
      Nnumerator ≤ N :=
    (le_max_right Ncutoff Nnumerator).trans
      ((le_max_right Nwindow
        (max Ncutoff Nnumerator)).trans htail)
  have hnumBound :=
    hnumerator N hnumeratorN M L hNM hMκ hrun
  have hnumLe :
      terminalBTwoMajorantNumerator N M L ≤
        δ * (N : ℝ) ^ 2 := by
    simpa only [
      abs_of_nonneg
        (terminalBTwoMajorantNumerator_nonneg N M L),
      abs_of_nonneg (sq_nonneg (N : ℝ))] using hnumBound
  have hratioNonneg :
      0 ≤ (N : ℝ) / (2 : ℝ) ^ L := by
    positivity
  have hbalance :
      (N : ℝ) / (2 : ℝ) ^ L ≤ B := by
    simpa only [B] using hw.2.2
  have hbalanceSq :
      ((N : ℝ) / (2 : ℝ) ^ L) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hratioNonneg hbalance 2
  rw [abs_of_nonneg
    (terminalBoundedConditionalBTwoAverage_nonneg N M L)]
  calc
    terminalBoundedConditionalBTwoAverage N M L ≤
        (2 * M : ℝ) / (2 : ℝ) ^ (2 * L) +
          ((boundedOrderedDependencyEdges N M L
            (terminalPrimeCutoff (L + 1))).card : ℝ) /
              (2 : ℝ) ^ (2 * L) +
          R2κ N M L / (2 : ℝ) ^ (2 * L) := by
      exact
        boundedConditionalBTwoAverage_le_strongFiniteMajorant
          (N := N) (M := M) (L := L)
          (Y := terminalPrimeCutoff (L + 1))
          hNtwo hw.2.1 htwoLY
    _ =
        terminalBTwoMajorantNumerator N M L /
          (2 : ℝ) ^ (2 * L) := by
      unfold terminalBTwoMajorantNumerator
      ring
    _ ≤
        (δ * (N : ℝ) ^ 2) /
          (2 : ℝ) ^ (2 * L) :=
      div_le_div_of_nonneg_right hnumLe (by positivity)
    _ = δ * ((N : ℝ) / (2 : ℝ) ^ L) ^ 2 := by
      rw [show 2 * L = L * 2 by omega, pow_mul]
      ring
    _ ≤ δ * B ^ 2 :=
      mul_le_mul_of_nonneg_left hbalanceSq hδ.le
    _ = ε := by
      dsimp only [δ]
      field_simp [ne_of_gt hBpos]

end

end BoundedRatioSteinChenSecondTermCritical
end PaperC
