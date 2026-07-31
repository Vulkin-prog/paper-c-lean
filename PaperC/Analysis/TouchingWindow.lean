import PaperC.Analysis.CriticalPointwiseIntervals
import PaperC.Probability.CriticalRunWindow

/-!
# The touching window in the manuscript run-length regime

This module contains the scale transport needed for Lemma 3.4(ii), separately
from its affine-algebraic content.  If

`|L - log₂ N| ≤ C`,

then the height `2L` eventually belongs, uniformly in `L`, to one fixed
critical window.  Starts `x` in the dyadic block also satisfy the geometric
hypotheses of `CriticalPointwiseIntervals.pointwise_all_intervals_on_window`.
-/

namespace PaperC
namespace TouchingWindow

/-- Fixed lower endpoint of the critical window used for touching pairs. -/
noncomputable def lowerConstant : ℝ :=
  1 / Real.log 2

/-- Fixed upper endpoint of the critical window used for touching pairs. -/
noncomputable def upperConstant : ℝ :=
  4 / Real.log 2

theorem lowerConstant_pos : 0 < lowerConstant := by
  unfold lowerConstant
  positivity

theorem lowerConstant_lt_upperConstant :
    lowerConstant < upperConstant := by
  unfold lowerConstant upperConstant
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  exact (div_lt_div_iff₀ hlog hlog).2 (by nlinarith)

/--
Uniformly in the manuscript run-length window, the touching height `2L`
eventually lies in the fixed window
`[lowerConstant * log N, upperConstant * log N]`.
-/
theorem criticalWindow_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      CriticalWindowParameters.InCriticalWindow
        lowerConstant upperConstant N (2 * L) := by
  let S : ℝ := max 1 (2 * C)
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (Real.exp (S * Real.log 2))
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hthreshold :
      Real.exp (S * Real.log 2) < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hlogThreshold :
      S * Real.log 2 < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos _) hthreshold
    simpa only [Real.log_exp] using hlogs
  let ell : ℝ := Real.log N / Real.log 2
  have hSell : S < ell := by
    dsimp only [ell]
    exact (lt_div_iff₀ hlogTwo).2 hlogThreshold
  have hellOne : (1 : ℝ) < ell :=
    (le_max_left 1 (2 * C)).trans_lt hSell
  have hellTwoC : 2 * C < ell :=
    (le_max_right 1 (2 * C)).trans_lt hSell
  have hC_lt_ell : C < ell := by
    nlinarith only [hC, hellTwoC]
  have hrun' : |(L : ℝ) - ell| ≤ C := by
    simpa only [CriticalRunWindow.InRunLengthWindow, ell] using hrun
  obtain ⟨hlower, hupper⟩ := abs_le.mp hrun'
  have hellMinusCLeL : ell - C ≤ (L : ℝ) := by
    linarith
  have hLLeEllPlusC : (L : ℝ) ≤ ell + C := by
    linarith
  have hcriticalLower :
      lowerConstant * Real.log N ≤ ((2 * L : ℕ) : ℝ) := by
    have hre :
        lowerConstant * Real.log N = ell := by
      dsimp [lowerConstant, ell]
      ring
    rw [hre]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hellMinusCLeL, hellTwoC]
  have hcriticalUpper :
      (((2 * L : ℕ) : ℝ)) ≤ upperConstant * Real.log N := by
    have hre :
        upperConstant * Real.log N = 4 * ell := by
      dsimp [upperConstant, ell]
      ring
    rw [hre]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hLLeEllPlusC, hC_lt_ell]
  exact
    ⟨lowerConstant_pos, lowerConstant_lt_upperConstant,
      hcriticalLower, hcriticalUpper⟩

/--
Eventually the touching height fits inside one main dyadic scale.
The proof uses the already isolated eventual translation threshold for a
critical window.
-/
theorem two_mul_runLength_le_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      2 * L ≤ N := by
  obtain ⟨Nwindow, hwindow⟩ :=
    criticalWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      lowerConstant_pos lowerConstant_lt_upperConstant
  refine ⟨max Nwindow Nadm, ?_⟩
  intro N hN L hrun
  have hcritical :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hAdmissible :=
    hadm N ((le_max_right _ _).trans hN) (2 * L) hcritical
  have htwiceHeight :
      2 * (2 * L) ≤ N :=
    CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
      hcritical hAdmissible.2.2.2.1
  omega

/--
The elementary geometry of a start in the dyadic block.  The sole scale
hypothesis `2L ≤ N` is exposed explicitly.
-/
theorem dyadicBlock_geometry
    {N L x : ℕ}
    (hLscale : 2 * L ≤ N)
    (hx : x ∈ dyadicBlock N) :
    N ≤ 2 * x ∧ x + 2 * L ≤ 3 * N := by
  have hxIco :
      x ∈ Finset.Ico N (2 * N) := by
    simpa only [dyadicBlock] using hx
  obtain ⟨hxLower, hxUpper⟩ := Finset.mem_Ico.mp hxIco
  omega

/--
Uniform eventual form of `dyadicBlock_geometry` under the literal run-length
window.
-/
theorem dyadicBlock_geometry_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ x ∈ dyadicBlock N,
        N ≤ 2 * x ∧ x + 2 * L ≤ 3 * N := by
  obtain ⟨Nlength, hlength⟩ :=
    two_mul_runLength_le_eventually hC
  refine ⟨Nlength, ?_⟩
  intro N hN L hrun x hx
  exact dyadicBlock_geometry (hlength N hN L hrun) hx

/--
Uniform pointwise defect bound at every start in the dyadic block, with
touching height `2L`, under the literal manuscript run-length condition.

Both the constant and the threshold are independent of `L` and `x`.
-/
theorem pointwise_defects_uniform
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
        CriticalRunWindow.InRunLengthWindow C N L →
        ∀ x ∈ dyadicBlock N,
          ((IntervalDefectBound.defectsInInterval (2 * L) x).card : ℝ) ≤
            K * (Real.log N / Real.log (Real.log N)) := by
  obtain ⟨K, hK, Npoint, hpoint⟩ :=
    CriticalPointwiseIntervals.pointwise_all_intervals_on_window
      lowerConstant_pos lowerConstant_lt_upperConstant
  obtain ⟨Nwindow, hwindow⟩ :=
    criticalWindow_eventually hC
  obtain ⟨Ngeometry, hgeometry⟩ :=
    dyadicBlock_geometry_eventually hC
  refine
    ⟨K, hK, max Npoint (max Nwindow Ngeometry), ?_⟩
  intro N hN L hrun x hx
  have hNpoint : Npoint ≤ N :=
    (le_max_left Npoint (max Nwindow Ngeometry)).trans hN
  have hNwindow : Nwindow ≤ N :=
    (le_trans (le_max_left Nwindow Ngeometry)
      (le_max_right Npoint (max Nwindow Ngeometry))).trans hN
  have hNgeometry : Ngeometry ≤ N :=
    (le_trans (le_max_right Nwindow Ngeometry)
      (le_max_right Npoint (max Nwindow Ngeometry))).trans hN
  have hcritical :=
    hwindow N hNwindow L hrun
  have hxgeometry :=
    hgeometry N hNgeometry L hrun x hx
  exact
    hpoint N hNpoint (2 * L) hcritical x
      hxgeometry.1 hxgeometry.2

end TouchingWindow
end PaperC
