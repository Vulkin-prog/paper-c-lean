import PaperC.Probability.CriticalFirstMoment

/-!
# The manuscript run-length window

This module converts the literal condition `|L-log₂ N| ≤ C` into the
logarithmic height window and balance condition used by
`CriticalFirstMoment`.
-/

namespace PaperC
namespace CriticalRunWindow

/-- The real-valued version of the manuscript window `|L-log₂ N| ≤ C`. -/
def InRunLengthWindow (C : ℝ) (N L : ℕ) : Prop :=
  |(L : ℝ) - Real.log N / Real.log 2| ≤ C

/-- A fixed lower critical-window constant. -/
noncomputable def lowerConstant : ℝ :=
  1 / (2 * Real.log 2)

/-- A fixed upper critical-window constant. -/
noncomputable def upperConstant : ℝ :=
  2 / Real.log 2

/-- The fixed balance constant implied by a run-length error at most `C`. -/
noncomputable def balanceConstant (C : ℝ) : ℝ :=
  Real.exp (C * Real.log 2)

theorem lowerConstant_pos : 0 < lowerConstant := by
  unfold lowerConstant
  positivity

theorem lowerConstant_lt_upperConstant :
    lowerConstant < upperConstant := by
  unfold lowerConstant upperConstant
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  apply (div_lt_div_iff₀ (by positivity) hlog).2
  nlinarith

theorem balanceConstant_nonneg (C : ℝ) :
    0 ≤ balanceConstant C := by
  unfold balanceConstant
  positivity

/--
Eventually the literal run-length window implies all hypotheses of
`CriticalFirstMoment.FirstMomentWindow`, with constants independent of
`N,L`.
-/
theorem firstMomentWindow_eventually
    {C : ℝ} (_hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      InRunLengthWindow C N L →
      CriticalFirstMoment.FirstMomentWindow
        lowerConstant upperConstant (balanceConstant C) N L := by
  let S : ℝ := max 1 (max (2 * C) (C + 1))
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
    (le_max_left 1 (max (2 * C) (C + 1))).trans_lt hSell
  have hellTwoC : 2 * C < ell :=
    (le_trans (le_max_left (2 * C) (C + 1))
      (le_max_right 1 (max (2 * C) (C + 1)))).trans_lt hSell
  have hellCOne : C + 1 < ell :=
    (le_trans (le_max_right (2 * C) (C + 1))
      (le_max_right 1 (max (2 * C) (C + 1)))).trans_lt hSell
  have hrun' : |(L : ℝ) - ell| ≤ C := by
    simpa only [InRunLengthWindow, ell] using hrun
  obtain ⟨hlower, hupper⟩ := abs_le.mp hrun'
  have hellMinusCLeL : ell - C ≤ (L : ℝ) := by linarith
  have hLLeEllPlusC : (L : ℝ) ≤ ell + C := by linarith
  have hLpos : 0 < L := by
    have hLreal : (1 : ℝ) < (L : ℝ) := by linarith
    have hLnat : 1 < L := by exact_mod_cast hLreal
    omega
  have hcriticalLower :
      lowerConstant * Real.log N ≤ (L + 1 : ℕ) := by
    have hre :
      lowerConstant * Real.log N = ell / 2 := by
      dsimp [lowerConstant, ell]
      ring
    rw [hre]
    have : ell / 2 ≤ (L : ℝ) := by nlinarith
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hcriticalUpper :
      ((L + 1 : ℕ) : ℝ) ≤ upperConstant * Real.log N := by
    have hre :
      upperConstant * Real.log N = 2 * ell := by
      dsimp [upperConstant, ell]
      ring
    rw [hre]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hcritical :
      CriticalWindowParameters.InCriticalWindow
        lowerConstant upperConstant N (L + 1) :=
    ⟨lowerConstant_pos, lowerConstant_lt_upperConstant,
      hcriticalLower, hcriticalUpper⟩
  have hNpos : 0 < (N : ℝ) :=
    (Real.exp_pos _).trans hthreshold
  have hlogN :
      Real.log N ≤ (L : ℝ) * Real.log 2 + C * Real.log 2 := by
    have hlower' : ell - C ≤ (L : ℝ) := hellMinusCLeL
    dsimp only [ell] at hlower'
    have := mul_le_mul_of_nonneg_right hlower' hlogTwo.le
    field_simp at this
    nlinarith
  have hpowExp :
      (2 : ℝ) ^ L =
        Real.exp ((L : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ L = (Real.exp (Real.log 2)) ^ L := by
        rw [Real.exp_log]
        norm_num
      _ = Real.exp ((L : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul (Real.log 2) L).symm
  have hbalance :
      (N : ℝ) / (2 : ℝ) ^ L ≤ balanceConstant C := by
    apply (div_le_iff₀ (pow_pos (by norm_num) L)).2
    unfold balanceConstant
    rw [hpowExp, ← Real.exp_add, ← Real.exp_log hNpos]
    exact Real.exp_le_exp.mpr (by linarith)
  exact ⟨hcritical, hLpos, hbalance⟩

/--
Corollary 3.3 with the manuscript's literal hypothesis:

`N * |E Z_{N,L} - N 2^{-L}| = N^(1/2+o_C(1))`

uniformly for `|L-log₂ N| ≤ C`.
-/
theorem normalized_error_uniformHalfPower
    {C : ℝ} (hC : 0 ≤ C) :
    UniformHalfPowerSubpolynomialOn
      (InRunLengthWindow C)
      (fun N L =>
        (N : ℝ) *
          ((dyadicExpectation N L : ℝ) -
            (N : ℝ) / (2 : ℝ) ^ L)) := by
  have hcore :=
    CriticalFirstMoment.normalized_error_uniformHalfPower
      lowerConstant_pos lowerConstant_lt_upperConstant
      (balanceConstant_nonneg C)
  obtain ⟨Nwindow, hNwindow⟩ := firstMomentWindow_eventually hC
  intro k hk
  obtain ⟨Ncore, hNcore⟩ := hcore k hk
  refine ⟨max Nwindow Ncore, ?_⟩
  intro N hN L hrun
  exact
    hNcore N ((le_max_right _ _).trans hN) L
      (hNwindow N ((le_max_left _ _).trans hN) L hrun)

/--
The same conclusion in the named notation
`N^(-1/2+o_C(1))`; this is the literal asymptotic assertion of
Corollary 3.3.
-/
theorem firstMoment_error_uniformNegativeHalfPower
    {C : ℝ} (hC : 0 ≤ C) :
    UniformNegativeHalfPowerSubpolynomialOn
      (InRunLengthWindow C)
      (fun N L =>
        (dyadicExpectation N L : ℝ) -
          (N : ℝ) / (2 : ℝ) ^ L) :=
  normalized_error_uniformHalfPower hC

end CriticalRunWindow
end PaperC
