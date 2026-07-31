import PaperC.Analysis.CriticalWeightedDefect

/-!
# Pointwise defect bounds on all nearby intervals

The canonical pointwise estimate in `CriticalWeightedDefect` is stated for
the interval beginning at the main scale.  This file transports it from the
scale `N` to every `U` with

`N ≤ 2U` and `U + H ≤ 3N`.

For large `N`, these inequalities put `U` between constant multiples of `N`.
Consequently a critical window at `N` becomes the slightly wider critical
window `(c₁ / 2, 2c₂)` at `U`, while

`log U / log log U ≤ 4 * log N / log log N`.
-/

namespace PaperC
namespace CriticalPointwiseIntervals

/--
At two scales differing by the ratios occurring in Proposition 3.2, the
critical window at `N` is contained in a fixed wider critical window at `U`.
-/
theorem criticalWindow_transport
    {c₁ c₂ : ℝ} {N H U : ℕ}
    (hc₁ : 0 < c₁)
    (hc₁c₂ : c₁ < c₂)
    (hwindow :
      CriticalWindowParameters.InCriticalWindow c₁ c₂ N H)
    (hNthree : 3 ≤ N)
    (hUlog : 0 < Real.log U)
    (hNtwoU : N ≤ 2 * U)
    (hUthreeN : U ≤ 3 * N) :
    CriticalWindowParameters.InCriticalWindow
      (c₁ / 2) (2 * c₂) U H := by
  have hUtwo : 2 ≤ U := by
    have honeU : (1 : ℝ) < (U : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg U)).mp hUlog
    exact_mod_cast honeU
  have hUNsq : U ≤ N * N := by
    have hthreeN_le : 3 * N ≤ N * N := by
      nlinarith
    exact hUthreeN.trans hthreeN_le
  have hNU_sq : N ≤ U * U := by
    have htwoU_le : 2 * U ≤ U * U := by
      nlinarith
    exact hNtwoU.trans htwoU_le
  have hNpos : 0 < (N : ℝ) := by positivity
  have hUpos : 0 < (U : ℝ) := by positivity
  have hlogU_le :
      Real.log U ≤ 2 * Real.log N := by
    calc
      Real.log U ≤ Real.log (N * N : ℕ) := by
        apply Real.log_le_log hUpos
        exact_mod_cast hUNsq
      _ = 2 * Real.log N := by
        norm_num only [Nat.cast_mul]
        rw [Real.log_mul hNpos.ne' hNpos.ne']
        ring
  have hlogN_le :
      Real.log N ≤ 2 * Real.log U := by
    calc
      Real.log N ≤ Real.log (U * U : ℕ) := by
        apply Real.log_le_log hNpos
        exact_mod_cast hNU_sq
      _ = 2 * Real.log U := by
        norm_num only [Nat.cast_mul]
        rw [Real.log_mul hUpos.ne' hUpos.ne']
        ring
  refine ⟨by positivity, by nlinarith, ?_, ?_⟩
  · have hlower := hwindow.2.2.1
    nlinarith
  · have hupper := hwindow.2.2.2
    have hc₂ : 0 < c₂ := hc₁.trans hc₁c₂
    nlinarith

/--
The logarithmic pointwise scale changes by at most a factor four under the
same bounded-ratio hypotheses.  The lower bounds on the two logarithms are
kept explicit so this lemma contains no hidden asymptotic threshold.
-/
theorem log_div_loglog_le_four
    {N U : ℕ}
    (hNlog : 4 < Real.log N)
    (hUlog : 4 < Real.log U)
    (hNtwoU : N ≤ 2 * U)
    (hUthreeN : U ≤ 3 * N) :
    Real.log U / Real.log (Real.log U) ≤
      4 * (Real.log N / Real.log (Real.log N)) := by
  have hNthree : 3 ≤ N := by
    by_contra h
    have hNle : N ≤ 2 := by omega
    have hNpos : 0 < (N : ℝ) := by
      have honeN : (1 : ℝ) < (N : ℝ) :=
        (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
      linarith
    have hlogNle : Real.log N ≤ Real.log 2 := by
      apply Real.log_le_log
      · exact hNpos
      · exact_mod_cast hNle
    nlinarith [Real.log_two_lt_d9]
  have hUtwo : 2 ≤ U := by
    have honeU : (1 : ℝ) < (U : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg U)).mp (by linarith)
    exact_mod_cast honeU
  have hUNsq : U ≤ N * N := by
    have hthreeN_le : 3 * N ≤ N * N := by
      nlinarith
    exact hUthreeN.trans hthreeN_le
  have hNU_sq : N ≤ U * U := by
    have htwoU_le : 2 * U ≤ U * U := by
      nlinarith
    exact hNtwoU.trans htwoU_le
  have hNpos : 0 < (N : ℝ) := by positivity
  have hUpos : 0 < (U : ℝ) := by positivity
  have hlogNpos : 0 < Real.log N := by linarith
  have hlogUpos : 0 < Real.log U := by linarith
  have hlogU_le :
      Real.log U ≤ 2 * Real.log N := by
    calc
      Real.log U ≤ Real.log (N * N : ℕ) := by
        apply Real.log_le_log hUpos
        exact_mod_cast hUNsq
      _ = 2 * Real.log N := by
        norm_num only [Nat.cast_mul]
        rw [Real.log_mul hNpos.ne' hNpos.ne']
        ring
  have hlogN_le :
      Real.log N ≤ 2 * Real.log U := by
    calc
      Real.log N ≤ Real.log (U * U : ℕ) := by
        apply Real.log_le_log hNpos
        exact_mod_cast hNU_sq
      _ = 2 * Real.log U := by
        norm_num only [Nat.cast_mul]
        rw [Real.log_mul hUpos.ne' hUpos.ne']
        ring
  have hlogN_le_sq :
      Real.log N ≤ (Real.log U) ^ 2 := by
    have htwo_le_logU : 2 ≤ Real.log U := by linarith
    have htwoLog_le_sq :
        2 * Real.log U ≤ (Real.log U) ^ 2 := by
      nlinarith
    exact hlogN_le.trans htwoLog_le_sq
  have hloglogN_le :
      Real.log (Real.log N) ≤
        2 * Real.log (Real.log U) := by
    calc
      Real.log (Real.log N) ≤ Real.log ((Real.log U) ^ 2) := by
        exact Real.log_le_log hlogNpos hlogN_le_sq
      _ = 2 * Real.log (Real.log U) := by
        rw [pow_two, Real.log_mul hlogUpos.ne' hlogUpos.ne']
        ring
  have hlogFour : 1 < Real.log (4 : ℝ) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hloglogUpos : 0 < Real.log (Real.log U) := by
    have hmono :
        Real.log (4 : ℝ) < Real.log (Real.log U) :=
      Real.log_lt_log (by norm_num) hUlog
    linarith
  have hloglogNpos : 0 < Real.log (Real.log N) := by
    have hmono :
        Real.log (4 : ℝ) < Real.log (Real.log N) :=
      Real.log_lt_log (by norm_num) hNlog
    linarith
  calc
    Real.log U / Real.log (Real.log U) ≤
        (2 * Real.log N) / Real.log (Real.log U) :=
      div_le_div_of_nonneg_right hlogU_le hloglogUpos.le
    _ ≤ (2 * Real.log N) /
        (Real.log (Real.log N) / 2) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · nlinarith
    _ = 4 * (Real.log N / Real.log (Real.log N)) := by
      field_simp
      ring

/--
Pointwise part of Proposition 3.2 simultaneously for every interval
`[U,U+H]` contained in the enlarged range `[N/2,3N]`.

The constants and threshold are uniform in both `H` and `U`.
-/
theorem pointwise_all_intervals_on_window
    {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁)
    (hc₁c₂ : c₁ < c₂) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H,
        CriticalWindowParameters.InCriticalWindow c₁ c₂ N H →
        ∀ U, N ≤ 2 * U → U + H ≤ 3 * N →
          ((IntervalDefectBound.defectsInInterval H U).card : ℝ) ≤
            K * (Real.log N / Real.log (Real.log N)) := by
  have hc₁half : 0 < c₁ / 2 := by positivity
  have hwindowOrder : c₁ / 2 < 2 * c₂ := by
    have hc₂ : 0 < c₂ := hc₁.trans hc₁c₂
    nlinarith
  obtain ⟨K, hK, Npoint, hpoint⟩ :=
    CriticalWeightedDefect.pointwise_uniformBigO_on_window
      hc₁half hwindowOrder
  obtain ⟨Nbasic, hNbasic⟩ :=
    exists_nat_gt (2 * Real.exp 4)
  refine ⟨4 * K, by positivity, max (2 * Npoint) Nbasic, ?_⟩
  intro N hN H hwindow U hNtwoU hcontained
  have hNpoint : 2 * Npoint ≤ N :=
    (le_max_left (2 * Npoint) Nbasic).trans hN
  have hNbasicN : Nbasic ≤ N :=
    (le_max_right (2 * Npoint) Nbasic).trans hN
  have hNlarge : 2 * Real.exp 4 < (N : ℝ) :=
    hNbasic.trans_le (by exact_mod_cast hNbasicN)
  have hUlarge : Real.exp 4 < (U : ℝ) := by
    have hcast : (N : ℝ) ≤ 2 * U := by exact_mod_cast hNtwoU
    nlinarith
  have hNexp : Real.exp 4 < (N : ℝ) :=
    (lt_mul_of_one_lt_left (Real.exp_pos 4) (by norm_num : (1 : ℝ) < 2)).trans
      hNlarge
  have hNlog : 4 < Real.log N := by
    have hmono := Real.log_lt_log (Real.exp_pos 4) hNexp
    simpa only [Real.log_exp] using hmono
  have hUlog : 4 < Real.log U := by
    have hmono := Real.log_lt_log (Real.exp_pos 4) hUlarge
    simpa only [Real.log_exp] using hmono
  have hUthreeN : U ≤ 3 * N := by omega
  have hwindowU :
      CriticalWindowParameters.InCriticalWindow
        (c₁ / 2) (2 * c₂) U H :=
    criticalWindow_transport hc₁ hc₁c₂ hwindow (by
      have hNthree : 3 ≤ N := by
        have hexpOne : (1 : ℝ) < Real.exp 4 := by
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.mpr (by norm_num)
        have hNtwoReal : (2 : ℝ) < (N : ℝ) := by
          nlinarith
        exact_mod_cast hNtwoReal
      exact hNthree)
      (by linarith) hNtwoU hUthreeN
  have hUpoint : Npoint ≤ U := by omega
  have hcanonical := hpoint U hUpoint H hwindowU
  have hscale :=
    log_div_loglog_le_four hNlog hUlog hNtwoU hUthreeN
  have hlogNpos : 0 < Real.log N := by linarith
  have hlogUpos : 0 < Real.log U := by linarith
  have hloglogNpos : 0 < Real.log (Real.log N) := by
    apply Real.log_pos
    linarith
  have hloglogUpos : 0 < Real.log (Real.log U) := by
    apply Real.log_pos
    linarith
  rw [abs_of_nonneg (by positivity),
    abs_of_pos (div_pos hlogUpos hloglogUpos)] at hcanonical
  calc
    ((IntervalDefectBound.defectsInInterval H U).card : ℝ) ≤
        K * (Real.log U / Real.log (Real.log U)) := hcanonical
    _ ≤ K * (4 * (Real.log N / Real.log (Real.log N))) :=
      mul_le_mul_of_nonneg_left hscale hK
    _ = (4 * K) *
        (Real.log N / Real.log (Real.log N)) := by ring

end CriticalPointwiseIntervals
end PaperC
