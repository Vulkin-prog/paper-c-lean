import PaperC.Asymptotics.PropositionSixteenOneCore
import PaperC.Asymptotics.CorrectedDefectEnvelope
import PaperC.Combinatorics.DefectiveVertexIntervalBound

set_option maxHeartbeats 2400000

/-!
# Uniform corrected-defect envelope on bounded-ratio intervals

The dyadic envelope in `CorrectedDefectEnvelope` is not directly applicable
to a pair whose two coordinates lie in different dyadic shells.  This file
therefore repeats the pointwise scale transport at the exact level needed by
Section 17.

For fixed `κ₀`, every interval beginning at `x - 1`, with
`N ≤ x < κ₀ N`, lies between polynomially comparable scales once `N` is
large.  The critical window and the logarithmic pointwise scale may then be
transported from `N` to `x - 1`.  Taking a finite supremum over the complete
bounding block `[N, κ₀N)` gives a single envelope which dominates every
subinterval `[N,M)` with `M ≤ κ₀N`.
-/

namespace PaperC
namespace BoundedRatioCorrectedDefectEnvelope

open Affine
open PropositionSixteenOne
open ResidualComponentCounts

noncomputable section

/-! ## Polynomially comparable scales -/

/--
The critical window at `N` remains a fixed wider critical window at `U`
when `N ≤ 2U` and the two scales are polynomially comparable.
-/
theorem criticalWindow_transport_of_sq_bounds
    {c₁ c₂ : ℝ} {N H U : ℕ}
    (hc₁ : 0 < c₁)
    (hc₁c₂ : c₁ < c₂)
    (hwindow :
      CriticalWindowParameters.InCriticalWindow c₁ c₂ N H)
    (hUlog : 0 < Real.log U)
    (hNtwoU : N ≤ 2 * U)
    (hUNsq : U ≤ N * N) :
    CriticalWindowParameters.InCriticalWindow
      (c₁ / 2) (2 * c₂) U H := by
  have hUtwo : 2 ≤ U := by
    have honeU : (1 : ℝ) < (U : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg U)).mp hUlog
    exact_mod_cast honeU
  have hNU_sq : N ≤ U * U := by
    have htwoU_le : 2 * U ≤ U * U := by
      nlinarith
    exact hNtwoU.trans htwoU_le
  have hNpos : 0 < (N : ℝ) := by
    have hNpositive : 0 < N := by
      by_contra hN
      have hNzero : N = 0 := Nat.eq_zero_of_not_pos hN
      subst N
      simp only [zero_mul] at hUNsq
      omega
    positivity
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
The scale `log U / loglog U` changes by at most a factor four under the same
polynomial comparison.  This is the exact logarithmic calculation used in
the dyadic pointwise transport, with the upper square bound exposed.
-/
theorem log_div_loglog_le_four_of_sq_bounds
    {N U : ℕ}
    (hNlog : 4 < Real.log N)
    (hUlog : 4 < Real.log U)
    (hNtwoU : N ≤ 2 * U)
    (hUNsq : U ≤ N * N) :
    Real.log U / Real.log (Real.log U) ≤
      4 * (Real.log N / Real.log (Real.log N)) := by
  have hUtwo : 2 ≤ U := by
    have honeU : (1 : ℝ) < (U : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg U)).mp (by linarith)
    exact_mod_cast honeU
  have hNU_sq : N ≤ U * U := by
    have htwoU_le : 2 * U ≤ U * U := by
      nlinarith
    exact hNtwoU.trans htwoU_le
  have hNpos : 0 < (N : ℝ) := by
    have honeN : (1 : ℝ) < (N : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
    positivity
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
Pointwise defect count on every interval whose left endpoint is between
`N/2` and `N²`.  The constants are uniform in the interval and its length.
-/
theorem pointwise_all_intervals_of_sq_bounds
    {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁)
    (hc₁c₂ : c₁ < c₂) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H,
        CriticalWindowParameters.InCriticalWindow c₁ c₂ N H →
        ∀ U, N ≤ 2 * U → U + H ≤ N * N →
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
    (lt_mul_of_one_lt_left (Real.exp_pos 4)
      (by norm_num : (1 : ℝ) < 2)).trans hNlarge
  have hNlog : 4 < Real.log N := by
    have hmono := Real.log_lt_log (Real.exp_pos 4) hNexp
    simpa only [Real.log_exp] using hmono
  have hUlog : 4 < Real.log U := by
    have hmono := Real.log_lt_log (Real.exp_pos 4) hUlarge
    simpa only [Real.log_exp] using hmono
  have hUNsq : U ≤ N * N := by omega
  have hwindowU :
      CriticalWindowParameters.InCriticalWindow
        (c₁ / 2) (2 * c₂) U H :=
    criticalWindow_transport_of_sq_bounds
      hc₁ hc₁c₂ hwindow (by linarith) hNtwoU hUNsq
  have hUpoint : Npoint ≤ U := by omega
  have hcanonical := hpoint U hUpoint H hwindowU
  have hscale :=
    log_div_loglog_le_four_of_sq_bounds
      hNlog hUlog hNtwoU hUNsq
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

/-! ## A single finite envelope for every endpoint `M ≤ κ₀N` -/

/--
Largest corrected-defect count in the complete bounding block
`[N, κ₀N)`.  It dominates all smaller endpoint choices.
-/
noncomputable def maxCanonicalCorrectedDefectCount
    (κ₀ A N L : ℕ) : ℕ :=
  (separatedBoundedRatioPairs N (κ₀ * N) L).sup fun pair =>
    canonicalCorrectedDefectCount A pair.1 pair.2 L

/-- Every pair in a bounded-ratio subinterval is bounded by the envelope. -/
theorem canonicalCorrectedDefectCount_le_max
    {κ₀ A N M L x y : ℕ}
    (hM : M ≤ κ₀ * N)
    (hpair : (x, y) ∈ separatedBoundedRatioPairs N M L) :
    canonicalCorrectedDefectCount A x y L ≤
      maxCanonicalCorrectedDefectCount κ₀ A N L := by
  unfold maxCanonicalCorrectedDefectCount
  have hbig :
      (x, y) ∈ separatedBoundedRatioPairs N (κ₀ * N) L := by
    have hp :=
      PropositionSixteenOne.mem_separatedBoundedRatioPairs.mp hpair
    apply
      PropositionSixteenOne.mem_separatedBoundedRatioPairs.mpr
    refine ⟨?_, ?_, hp.2.2⟩
    · apply PropositionSixteenOne.mem_boundedRatioBlock.mpr
      exact
        ⟨(PropositionSixteenOne.mem_boundedRatioBlock.mp hp.1).1,
          (PropositionSixteenOne.mem_boundedRatioBlock.mp hp.1).2.trans_le
            hM⟩
    · apply PropositionSixteenOne.mem_boundedRatioBlock.mpr
      exact
        ⟨(PropositionSixteenOne.mem_boundedRatioBlock.mp hp.2.1).1,
          (PropositionSixteenOne.mem_boundedRatioBlock.mp hp.2.1).2.trans_le
            hM⟩
  exact Finset.le_sup
    (f := fun pair : ℕ × ℕ =>
      canonicalCorrectedDefectCount A pair.1 pair.2 L)
    hbig

/-- A pointwise real bound passes to the finite bounded-ratio maximum. -/
theorem maxCanonicalCorrectedDefectCount_cast_le
    {κ₀ A N L : ℕ} {R : ℝ}
    (hR : 0 ≤ R)
    (hpoint :
      ∀ pair ∈ separatedBoundedRatioPairs N (κ₀ * N) L,
        (canonicalCorrectedDefectCount
            A pair.1 pair.2 L : ℝ) ≤ R) :
    (maxCanonicalCorrectedDefectCount κ₀ A N L : ℝ) ≤ R := by
  classical
  have aux :
      ∀ s : Finset (ℕ × ℕ),
        (∀ pair ∈ s,
          (canonicalCorrectedDefectCount
              A pair.1 pair.2 L : ℝ) ≤ R) →
        ((s.sup fun pair =>
            canonicalCorrectedDefectCount
              A pair.1 pair.2 L : ℕ) : ℝ) ≤ R := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _h
        simpa using hR
    | @insert pair s hpairNotMem ih =>
        intro hs
        rw [Finset.sup_insert, Nat.cast_max]
        apply max_le
        · exact hs pair (Finset.mem_insert_self pair s)
        · apply ih
          intro other hother
          exact hs other (Finset.mem_insert_of_mem hother)
  exact aux (separatedBoundedRatioPairs N (κ₀ * N) L) hpoint

/--
Uniform logarithm-over-logarithm bound for the corrected defect throughout
the complete bounded-ratio block.
-/
theorem maxCanonicalCorrectedDefectCount_log_bound_eventually
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
        CriticalRunWindow.InRunLengthWindow C N L →
        ∀ A,
          (maxCanonicalCorrectedDefectCount κ₀ A N L : ℝ) ≤
            K * (Real.log N / Real.log (Real.log N)) := by
  let c₁ := CriticalRunWindow.lowerConstant
  let c₂ := CriticalRunWindow.upperConstant
  have hc₁ : 0 < c₁ := by
    simpa only [c₁] using CriticalRunWindow.lowerConstant_pos
  have hc₁c₂ : c₁ < c₂ := by
    simpa only [c₁, c₂] using
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Kpoint, hKpoint, Npoint, hpoint⟩ :=
    pointwise_all_intervals_of_sq_bounds hc₁ hc₁c₂
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  have hc₂ : 0 ≤ c₂ := hc₁.le.trans hc₁c₂.le
  obtain ⟨Nlength, hlength⟩ :=
    ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually
      c₂ hc₂ 1 (by omega)
  obtain ⟨Nlog, hNlog⟩ :=
    exists_nat_gt (Real.exp (Real.exp 0))
  let N₀ :=
    max Nwindow
      (max Nlength
        (max Nlog
          (max Npoint (max (κ₀ + 2) 4))))
  refine ⟨2 * Kpoint, by positivity, N₀, ?_⟩
  intro N hN L hrun A
  have hNwindow : Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have htail :
      max Nlength
        (max Nlog (max Npoint (max (κ₀ + 2) 4))) ≤ N :=
    (le_max_right _ _).trans hN
  have hNlength : Nlength ≤ N :=
    (le_max_left _ _).trans htail
  have htail₂ :
      max Nlog (max Npoint (max (κ₀ + 2) 4)) ≤ N :=
    (le_max_right _ _).trans htail
  have hNlogN : Nlog ≤ N :=
    (le_max_left _ _).trans htail₂
  have htail₃ : max Npoint (max (κ₀ + 2) 4) ≤ N :=
    (le_max_right _ _).trans htail₂
  have hNpointN : Npoint ≤ N :=
    (le_max_left _ _).trans htail₃
  have htail₄ : max (κ₀ + 2) 4 ≤ N :=
    (le_max_right _ _).trans htail₃
  have hNkappa : κ₀ + 2 ≤ N :=
    (le_max_left _ _).trans htail₄
  have hNfour : 4 ≤ N :=
    (le_max_right _ _).trans htail₄
  have hfirst := hwindow N hNwindow L hrun
  have hcritical :
      CriticalWindowParameters.InCriticalWindow c₁ c₂ N (L + 1) := by
    simpa only [c₁, c₂] using hfirst.1
  have hlength' :=
    hlength N hNlength (L + 1) hfirst.1.2.2.2
  have hLheight : L + 1 ≤ N := by
    norm_num only [pow_one, Nat.cast_add, Nat.cast_one] at hlength'
    have hnat : (L + 1) + 1 ≤ N := by
      exact_mod_cast hlength'
    omega
  have hthreshold :
      Real.exp (Real.exp 0) < (N : ℝ) :=
    hNlog.trans_le (by exact_mod_cast hNlogN)
  have hlogN :
      Real.exp 0 < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos (Real.exp 0)) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hlogNpos : 0 < Real.log N :=
    (Real.exp_pos 0).trans hlogN
  have hloglogNpos : 0 < Real.log (Real.log N) := by
    have hone : 1 < Real.log N := by
      simpa only [Real.exp_zero] using hlogN
    exact Real.log_pos hone
  have hscaleNonneg :
      0 ≤ Real.log N / Real.log (Real.log N) :=
    div_nonneg hlogNpos.le hloglogNpos.le
  apply maxCanonicalCorrectedDefectCount_cast_le
    (mul_nonneg (mul_nonneg (by norm_num) hKpoint) hscaleNonneg)
  intro pair hpair
  have hp := mem_separatedBoundedRatioPairs.mp hpair
  have hx := mem_boundedRatioBlock.mp hp.1
  have hy := mem_boundedRatioBlock.mp hp.2.1
  have hxPos : 1 ≤ pair.1 := by omega
  have hyPos : 1 ≤ pair.2 := by omega
  have hxLower : N ≤ 2 * (pair.1 - 1) := by omega
  have hyLower : N ≤ 2 * (pair.2 - 1) := by omega
  have hxContained : (pair.1 - 1) + (L + 1) ≤ N * N := by
    have hxUpper : pair.1 < κ₀ * N := hx.2
    have hlinear : κ₀ * N + N ≤ N * N := by
      nlinarith
    omega
  have hyContained : (pair.2 - 1) + (L + 1) ≤ N * N := by
    have hyUpper : pair.2 < κ₀ * N := hy.2
    have hlinear : κ₀ * N + N ≤ N * N := by
      nlinarith
    omega
  have hleft :=
    hpoint N hNpointN (L + 1) hcritical
      (pair.1 - 1) hxLower hxContained
  have hright :=
    hpoint N hNpointN (L + 1) hcritical
      (pair.2 - 1) hyLower hyContained
  have hfinite :=
    DefectiveVertexIntervalBound.canonicalCorrectedDefectCount_le_interval_sum
      (L := L) A hxPos hyPos
  have hcast :
      (canonicalCorrectedDefectCount A pair.1 pair.2 L : ℝ) ≤
        ((IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1 - 1)).card : ℝ) +
        ((IntervalDefectBound.defectsInInterval
            (L + 1) (pair.2 - 1)).card : ℝ) := by
    exact_mod_cast hfinite
  calc
    (canonicalCorrectedDefectCount A pair.1 pair.2 L : ℝ) ≤
        ((IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1 - 1)).card : ℝ) +
        ((IntervalDefectBound.defectsInInterval
            (L + 1) (pair.2 - 1)).card : ℝ) :=
      hcast
    _ ≤
        Kpoint * (Real.log N / Real.log (Real.log N)) +
          Kpoint * (Real.log N / Real.log (Real.log N)) :=
      add_le_add hleft hright
    _ =
        (2 * Kpoint) *
          (Real.log N / Real.log (Real.log N)) := by ring

/--
The bounded-ratio corrected-defect loss is uniformly subpolynomial:
`4^(max D#) = N^o(1)`.
-/
theorem four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (((4 ^
          maxCanonicalCorrectedDefectCount κ₀ A N L : ℕ) : ℝ))) := by
  obtain ⟨K, hK, Nbound, hbound⟩ :=
    maxCanonicalCorrectedDefectCount_log_bound_eventually hC κ₀
  have htwo :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          (((2 ^
            (2 * maxCanonicalCorrectedDefectCount κ₀ A N L) :
              ℕ) : ℝ))) := by
    apply
      ExpSqrtLog.uniformSubpolynomialOn_two_pow_log_div_loglog_eventually
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          2 * maxCanonicalCorrectedDefectCount κ₀ A N L)
        (2 * K) (mul_nonneg (by norm_num) hK)
    refine ⟨Nbound, ?_⟩
    intro N hN L hrun
    have hmax := hbound N hN L hrun A
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      2 * (maxCanonicalCorrectedDefectCount κ₀ A N L : ℝ) ≤
          2 * (K * (Real.log N / Real.log (Real.log N))) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ =
          (2 * K) * Real.log N / Real.log (Real.log N) := by
        ring
  simpa [pow_mul, pow_two] using htwo

end

end BoundedRatioCorrectedDefectEnvelope
end PaperC
