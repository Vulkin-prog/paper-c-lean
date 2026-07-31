import PaperC.Asymptotics.BoundedRatioWeightedDefect

set_option maxHeartbeats 1800000

/-!
# Terminal bad starts on a fixed retained interval

This module specializes the bounded-ratio estimates of
`BoundedRatioBadStarts` and `BoundedRatioWeightedDefect` to the retained
interval

`[M / 2^j, M)`.

The only extra point is the integer rounding in `M / 2^j`.  Once this
quotient is nonzero, it lies in a bounded-ratio interval with ratio at most
`2^(j+1)`.  Consequently a critical run-length window at scale `M`
transports to the explicitly enlarged window with constant
`C + (j+1)`.
-/

namespace PaperC
namespace BoundedRatioFixedJBadStarts

open BoundedRatioBadStarts
open BoundedRatioSteinChen
open BoundedRatioWeightedDefect
open FiniteCylinderCountTransport
open TerminalPrimeCutoff

noncomputable section

/-- Explicit critical-window constant after passing from `M` to `M / 2^j`. -/
def fixedJWindowConstant (C : ℝ) (j : ℕ) : ℝ :=
  C + (j + 1 : ℕ)

theorem fixedJWindowConstant_nonneg
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    0 ≤ fixedJWindowConstant C j := by
  unfold fixedJWindowConstant
  positivity

/--
The rounding loss in `M / 2^j` costs at most one additional factor `2`.
-/
theorem fixedJ_division_upper_bound
    {M j : ℕ} (hM : 2 ^ j ≤ M) :
    M ≤ 2 ^ (j + 1) * (M / 2 ^ j) := by
  let q := 2 ^ j
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hquotient : 1 ≤ M / q := by
    rw [Nat.le_div_iff_mul_le hq]
    simpa only [one_mul] using hM
  have hstrict : M < M / q * q + q :=
    Nat.lt_div_mul_add hq
  calc
    M ≤ M / q * q + q := hstrict.le
    _ = q * (M / q) + q := by ring
    _ ≤ q * (M / q) + q * (M / q) :=
      by
        simpa only [Nat.mul_one] using
          Nat.add_le_add_left
            (Nat.mul_le_mul_left q hquotient) (q * (M / q))
    _ = 2 ^ (j + 1) * (M / 2 ^ j) := by
      dsimp only [q]
      rw [pow_succ]
      ring

/--
For `j ≥ 1`, the retained interval satisfies both bounded-ratio side
conditions used by the uniform estimates.
-/
theorem fixedJ_boundedRatio_bounds
    {M j : ℕ} (hj : 1 ≤ j) (hM : 2 ^ j ≤ M) :
    2 * (M / 2 ^ j) ≤ M ∧
      M ≤ 2 ^ (j + 1) * (M / 2 ^ j) := by
  have htwoPow : 2 ≤ 2 ^ j := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  constructor
  · calc
      2 * (M / 2 ^ j) ≤ 2 ^ j * (M / 2 ^ j) :=
        Nat.mul_le_mul_right (M / 2 ^ j) htwoPow
      _ = (M / 2 ^ j) * 2 ^ j := by ring
      _ ≤ M := Nat.div_mul_le_self M (2 ^ j)
  · exact fixedJ_division_upper_bound hM

/--
Transport of the literal critical window through the rounded quotient
`M / 2^j`.  The extra `j+1` absorbs both the scale factor `2^j` and the
single factor `2` lost to integer division.
-/
theorem inRunLengthWindow_div_twoPow
    {C : ℝ} {M L j : ℕ}
    (hM : 2 ^ j ≤ M)
    (hrun : CriticalRunWindow.InRunLengthWindow C M L) :
    CriticalRunWindow.InRunLengthWindow
      (fixedJWindowConstant C j) (M / 2 ^ j) L := by
  let N := M / 2 ^ j
  have hN : 1 ≤ N := by
    dsimp only [N]
    rw [Nat.le_div_iff_mul_le (pow_pos (by norm_num) j)]
    simpa only [one_mul] using hM
  have hNM : N ≤ M := by
    dsimp only [N]
    exact Nat.div_le_self M (2 ^ j)
  have hMN : M ≤ 2 ^ (j + 1) * N := by
    dsimp only [N]
    exact fixedJ_division_upper_bound hM
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast hN.trans hNM
  have hlogNM :
      Real.log (N : ℝ) ≤ Real.log (M : ℝ) := by
    apply Real.log_le_log hNpos
    exact_mod_cast hNM
  have hfactorPos : (0 : ℝ) < 2 ^ (j + 1) := by
    positivity
  have hlogUpper :
      Real.log (M : ℝ) ≤
        ((j + 1 : ℕ) : ℝ) * Real.log 2 +
          Real.log (N : ℝ) := by
    calc
      Real.log (M : ℝ) ≤
          Real.log (((2 ^ (j + 1) * N : ℕ) : ℝ)) := by
        apply Real.log_le_log hMpos
        exact_mod_cast hMN
      _ =
          ((j + 1 : ℕ) : ℝ) * Real.log 2 +
            Real.log (N : ℝ) := by
        norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [Real.log_mul hfactorPos.ne' hNpos.ne', Real.log_pow]
  have hlogDifferenceNonneg :
      0 ≤
        Real.log (M : ℝ) / Real.log 2 -
          Real.log (N : ℝ) / Real.log 2 := by
    exact sub_nonneg.mpr
      (div_le_div_of_nonneg_right hlogNM hlogTwo.le)
  have hlogDifferenceLe :
      Real.log (M : ℝ) / Real.log 2 -
          Real.log (N : ℝ) / Real.log 2 ≤
        ((j + 1 : ℕ) : ℝ) := by
    rw [show
      Real.log (M : ℝ) / Real.log 2 -
          Real.log (N : ℝ) / Real.log 2 =
        (Real.log (M : ℝ) - Real.log (N : ℝ)) /
          Real.log 2 by ring]
    apply (div_le_iff₀ hlogTwo).2
    linarith
  have hlogDifferenceAbs :
      |Real.log (M : ℝ) / Real.log 2 -
          Real.log (N : ℝ) / Real.log 2| ≤
        ((j + 1 : ℕ) : ℝ) := by
    rw [abs_of_nonneg hlogDifferenceNonneg]
    exact hlogDifferenceLe
  unfold CriticalRunWindow.InRunLengthWindow at hrun ⊢
  dsimp only [N] at *
  rw [show
    (L : ℝ) - Real.log (M / 2 ^ j : ℕ) / Real.log 2 =
      ((L : ℝ) - Real.log (M : ℕ) / Real.log 2) +
        (Real.log (M : ℕ) / Real.log 2 -
          Real.log (M / 2 ^ j : ℕ) / Real.log 2) by ring]
  calc
    |((L : ℝ) - Real.log (M : ℕ) / Real.log 2) +
        (Real.log (M : ℕ) / Real.log 2 -
          Real.log (M / 2 ^ j : ℕ) / Real.log 2)| ≤
        |(L : ℝ) - Real.log (M : ℕ) / Real.log 2| +
          |Real.log (M : ℕ) / Real.log 2 -
            Real.log (M / 2 ^ j : ℕ) / Real.log 2| :=
      abs_add _ _
    _ ≤ fixedJWindowConstant C j := by
      exact add_le_add hrun hlogDifferenceAbs

/--
Generic fixed-`j` specialization of uniform bounded-ratio convergence to
zero.  Its threshold absorbs the lower-scale threshold as well as the
integer-division rounding.
-/
theorem fixedJ_uniformLittleOOne_of_boundedRatio
    {C : ℝ} {j : ℕ} (hj : 1 ≤ j)
    {f : ℕ → ℕ → ℕ → ℝ}
    (hf :
      UniformLittleOOneInBoundedRatioWindow
        (fixedJWindowConstant C j) (2 ^ (j + 1)) f) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦ f (M / 2 ^ j) M L)
      (fun _ _ ↦ 1) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hf ε hε
  refine ⟨2 ^ j * max N₀ 1, ?_⟩
  intro M hM L hrun
  have hpowPos : 0 < 2 ^ j := by positivity
  have hpowM : 2 ^ j ≤ M := by
    calc
      2 ^ j = 2 ^ j * 1 := by simp
      _ ≤ 2 ^ j * max N₀ 1 :=
        Nat.mul_le_mul_left _ (le_max_right N₀ 1)
      _ ≤ M := hM
  have hN₀M : N₀ ≤ M / 2 ^ j := by
    rw [Nat.le_div_iff_mul_le hpowPos]
    calc
      N₀ * 2 ^ j ≤ max N₀ 1 * 2 ^ j :=
        Nat.mul_le_mul_right _ (le_max_left N₀ 1)
      _ = 2 ^ j * max N₀ 1 := by ring
      _ ≤ M := hM
  obtain ⟨htwo, hratio⟩ :=
    fixedJ_boundedRatio_bounds hj hpowM
  have hrunN :=
    inRunLengthWindow_div_twoPow hpowM hrun
  have hbound :=
    hN₀ (M / 2 ^ j) hN₀M M L htwo hratio hrunN
  simpa only [abs_one, mul_one] using hbound

/--
For fixed `j ≥ 1`, the normalized number of terminal bad starts in
`[M/2^j,M)` is uniformly `o_C(1)`.
-/
theorem retainedTerminalBadStarts_normalized_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) {j : ℕ} (hj : 1 ≤ j) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        ((boundedTerminalBadStarts (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) /
            (2 : ℝ) ^ L)
      (fun _ _ ↦ 1) := by
  exact
    fixedJ_uniformLittleOOne_of_boundedRatio
      (C := C) (j := j) hj
      (normalized_boundedTerminalBadStarts_uniformLittleOOne
        (fixedJWindowConstant_nonneg hC j) (2 ^ (j + 1)))

/--
For fixed `j ≥ 1`, the normalized weighted terminal-defect mass is
uniformly `o_C(1)`.
-/
theorem retainedTerminalDefectWeightMass_normalized_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) {j : ℕ} (hj : 1 ≤ j) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        2 * boundedTerminalDefectWeightMass
          (M / 2 ^ j) M L (L + 1) /
            (2 : ℝ) ^ L)
      (fun _ _ ↦ 1) := by
  exact
    fixedJ_uniformLittleOOne_of_boundedRatio
      (C := C) (j := j) hj
      (normalized_boundedTerminalDefectWeightMass_uniformLittleOOne
        (fixedJWindowConstant_nonneg hC j) (2 ^ (j + 1)))

/--
The same conclusion without the harmless factor `2` used in the probability
majorant.
-/
theorem retainedTerminalDefectWeightMass_div_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) {j : ℕ} (hj : 1 ≤ j) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        boundedTerminalDefectWeightMass
          (M / 2 ^ j) M L (L + 1) /
            (2 : ℝ) ^ L)
      (fun _ _ ↦ 1) := by
  have htwice :=
    retainedTerminalDefectWeightMass_normalized_uniformLittleOOne hC hj
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := htwice ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L hrun
  have hbound := hM₀ M hM L hrun
  have hweightNonneg :
      0 ≤
        boundedTerminalDefectWeightMass
          (M / 2 ^ j) M L (L + 1) := by
    unfold boundedTerminalDefectWeightMass
    positivity
  have hmassNonneg :
      0 ≤
        boundedTerminalDefectWeightMass
          (M / 2 ^ j) M L (L + 1) /
            (2 : ℝ) ^ L := by
    exact div_nonneg hweightNonneg (by positivity)
  rw [abs_of_nonneg hmassNonneg]
  simp only [abs_one, mul_one]
  rw [abs_of_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hweightNonneg)
      (by positivity))] at hbound
  simp only [abs_one, mul_one] at hbound
  calc
    boundedTerminalDefectWeightMass
          (M / 2 ^ j) M L (L + 1) /
          (2 : ℝ) ^ L ≤
        2 *
          (boundedTerminalDefectWeightMass
            (M / 2 ^ j) M L (L + 1) /
            (2 : ℝ) ^ L) := by
      linarith
    _ =
        2 * boundedTerminalDefectWeightMass
          (M / 2 ^ j) M L (L + 1) /
            (2 : ℝ) ^ L := by ring
    _ ≤ ε := hbound

/--
For fixed `j ≥ 1`, the complete probability mass of terminal bad starts
in `[M/2^j,M)` is uniformly `o_C(1)`.
-/
theorem retainedBadStartProbabilityMass_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) {j : ℕ} (hj : 1 ≤ j) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        boundedBadStartProbabilityMass
          (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1)))
      (fun _ _ ↦ 1) := by
  exact
    fixedJ_uniformLittleOOne_of_boundedRatio
      (C := C) (j := j) hj
      (boundedBadStartProbabilityMass_uniformLittleOOne
        (fixedJWindowConstant_nonneg hC j) (2 ^ (j + 1)))

/--
Exact fixed-`j` mean decomposition at the terminal cutoff.
-/
theorem retainedFullStartMean_eq_goodParameter_add_badMass
    {M L j : ℕ}
    (hbase : 2 ≤ M / 2 ^ j) (hL : 0 < L) :
    boundedFullStartMean (M / 2 ^ j) M L =
      ((boundedGoodStarts (M / 2 ^ j) M L
        (terminalPrimeCutoff (L + 1))).card : ℝ) /
          (2 : ℝ) ^ L +
        boundedBadStartProbabilityMass
          (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1)) := by
  apply boundedFullStartMean_eq_goodParameter_add_badMass hbase hL
  exact le_terminalPrimeCutoff (by omega)

/--
The exact mean decomposition with the good cardinal eliminated by the
good/bad partition.
-/
theorem retainedFullStartMean_eq_length_sub_badCard_add_badMass
    {M L j : ℕ}
    (hbase : 2 ≤ M / 2 ^ j) (hL : 0 < L) :
    boundedFullStartMean (M / 2 ^ j) M L =
      (((M - M / 2 ^ j) -
        (boundedTerminalBadStarts (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1))).card : ℕ) : ℝ) /
          (2 : ℝ) ^ L +
        boundedBadStartProbabilityMass
          (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1)) := by
  rw [retainedFullStartMean_eq_goodParameter_add_badMass hbase hL]
  have hpartition :=
    card_boundedGood_add_card_boundedBad
      (L := L) (Y := terminalPrimeCutoff (L + 1))
      (Nat.div_le_self M (2 ^ j))
  have hgoodCard :
      (boundedGoodStarts (M / 2 ^ j) M L
        (terminalPrimeCutoff (L + 1))).card =
      (M - M / 2 ^ j) -
        (boundedTerminalBadStarts (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1))).card := by
    omega
  rw [hgoodCard]

/--
Exact correction of the retained-length parameter: the mean error is the
bad-start probability mass minus the normalized bad-start cardinal.
-/
theorem retainedFullStartMean_sub_lengthParameter_eq
    {M L j : ℕ}
    (hbase : 2 ≤ M / 2 ^ j) (hL : 0 < L) :
    boundedFullStartMean (M / 2 ^ j) M L -
        ((M - M / 2 ^ j : ℕ) : ℝ) / (2 : ℝ) ^ L =
      boundedBadStartProbabilityMass
          (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1)) -
        ((boundedTerminalBadStarts (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) /
            (2 : ℝ) ^ L := by
  rw [retainedFullStartMean_eq_goodParameter_add_badMass hbase hL]
  have hpartition :
      ((boundedGoodStarts (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) +
        ((boundedTerminalBadStarts (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) =
        ((M - M / 2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast
      card_boundedGood_add_card_boundedBad
        (L := L) (Y := terminalPrimeCutoff (L + 1))
        (Nat.div_le_self M (2 ^ j))
  rw [← hpartition]
  ring

/--
For fixed `j ≥ 1`, the exact retained mean has the deterministic parameter
`|[M/2^j,M)| / 2^L` up to a uniform `o_C(1)` error.
-/
theorem retainedFullStartMean_sub_lengthParameter_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) {j : ℕ} (hj : 1 ≤ j) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        boundedFullStartMean (M / 2 ^ j) M L -
          ((M - M / 2 ^ j : ℕ) : ℝ) / (2 : ℝ) ^ L)
      (fun _ _ ↦ 1) := by
  have hmass :=
    retainedBadStartProbabilityMass_uniformLittleOOne hC hj
  have hcard :=
    retainedTerminalBadStarts_normalized_uniformLittleOOne hC hj
  obtain ⟨Mwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Mmass, hmassBound⟩ := hmass (ε / 2) (by positivity)
  obtain ⟨Mcard, hcardBound⟩ := hcard (ε / 2) (by positivity)
  refine
    ⟨max (2 ^ (j + 1))
      (max Mwindow (max Mmass Mcard)), ?_⟩
  intro M hM L hrun
  have hbase : 2 ≤ M / 2 ^ j := by
    rw [Nat.le_div_iff_mul_le (pow_pos (by norm_num) j)]
    calc
      2 * 2 ^ j = 2 ^ (j + 1) := by
        rw [pow_succ]
        ring
      _ ≤ M :=
        (le_max_left (2 ^ (j + 1))
          (max Mwindow (max Mmass Mcard))).trans hM
  have htail :
      max Mwindow (max Mmass Mcard) ≤ M :=
    (le_max_right (2 ^ (j + 1))
      (max Mwindow (max Mmass Mcard))).trans hM
  have hw :=
    hwindow M ((le_max_left _ _).trans htail) L hrun
  have htail' :
      max Mmass Mcard ≤ M :=
    (le_max_right Mwindow (max Mmass Mcard)).trans htail
  have hm :=
    hmassBound M ((le_max_left _ _).trans htail') L hrun
  have hc :=
    hcardBound M ((le_max_right _ _).trans htail') L hrun
  simp only [abs_one, mul_one] at hm hc ⊢
  rw [retainedFullStartMean_sub_lengthParameter_eq hbase hw.2.1]
  calc
    |boundedBadStartProbabilityMass
          (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1)) -
        ((boundedTerminalBadStarts (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) /
            (2 : ℝ) ^ L| ≤
        |boundedBadStartProbabilityMass
          (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1))| +
        |((boundedTerminalBadStarts (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) /
            (2 : ℝ) ^ L| :=
      abs_sub _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hm hc
    _ = ε := by ring

end

end BoundedRatioFixedJBadStarts
end PaperC
