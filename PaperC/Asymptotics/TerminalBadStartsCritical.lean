import PaperC.Asymptotics.DependencyEdgesCritical
import PaperC.Asymptotics.ExpSqrtLog
import PaperC.Asymptotics.RationalPowerLittleO
import PaperC.Probability.TerminalBadStartBound

/-!
# Terminal bad starts in the critical run-length window

This file closes the asymptotic step in Lemma 13.3.  The finite estimate in
`TerminalBadStartBound` contains the readable exponential loss

`exp (2 (B² log B)^(1/4) + 168 sqrt 2 B / sqrt(log B))`.

For every integral accuracy parameter `m`, once

* `m⁴ ≤ B`, and
* `exp(m²) ≤ B`,

that exponent is at most `(2 + 168 sqrt 2) B / m`.  Since
`B = L+1 = O_C(log N)` and `B` tends uniformly to infinity in the critical
window, the exponential loss is uniformly subpolynomial.  Combining this
with the finite square-root estimate proves the literal
`N^(1/2+o_C(1))` assertion and its two consequences
`#D_Y = o_C(N)` and `2^{-L} #D_Y = o_C(1)`.
-/

namespace PaperC
namespace TerminalBadStartsCritical

open TerminalPrimeCutoff
open TerminalBadStartBound
open BadStartCount

noncomputable section

/--
The readable terminal exponent has an arbitrarily small linear coefficient
once the height is large enough.
-/
theorem terminalBadStartReadableExponent_le_div
    {B m : ℕ}
    (hm : 1 ≤ m)
    (hmfour : m ^ 4 ≤ B)
    (hexp : Real.exp ((m : ℝ) ^ 2) ≤ (B : ℝ)) :
    terminalBadStartReadableExponent B ≤
      (2 + 168 * Real.sqrt 2) * (B : ℝ) / (m : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hmfourReal : (m : ℝ) ^ 4 ≤ (B : ℝ) := by
    exact_mod_cast hmfour
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    have : (0 : ℝ) < (m : ℝ) ^ 4 := pow_pos hmpos _
    exact this.trans_le hmfourReal
  have hscaleCube :
      terminalPrimeScale B ≤ (B : ℝ) ^ 3 := by
    change (B : ℝ) ^ 2 * Real.log (B : ℝ) ≤ (B : ℝ) ^ 3
    calc
      (B : ℝ) ^ 2 * Real.log (B : ℝ) ≤
          (B : ℝ) ^ 2 * (B : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_self hBpos.le) (sq_nonneg (B : ℝ))
      _ = (B : ℝ) ^ 3 := by ring
  have hcubeDiv :
      (B : ℝ) ^ 3 ≤ ((B : ℝ) / (m : ℝ)) ^ 4 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos hmpos 4)).2
    calc
      (B : ℝ) ^ 3 * (m : ℝ) ^ 4 ≤
          (B : ℝ) ^ 3 * (B : ℝ) :=
        mul_le_mul_of_nonneg_left hmfourReal (by positivity)
      _ = (B : ℝ) ^ 4 := by ring
  have hfourthRoot :
      Real.sqrt (Real.sqrt (terminalPrimeScale B)) ≤
        (B : ℝ) / (m : ℝ) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨(div_nonneg hBpos.le hmpos.le), ?_⟩
    apply (Real.sqrt_le_iff).2
    refine ⟨sq_nonneg ((B : ℝ) / (m : ℝ)), ?_⟩
    calc
      terminalPrimeScale B ≤ (B : ℝ) ^ 3 := hscaleCube
      _ ≤ ((B : ℝ) / (m : ℝ)) ^ 4 := hcubeDiv
      _ = (((B : ℝ) / (m : ℝ)) ^ 2) ^ 2 := by ring
  have hlog :
      (m : ℝ) ^ 2 ≤ Real.log (B : ℝ) := by
    have hlogMono :=
      Real.log_le_log (Real.exp_pos ((m : ℝ) ^ 2)) hexp
    simpa only [Real.log_exp] using hlogMono
  have hsqrtLog :
      (m : ℝ) ≤ Real.sqrt (Real.log (B : ℝ)) := by
    exact Real.le_sqrt_of_sq_le hlog
  have hfirst :
      2 * Real.sqrt (Real.sqrt (terminalPrimeScale B)) ≤
        2 * (B : ℝ) / (m : ℝ) := by
    calc
      2 * Real.sqrt (Real.sqrt (terminalPrimeScale B)) ≤
          2 * ((B : ℝ) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hfourthRoot (by norm_num)
      _ = 2 * (B : ℝ) / (m : ℝ) := by ring
  have hcoefficientNonneg :
      0 ≤ 168 * Real.sqrt 2 * (B : ℝ) := by positivity
  have hsecond :
      168 * Real.sqrt 2 * (B : ℝ) /
          Real.sqrt (Real.log (B : ℝ)) ≤
        168 * Real.sqrt 2 * (B : ℝ) / (m : ℝ) := by
    exact div_le_div_of_nonneg_left
      hcoefficientNonneg hmpos hsqrtLog
  unfold terminalBadStartReadableExponent
  calc
    2 * Real.sqrt (Real.sqrt (terminalPrimeScale B)) +
          168 * Real.sqrt 2 * (B : ℝ) /
            Real.sqrt (Real.log (B : ℝ)) ≤
        2 * (B : ℝ) / (m : ℝ) +
          168 * Real.sqrt 2 * (B : ℝ) / (m : ℝ) :=
      add_le_add hfirst hsecond
    _ = (2 + 168 * Real.sqrt 2) * (B : ℝ) / (m : ℝ) := by
      ring

/--
The exponential loss in the terminal bad-start estimate is uniformly
subpolynomial in the literal critical run-length window.
-/
theorem terminalExponentFactor_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L =>
        Real.exp
          (terminalBadStartReadableExponent (L + 1))) := by
  intro k hk
  let A : ℝ :=
    2 + 168 * Real.sqrt 2
  have hApos : 0 < A := by
    dsimp only [A]
    positivity
  have hupperPos : 0 < CriticalRunWindow.upperConstant :=
    CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨m : ℕ, hmLarge⟩ :=
    exists_nat_gt
      ((k : ℝ) * A * CriticalRunWindow.upperConstant)
  have hm : 1 ≤ m := by
    have hpositive :
        0 <
          (k : ℝ) * A * CriticalRunWindow.upperConstant := by
      positivity
    have hmpos : (0 : ℝ) < (m : ℝ) :=
      hpositive.trans hmLarge
    exact_mod_cast hmpos
  let M : ℕ := ⌈Real.exp ((m : ℝ) ^ 2)⌉₊
  obtain ⟨Nfour, hfour⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC (m ^ 4)
  obtain ⟨Nexp, hexpHeight⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC M
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  refine ⟨max Nwindow (max Nfour Nexp), ?_⟩
  intro N hN L hrun
  have hNtail :
      max Nfour Nexp ≤ N :=
    (le_max_right Nwindow (max Nfour Nexp)).trans hN
  have hmfour :
      m ^ 4 ≤ L + 1 :=
    hfour N ((le_max_left Nfour Nexp).trans hNtail) L hrun
  have hM :
      M ≤ L + 1 :=
    hexpHeight N ((le_max_right Nfour Nexp).trans hNtail) L hrun
  have hexp :
      Real.exp ((m : ℝ) ^ 2) ≤ (((L + 1 : ℕ) : ℝ)) := by
    calc
      Real.exp ((m : ℝ) ^ 2) ≤ (M : ℝ) := by
        exact Nat.le_ceil _
      _ ≤ (((L + 1 : ℕ) : ℝ)) := by
        exact_mod_cast hM
  have hreadable :=
    terminalBadStartReadableExponent_le_div hm hmfour hexp
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hheight :
      (((L + 1 : ℕ) : ℝ)) ≤
        CriticalRunWindow.upperConstant * Real.log N :=
    hw.1.2.2.2
  have hlogNpos : 0 < Real.log (N : ℝ) := by
    have hBpos : (0 : ℝ) < (((L + 1 : ℕ) : ℝ)) := by positivity
    have :
        0 <
          CriticalRunWindow.upperConstant * Real.log (N : ℝ) :=
      hBpos.trans_le hheight
    by_contra h
    have hlogNonpos : Real.log (N : ℝ) ≤ 0 := le_of_not_gt h
    have hproductNonpos :
        CriticalRunWindow.upperConstant * Real.log (N : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hupperPos.le hlogNonpos
    exact (not_lt_of_ge hproductNonpos) this
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hcoefficient :
      (k : ℝ) * A * CriticalRunWindow.upperConstant / (m : ℝ) < 1 := by
    exact (div_lt_one hmpos).2 hmLarge
  have hexponent :
      (k : ℝ) *
          terminalBadStartReadableExponent (L + 1) ≤
        Real.log N := by
    calc
      (k : ℝ) *
            terminalBadStartReadableExponent (L + 1) ≤
          (k : ℝ) *
            (A * (((L + 1 : ℕ) : ℝ)) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hreadable (Nat.cast_nonneg k)
      _ ≤
          (k : ℝ) *
            (A *
              (CriticalRunWindow.upperConstant * Real.log N) /
                (m : ℝ)) := by
        gcongr
      _ =
          ((k : ℝ) * A * CriticalRunWindow.upperConstant / (m : ℝ)) *
            Real.log N := by ring
      _ ≤ 1 * Real.log N :=
        mul_le_mul_of_nonneg_right hcoefficient.le hlogNpos.le
      _ = Real.log N := one_mul _
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hNone : (1 : ℝ) < (N : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg N)).mp hlogNpos
    exact zero_lt_one.trans hNone
  rw [abs_of_pos (Real.exp_pos _)]
  calc
    (Real.exp
          (terminalBadStartReadableExponent (L + 1))) ^ k =
        Real.exp
          ((k : ℝ) *
            terminalBadStartReadableExponent (L + 1)) := by
      rw [Real.exp_nat_mul]
    _ ≤
        Real.exp (Real.log N) :=
      Real.exp_le_exp.mpr hexponent
    _ = (N : ℝ) := Real.exp_log hNpos

/-- The subpolynomial residual left after extracting `sqrt N`. -/
noncomputable def terminalBadStartResidual
    (_C : ℝ) (_N L : ℕ) : ℝ :=
  2 * Real.sqrt 3 *
    ((((L + 1 : ℕ) : ℝ)) *
      Real.exp
        (terminalBadStartReadableExponent (L + 1)))

theorem terminalBadStartResidual_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (terminalBadStartResidual C) := by
  have hheight :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial hC
  have hexponential :=
    terminalExponentFactor_uniformSubpolynomial hC
  unfold terminalBadStartResidual
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      (2 * Real.sqrt 3)
      (ExpSqrtLog.uniformSubpolynomialOn_mul hheight hexponential)

/--
Strong form of Lemma 13.3:

`#D_Y = N^(1/2+o_C(1))`

at `Y = floor((L+1)² log(L+1))`, uniformly in the literal critical window.
-/
theorem terminalBadStarts_terminalCutoff_uniformHalfPower
    {C : ℝ} (hC : 0 ≤ C) :
    UniformHalfPowerSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ((terminalBadStarts N L
          (terminalPrimeCutoff (L + 1))).card : ℝ)) := by
  apply UniformHalfPower.of_sqrt_mul_subpolynomial
    (terminalBadStartResidual_uniformSubpolynomial hC)
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nsixteen, hsixteen⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity hC 16
  refine ⟨max Nwindow (max Nadm Nsixteen), ?_⟩
  intro N hN L hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hNtail :
      max Nadm Nsixteen ≤ N :=
    (le_max_right Nwindow (max Nadm Nsixteen)).trans hN
  have hAdm :=
    hadm N ((le_max_left Nadm Nsixteen).trans hNtail)
      (L + 1) hw.1
  have hB :
      16 ≤ L + 1 :=
    hsixteen N ((le_max_right Nadm Nsixteen).trans hNtail) L hrun
  have htwoB : 2 * (L + 1) ≤ N :=
    CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
      hAdm.1 hAdm.2.2.2.1
  have hcutoff :
      dyadicCutoff N L ≤ 3 * N := by
    unfold dyadicCutoff
    omega
  have hsqrtCutoff :
      Real.sqrt (dyadicCutoff N L) ≤
        Real.sqrt 3 * Real.sqrt N := by
    calc
      Real.sqrt (dyadicCutoff N L) ≤
          Real.sqrt (((3 * N : ℕ) : ℝ)) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast hcutoff
      _ = Real.sqrt 3 * Real.sqrt N := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hfinite :=
    card_terminalBadStarts_terminalPrimeCutoff_le_readable
      (N := N) (L := L) (B := L + 1)
      (by omega) hB
  rw [abs_of_nonneg (by positivity),
    abs_of_nonneg (by
      unfold terminalBadStartResidual
      positivity)]
  calc
    ((terminalBadStarts N L
        (terminalPrimeCutoff (L + 1))).card : ℝ) ≤
        2 * L * Real.sqrt (dyadicCutoff N L) *
          Real.exp (terminalBadStartReadableExponent (L + 1)) :=
      hfinite
    _ ≤
        2 * (L + 1) *
          (Real.sqrt 3 * Real.sqrt N) *
          Real.exp (terminalBadStartReadableExponent (L + 1)) := by
      gcongr
      exact_mod_cast Nat.le_succ L
    _ = Real.sqrt N * terminalBadStartResidual C N L := by
      unfold terminalBadStartResidual
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring

/-- Lemma 13.3 in the weaker manuscript form `#D_Y = o_C(N)`. -/
theorem terminalBadStarts_terminalCutoff_uniformLittleOLinear
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ((terminalBadStarts N L
          (terminalPrimeCutoff (L + 1))).card : ℝ))
      (fun N _ => (N : ℝ)) := by
  have hhalf :=
    terminalBadStarts_terminalCutoff_uniformHalfPower hC
  have hrat :
      UniformRationalPowerSubpolynomialOn 1 2
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          ((terminalBadStarts N L
            (terminalPrimeCutoff (L + 1))).card : ℝ)) := by
    simpa [UniformHalfPowerSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn] using hhalf
  simpa only [pow_one] using
    (UniformRationalPower.littleO_natPower_of_lt
      (p := 1) (q := 2) (r := 1) (by omega) hrat)

/--
The normalized cardinal contribution in Lemma 13.4 vanishes:
`2^{-L} #D_Y = o_C(1)`.
-/
theorem normalized_terminalBadStarts_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ((terminalBadStarts N L
          (terminalPrimeCutoff (L + 1))).card : ℝ) /
            (2 : ℝ) ^ L)
      (fun _ _ => 1) := by
  have hcount :=
    terminalBadStarts_terminalCutoff_uniformLittleOLinear hC
  have hbalancePos :
      0 < CriticalRunWindow.balanceConstant C := by
    unfold CriticalRunWindow.balanceConstant
    positivity
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Ncount, hcountBound⟩ :=
    hcount (ε / CriticalRunWindow.balanceConstant C)
      (div_pos hε hbalancePos)
  refine ⟨max Nwindow Ncount, ?_⟩
  intro N hN L hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hc :=
    hcountBound N ((le_max_right _ _).trans hN) L hrun
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hcardNonneg :
      0 ≤
        ((terminalBadStarts N L
          (terminalPrimeCutoff (L + 1))).card : ℝ) := by
    positivity
  simp only [abs_div, abs_of_nonneg hcardNonneg,
    abs_of_pos hpowPos, abs_one, mul_one,
    abs_of_nonneg hNnonneg] at hc ⊢
  calc
    ((terminalBadStarts N L
          (terminalPrimeCutoff (L + 1))).card : ℝ) /
          (2 : ℝ) ^ L ≤
        ((ε / CriticalRunWindow.balanceConstant C) * (N : ℝ)) /
          (2 : ℝ) ^ L :=
      div_le_div_of_nonneg_right hc hpowPos.le
    _ =
        (ε / CriticalRunWindow.balanceConstant C) *
          ((N : ℝ) / (2 : ℝ) ^ L) := by ring
    _ ≤
        (ε / CriticalRunWindow.balanceConstant C) *
          CriticalRunWindow.balanceConstant C :=
      mul_le_mul_of_nonneg_left hw.2.2
        (div_nonneg hε.le hbalancePos.le)
    _ = ε := by
      field_simp

end

end TerminalBadStartsCritical
end PaperC
