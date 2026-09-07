import PaperCV282.MacroscopicGeometry
import PaperC.Analysis.CriticalWindowParameters

/-!
# Logarithmic transport to each macroscopic root

Each root `x-1` is treated at its own scale. The common thresholds precede
the choice of `x`, and no comparison between two starts is required.
-/

namespace PaperC.V282.MacroscopicLogarithms

open MacroscopicGeometry

noncomputable section

/-- Every fixed natural lower bound eventually holds for every macroscopic root. -/
theorem root_ge_eventually (delta : ℝ) (hdelta : 0 < delta) (K : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ x ∈ macroscopicStarts M delta,
      K ≤ x - 1 := by
  obtain ⟨Mzero, hzero⟩ := exists_nat_gt
    (Real.exp (Real.log (K + 2 : ℝ) / delta))
  refine ⟨Mzero, ?_⟩
  intro M hM x hx
  have hlarge : Real.exp (Real.log (K + 2 : ℝ) / delta) < (M : ℝ) :=
    hzero.trans_le (by exact_mod_cast hM)
  have hMpos : (0 : ℝ) < M := (Real.exp_pos _).trans hlarge
  have hlog : Real.log (K + 2 : ℝ) / delta < Real.log M := by
    have h := Real.log_lt_log (Real.exp_pos _) hlarge
    simpa only [Real.log_exp] using h
  have hscaled : Real.log (K + 2 : ℝ) < Real.log M * delta :=
    (div_lt_iff₀ hdelta).mp hlog
  have hpower : (K + 2 : ℝ) < (M : ℝ) ^ delta := by
    rw [Real.rpow_def_of_pos hMpos]
    simpa only [Real.exp_log (by positivity : (0 : ℝ) < K + 2)] using
      Real.exp_lt_exp.mpr hscaled
  have hxLower := ((mem_macroscopicStarts_iff_real M delta x).mp hx).1
  have hKx : K + 2 < x := by exact_mod_cast hpower.trans_le hxLower
  omega

/-- Polynomial comparison of the root and the ambient scale, in logarithms. -/
theorem root_log_bounds {M x : ℕ} {delta : ℝ}
    (hM : 2 ≤ M) (hxThree : 3 ≤ x)
    (hx : x ∈ macroscopicStarts M delta) :
    delta * Real.log M ≤ 2 * Real.log (x - 1 : ℕ) ∧
      Real.log (x - 1 : ℕ) ≤ Real.log M := by
  have hxData := (mem_macroscopicStarts_iff_real M delta x).mp hx
  have hrootPos : (0 : ℝ) < (x - 1 : ℕ) := by exact_mod_cast (show 0 < x - 1 by omega)
  have hxSquare : x ≤ (x - 1) ^ 2 := by
    have hxEq : x = (x - 1) + 1 := by omega
    nlinarith
  have hpower : (M : ℝ) ^ delta ≤ ((x - 1 : ℕ) : ℝ) ^ 2 :=
    hxData.1.trans (by exact_mod_cast hxSquare)
  refine ⟨?_, ?_⟩
  · calc
      delta * Real.log M = Real.log ((M : ℝ) ^ delta) :=
        (Real.log_rpow (by positivity) delta).symm
      _ ≤ Real.log (((x - 1 : ℕ) : ℝ) ^ 2) :=
        Real.log_le_log (Real.rpow_pos_of_pos (by positivity) _) hpower
      _ = 2 * Real.log (x - 1 : ℕ) := by rw [Real.log_pow]; norm_num
  · apply Real.log_le_log hrootPos
    have hxM : x < M := hxData.2
    exact_mod_cast (show x - 1 ≤ M by omega)

/-- The logarithm-over-logarithm scale grows by at most a factor two. -/
theorem log_div_loglog_le_two_of_log_bounds {M U : ℕ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hUlog : 1 < Real.log U) (hUdelta : 2 / delta ≤ Real.log U)
    (hlower : delta * Real.log M ≤ 2 * Real.log U)
    (hupper : Real.log U ≤ Real.log M) :
    Real.log U / Real.log (Real.log U) ≤
      2 * (Real.log M / Real.log (Real.log M)) := by
  have hMlog : 1 < Real.log M := hUlog.trans_le hupper
  have hUlogPos : 0 < Real.log U := by linarith
  have hMlogPos : 0 < Real.log M := by linarith
  have hUloglog : 0 < Real.log (Real.log U) := Real.log_pos hUlog
  have hMloglog : 0 < Real.log (Real.log M) := Real.log_pos hMlog
  have hdeltaU : 2 ≤ Real.log U * delta := (div_le_iff₀ hdelta).mp hUdelta
  have hlogSquare : Real.log M ≤ (Real.log U) ^ 2 := by nlinarith
  have hloglog : Real.log (Real.log M) ≤ 2 * Real.log (Real.log U) := by
    calc
      Real.log (Real.log M) ≤ Real.log ((Real.log U) ^ 2) :=
        Real.log_le_log hMlogPos hlogSquare
      _ = 2 * Real.log (Real.log U) := by rw [Real.log_pow]; norm_num
  calc
    Real.log U / Real.log (Real.log U) ≤
        Real.log M / Real.log (Real.log U) :=
      div_le_div_of_nonneg_right hupper hUloglog.le
    _ ≤ Real.log M / (Real.log (Real.log M) / 2) := by
      apply div_le_div_of_nonneg_left hMlogPos.le (by positivity)
      linarith
    _ = 2 * (Real.log M / Real.log (Real.log M)) := by ring

/-- A common threshold supplies the complete transport data for every root. -/
theorem root_log_transport_eventually
    (delta : ℝ) (hdelta : 0 < delta) (K : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ x ∈ macroscopicStarts M delta,
      K ≤ x - 1 ∧ 1 < Real.log (x - 1 : ℕ) ∧
      delta * Real.log M ≤ 2 * Real.log (x - 1 : ℕ) ∧
      Real.log (x - 1 : ℕ) ≤ Real.log M ∧
      Real.log (x - 1 : ℕ) / Real.log (Real.log (x - 1 : ℕ)) ≤
        2 * (Real.log M / Real.log (Real.log M)) := by
  let T : ℝ := max 2 (2 / delta)
  let Kroot : ℕ := max K (max 2 (⌈Real.exp T⌉₊ + 1))
  obtain ⟨Mroot, hroot⟩ := root_ge_eventually delta hdelta Kroot
  refine ⟨max Mroot 2, ?_⟩
  intro M hM x hx
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hM
  have hKroot : Kroot ≤ x - 1 := hroot M ((le_max_left _ _).trans hM) x hx
  have hK : K ≤ x - 1 := (le_max_left _ _).trans hKroot
  have htail : max 2 (⌈Real.exp T⌉₊ + 1) ≤ x - 1 := (le_max_right _ _).trans hKroot
  have htwo : 2 ≤ x - 1 := (le_max_left _ _).trans htail
  have hceil : ⌈Real.exp T⌉₊ + 1 ≤ x - 1 := (le_max_right _ _).trans htail
  have hexp : Real.exp T < ((x - 1 : ℕ) : ℝ) := by
    have hc := Nat.le_ceil (Real.exp T)
    have hc' : (⌈Real.exp T⌉₊ : ℝ) + 1 ≤ ((x - 1 : ℕ) : ℝ) := by exact_mod_cast hceil
    linarith
  have hlog : T < Real.log (x - 1 : ℕ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hexp
    simpa only [Real.log_exp] using h
  have hlogOne : 1 < Real.log (x - 1 : ℕ) := by
    have : 2 ≤ T := le_max_left _ _
    linarith
  have hlogDelta : 2 / delta ≤ Real.log (x - 1 : ℕ) :=
    (le_max_right _ _).trans hlog.le
  have hb := root_log_bounds hMtwo (by omega) hx
  exact ⟨hK, hlogOne, hb.1, hb.2,
    log_div_loglog_le_two_of_log_bounds hdelta hlogOne hlogDelta hb.1 hb.2⟩

/-- A fixed ambient logarithmic band transports to a wider fixed root band. -/
theorem criticalWindow_of_root_log_bounds
    {betaMin betaMax delta : ℝ} {M U B : ℕ}
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hUlog : 0 ≤ Real.log U)
    (hlower : delta * Real.log M ≤ 2 * Real.log U)
    (hupper : Real.log U ≤ Real.log M)
    (hBmin : betaMin * Real.log M ≤ (B : ℝ))
    (hBmax : (B : ℝ) ≤ betaMax * Real.log M) :
    CriticalWindowParameters.InCriticalWindow
      (betaMin / 2) (betaMax + 2 * betaMax / delta) U B := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  have hquot : 0 < 2 * betaMax / delta := by positivity
  refine ⟨by positivity, by linarith, ?_, ?_⟩
  · nlinarith
  · have hscaled : (B : ℝ) * delta ≤ 2 * betaMax * Real.log U := by
      nlinarith
    have hdiv : (B : ℝ) ≤ 2 * betaMax * Real.log U / delta :=
      (le_div_iff₀ hdelta).mpr hscaled
    calc
      (B : ℝ) ≤ 2 * betaMax * Real.log U / delta := hdiv
      _ = (2 * betaMax / delta) * Real.log U := by ring
      _ ≤ (betaMax + 2 * betaMax / delta) * Real.log U :=
        mul_le_mul_of_nonneg_right (by linarith) hUlog

end
end PaperC.V282.MacroscopicLogarithms
