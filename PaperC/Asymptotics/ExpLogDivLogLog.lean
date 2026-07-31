import PaperC.Analysis.CriticalWeightedDefect
import PaperC.Probability.CriticalRunWindow

/-!
# Exponential losses at the logarithm-over-logarithm scale

This module packages the elementary implication

`E(N,L) ≤ D * log N / log log N`

`⇒ exp (E(N,L)) = N^(o(1))`,

with the uniform quantifier order used throughout Paper C.  It then
specializes the result to the integral quotient

`(L + 1) / Nat.log 2 (L + 1)`

in the manuscript's run-length window.
-/

namespace PaperC
namespace ExpLogDivLogLog

/--
An exponential whose exponent is bounded by `D * log N / log log N`
is eventually smaller than every reciprocal power of `N`.
-/
theorem exp_log_div_loglog_pow_le_nat_eventually
    (D : ℝ) (hD : 0 ≤ D) (k : ℕ) (_hk : 0 < k) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ E : ℝ,
      E ≤ D * Real.log N / Real.log (Real.log N) →
      Real.exp E ^ k ≤ (N : ℝ) := by
  let A : ℝ := (k : ℝ) * D
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (Real.exp (Real.exp A))
  refine ⟨N₀, ?_⟩
  intro N hNN₀ E hE
  have hthreshold :
      Real.exp (Real.exp A) < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hNN₀)
  have hlogN :
      Real.exp A < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos (Real.exp A)) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hloglogN :
      A < Real.log (Real.log N) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos A) hlogN
    simpa only [Real.log_exp] using hlogs
  have hlogNpos : 0 < Real.log N :=
    (Real.exp_pos A).trans hlogN
  have hloglogNpos : 0 < Real.log (Real.log N) :=
    hA.trans_lt hloglogN
  have hscaled :
      (k : ℝ) * E ≤ Real.log N := by
    calc
      (k : ℝ) * E ≤
          (k : ℝ) *
            (D * Real.log N / Real.log (Real.log N)) :=
        mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg k)
      _ = Real.log N *
          (A / Real.log (Real.log N)) := by
        dsimp [A]
        ring
      _ ≤ Real.log N * 1 := by
        apply mul_le_mul_of_nonneg_left _ hlogNpos.le
        exact (div_le_one hloglogNpos).2 hloglogN.le
      _ = Real.log N := mul_one _
  have hNpos : 0 < (N : ℝ) :=
    (Real.exp_pos _).trans hthreshold
  calc
    Real.exp E ^ k = Real.exp ((k : ℝ) * E) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (Real.log N) :=
      Real.exp_le_exp.mpr hscaled
    _ = (N : ℝ) := Real.exp_log hNpos

/--
Uniform eventual-bound form of
`exp_log_div_loglog_pow_le_nat_eventually`.
-/
theorem uniformSubpolynomialOn_exp_log_div_loglog_eventually
    (admissible : ℕ → ℕ → Prop)
    (E : ℕ → ℕ → ℝ)
    (D : ℝ) (hD : 0 ≤ D)
    (hE :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        E N L ≤
          D * Real.log N / Real.log (Real.log N)) :
    UniformSubpolynomialOn admissible
      (fun N L => Real.exp (E N L)) := by
  intro k hk
  obtain ⟨Npow, hNpow⟩ :=
    exp_log_div_loglog_pow_le_nat_eventually D hD k hk
  obtain ⟨Nbound, hNbound⟩ := hE
  refine ⟨max Npow Nbound, ?_⟩
  intro N hN L hNL
  have hexp : 0 ≤ Real.exp (E N L) := (Real.exp_pos _).le
  simpa only [abs_of_nonneg hexp] using
    hNpow N ((le_max_left _ _).trans hN) (E N L)
      (hNbound N ((le_max_right _ _).trans hN) L hNL)

/--
In the literal run-length window, the exponential loss

`exp (A * (L+1) / Nat.log 2 (L+1))`

is uniformly `N^(o(1))`.  The coefficient `A` and the window width `C`
are fixed nonnegative reals.
-/
theorem criticalRunWindow_exp_height_div_natLog_uniformSubpolynomial
    {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L =>
        Real.exp
          (A * (L + 1 : ℕ) /
            (Nat.log 2 (L + 1) : ℝ))) := by
  let c₁ := CriticalRunWindow.lowerConstant
  let c₂ := CriticalRunWindow.upperConstant
  let D : ℝ := A * (8 * c₂)
  have hc₁ : 0 < c₁ := by
    simpa only [c₁] using CriticalRunWindow.lowerConstant_pos
  have hc₁c₂ : c₁ < c₂ := by
    simpa only [c₁, c₂] using
      CriticalRunWindow.lowerConstant_lt_upperConstant
  have hc₂ : 0 < c₂ := hc₁.trans hc₁c₂
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hNadm⟩ :=
    CriticalWeightedDefect.admissible_eventually hc₁ hc₁c₂
  obtain ⟨Nlog, hNlog⟩ :=
    CriticalWeightedDefect.eventually_loglog_le_eight_log_height
      (c₂ := c₂) hc₁
  obtain ⟨Nheight, hNheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := c₂) hc₁ 8
  apply uniformSubpolynomialOn_exp_log_div_loglog_eventually
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L =>
        A * (L + 1 : ℕ) / (Nat.log 2 (L + 1) : ℝ))
      D hD
  refine ⟨max Nwindow (max Nadm (max Nlog Nheight)), ?_⟩
  intro N hN L hrun
  have hNwindowN : Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail : max Nadm (max Nlog Nheight) ≤ N :=
    (le_max_right _ _).trans hN
  have hNadmN : Nadm ≤ N :=
    (le_max_left _ _).trans hNtail
  have hNlogHeight : max Nlog Nheight ≤ N :=
    (le_max_right _ _).trans hNtail
  have hNlogN : Nlog ≤ N :=
    (le_max_left _ _).trans hNlogHeight
  have hNheightN : Nheight ≤ N :=
    (le_max_right _ _).trans hNlogHeight
  have hcritical :
      CriticalWindowParameters.InCriticalWindow c₁ c₂ N (L + 1) := by
    simpa only [c₁, c₂] using
      (hNwindow N hNwindowN L hrun).1
  have hadm :
      CriticalWeightedDefect.Admissible c₁ c₂ N (L + 1) :=
    hNadm N hNadmN (L + 1) hcritical
  obtain ⟨hloglogPos, hloglogLe⟩ :=
    hNlog N hNlogN (L + 1) hadm
  have hheight : (8 : ℕ) ≤ L + 1 := by
    exact hNheight N hNheightN (L + 1) hadm
  have hnatLog :
      Real.log (L + 1 : ℕ) ≤
        (Nat.log 2 (L + 1) : ℝ) :=
    CriticalWindowScale.real_log_le_nat_log_two hheight
  have hdenomPos : 0 < (Nat.log 2 (L + 1) : ℝ) := by
    have : 0 < Nat.log 2 (L + 1) := by
      exact Nat.log_pos (by norm_num) (by omega)
    exact_mod_cast this
  have hlogNpos : 0 < Real.log N := by
    have hupper :
        ((L + 1 : ℕ) : ℝ) ≤ c₂ * Real.log N :=
      hcritical.2.2.2
    have hheightPos : 0 < ((L + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hratio :
      ((L + 1 : ℕ) : ℝ) /
          (Nat.log 2 (L + 1) : ℝ) ≤
        (8 * c₂) * Real.log N /
          Real.log (Real.log N) := by
    apply (div_le_div_iff₀ hdenomPos hloglogPos).2
    calc
      ((L + 1 : ℕ) : ℝ) * Real.log (Real.log N)
          ≤ (c₂ * Real.log N) * Real.log (Real.log N) :=
        mul_le_mul_of_nonneg_right hcritical.2.2.2 hloglogPos.le
      _ ≤ (c₂ * Real.log N) *
          (8 * (Nat.log 2 (L + 1) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hloglogLe.trans
          (mul_le_mul_of_nonneg_left hnatLog (by norm_num))
      _ = ((8 * c₂) * Real.log N) *
          (Nat.log 2 (L + 1) : ℝ) := by ring
  calc
    A * (L + 1 : ℕ) / (Nat.log 2 (L + 1) : ℝ)
        = A *
          (((L + 1 : ℕ) : ℝ) /
            (Nat.log 2 (L + 1) : ℝ)) := by ring
    _ ≤ A *
        ((8 * c₂) * Real.log N /
          Real.log (Real.log N)) :=
      mul_le_mul_of_nonneg_left hratio hA
    _ = D * Real.log N / Real.log (Real.log N) := by
      dsimp [D]
      ring

end ExpLogDivLogLog
end PaperC
