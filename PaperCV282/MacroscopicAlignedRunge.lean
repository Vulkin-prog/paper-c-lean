import PaperCV282.MacroscopicLogarithms
import PaperCV282.MacroscopicCanonicalCode
import PaperC.Asymptotics.AlignedRungeGrowth
import PaperC.Asymptotics.TheoremEightAlignedClosure

/-!
# Hamming and Runge budgets in the macroscopic logarithmic band

The lower logarithmic bound supplies the Hamming threshold. The upper bound
transports to each root independently and supplies the quantitative Runge
contradiction. No critical balance or bounded endpoint ratio is assumed.
-/

namespace PaperC.V282.MacroscopicAlignedRunge

open MacroscopicGeometry MacroscopicLogarithms TheoremEightHammingBudget

noncomputable section

/-- Every fixed height threshold follows uniformly from a positive logarithmic lower bound. -/
theorem height_ge_eventually (betaMin : ℝ) (hbetaMin : 0 < betaMin) (T : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ B : ℕ,
      betaMin * Real.log M ≤ (B : ℝ) → T ≤ B := by
  obtain ⟨Mzero, hzero⟩ := exists_nat_gt (Real.exp ((T : ℝ) / betaMin))
  refine ⟨Mzero, ?_⟩
  intro M hM B hB
  have hlarge : Real.exp ((T : ℝ) / betaMin) < (M : ℝ) :=
    hzero.trans_le (by exact_mod_cast hM)
  have hlog : (T : ℝ) / betaMin < Real.log M := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hlarge
  have hscaled : (T : ℝ) < betaMin * Real.log M := by
    have h := (div_lt_iff₀ hbetaMin).mp hlog
    nlinarith
  exact_mod_cast (hscaled.trans_le hB).le

/-- The double logarithm of the height eventually exceeds every fixed real budget. -/
theorem height_loglog_gt_eventually
    (betaMin : ℝ) (hbetaMin : 0 < betaMin) (R : ℝ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ B : ℕ,
      betaMin * Real.log M ≤ (B : ℝ) → R < Real.log (Real.log B) := by
  obtain ⟨Mzero, hheight⟩ :=
    height_ge_eventually betaMin hbetaMin (⌈Real.exp (Real.exp R)⌉₊ + 1)
  refine ⟨Mzero, ?_⟩
  intro M hM B hB
  have hnat := hheight M hM B hB
  have hcast : (⌈Real.exp (Real.exp R)⌉₊ : ℝ) + 1 ≤ (B : ℝ) := by exact_mod_cast hnat
  have hceil := Nat.le_ceil (Real.exp (Real.exp R))
  have hexp : Real.exp (Real.exp R) < (B : ℝ) := by linarith
  have hlog : Real.exp R < Real.log B := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hexp
  simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hlog

/-- The Hamming threshold is kept symbolic to avoid evaluating an enormous closed power. -/
theorem hamming_numerics_eventually_of_threshold
    (T : ℕ) (hT : 16384 ≤ T) (betaMin : ℝ) (hbetaMin : 0 < betaMin) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ B : ℕ,
      betaMin * Real.log M ≤ (B : ℝ) →
      64 ≤ B ∧
      (componentHammingRadius B : ℝ) ≤
        65 * (B : ℝ) / (Real.log B * Real.log (Real.log B)) ∧
      ∀ m : ℕ, B / 16 ≤ m →
        1 ≤ componentHammingRadius B ∧ 2 * componentHammingRadius B ≤ m ∧
        PrimesUpTo.count B + 2 ≤ m ∧
        2 * componentHammingRadius B *
          2 ^ ((PrimesUpTo.count B + 2) / componentHammingRadius B + 1) ≤ m := by
  obtain ⟨Mzero, hheight⟩ := height_ge_eventually betaMin hbetaMin (max 64 (2 ^ (2 ^ T)))
  refine ⟨Mzero, ?_⟩
  intro M hM B hB
  have hlarge := hheight M hM B hB
  have hB64 : 64 ≤ B := (le_max_left _ _).trans hlarge
  have hpow : 2 ^ (2 ^ T) ≤ B := (le_max_right _ _).trans hlarge
  have hlog : 2 ^ T ≤ Nat.log 2 B := Nat.le_log_of_pow_le Nat.one_lt_two hpow
  have hloglog : 16384 ≤ Nat.log 2 (Nat.log 2 B) :=
    hT.trans (Nat.le_log_of_pow_le Nat.one_lt_two hlog)
  exact ⟨hB64, TheoremEightAlignedClosure.componentHammingRadius_cast_le_real_log hloglog,
    fun m hm => componentHammingRadius_conditions_of_loglog hloglog hm⟩

/-- The fixed Hamming radius works in every positive logarithmic band. -/
theorem hamming_numerics_eventually (betaMin : ℝ) (hbetaMin : 0 < betaMin) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ B : ℕ,
      betaMin * Real.log M ≤ (B : ℝ) →
      64 ≤ B ∧
      (componentHammingRadius B : ℝ) ≤
        65 * (B : ℝ) / (Real.log B * Real.log (Real.log B)) ∧
      ∀ m : ℕ, B / 16 ≤ m →
        1 ≤ componentHammingRadius B ∧ 2 * componentHammingRadius B ≤ m ∧
        PrimesUpTo.count B + 2 ≤ m ∧
        2 * componentHammingRadius B *
          2 ^ ((PrimesUpTo.count B + 2) / componentHammingRadius B + 1) ≤ m :=
  hamming_numerics_eventually_of_threshold 16384 le_rfl betaMin hbetaMin

/-- Runge's finite upper bound is eventually below every macroscopic base. -/
theorem rungeScale_lt_macroscopic_eventually
    (betaMin betaMax delta D : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hD : 0 ≤ D) (A : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ B : ℕ,
      betaMin * Real.log M ≤ (B : ℝ) → (B : ℝ) ≤ betaMax * Real.log M →
      ∀ H : ℕ, 1 ≤ H → H ≤ B ^ A → ∀ t : ℕ,
      (t : ℝ) ≤ D * B / (Real.log B * Real.log (Real.log B)) →
      ∀ k : ℕ, 1 ≤ k → k ≤ 43 * t → ∀ a : ℕ, 1 ≤ a →
      ∀ x ∈ macroscopicStarts M delta,
        (128 * (2 * k) * (3 * H * B)) ^ (4 * k) < a * x := by
  let c : ℝ := betaMax + 2 * betaMax / delta
  let coefficient : ℝ := 172 * (A + 6 : ℕ) * D * c
  obtain ⟨Mheight, hheight⟩ := height_ge_eventually betaMin hbetaMin
    (max 768 (max ⌈D⌉₊ (⌈Real.exp 1⌉₊ + 1)))
  obtain ⟨Mlogs, hlogs⟩ := height_loglog_gt_eventually betaMin hbetaMin (max 1 coefficient)
  obtain ⟨Mroot, hroot⟩ := root_log_transport_eventually delta hdelta 2
  refine ⟨max Mheight (max Mlogs Mroot), ?_⟩
  intro M hM B hBmin hBmax H hH hHupper t ht k hk hkt a ha x hx
  have hMheight : Mheight ≤ M := (le_max_left _ _).trans hM
  have htail : max Mlogs Mroot ≤ M := (le_max_right _ _).trans hM
  have hMlogs : Mlogs ≤ M := (le_max_left _ _).trans htail
  have hMroot : Mroot ≤ M := (le_max_right _ _).trans htail
  have hlarge := hheight M hMheight B hBmin
  have hB768 : 768 ≤ B := (le_max_left _ _).trans hlarge
  have hBtail : max ⌈D⌉₊ (⌈Real.exp 1⌉₊ + 1) ≤ B := (le_max_right _ _).trans hlarge
  have hDnat : ⌈D⌉₊ ≤ B := (le_max_left _ _).trans hBtail
  have hDleB : D ≤ (B : ℝ) := (Nat.le_ceil D).trans (by exact_mod_cast hDnat)
  have hBexp : ⌈Real.exp 1⌉₊ + 1 ≤ B := (le_max_right _ _).trans hBtail
  have hexpB : Real.exp 1 < (B : ℝ) := by
    have hceil := Nat.le_ceil (Real.exp 1)
    have hcast : (⌈Real.exp 1⌉₊ : ℝ) + 1 ≤ (B : ℝ) := by exact_mod_cast hBexp
    linarith
  have hlogB : 1 ≤ Real.log B := by
    have : 1 < Real.log B := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hexpB
    exact this.le
  have hbudget := hlogs M hMlogs B hBmin
  have hloglogB : 1 ≤ Real.log (Real.log B) := (le_max_left _ _).trans hbudget.le
  have hcoefficient : coefficient < Real.log (Real.log B) :=
    (le_max_right _ _).trans_lt hbudget
  obtain ⟨hrootTwo, hrootLog, hlower, hupper, _⟩ := hroot M hMroot x hx
  have hwindow := criticalWindow_of_root_log_bounds
    hbetaMin hbeta hdelta (by linarith) hlower hupper hBmin hBmax
  exact AlignedRungeGrowth.rungeScale_lt_of_log_budget
    (N := x - 1) (B := B) (H := H) (t := t) (k := k)
    (a := a) (x := x) (A := A) (D := D) (c₂ := c)
    hD hrootTwo (Nat.sub_le x 1) ha hB768 hH hHupper hk hkt
    hlogB hloglogB hDleB hwindow.2.2.2 ht hcoefficient

/-- The polynomial root radius lies below half of each macroscopic base. -/
theorem translationRange_macroscopic_eventually
    (betaMin betaMax delta : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (A : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ B : ℕ,
      betaMin * Real.log M ≤ (B : ℝ) → (B : ℝ) ≤ betaMax * Real.log M →
      ∀ H : ℕ, H ≤ B ^ A → ∀ a : ℕ, 1 ≤ a →
      ∀ x ∈ macroscopicStarts M delta, 2 * (3 * H * B) ≤ a * x := by
  obtain ⟨Mheight, hheight⟩ := height_ge_eventually betaMin hbetaMin 2
  obtain ⟨Mpower, hpower⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    betaMax delta (hbetaMin.trans hbeta).le hdelta (A + 3) (by omega)
  refine ⟨max Mheight Mpower, ?_⟩
  intro M hM B hBmin hBmax H hHupper a ha x hx
  have hBtwo : 2 ≤ B := hheight M ((le_max_left _ _).trans hM) B hBmin
  have hpoly : 2 * (3 * H * B) < (B + 1) ^ (A + 3) := by
    calc
      2 * (3 * H * B) ≤ 6 * B ^ A * B := by nlinarith
      _ = 6 * B ^ (A + 1) := by rw [pow_succ]; ring
      _ < (B + 1) ^ ((A + 1) + 2) :=
        AlignedRungeGrowth.six_mul_pow_lt_succ_pow_add_two B (A + 1) hBtwo (by omega)
      _ = (B + 1) ^ (A + 3) := by congr 1
  have hpolyReal : ((B + 1) ^ (A + 3) : ℕ) < (M : ℝ) ^ delta := by
    exact_mod_cast hpower M ((le_max_right _ _).trans hM) B hBmax
  have hxLower := ((mem_macroscopicStarts_iff_real M delta x).mp hx).1
  have hbase : (B + 1) ^ (A + 3) < x := by exact_mod_cast hpolyReal.trans_le hxLower
  exact (hpoly.trans hbase).le.trans (by simpa using Nat.mul_le_mul_right x ha)

end
end PaperC.V282.MacroscopicAlignedRunge
