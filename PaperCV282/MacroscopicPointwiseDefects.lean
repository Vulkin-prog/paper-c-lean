import PaperCV282.MacroscopicLogarithms
import PaperC.Combinatorics.DefectiveVertexIntervalBound
import PaperC.Asymptotics.ExpSqrtLog

/-!
# Uniform pointwise defects on the macroscopic interval

The old pointwise interval estimate applies separately at `x-1` and `y-1`.
The resulting bound is uniform in both starts, the window length, and the
canonical coding parameter. In particular, it does not require comparable
starts or the critical balance `2^(L+1)` of order `M`.
-/

namespace PaperC.V282.MacroscopicPointwiseDefects

open MacroscopicGeometry MacroscopicLogarithms ResidualComponentCounts

noncomputable section

/-- Defects in every root interval obey a common logarithmic bound. -/
theorem root_defects_log_bound_eventually
    (betaMin betaMax delta : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hdelta : 0 < delta) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ B : ℕ,
      betaMin * Real.log M ≤ (B : ℝ) → (B : ℝ) ≤ betaMax * Real.log M →
      ∀ x ∈ macroscopicStarts M delta,
        ((IntervalDefectBound.defectsInInterval B (x - 1)).card : ℝ) ≤
          K * (Real.log M / Real.log (Real.log M)) := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  have hquot : 0 < 2 * betaMax / delta := by positivity
  have hband : betaMin / 2 < betaMax + 2 * betaMax / delta := by linarith
  obtain ⟨K, hK, Upoint, hpoint⟩ :=
    CriticalWeightedDefect.pointwise_uniformBigO_on_window
      (by positivity : 0 < betaMin / 2) hband
  obtain ⟨Mzero, htransport⟩ := root_log_transport_eventually delta hdelta Upoint
  refine ⟨2 * K, by positivity, Mzero, ?_⟩
  intro M hM B hBmin hBmax x hx
  obtain ⟨hUlarge, hUlog, hlower, hupper, hratio⟩ := htransport M hM x hx
  have hwindow := criticalWindow_of_root_log_bounds
    hbetaMin hbeta hdelta (by linarith) hlower hupper hBmin hBmax
  have hlocal := hpoint (x - 1) hUlarge B hwindow
  have hratioNonneg :
      0 ≤ Real.log (x - 1 : ℕ) / Real.log (Real.log (x - 1 : ℕ)) :=
    div_nonneg (by linarith) (Real.log_pos hUlog).le
  rw [abs_of_nonneg (by positivity), abs_of_nonneg hratioNonneg] at hlocal
  calc
    ((IntervalDefectBound.defectsInInterval B (x - 1)).card : ℝ) ≤
        K * (Real.log (x - 1 : ℕ) / Real.log (Real.log (x - 1 : ℕ))) := hlocal
    _ ≤ K * (2 * (Real.log M / Real.log (Real.log M))) :=
      mul_le_mul_of_nonneg_left hratio hK
    _ = (2 * K) * (Real.log M / Real.log (Real.log M)) := by ring

/-- The corrected defect has a common bound, before choosing either start or channel. -/
theorem correctedDefect_log_bound_eventually
    (betaMin betaMax delta : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hdelta : 0 < delta) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ A x : ℕ, x ∈ macroscopicStarts M delta →
      ∀ y : ℕ, y ∈ macroscopicStarts M delta →
        (canonicalCorrectedDefectCount A x y L : ℝ) ≤
          K * (Real.log M / Real.log (Real.log M)) := by
  obtain ⟨K, hK, Mpoint, hpoint⟩ :=
    root_defects_log_bound_eventually betaMin betaMax delta hbetaMin hbeta hdelta
  refine ⟨2 * K, by positivity, max Mpoint 2, ?_⟩
  intro M hM L hLmin hLmax A x hx y hy
  have hMpoint : Mpoint ≤ M := (le_max_left _ _).trans hM
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hM
  have hxTwo := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hx)).1
  have hyTwo := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hy)).1
  have hleft := hpoint M hMpoint (L + 1) (by exact_mod_cast hLmin)
    (by exact_mod_cast hLmax) x hx
  have hright := hpoint M hMpoint (L + 1) (by exact_mod_cast hLmin)
    (by exact_mod_cast hLmax) y hy
  have hfinite := DefectiveVertexIntervalBound.canonicalCorrectedDefectCount_le_interval_sum
    A (by omega : 1 ≤ x) (by omega : 1 ≤ y) (L := L)
  have hcast : (canonicalCorrectedDefectCount A x y L : ℝ) ≤
      ((IntervalDefectBound.defectsInInterval (L + 1) (x - 1)).card : ℝ) +
        ((IntervalDefectBound.defectsInInterval (L + 1) (y - 1)).card : ℝ) := by
    exact_mod_cast hfinite
  calc
    (canonicalCorrectedDefectCount A x y L : ℝ) ≤
        ((IntervalDefectBound.defectsInInterval (L + 1) (x - 1)).card : ℝ) +
          ((IntervalDefectBound.defectsInInterval (L + 1) (y - 1)).card : ℝ) := hcast
    _ ≤ K * (Real.log M / Real.log (Real.log M)) +
        K * (Real.log M / Real.log (Real.log M)) := add_le_add hleft hright
    _ = (2 * K) * (Real.log M / Real.log (Real.log M)) := by ring

/-- Reciprocal-power uniform subpolynomiality of the corrected-defect factor. -/
theorem two_pow_correctedDefect_pow_le_eventually
    (betaMin betaMax delta : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hdelta : 0 < delta)
    (k : ℕ) (hk : 0 < k) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ A x : ℕ, x ∈ macroscopicStarts M delta →
      ∀ y : ℕ, y ∈ macroscopicStarts M delta →
        ((2 : ℝ) ^ canonicalCorrectedDefectCount A x y L) ^ k ≤ (M : ℝ) := by
  obtain ⟨K, hK, Mpoint, hpoint⟩ :=
    correctedDefect_log_bound_eventually betaMin betaMax delta hbetaMin hbeta hdelta
  obtain ⟨Mexp, hexp⟩ := ExpSqrtLog.two_pow_log_div_loglog_pow_le_nat_eventually K hK k hk
  refine ⟨max Mpoint Mexp, ?_⟩
  intro M hM L hLmin hLmax A x hx y hy
  have hcount := hpoint M ((le_max_left _ _).trans hM) L hLmin hLmax A x hx y hy
  have hpow := hexp M ((le_max_right _ _).trans hM)
    (canonicalCorrectedDefectCount A x y L) (by simpa only [mul_div_assoc] using hcount)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpow

/-- Literal real-exponent form, uniform in the length, both starts and coding parameter. -/
theorem two_pow_correctedDefect_le_rpow_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ A x : ℕ, x ∈ macroscopicStarts M delta →
      ∀ y : ℕ, y ∈ macroscopicStarts M delta →
        (2 : ℝ) ^ canonicalCorrectedDefectCount A x y L ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hepsilon
  obtain ⟨Mpower, hpower⟩ := two_pow_correctedDefect_pow_le_eventually
    betaMin betaMax delta hbetaMin hbeta hdelta (n + 1) (by omega)
  refine ⟨max Mpower 1, ?_⟩
  intro M hM L hLmin hLmax A x hx y hy
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (le_max_right Mpower 1).trans hM
  have hpow := hpower M ((le_max_left _ _).trans hM) L hLmin hLmax A x hx y hy
  have hroot : (2 : ℝ) ^ canonicalCorrectedDefectCount A x y L ≤
      (M : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (by positivity : (0 : ℝ) < n + 1)).mpr
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
    exact hpow
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hMone hn.le)

end
end PaperC.V282.MacroscopicPointwiseDefects
