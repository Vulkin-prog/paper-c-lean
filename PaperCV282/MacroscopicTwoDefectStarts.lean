import PaperCV282.PolynomialPellCount
import PaperCV282.MacroscopicCanonicalCode
import PaperCV282.MacroscopicSmoothKernels
import PaperCV282.LogarithmicWordPowers
import PaperC.Asymptotics.BoundedRatioManyDefectsFibers

/-!
# Two defective occurrences in macroscopic windows

The unequal squarefree-kernel case maps to the internally proved Pell
count. Equal kernels are excluded in the macroscopic high zone by the
retained elementary factorization argument.
-/

namespace PaperC.V282.MacroscopicTwoDefectStarts

open BoundedRatioManyDefectsFibers BoundedRatioDistinctKernelTwoDefects
open BoundedRatioTwoDefectStarts HighZoneTwoDefects SquarefreeSmoothCount
open PolynomialPellCount MacroscopicGeometry

noncomputable section

/-- The distinct-kernel base count with the actual smooth-kernel population still explicit. -/
theorem card_distinctKernelDefectBases_le_smooth_factor_eventually
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ B : ℕ, B ≤ M → ∀ N : ℕ, 2 ≤ N →
      ((distinctKernelDefectBases N M B).card : ℝ) ≤
        ((squarefreeSmoothUpTo B (M ^ 2)).card : ℝ) ^ 2 * (B + 1 : ℝ) ^ 2 *
          (M : ℝ) ^ epsilon := by
  obtain ⟨Mpell, hpell⟩ := pellBox_atMost_rpow_eventually 2 epsilon hepsilon
  refine ⟨max Mpell 2, ?_⟩
  intro M hM B hB N hN
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hM
  have hambient : M + B ≤ M ^ 2 := by nlinarith
  have hMpow : M ≤ M ^ 2 := by nlinarith
  have hcover := distinctKernelDefectBases_subset_distinctPaired
    (N := N) (M := M) (B := B) (Y := M ^ 2) hN hambient
  have hcard : ((distinctKernelDefectBases N M B).card : ℝ) ≤
      ((distinctPairedDefectStarts (squarefreeSmoothUpTo B (M ^ 2))
        (Finset.range (B + 1)) (M ^ 2) M).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hcover
  refine hcard.trans ?_
  have hfinite := card_distinctPairedDefectStarts_le
    (D := squarefreeSmoothUpTo B (M ^ 2)) (I := Finset.range (B + 1))
    (H := M ^ 2) (X := M) (R := (M : ℝ) ^ epsilon) (by positivity) (by
      intro d1 hd1 d2 hd2 hdne i1 hi1 i2 hi2 hine
      have hdata1 := mem_squarefreeSmoothUpTo.mp hd1
      have hdata2 := mem_squarefreeSmoothUpTo.mp hd2
      have hi1B : i1 ≤ B := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi1
      have hi2B : i2 ≤ B := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi2
      have hdiff : ((i1 : ℤ) - (i2 : ℤ)).natAbs ≤ M ^ 2 :=
        (Int.natAbs_coe_sub_coe_le_of_le hi1B hi2B).trans (hB.trans hMpow)
      apply MultipleDefects.twoDefectWitnessBox_atMost
      exact hpell M ((le_max_left _ _).trans hM) d1 d2 (M ^ 2) ((i1 : ℤ) - (i2 : ℤ))
        (by omega) (by omega)
        (TerminalPartnerPell.not_isSquare_ratio_of_squarefree_of_ne hdata1.1 hdata2.1
          hdata1.2.2.1 hdata2.2.2.1 hdne)
        (by apply sub_ne_zero.mpr; exact_mod_cast hine)
        hdata1.2.1 hdata2.2.1 le_rfl hdiff)
  simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hfinite

/-- Equal squarefree kernels disappear beyond a threshold uniform in the logarithmic length. -/
theorem twoDefectBaseCover_eq_distinct_eventually
    (C delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ C * Real.log M →
      twoDefectBaseCover ⌈(M : ℝ) ^ delta⌉₊ M (L + 1) =
        distinctKernelDefectBases ⌈(M : ℝ) ^ delta⌉₊ M (L + 1) := by
  obtain ⟨Mpower, hpower⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    C delta hC hdelta 2 (by omega)
  refine ⟨Mpower, ?_⟩
  intro M hM L hL
  have hp := hpower M hM (L + 1) (by simpa using hL)
  have hceil := Nat.le_ceil ((M : ℝ) ^ delta)
  have hhigh : (L + 1) ^ 2 + 1 < ⌈(M : ℝ) ^ delta⌉₊ := by
    have hnat : (L + 1) ^ 2 + 1 ≤ (L + 1 + 1) ^ 2 := by
      have hsq : (L + 1) ^ 2 < (L + 1 + 1) ^ 2 :=
        (Nat.pow_lt_pow_iff_left (by omega : (2 : ℕ) ≠ 0)).mpr (by omega)
      omega
    have hreal : (((L + 1) ^ 2 + 1 : ℕ) : ℝ) < (⌈(M : ℝ) ^ delta⌉₊ : ℝ) := by
      calc
        _ ≤ (((L + 1 + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
        _ < (M : ℝ) ^ delta := by exact_mod_cast hp
        _ ≤ _ := hceil
    exact_mod_cast hreal
  exact twoDefectBaseCover_eq_distinctKernel hhigh

/-- The distinct-kernel base population is subpolynomial throughout the full logarithmic band. -/
theorem card_distinctKernelDefectBases_le_rpow_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ N : ℕ, 2 ≤ N →
      ((distinctKernelDefectBases N M (L + 1)).card : ℝ) ≤ (M : ℝ) ^ epsilon := by
  have heps : 0 < epsilon / 4 := by linarith
  obtain ⟨Mpell, hpell⟩ := card_distinctKernelDefectBases_le_smooth_factor_eventually
    (epsilon / 4) heps
  obtain ⟨Msmooth, hsmooth⟩ := MacroscopicSmoothKernels.card_squarefreeSmoothUpTo_le_rpow_eventually
    betaMin betaMax (epsilon / 4) hbetaMin hbetaMax heps
  obtain ⟨Moffset, hoffset⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    betaMax hbetaMax.le 4 2 (epsilon / 4) heps
  obtain ⟨Mlength, hlength⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    betaMax 1 hbetaMax.le (by norm_num) 1 (by omega)
  refine ⟨max Mpell (max Msmooth (max Moffset (max Mlength 2))), ?_⟩
  intro M hM L hlower hupper N hN
  have hrest1 : max Msmooth (max Moffset (max Mlength 2)) ≤ M := (le_max_right _ _).trans hM
  have hrest2 : max Moffset (max Mlength 2) ≤ M := (le_max_right _ _).trans hrest1
  have hrest3 : max Mlength 2 ≤ M := (le_max_right _ _).trans hrest2
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hrest3
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlen := hlength M ((le_max_left _ _).trans hrest3) (L + 1) (by simpa using hupper)
  have hBM : L + 1 ≤ M := by
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hlen
    have : (L + 1 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hf := hpell M ((le_max_left _ _).trans hM) (L + 1) hBM N hN
  have hs := hsmooth M ((le_max_left _ _).trans hrest1) L hlower hupper (M ^ 2)
  have ho := hoffset M ((le_max_left _ _).trans hrest2) L (by simpa using hupper)
  have hoff : (L + 1 + 1 : ℝ) ^ 2 ≤ (M : ℝ) ^ (epsilon / 4) := by
    have hB : (1 : ℝ) ≤ L + 1 := by have h := Nat.cast_nonneg (α := ℝ) L; linarith
    have hpoly : (L + 1 + 1 : ℝ) ^ 2 ≤ 4 * (L + 1 : ℝ) ^ 2 := by nlinarith
    exact hpoly.trans (by simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (L + 1 : ℝ) ^ 2)] using ho)
  calc
    _ ≤ ((squarefreeSmoothUpTo (L + 1) (M ^ 2)).card : ℝ) ^ 2 *
        (L + 1 + 1 : ℝ) ^ 2 * (M : ℝ) ^ (epsilon / 4) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hf
    _ ≤ ((M : ℝ) ^ (epsilon / 4)) ^ 2 *
        (M : ℝ) ^ (epsilon / 4) * (M : ℝ) ^ (epsilon / 4) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hs 2) hoff (by positivity) (by positivity)
    _ = _ := by
      rw [pow_two, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
      congr 1
      ring

/-- Lemma 3.20 for the actual equal/distinct base cover on the macroscopic domain. -/
theorem card_twoDefectBaseCover_le_rpow_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ((twoDefectBaseCover ⌈(M : ℝ) ^ delta⌉₊ M (L + 1)).card : ℝ) ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨Mdistinct, hdistinct⟩ := card_distinctKernelDefectBases_le_rpow_eventually
    betaMin betaMax epsilon hbetaMin hbetaMax hepsilon
  obtain ⟨Mequal, hequal⟩ := twoDefectBaseCover_eq_distinct_eventually betaMax delta hbetaMax.le hdelta
  refine ⟨max Mdistinct (max Mequal 2), ?_⟩
  intro M hM L hlower hupper
  have hrest : max Mequal 2 ≤ M := (le_max_right _ _).trans hM
  rw [hequal M ((le_max_left _ _).trans hrest) L hupper]
  exact hdistinct M ((le_max_left _ _).trans hM) L hlower hupper _
    (two_le_macroscopic_lowerEndpoint ((le_max_right _ _).trans hrest) hdelta)

end
end PaperC.V282.MacroscopicTwoDefectStarts
