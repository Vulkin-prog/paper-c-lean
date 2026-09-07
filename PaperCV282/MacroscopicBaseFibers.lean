import PaperCV282.MacroscopicComponentFibers
import PaperCV282.MacroscopicOneSidedFibers
import PaperCV282.MacroscopicCanonicalCode

/-!
# Uniform counts with one start and one component shape fixed

The polynomial split-product theorem replaces the historical external
Evertse--Silverman input in every mobile degree at least two. Summing
the actual smooth square classes preserves subpolynomiality.
-/

namespace PaperC.V282.MacroscopicBaseFibers

open PropositionSixteenOne BoundedRatioComponentHosts BoundedRatioNonterminalHostCounts
open BoundedRatioManyDefectsFibers BoundedRatioManyDefectsFixedFibers
open MacroscopicComponentFibers MacroscopicOneSidedFibers SquarefreeSmoothCount

noncomputable section

/-- Both oriented fixed-square-class fibres are bounded uniformly in their actual arithmetic data. -/
theorem fixedSquareClassFibers_le_rpow_eventually
    (K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, L ≤ M → ∀ N A : ℕ, 2 ≤ N →
      ∀ shape ∈ boundedOffsetShapes L K, ∀ base ∈ boundedStartBases N M,
      ∀ d ∈ squarefreeSmoothUpTo (L + 1) ((M + L) ^ K),
      (2 ≤ shape.2.card →
        ((leftFixedSquareClassFiber N M A L K base shape d).card : ℝ) ≤ (M : ℝ) ^ epsilon) ∧
      (2 ≤ shape.1.card →
        ((rightFixedSquareClassFiber N M A L K base shape d).card : ℝ) ≤ (M : ℝ) ^ epsilon) := by
  obtain ⟨Msplit, hsplit⟩ := offsetProductNatFiber_atMost_rpow_eventually (4 * K + 2) K epsilon hepsilon
  refine ⟨max Msplit 2, ?_⟩
  intro M hM L hL N A hN shape hshape base hbase d hd
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hM
  have hshapeData := mem_boundedOffsetShapes.mp hshape
  have hMpow : M ≤ M ^ (4 * K + 2) := by
    calc
      M ≤ M ^ 2 := by nlinarith
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hBpow : L + 1 ≤ M ^ (4 * K + 2) := by
    calc
      L + 1 ≤ M ^ 2 := by nlinarith
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  constructor
  · intro hdegree
    apply card_leftFixedSquareClassFiber_cast_le hN shape
    apply hsplit M ((le_max_left _ _).trans hM) L
      (leftNormalizedCoefficient shape base d) M shape.2 hdegree (by omega)
      (leftNormalizedCoefficient_pos shape base d)
    · exact (leftNormalizedCoefficient_le_polynomial hN hMtwo hL shape hshape hbase hd).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    · exact hMpow
    · exact hBpow
  · intro hdegree
    apply card_rightFixedSquareClassFiber_cast_le hN shape
    apply hsplit M ((le_max_left _ _).trans hM) L
      (rightNormalizedCoefficient shape base d) M shape.1 hdegree (by omega)
      (rightNormalizedCoefficient_pos shape base d)
    · exact (rightNormalizedCoefficient_le_polynomial hN hMtwo hL shape hshape hbase hd).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    · exact hMpow
    · exact hBpow

/-- Summing all actual square classes closes both mobile-degree-at-least-two fibres. -/
theorem baseShapeFibers_le_rpow_eventually
    (K : ℕ) (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ N A : ℕ, 2 ≤ N →
      ∀ shape ∈ boundedOffsetShapes L K, ∀ base ∈ boundedStartBases N M,
      (2 ≤ shape.2.card → ((leftBaseShapeFiber N M A L K base shape).card : ℝ) ≤ (M : ℝ) ^ epsilon) ∧
      (2 ≤ shape.1.card → ((rightBaseShapeFiber N M A L K base shape).card : ℝ) ≤ (M : ℝ) ^ epsilon) := by
  have heps : 0 < epsilon / 2 := by linarith
  obtain ⟨Mfixed, hfixed⟩ := fixedSquareClassFibers_le_rpow_eventually K (epsilon / 2) heps
  obtain ⟨Msmooth, hsmooth⟩ := MacroscopicSmoothKernels.card_squarefreeSmoothUpTo_le_rpow_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbetaMax heps
  obtain ⟨Mlength, hlength⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    betaMax 1 hbetaMax.le (by norm_num) 1 (by omega)
  refine ⟨max Mfixed (max Msmooth (max Mlength 2)), ?_⟩
  intro M hM L hlower hupper N A hN shape hshape base hbase
  have hrest1 : max Msmooth (max Mlength 2) ≤ M := (le_max_right _ _).trans hM
  have hrest2 : max Mlength 2 ≤ M := (le_max_right _ _).trans hrest1
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hrest2
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlen := hlength M ((le_max_left _ _).trans hrest2) (L + 1) (by simpa using hupper)
  have hL : L ≤ M := by
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hlen
    have : (L : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hf := hfixed M ((le_max_left _ _).trans hM) L hL N A hN shape hshape base hbase
  have hs := hsmooth M ((le_max_left _ _).trans hrest1) L hlower hupper ((M + L) ^ K)
  have hproduct : ((squarefreeSmoothUpTo (L + 1) ((M + L) ^ K)).card : ℝ) *
      (M : ℝ) ^ (epsilon / 2) ≤ (M : ℝ) ^ epsilon := by
    calc
      _ ≤ (M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]
  constructor
  · intro hdegree
    exact (card_leftBaseShapeFiber_cast_le_of_fixed_counts hN shape
      (fun d hd => (hf d hd).1 hdegree)).trans hproduct
  · intro hdegree
    exact (card_rightBaseShapeFiber_cast_le_of_fixed_counts hN shape
      (fun d hd => (hf d hd).2 hdegree)).trans hproduct

end
end PaperC.V282.MacroscopicBaseFibers
