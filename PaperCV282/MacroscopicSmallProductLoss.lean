import PaperCV282.SmallProductComponentBound
import PaperCV282.MacroscopicAlignedRunge
import PaperCV282.MacroscopicPointwiseDefects
import PaperCV282.ResidualSectorPartition

/-!
# Pointwise subpolynomial loss on the small-product sector

Since `P#` has `c#` distinct factors greater than `B`, the condition
`P# <= M` already makes `2^c#` subpolynomial. The proved pointwise defect
bound and `tau <= D# + c#` give the same conclusion for `2^tau`.
All thresholds precede the coding parameter, both starts and any pair mask.
-/

namespace PaperC.V282.MacroscopicSmallProductLoss

open Affine CanonicalResidualComponents ResidualComponentCounts
open SmallProductComponentBound MacroscopicGeometry MacroscopicAlignedRunge
open MacroscopicPointwiseDefects PropositionSixteenOne ResidualSectorPartition

noncomputable section

/-- A logarithmic lower bound alone controls every fixed power of the component factor. -/
theorem two_pow_componentCount_pow_le_eventually
    (betaMin : ℝ) (hbetaMin : 0 < betaMin) (k : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      ∀ A x y : ℕ, ∀ hx : 2 ≤ x, ∀ hy : 2 ≤ y,
      canonicalResidualPrimeProduct (A := A) (L := L)
        (show 1 ≤ x by omega) (show 1 ≤ y by omega) ≤ M →
      ((2 : ℝ) ^ canonicalResidualComponentCount A x y L) ^ k ≤ (M : ℝ) := by
  obtain ⟨Mzero, hheight⟩ := height_ge_eventually betaMin hbetaMin (2 ^ k)
  refine ⟨Mzero, ?_⟩
  intro M hM L hLmin A x y hx hy hproduct
  have hheight' : 2 ^ k ≤ L + 1 := hheight M hM (L + 1) (by exact_mod_cast hLmin)
  exact_mod_cast two_pow_componentCount_pow_le_of_smallProduct
    hx hy (hheight'.trans (by omega : L + 1 ≤ L + 2)) hproduct

/-- Literal real-exponent form of the small-product component bound. -/
theorem two_pow_componentCount_le_rpow_eventually
    (betaMin epsilon : ℝ) (hbetaMin : 0 < betaMin) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      ∀ A x y : ℕ, ∀ hx : 2 ≤ x, ∀ hy : 2 ≤ y,
      canonicalResidualPrimeProduct (A := A) (L := L)
        (show 1 ≤ x by omega) (show 1 ≤ y by omega) ≤ M →
      (2 : ℝ) ^ canonicalResidualComponentCount A x y L ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hepsilon
  obtain ⟨Mpower, hpower⟩ := two_pow_componentCount_pow_le_eventually betaMin hbetaMin (n + 1)
  refine ⟨max Mpower 1, ?_⟩
  intro M hM L hLmin A x y hx hy hproduct
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (le_max_right Mpower 1).trans hM
  have hpow := hpower M ((le_max_left _ _).trans hM) L hLmin A x y hx hy hproduct
  have hroot : (2 : ℝ) ^ canonicalResidualComponentCount A x y L ≤
      (M : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (by positivity : (0 : ℝ) < n + 1)).mpr
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
    exact hpow
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hMone hn.le)

/-- The full residual exponential is uniformly subpolynomial when the actual prime product is small. -/
theorem two_pow_pairTau_le_rpow_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : ℕ,
      ∀ p : SeparatedBoundedRatioPair N M L,
        p.1.1 ∈ macroscopicStarts M delta → p.1.2 ∈ macroscopicStarts M delta →
        smallPrimeProduct A hN p →
          (2 : ℝ) ^ pairTau A hN p ≤ (M : ℝ) ^ epsilon := by
  have heps : 0 < epsilon / 2 := by linarith
  obtain ⟨Mcomponent, hcomponent⟩ := two_pow_componentCount_le_rpow_eventually
    betaMin (epsilon / 2) hbetaMin heps
  obtain ⟨Mdefect, hdefect⟩ := two_pow_correctedDefect_le_rpow_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  refine ⟨max Mcomponent (max Mdefect 1), ?_⟩
  intro M hM L hLmin hLmax N hN A p hx hy hsmall
  have htail : max Mdefect 1 ≤ M := (le_max_right _ _).trans hM
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by have := (le_max_right _ _).trans htail; omega)
  have hp := mem_separatedBoundedRatioPairs.mp p.2
  have hcoords := pair_coordinates_two_le hN p
  have hc := hcomponent M ((le_max_left _ _).trans hM) L hLmin
    A p.1.1 p.1.2 hcoords.1 hcoords.2 hsmall
  have hd := hdefect M ((le_max_left _ _).trans htail) L hLmin hLmax
    A p.1.1 hx p.1.2 hy
  have ht : pairTau A hN p ≤ canonicalCorrectedDefectCount A p.1.1 p.1.2 L +
      canonicalResidualComponentCount A p.1.1 p.1.2 L := by
    unfold pairTau
    exact residualTau_le_canonicalCorrected_add_residual hcoords.1 hcoords.2
      (startWindow_le_boundedRatioCutoff hp.1 le_rfl)
      (startWindow_le_boundedRatioCutoff hp.2.1 le_rfl)
  calc
    (2 : ℝ) ^ pairTau A hN p ≤
        (2 : ℝ) ^ (canonicalCorrectedDefectCount A p.1.1 p.1.2 L +
          canonicalResidualComponentCount A p.1.1 p.1.2 L) :=
      pow_le_pow_right₀ (by norm_num) ht
    _ = (2 : ℝ) ^ canonicalCorrectedDefectCount A p.1.1 p.1.2 L *
        (2 : ℝ) ^ canonicalResidualComponentCount A p.1.1 p.1.2 L := pow_add _ _ _
    _ ≤ (M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2) :=
      mul_le_mul hd hc (by positivity) (by positivity)
    _ = (M : ℝ) ^ (epsilon / 2 + epsilon / 2) := (Real.rpow_add hMpos _ _).symm
    _ = (M : ℝ) ^ epsilon := by congr 1; ring

end
end PaperC.V282.MacroscopicSmallProductLoss
