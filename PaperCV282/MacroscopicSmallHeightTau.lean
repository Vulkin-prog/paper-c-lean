import PaperCV282.MacroscopicSmallHeightComponents
import PaperCV282.MacroscopicPointwiseDefects
import PaperC.Asymptotics.PropositionSixteenOneCore

/-!
# Residual dimension on positive small canonical channels

The exact quotient-core inequality is combined with the proved
macroscopic defect bound and the small-height prime-support envelope.
The resulting binary residual factor is uniformly subpolynomial on the
full logarithmic band. The large-product test is unnecessary for this
bound, so it applies to the whole positive small-height population.
-/

namespace PaperC.V282.MacroscopicSmallHeightTau

open Affine Affine.CanonicalRationalCode ResidualComponentCounts
open SmallHeightResidualComponentEnvelope PropositionSixteenOne
open MacroscopicGeometry MacroscopicShallowSigma MacroscopicSmallHeightComponents
open MacroscopicPointwiseDefects

noncomputable section

/-- The finite residual dimension is bounded by the corrected defects and
the common component envelope on every adequate positive window pair. -/
theorem residualTau_le_corrected_add_componentEnvelope
    {K A L x y : ℕ} (hB : 8 ≤ L + 1) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxK : x + L ≤ K) (hyK : y + L ≤ K)
    (hsmall : hasSmallPositiveCanonicalHeight A L x y) :
    residualTau K A x y L hx hy ≤
      canonicalCorrectedDefectCount A x y L + smallHeightResidualComponentEnvelope L := by
  exact (residualTau_le_canonicalCorrected_add_residual hx hy hxK hyK).trans
    (Nat.add_le_add_left (canonicalResidualComponentCount_le_envelope hB hx hy hsmall) _)

/-- The true residual binary factor is uniformly subpolynomial on the
macroscopic interval, before either start or the coding parameter is chosen. -/
theorem two_pow_residualTau_le_rpow_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ A x : ℕ, x ∈ macroscopicStarts M delta →
      ∀ y : ℕ, y ∈ macroscopicStarts M delta →
      ∀ hx : 2 ≤ x, ∀ hy : 2 ≤ y,
      hasSmallPositiveCanonicalHeight A L x y →
      (2 : ℝ) ^ residualTau (M + L) A x y L hx hy ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨Mdefect, hdefect⟩ := two_pow_correctedDefect_le_rpow_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta (by positivity)
  obtain ⟨Mcomponent, hcomponent⟩ := two_pow_componentEnvelope_le_rpow_eventually
    betaMin betaMax hbetaMin (hbetaMin.trans hbeta) (epsilon / 2) (by positivity)
  obtain ⟨Mlength, hlength⟩ := length_ge_eventually_of_logarithmic_lower betaMin hbetaMin 8
  refine ⟨max Mdefect (max Mcomponent (max Mlength 1)), ?_⟩
  intro M hM L hlower hupper A x hx y hy hxTwo hyTwo hsmall
  have hMd : Mdefect ≤ M := (le_max_left _ _).trans hM
  have hrest : max Mcomponent (max Mlength 1) ≤ M := (le_max_right _ _).trans hM
  have hMc : Mcomponent ≤ M := (le_max_left _ _).trans hrest
  have htail : max Mlength 1 ≤ M := (le_max_right _ _).trans hrest
  have hMl : Mlength ≤ M := (le_max_left _ _).trans htail
  have hMone : 1 ≤ M := (le_max_right _ _).trans htail
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hB : 8 ≤ L + 1 := by
    exact_mod_cast hlength M hMl L (by simpa only [Nat.cast_add, Nat.cast_one] using hlower)
  have hxM : x ≤ M := ((mem_macroscopicStarts M delta x).mp hx).2.le
  have hyM : y ≤ M := ((mem_macroscopicStarts M delta y).mp hy).2.le
  have htau := residualTau_le_corrected_add_componentEnvelope hB hxTwo hyTwo
    (Nat.add_le_add_right hxM L) (Nat.add_le_add_right hyM L) hsmall
  have hD := hdefect M hMd L hlower hupper A x hx y hy
  have hC := hcomponent M hMc L
    (by simpa only [Nat.cast_add, Nat.cast_one] using hlower)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hupper)
  calc
    _ ≤ (2 : ℝ) ^ (canonicalCorrectedDefectCount A x y L +
        smallHeightResidualComponentEnvelope L) := pow_le_pow_right₀ (by norm_num) htau
    _ = (2 : ℝ) ^ canonicalCorrectedDefectCount A x y L *
        (2 : ℝ) ^ smallHeightResidualComponentEnvelope L := pow_add _ _ _
    _ ≤ (M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2) :=
      mul_le_mul hD hC (by positivity) (by positivity)
    _ = (M : ℝ) ^ epsilon := by
      rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- The same bound on the historical subtype used by the exact sector masses. -/
theorem two_pow_pairTau_le_rpow_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ A : ℕ, ∀ hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊,
      ∀ pair : SeparatedBoundedRatioPair ⌈(M : ℝ) ^ delta⌉₊ M L,
      hasSmallPositiveCanonicalHeight A L pair.1.1 pair.1.2 →
      (2 : ℝ) ^ pairTau A hN pair ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨Mzero, hMzero⟩ := two_pow_residualTau_le_rpow_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨Mzero, ?_⟩
  intro M hM L hlower hupper A hN pair hsmall
  have hcoordinates := pair_coordinates_two_le hN pair
  have hp := mem_separatedBoundedRatioPairs.mp pair.2
  exact hMzero M hM L hlower hupper A pair.1.1 hp.1 pair.1.2 hp.2.1
    hcoordinates.1 hcoordinates.2 hsmall

/-- Literal little-oh formulation for the true residual dimension on the
same macroscopic band and exact historical pair representation. -/
theorem pairTau_le_epsilon_length_eventually
    (betaMin betaMax delta eta : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (heta : 0 < eta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ A : ℕ, ∀ hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊,
      ∀ pair : SeparatedBoundedRatioPair ⌈(M : ℝ) ^ delta⌉₊ M L,
      hasSmallPositiveCanonicalHeight A L pair.1.1 pair.1.2 →
      (pairTau A hN pair : ℝ) ≤ eta * (L + 1 : ℝ) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Mweight, hweight⟩ := two_pow_pairTau_le_rpow_eventually
    betaMin betaMax delta (eta * betaMin * Real.log 2)
    hbetaMin hbeta hdelta (by positivity)
  refine ⟨max Mweight 1, ?_⟩
  intro M hM L hlower hupper A hN pair hsmall
  have hMone : 1 ≤ M := (le_max_right _ _).trans hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hpow := hweight M ((le_max_left _ _).trans hM) L hlower hupper A hN pair hsmall
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ pairTau A hN pair) hpow
  rw [Real.log_pow, Real.log_rpow hMpos] at hlog
  have hdim : (pairTau A hN pair : ℝ) ≤ eta * (betaMin * Real.log M) := by
    apply (mul_le_mul_iff_right₀ hlogTwo).mp
    nlinarith only [hlog]
  exact hdim.trans (mul_le_mul_of_nonneg_left hlower heta.le)

end
end PaperC.V282.MacroscopicSmallHeightTau
