import PaperCV282.TerminalPartnerCount
import PaperCV282.TerminalSliceContainer
import PaperCV282.KernelEnergyCounting
import PaperCV282.MacroscopicKernelEnergy

/-!
# Counts of ordered terminal masks on a larger-start slice

The hypotheses refer to actual larger starts, smaller partners and window
kernel counts. Both orientations are retained. The two-small-kernel branch
uses the literal binomial energy; the one-small-kernel branch uses the
actual first-start container. All thresholds precede the chosen pair mask.
-/

namespace PaperC.V282.TerminalSliceCounting

open OrderedPairCounting KernelWindowEnergy KernelEnergyCounting MacroscopicKernelEnergy
open TerminalPartnerCount TerminalSliceContainer LogarithmicWordPowers

noncomputable section

/-- Two small kernels at the larger start give the complete two-thirds pair count. -/
theorem card_pairs_with_two_small_kernels_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      betaMin * Real.log X ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log X →
      ∀ s : Finset (ℕ × ℕ), largerStarts s ⊆ Finset.Ico X (2 * X) →
      (∀ x ∈ largerStarts s, smallerPartners s x ⊆ twoKernelPartnerStarts X L x) →
      (∀ x ∈ largerStarts s,
        2 ≤ (smallKernelOffsets (L + 1) (Nat.sqrt (6 * X * (L + 1))) L x).card) →
      (s.card : ℝ) ≤ (X : ℝ) ^ (2 / (3 : ℝ) + epsilon) := by
  have heps : 0 < epsilon / 3 := by positivity
  obtain ⟨Xpartner, hpartner⟩ := card_twoKernelPartnerStarts_le_rpow_eventually
    betaMin betaMax (epsilon / 3) hbetaMin hbetaMax heps
  obtain ⟨Xenergy, henergy⟩ := lemma_three_twenty_four
    betaMax (Real.sqrt 6) (epsilon / 3) hbetaMax.le (by positivity) heps
  obtain ⟨Xfactor, hfactor⟩ := polynomial_factor_le_rpow_eventually
    betaMax hbetaMax.le 2 2 (epsilon / 3) heps
  refine ⟨max Xpartner (max Xenergy (max Xfactor 1)), ?_⟩
  intro X hX L hlower hupper s hstarts hpartners hsmall
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hp : ∀ x ∈ largerStarts s, ((smallerPartners s x).card : ℝ) ≤ (X : ℝ) ^ (epsilon / 3) := by
    intro x hx
    have hh : ((smallerPartners s x).card : ℝ) ≤ ((twoKernelPartnerStarts X L x).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (hpartners x hx)
    exact hh.trans (hpartner X (by omega) L hlower hupper x)
  have he := henergy X (by omega) L hupper (Nat.sqrt (6 * X * (L + 1)))
    (by simpa only [Nat.cast_add, Nat.cast_one] using nat_sqrt_terminal_cap_le X (L + 1))
  have hf : 2 * (L + 1 : ℝ) ^ 2 ≤ (X : ℝ) ^ (epsilon / 3) := by
    simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (L + 1 : ℝ) ^ 2)]
      using hfactor X (by omega) L (by simpa using hupper)
  have hfinite := card_pairs_le_two_energy_mul (Finset.Ico X (2 * X)) s
    (by positivity : 0 ≤ (X : ℝ) ^ (epsilon / 3)) hstarts hsmall hp
  calc
    _ ≤ _ := hfinite
    _ ≤ 2 * ((X : ℝ) ^ (2 / (3 : ℝ) + epsilon / 3) * (L + 1 : ℝ) ^ 2) *
        (X : ℝ) ^ (epsilon / 3) := by gcongr
    _ = (2 * (L + 1 : ℝ) ^ 2) * (X : ℝ) ^ (2 / (3 : ℝ) + epsilon / 3) *
        (X : ℝ) ^ (epsilon / 3) := by ring
    _ ≤ (X : ℝ) ^ (epsilon / 3) * (X : ℝ) ^ (2 / (3 : ℝ) + epsilon / 3) *
        (X : ℝ) ^ (epsilon / 3) := by gcongr
    _ = _ := by rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]; congr 1; ring

/-- One small kernel at the larger start gives the complete three-quarter pair count. -/
theorem card_pairs_with_one_small_kernel_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      betaMin * Real.log X ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log X →
      ∀ s : Finset (ℕ × ℕ), largerStarts s ⊆ Finset.Ico X (2 * X) →
      (∀ x ∈ largerStarts s, smallerPartners s x ⊆ twoKernelPartnerStarts X L x) →
      (∀ x ∈ largerStarts s,
        1 ≤ (smallKernelOffsets (L + 1) (Nat.sqrt (6 * X * (L + 1))) L x).card) →
      (s.card : ℝ) ≤ (X : ℝ) ^ (3 / (4 : ℝ) + epsilon) := by
  have heps : 0 < epsilon / 3 := by positivity
  obtain ⟨Xpartner, hpartner⟩ := card_twoKernelPartnerStarts_le_rpow_eventually
    betaMin betaMax (epsilon / 3) hbetaMin hbetaMax heps
  obtain ⟨Xcontainer, hcontainer⟩ := card_determinantCapFirstStarts_le_three_quarters_eventually
    betaMax (epsilon / 3) hbetaMax.le heps
  obtain ⟨Xfactor, hfactor⟩ := polynomial_factor_le_rpow_eventually
    betaMax hbetaMax.le 2 0 (epsilon / 3) heps
  refine ⟨max Xpartner (max Xcontainer (max Xfactor 1)), ?_⟩
  intro X hX L hlower hupper s hstarts hpartners hsmall
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hp : ∀ x ∈ largerStarts s, ((smallerPartners s x).card : ℝ) ≤ (X : ℝ) ^ (epsilon / 3) := by
    intro x hx
    have hh : ((smallerPartners s x).card : ℝ) ≤ ((twoKernelPartnerStarts X L x).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (hpartners x hx)
    exact hh.trans (hpartner X (by omega) L hlower hupper x)
  have hsub : largerStarts s ⊆ smallKernelFirstStarts X L (Nat.sqrt (6 * X * (L + 1))) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hstarts hx, Finset.card_pos.mp (hsmall x hx)⟩
  have hc : ((largerStarts s).card : ℝ) ≤ (X : ℝ) ^ (3 / (4 : ℝ) + epsilon / 3) := by
    have hh : ((largerStarts s).card : ℝ) ≤
        ((smallKernelFirstStarts X L (Nat.sqrt (6 * X * (L + 1)))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hh.trans (hcontainer X (by omega) L hupper)
  have hf : (2 : ℝ) ≤ (X : ℝ) ^ (epsilon / 3) := by
    simpa using hfactor X (by omega) L (by simpa using hupper)
  have hfinite := card_le_two_mul_largerStarts_mul s ((X : ℝ) ^ (epsilon / 3)) hp
  calc
    _ ≤ _ := hfinite
    _ ≤ 2 * (X : ℝ) ^ (3 / (4 : ℝ) + epsilon / 3) * (X : ℝ) ^ (epsilon / 3) := by gcongr
    _ ≤ (X : ℝ) ^ (epsilon / 3) * (X : ℝ) ^ (3 / (4 : ℝ) + epsilon / 3) *
        (X : ℝ) ^ (epsilon / 3) := by gcongr
    _ = _ := by rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]; congr 1; ring

end
end PaperC.V282.TerminalSliceCounting
