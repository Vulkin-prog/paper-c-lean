import PaperCV282.TerminalSectorMasks
import PaperCV282.TerminalSliceCounting
import PaperCV282.SectorEightWeights

/-!
# Weighted bounds for the actual terminal sector on a larger-start slice

The branch with two forced small kernels uses energy. Its complement
has a two-thirds word-space weight and uses the first-start container.
This finite split retains any real cap and avoids summing rank strata.
-/

namespace PaperC.V282.SectorEightSliceMass

open PropositionSixteenOne ResidualSectorPartition ResidualSectorMass
open SectorEightGeometry TerminalSliceGeometry TerminalSectorMasks TerminalSliceCounting
open SectorEightWeights LogarithmicWordPowers MacroscopicCanonicalCode
open scoped BigOperators

noncomputable section

/-- A subpolynomial pointwise coefficient combines with the actual finite cardinality. -/
theorem weighted_sum_le_rpow_of_card_bound {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (w : alpha → ℝ) {X : ℕ} {a eta c U : ℝ}
    (hX : 0 < X) (hU : 0 ≤ U)
    (hcard : (s.card : ℝ) ≤ (X : ℝ) ^ (a + eta))
    (hcoefficient : c ≤ (X : ℝ) ^ eta)
    (hweight : ∀ p ∈ s, w p ≤ c * U) :
    (∑ p ∈ s, w p) ≤ (X : ℝ) ^ (2 * eta) * ((X : ℝ) ^ a * U) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  calc
    _ ≤ ∑ _p ∈ s, (X : ℝ) ^ eta * U := Finset.sum_le_sum fun p hp =>
      (hweight p hp).trans (mul_le_mul_of_nonneg_right hcoefficient hU)
    _ = (s.card : ℝ) * ((X : ℝ) ^ eta * U) := by simp
    _ ≤ (X : ℝ) ^ (a + eta) * ((X : ℝ) ^ eta * U) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [Real.rpow_add hXpos, show 2 * eta = eta + eta by ring,
      Real.rpow_add hXpos]; ring

/-- Two actual terminal populations give a uniform bound for any compatible weight. -/
theorem sum_sector_eight_slice_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      betaMin * Real.log X ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log X →
      ∀ N M A : ℕ, ∀ hN : 2 ≤ N, 1 ≤ A →
      ∀ s : Finset (SeparatedBoundedRatioPair N M L), s ⊆ sectorPairs N M A L hN 7 →
      (∀ p ∈ s, X ≤ max p.1.1 p.1.2 ∧ max p.1.1 p.1.2 < 2 * X) →
      ∀ U V : ℝ, 0 ≤ U → 0 ≤ V → ∀ w : SeparatedBoundedRatioPair N M L → ℝ,
      (∀ p ∈ s, w p ≤ 4 * U) →
      (∀ p ∈ s, L + 1 - 3 * terminalIndex A p - 1 ≤ 1 → w p ≤ 8 * V) →
      (∑ p ∈ s, w p) ≤ (X : ℝ) ^ epsilon *
        ((X : ℝ) ^ (2 / (3 : ℝ)) * U + (X : ℝ) ^ (3 / (4 : ℝ)) * V) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Xtwo, htwo⟩ := card_pairs_with_two_small_kernels_le_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbetaMax heps
  obtain ⟨Xone, hone⟩ := card_pairs_with_one_small_kernel_le_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbetaMax heps
  obtain ⟨Xfactor, hfactor⟩ := polynomial_factor_le_rpow_eventually
    betaMax hbetaMax.le 8 0 (epsilon / 2) heps
  obtain ⟨Xlength, hlength⟩ := logarithmic_power_lt_rpow_eventually
    betaMax 1 hbetaMax.le (by norm_num) 1 (by omega)
  refine ⟨max Xtwo (max Xone (max Xfactor (max Xlength 1))), ?_⟩
  intro X hX L hlower hupper N M A hN hA s hs hscale U V hU hV w hweight hexception
  have hXpos : 0 < X := by omega
  have hLX : L ≤ X := by
    have hh := hlength X (by omega) (L + 1) (by simpa using hupper)
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hh
    exact_mod_cast (show (L : ℝ) ≤ X by linarith)
  have hfactorEight : (8 : ℝ) ≤ (X : ℝ) ^ (epsilon / 2) := by
    simpa using hfactor X (by omega) L (by simpa using hupper)
  let d := s.filter fun p => 2 ≤ L + 1 - 3 * terminalIndex A p - 1
  let e := s.filter fun p => ¬ 2 ≤ L + 1 - 3 * terminalIndex A p - 1
  have hdsub : d ⊆ s := Finset.filter_subset _ _
  have hesub : e ⊆ s := Finset.filter_subset _ _
  have hdgeometry := image_geometry hN hA (Finset.Subset.trans hdsub hs)
    (fun p hp => hscale p (hdsub hp)) hLX (fun p hp => (Finset.mem_filter.mp hp).2)
  have hegeometry := image_geometry_one hN hA (Finset.Subset.trans hesub hs)
    (fun p hp => hscale p (hesub hp)) hLX
  have hdcard : (d.card : ℝ) ≤ (X : ℝ) ^ (2 / (3 : ℝ) + epsilon / 2) := by
    have hh := htwo X (by omega) L hlower hupper (d.image Subtype.val)
      hdgeometry.1 (fun x _ => hdgeometry.2.1 x) hdgeometry.2.2
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using hh
  have hecard : (e.card : ℝ) ≤ (X : ℝ) ^ (3 / (4 : ℝ) + epsilon / 2) := by
    have hh := hone X (by omega) L hlower hupper (e.image Subtype.val)
      hegeometry.1 (fun x _ => hegeometry.2.1 x) hegeometry.2.2
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using hh
  have hdweight := weighted_sum_le_rpow_of_card_bound d w hXpos hU hdcard
    (show (4 : ℝ) ≤ (X : ℝ) ^ (epsilon / 2) by linarith)
    (fun p hp => hweight p (hdsub hp))
  have heweight := weighted_sum_le_rpow_of_card_bound e w hXpos hV hecard hfactorEight
    (fun p hp => hexception p (hesub hp) (by have hh := (Finset.mem_filter.mp hp).2; omega))
  have hsplit : (∑ p ∈ d, w p) + (∑ p ∈ e, w p) = ∑ p ∈ s, w p :=
    Finset.sum_filter_add_sum_filter_not s _ w
  rw [show 2 * (epsilon / 2) = epsilon by ring] at hdweight heweight
  rw [← hsplit]
  exact (add_le_add hdweight heweight).trans_eq (by ring)

end
end PaperC.V282.SectorEightSliceMass
