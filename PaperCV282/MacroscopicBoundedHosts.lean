import PaperCV282.MacroscopicBaseFibers
import PaperCV282.SizeTwoHostAsymptotics
import PaperC.Asymptotics.BoundedRatioNonterminalRealHosts

/-!
# Unconditional counts of hosts with a bounded residual component

The exact finite source disjunction separates two singleton offsets from
the orientations with mobile degree at least two. Both arithmetic branches
have been proved internally; summing bases and shapes gives `M^(1+epsilon)`.
-/

namespace PaperC.V282.MacroscopicBoundedHosts

open PropositionSixteenOne BoundedRatioComponentHosts BoundedRatioNonterminalHostCounts
open BoundedRatioNonterminalRealHosts MacroscopicBaseFibers SizeTwoHostAsymptotics

noncomputable section

/-- A fixed shape with two offsets is contained in the genuine size-two host set. -/
theorem twoOffsetShape_subset_sizeTwoHosts
    {N M A L K : ℕ} (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hsize : shape.1.card + shape.2.card = 2) :
    boundedComponentHostsOfShape N M A L K shape ⊆ boundedComponentHosts N M A L 2 := by
  intro pair hpair
  obtain ⟨_, C, hC, _, hleft, hright⟩ := mem_boundedComponentHostsOfShape.mp hpair
  have hcard := card_componentOffsets pair.1.1 pair.1.2 L C
  rw [hleft, hright] at hcard
  exact mem_boundedComponentHosts.mpr ⟨C, hC, by omega⟩

/-- Every fixed support-size bound has a uniform linear host profile.
The lower endpoint and canonical selector are quantified after the threshold. -/
theorem card_boundedHosts_le_linear_profile_eventually
    (K : ℕ) (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ N A : ℕ, 2 ≤ N →
      ((boundedComponentHosts N M A L K).card : ℝ) ≤ (M : ℝ) ^ epsilon * M := by
  have heps : 0 < epsilon / 2 := by linarith
  obtain ⟨Mtwo, htwo⟩ := card_sizeTwoHosts_le_linear_profile_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbetaMax.le heps
  obtain ⟨Mfib, hfib⟩ := baseShapeFibers_le_rpow_eventually
    K betaMin betaMax (epsilon / 2) hbetaMin hbetaMax heps
  obtain ⟨Mshape, hshape⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    betaMax hbetaMax.le ((K + 1 : ℝ) ^ 2) (2 * K) (epsilon / 2) heps
  refine ⟨max Mtwo (max Mfib (max Mshape 2)), ?_⟩
  intro M hM L hlower hupper N A hN
  have hrest1 : max Mfib (max Mshape 2) ≤ M := (le_max_right _ _).trans hM
  have hrest2 : max Mshape 2 ≤ M := (le_max_right _ _).trans hrest1
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hrest2
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have htwoCount := htwo M ((le_max_left _ _).trans hM) L hlower hupper N A hN
  have hf := hfib M ((le_max_left _ _).trans hrest1) L hlower hupper N A hN
  have hs := hshape M ((le_max_left _ _).trans hrest2) L (by simpa using hupper)
  rw [abs_of_nonneg (by positivity)] at hs
  have hsCast : ((((K + 1) * (L + 1) ^ K) ^ 2 : ℕ) : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    convert hs using 1
    push_cast
    ring
  have hsource := card_boundedComponentHosts_cast_le_sourceDisjunction hN
    ((M : ℝ) ^ (epsilon / 2) * M) ((M : ℝ) ^ (epsilon / 2))
    (by positivity) (by positivity)
    (fun shape _ hsize => (show ((boundedComponentHostsOfShape N M A L K shape).card : ℝ) ≤
        ((boundedComponentHosts N M A L 2).card : ℝ) by
      exact_mod_cast Finset.card_le_card (twoOffsetShape_subset_sizeTwoHosts shape hsize)).trans htwoCount)
    (fun shape hshape hdegree base hbase => (hf shape hshape base hbase).1 hdegree)
    (fun shape hshape hdegree base hbase => (hf shape hshape base hbase).2 hdegree)
  have hmax : max ((M : ℝ) ^ (epsilon / 2) * M)
      (((M - N : ℕ) : ℝ) * (M : ℝ) ^ (epsilon / 2)) ≤ (M : ℝ) ^ (epsilon / 2) * M := by
    apply max_le le_rfl
    have hwidth : ((M - N : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M N
    calc
      _ ≤ (M : ℝ) * (M : ℝ) ^ (epsilon / 2) := mul_le_mul_of_nonneg_right hwidth (by positivity)
      _ = _ := mul_comm _ _
  calc
    _ ≤ _ := hsource
    _ ≤ (M : ℝ) ^ (epsilon / 2) * ((M : ℝ) ^ (epsilon / 2) * M) :=
      mul_le_mul hsCast hmax (by positivity) (by positivity)
    _ = _ := by rw [← mul_assoc, ← Real.rpow_add hMpos,
      show epsilon / 2 + epsilon / 2 = epsilon by ring]

end
end PaperC.V282.MacroscopicBoundedHosts
