import PaperCV282.FullHostComparison
import PaperC.Asymptotics.PropositionSixteenOneCore
import PaperC.Combinatorics.ResidualComponentCounts
import PaperCV282.LogarithmicWordPowers

/-!
# Finite mass bounds from relational hosts and a rank envelope

Only hosts with positive nullity contribute to the homogeneous weight.
The resulting estimate applies to every mask, including the exact shallow
population, without imposing an endpoint ratio. Residual weights are
controlled using the proved canonical quotient inequality.
-/

namespace PaperC.V282.HostRankMass

open Affine FullHostComparison TwoWindowParity TwoWindowSquareHosts
open PropositionSixteenOne ResidualComponentCounts
open scoped BigOperators

noncomputable section

/-- Homogeneous natural mass on an arbitrary finite pair mask. -/
def relationWeightMass (K L : ℕ) (s : Finset (ℕ × ℕ)) : ℕ :=
  ∑ xy ∈ s, (2 ^ relationRho (twoStartSystem K xy.1 xy.2 L) - 1)

/-- Zero-nullity pairs have zero homogeneous weight. -/
theorem relationWeightMass_eq_sum_hosts (K L : ℕ) (s : Finset (ℕ × ℕ)) :
    relationWeightMass K L s =
      ∑ xy ∈ startRelationHosts K L s,
        (2 ^ relationRho (twoStartSystem K xy.1 xy.2 L) - 1) := by
  classical
  unfold relationWeightMass startRelationHosts
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro xy hxy
  split_ifs with h
  · rfl
  · simp only [ne_eq, not_not] at h
    simp [h]

/-- Monotonicity in the chosen mask. -/
theorem relationWeightMass_mono (K L : ℕ) {s t : Finset (ℕ × ℕ)}
    (hst : s ⊆ t) : relationWeightMass K L s ≤ relationWeightMass K L t := by
  exact Finset.sum_le_sum_of_subset hst

/-- A constant natural envelope need only hold on positive-nullity hosts. -/
theorem relationWeightMass_le_hosts_mul
    (K L W : ℕ) (s : Finset (ℕ × ℕ))
    (hW : ∀ xy ∈ startRelationHosts K L s,
      2 ^ relationRho (twoStartSystem K xy.1 xy.2 L) - 1 ≤ W) :
    relationWeightMass K L s ≤ (startRelationHosts K L s).card * W := by
  rw [relationWeightMass_eq_sum_hosts]
  calc
    _ ≤ ∑ _xy ∈ startRelationHosts K L s, W := Finset.sum_le_sum hW
    _ = _ := by simp

/-- Real-valued host envelope, useful for nonintegral analytic bounds. -/
theorem relationWeightMass_cast_le_hosts_mul
    (K L : ℕ) (W : ℝ) (s : Finset (ℕ × ℕ))
    (hW : ∀ xy ∈ startRelationHosts K L s,
      ((2 ^ relationRho (twoStartSystem K xy.1 xy.2 L) - 1 : ℕ) : ℝ) ≤ W) :
    (relationWeightMass K L s : ℝ) ≤ ((startRelationHosts K L s).card : ℝ) * W := by
  rw [relationWeightMass_eq_sum_hosts, Nat.cast_sum]
  calc
    _ ≤ ∑ _xy ∈ startRelationHosts K L s, W := Finset.sum_le_sum hW
    _ = _ := by simp

/-- Extract a general integer rank budget into its two exponential factors. -/
theorem relationWeightMass_le_hosts_mul_rankEnvelope
    (K L E r : ℕ) (s : Finset (ℕ × ℕ))
    (hrank : ∀ xy ∈ s, relationRho (twoStartSystem K xy.1 xy.2 L) ≤ E + r) :
    relationWeightMass K L s ≤ (startRelationHosts K L s).card * 2 ^ E * 2 ^ r := by
  have hb : relationWeightMass K L s ≤ (startRelationHosts K L s).card * (2 ^ E * 2 ^ r) := by
    apply relationWeightMass_le_hosts_mul
    intro xy hxy
    have hm : xy ∈ s := (Finset.mem_filter.mp hxy).1
    calc
      _ ≤ 2 ^ relationRho (twoStartSystem K xy.1 xy.2 L) := Nat.sub_le _ _
      _ ≤ 2 ^ (E + r) := Nat.pow_le_pow_right (by omega) (hrank xy hm)
      _ = _ := pow_add _ _ _
  simpa only [mul_assoc] using hb

/-- Positive starts and adequate cutoff replace the start hosts by full hosts. -/
theorem relationWeightMass_cast_le_full_hosts_mul
    (K L : ℕ) {W : ℝ} (hWpos : 0 ≤ W) (s : Finset (ℕ × ℕ))
    (hpos : ∀ xy ∈ s, 2 ≤ xy.1 ∧ 2 ≤ xy.2)
    (hcut : ∀ xy ∈ s, xy.1 + L ≤ K + 1 ∧ xy.2 + L ≤ K + 1)
    (hW : ∀ xy ∈ startRelationHosts K L s,
      ((2 ^ relationRho (twoStartSystem K xy.1 xy.2 L) - 1 : ℕ) : ℝ) ≤ W) :
    (relationWeightMass K L s : ℝ) ≤ ((squareProductHosts L s).card : ℝ) * W := by
  refine (relationWeightMass_cast_le_hosts_mul K L W s hW).trans ?_
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast card_startRelationHosts_le_squareProductHosts K L s hpos hcut) hWpos

/-- The residual weight never exceeds the full homogeneous weight. -/
theorem residualWeight_le_homogeneousWeight
    {N M A L : ℕ} (hN : 2 ≤ N) (p : SeparatedBoundedRatioPair N M L) :
    residualWeight A hN p ≤ homogeneousWeight p := by
  rw [homogeneousWeight_eq_systematic_add_residual (A := A) hN p]
  omega

/-- The shallow density test extracts the literal sixth of the word length. -/
theorem pairRho_le_sixth_add_error
    {N M A L E : ℕ} (hN : 2 ≤ N) (p : SeparatedBoundedRatioPair N M L)
    (hc : 6 * canonicalResidualComponentCount A p.1.1 p.1.2 L ≤ L + 1)
    (he : pairSigma A p + canonicalCorrectedDefectCount A p.1.1 p.1.2 L ≤ E) :
    pairRho p ≤ E + (L + 1) / 6 := by
  have ht : pairTau A hN p ≤ canonicalCorrectedDefectCount A p.1.1 p.1.2 L +
      canonicalResidualComponentCount A p.1.1 p.1.2 L := by
    have hp := mem_separatedBoundedRatioPairs.mp p.2
    unfold pairTau
    apply residualTau_le_canonicalCorrected_add_residual
      (pair_coordinates_two_le hN p).1 (pair_coordinates_two_le hN p).2
    · exact startWindow_le_boundedRatioCutoff hp.1 (le_refl L)
    · exact startWindow_le_boundedRatioCutoff hp.2.1 (le_refl L)
  have hdiv : canonicalResidualComponentCount A p.1.1 p.1.2 L ≤ (L + 1) / 6 := by
    omega
  rw [pairRho_eq_pairSigma_add_pairTau (A := A) hN p]
  omega

/-- The floor sixth is bounded by the real sixth root of the exact word count. -/
theorem two_pow_sixth_le_word_rpow (L : ℕ) :
    (2 : ℝ) ^ ((L + 1) / 6) ≤ ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ)) := by
  rw [← Real.rpow_natCast (2 : ℝ) ((L + 1) / 6)]
  rw [← Real.rpow_natCast (2 : ℝ) (L + 1), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h : 6 * ((L + 1) / 6) ≤ L + 1 := Nat.mul_div_le (L + 1) 6
  have hcast : (6 : ℝ) * (((L + 1) / 6 : ℕ) : ℝ) ≤ (L + 1 : ℕ) := by exact_mod_cast h
  linarith

/-- Pointwise shallow homogeneous weight with separately visible error factors. -/
theorem homogeneousWeight_cast_le_shallow_factors
    {N M A L : ℕ} (hN : 2 ≤ N) (p : SeparatedBoundedRatioPair N M L)
    (hc : 6 * canonicalResidualComponentCount A p.1.1 p.1.2 L ≤ L + 1) :
    (homogeneousWeight p : ℝ) ≤
      (2 : ℝ) ^ pairSigma A p *
        (2 : ℝ) ^ canonicalCorrectedDefectCount A p.1.1 p.1.2 L *
        ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ)) := by
  have hr := pairRho_le_sixth_add_error hN p hc (le_refl _)
  have hb : homogeneousWeight p ≤
      2 ^ pairSigma A p * 2 ^ canonicalCorrectedDefectCount A p.1.1 p.1.2 L *
        2 ^ ((L + 1) / 6) := by
    unfold homogeneousWeight
    calc
      _ ≤ 2 ^ pairRho p := Nat.sub_le _ _
      _ ≤ 2 ^ (pairSigma A p + canonicalCorrectedDefectCount A p.1.1 p.1.2 L +
          (L + 1) / 6) := Nat.pow_le_pow_right (by omega) hr
      _ = _ := by rw [pow_add, pow_add]
  have hb' : (homogeneousWeight p : ℝ) ≤
      (2 : ℝ) ^ pairSigma A p * (2 : ℝ) ^ canonicalCorrectedDefectCount A p.1.1 p.1.2 L *
        (2 : ℝ) ^ ((L + 1) / 6) := by exact_mod_cast hb
  exact hb'.trans (mul_le_mul_of_nonneg_left (two_pow_sixth_le_word_rpow L) (by positivity))

end
end PaperC.V282.HostRankMass
