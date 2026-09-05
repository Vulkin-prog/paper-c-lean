import PaperCV282.FullIntervalHostAsymptotics

/-!
# Real-exponent form of the uniform host estimate

The previous integer-power statement implies the literal
`M^epsilon * M^(3/2)` bound. Thresholds remain independent of the
chosen length, finite pair mask, and positive macroscopic exponent.
-/

namespace PaperC.V282.HostRealPowers

open FullIntervalHostAsymptotics FullHostComparison TwoWindowSquareHosts
open MacroscopicGeometry TwoWindowParity

noncomputable section

/-- Taking a positive integer root of a natural-power inequality. -/
theorem le_rpow_div_of_pow_le {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    {p q : ℕ} (hq : 0 < q) (h : a ^ q ≤ M ^ p) :
    a ≤ M ^ ((p : ℝ) / q) := by
  have hroot : a ≤ (M ^ p) ^ ((q : ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos ha (by positivity)
      (by exact_mod_cast hq)).mpr
    simpa only [Real.rpow_natCast] using h
  simpa only [← Real.rpow_natCast M p, ← Real.rpow_mul hM, div_eq_mul_inv] using hroot

/-- The positive-power host estimate with an arbitrary real error exponent. -/
theorem card_squareProductHosts_le_real_profile
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      ∀ s : Finset (ℕ × ℕ), s ⊆ Finset.Icc 2 M ×ˢ Finset.Icc 2 M →
      ((squareProductHosts L s).card : ℝ) ≤ (M : ℝ) ^ ε * (M : ℝ) ^ (3 / (2 : ℝ)) := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  let k := n + 1
  have hk : 0 < k := by dsimp [k]; omega
  obtain ⟨Mcore, hcore⟩ := card_squareProductHosts_uniformThreeHalves_logarithmic C hC k hk
  refine ⟨max Mcore 1, ?_⟩
  intro M hM L hL s hs
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (le_max_right Mcore 1).trans hM
  have hroot := le_rpow_div_of_pow_le (by positivity :
      (0 : ℝ) ≤ ((squareProductHosts L s).card : ℝ)) (by positivity : (0 : ℝ) ≤ M)
    (by omega : 0 < 2 * k) (hcore M ((le_max_left _ _).trans hM) L hL s hs)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hfrac : ((3 * k + 1 : ℕ) : ℝ) / ((2 * k : ℕ) : ℝ) ≤ ε + 3 / (2 : ℝ) := by
    have hn' : 1 / (k : ℝ) < ε := by simpa [k] using hn
    have hsmall : 1 / (2 * (k : ℝ)) ≤ 1 / (k : ℝ) := by
      apply one_div_le_one_div_of_le hkpos
      linarith
    have heq : ((3 * k + 1 : ℕ) : ℝ) / ((2 * k : ℕ) : ℝ) =
        3 / (2 : ℝ) + 1 / (2 * (k : ℝ)) := by
      push_cast
      field_simp
    rw [heq]
    linarith
  calc
    _ ≤ _ := hroot
    _ ≤ (M : ℝ) ^ (ε + 3 / (2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hMone hfrac
    _ = _ := Real.rpow_add (by positivity) _ _

/-- Start hosts inherit the same bound with a cutoff containing the mask. -/
theorem card_startRelationHosts_le_real_profile
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      ∀ s : Finset (ℕ × ℕ), s ⊆ Finset.Icc 2 M ×ˢ Finset.Icc 2 M →
      ((startRelationHosts (M + L) L s).card : ℝ) ≤
        (M : ℝ) ^ ε * (M : ℝ) ^ (3 / (2 : ℝ)) := by
  obtain ⟨M₀, hM₀⟩ := card_squareProductHosts_le_real_profile C hC ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L hL s hs
  have hcomp : (startRelationHosts (M + L) L s).card ≤ (squareProductHosts L s).card := by
    apply card_startRelationHosts_le_squareProductHosts
    · intro xy hxy
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hs hxy)
      exact ⟨(Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp hy).1⟩
    · intro xy hxy
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hs hxy)
      have hxM := (Finset.mem_Icc.mp hx).2
      have hyM := (Finset.mem_Icc.mp hy).2
      constructor <;> omega
  have hcomp' : ((startRelationHosts (M + L) L s).card : ℝ) ≤
      ((squareProductHosts L s).card : ℝ) := by exact_mod_cast hcomp
  exact hcomp'.trans (hM₀ M hM L hL s hs)

/-- Proposition 3.7 in the literal real-exponent notation. -/
theorem proposition_three_seven_real
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M → ∀ δ : ℝ, 0 < δ →
      ((startRelationHosts (M + L) L (separatedPairs (macroscopicStarts M δ) L)).card : ℝ) ≤
        ((squareProductHosts L (separatedPairs (macroscopicStarts M δ) L)).card : ℝ) ∧
      ((squareProductHosts L (separatedPairs (macroscopicStarts M δ) L)).card : ℝ) ≤
        (M : ℝ) ^ ε * (M : ℝ) ^ (3 / (2 : ℝ)) := by
  obtain ⟨Mh, hh⟩ := card_squareProductHosts_le_real_profile C hC ε hε
  obtain ⟨Mc, hc⟩ := proposition_three_seven C hC 1 (by omega)
  refine ⟨max Mh (max Mc 2), ?_⟩
  intro M hM L hL δ hδ
  have hrest : max Mc 2 ≤ M := (le_max_right _ _).trans hM
  have hcomp := (hc M ((le_max_left _ _).trans hrest) L hL δ hδ).1
  exact ⟨by exact_mod_cast hcomp,
    hh M ((le_max_left _ _).trans hM) L hL _
      (separatedPairs_macroscopicStarts_subset_Icc_product
        ((le_max_right _ _).trans hrest) hδ L)⟩

end
end PaperC.V282.HostRealPowers
