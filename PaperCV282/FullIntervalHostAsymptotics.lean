import PaperCV282.FullIntervalHostCounting
import PaperC.Asymptotics.RelationalHostsThreeHalves
import PaperCV282.MacroscopicGeometry
import PaperCV282.FullHostComparison

/-!
# Uniform global positive-interval estimates for unrestricted square-product hosts

The full prime equations give the retained congruence cover without block
parity restrictions. Its weighted kernel sum has an elementary Euler-product
majorant. The same explicit majorant works for every mask inside the global positive-interval
square, and is `N^(3/2+o(1))` uniformly when `L + 1 ≤ C log N`.
The global square includes pairs at different spatial scales. The
weighted rank-profile assertion remains a separate result.
-/

namespace PaperC.V282.FullIntervalHostAsymptotics

open Affine TwoWindowParity TwoWindowSquareHosts
open RelationalHostBound RelationalHostsThreeHalves
open scoped BigOperators

noncomputable section

/-- Real-valued finite kernel-sum bound, for any mask in the global positive-interval square. -/
theorem card_squareProductHosts_cast_le_kernelSum
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ Finset.Icc 2 N ×ˢ Finset.Icc 2 N) :
    ((squareProductHosts L s).card : ℝ) ≤
      8 * (L + 1 : ℝ) * (N : ℝ) *
        ∑ n ∈ Finset.Icc 1 (3 * N),
          LargeKernelWeightedCounting.largeKernelWeight (L + 1) n := by
  have hq := FullIntervalHostCounting.card_squareProductHosts_Icc_cast_le_kernelSumQ hN hL s hs
  have hcast := (Rat.cast_le (K := ℝ)).2 hq
  simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_sum, cast_largeKernelWeightQ] using hcast

/-- An explicit majorant independent of the chosen pair mask. -/
theorem card_squareProductHosts_cast_le_exp_bound
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ Finset.Icc 2 N ×ˢ Finset.Icc 2 N) :
    ((squareProductHosts L s).card : ℝ) ≤
      8 * (L + 1 : ℝ) * (N : ℝ) * Real.sqrt (3 * N) *
        Real.exp (4 * Real.sqrt (L + 1)) := by
  have hfinite := card_squareProductHosts_cast_le_kernelSum hN hL s hs
  have hsum := sum_largeKernelWeight_le_sqrt_mul_exp (L + 1) (3 * N) (by omega)
  have hsum' :
      (∑ n ∈ Finset.Icc 1 (3 * N),
          LargeKernelWeightedCounting.largeKernelWeight (L + 1) n) ≤
        Real.sqrt (3 * (N : ℝ)) * Real.exp (4 * Real.sqrt (L + 1 : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hsum
  calc
    _ ≤ _ := hfinite
    _ ≤ 8 * (L + 1 : ℝ) * (N : ℝ) *
        (Real.sqrt (3 * (N : ℝ)) * Real.exp (4 * Real.sqrt (L + 1 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = _ := by ring

/-- The bound holds for every global positive-interval mask, with thresholds independent of it.
The power formulation means: for each positive integer `k`, eventually
`card^(2*k) ≤ N^(3*k+1)` throughout the admissible length range. -/
theorem card_squareProductHosts_uniformThreeHalves
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      Admissible C N L → ∀ s : Finset (ℕ × ℕ),
      s ⊆ Finset.Icc 2 N ×ˢ Finset.Icc 2 N →
      ((squareProductHosts L s).card : ℝ) ^ (2 * k) ≤ (N : ℝ) ^ (3 * k + 1) := by
  classical
  have hfull : UniformThreeHalvesSubpolynomialOn (Admissible C)
      (fun N L => ((squareProductHosts L (Finset.Icc 2 N ×ˢ Finset.Icc 2 N)).card : ℝ)) := by
    apply UniformThreeHalves.of_linear_sqrt_mul_subpolynomial
      (relationalHostResidual_uniformSubpolynomial C hC)
    refine ⟨2, ?_⟩
    intro N _ L hNL
    have hfinite := card_squareProductHosts_cast_le_exp_bound hNL.1 hNL.2.1
      (Finset.Icc 2 N ×ˢ Finset.Icc 2 N) (fun _ h => h)
    rw [abs_of_nonneg (by positivity :
      0 ≤ ((squareProductHosts L (Finset.Icc 2 N ×ˢ Finset.Icc 2 N)).card : ℝ))]
    refine hfinite.trans_eq ?_
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hresidual : 0 ≤ relationalHostResidual N L := by
      unfold relationalHostResidual
      positivity
    rw [abs_of_nonneg hresidual]
    unfold relationalHostResidual
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  intro k hk
  obtain ⟨N₀, hN₀⟩ := hfull k hk
  refine ⟨N₀, ?_⟩
  intro N hN L hNL s hs
  have hsubset : squareProductHosts L s ⊆
      squareProductHosts L (Finset.Icc 2 N ×ˢ Finset.Icc 2 N) :=
    Finset.filter_subset_filter _ hs
  have hcard : ((squareProductHosts L s).card : ℝ) ≤
      ((squareProductHosts L (Finset.Icc 2 N ×ˢ Finset.Icc 2 N)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hbound := hN₀ N hN L hNL
  rw [abs_of_nonneg (by positivity)] at hbound
  exact (pow_le_pow_left₀ (by positivity) hcard _).trans hbound

/-- Uniform global positive-interval `N^(3/2+o(1))` bound for the actual separated full hosts. -/
theorem card_separated_squareProductHosts_uniformThreeHalves
    (C : ℝ) (hC : 0 ≤ C) :
    UniformThreeHalvesSubpolynomialOn (Admissible C)
      (fun N L => ((squareProductHosts L (separatedPairs (Finset.Icc 2 N) L)).card : ℝ)) := by
  intro k hk
  obtain ⟨N₀, hN₀⟩ := card_squareProductHosts_uniformThreeHalves C hC k hk
  refine ⟨N₀, ?_⟩
  intro N hN L hNL
  rw [abs_of_nonneg (by positivity)]
  exact hN₀ N hN L hNL _ (Finset.filter_subset _ _)

/-- In a fixed logarithmic band the finite condition `L ≤ N` is automatic
eventually. The resulting threshold is still independent of every pair mask. -/
theorem card_squareProductHosts_uniformThreeHalves_logarithmic
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ Finset.Icc 2 N ×ˢ Finset.Icc 2 N →
      ((squareProductHosts L s).card : ℝ) ^ (2 * k) ≤ (N : ℝ) ^ (3 * k + 1) := by
  obtain ⟨Nlength, hlength⟩ :=
    ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually C hC 1 (by omega)
  intro k hk
  obtain ⟨Ncore, hcore⟩ := card_squareProductHosts_uniformThreeHalves C hC k hk
  refine ⟨max Nlength (max Ncore 2), ?_⟩
  intro N hN L hlog s hs
  have hNlength : Nlength ≤ N := (le_max_left _ _).trans hN
  have hNrest : max Ncore 2 ≤ N := (le_max_right _ _).trans hN
  have hNcore : Ncore ≤ N := (le_max_left _ _).trans hNrest
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hNrest
  have hlength' : (L + 1 : ℕ) + 1 ≤ N := by
    have hreal := hlength N hNlength (L + 1) hlog
    simp only [pow_one] at hreal
    exact_mod_cast hreal
  exact hcore N hNcore L ⟨hNtwo, by omega, hlog⟩ s hs

/-- The unrestricted macroscopic host bound of Proposition 3.7. The threshold
also works for all positive macroscopic exponents `δ`, since every such
start interval lies in the same global positive square. -/
theorem proposition_three_seven_full_hosts
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ k : ℕ, 0 < k → ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      ∀ δ : ℝ, 0 < δ →
      ((squareProductHosts L
        (separatedPairs (MacroscopicGeometry.macroscopicStarts M δ) L)).card : ℝ) ^
        (2 * k) ≤ (M : ℝ) ^ (3 * k + 1) := by
  intro k hk
  obtain ⟨Mcore, hcore⟩ := card_squareProductHosts_uniformThreeHalves_logarithmic C hC k hk
  refine ⟨max Mcore 2, ?_⟩
  intro M hM L hlog δ hδ
  exact hcore M ((le_max_left _ _).trans hM) L hlog _
    (MacroscopicGeometry.separatedPairs_macroscopicStarts_subset_Icc_product
      ((le_max_right _ _).trans hM) hδ L)

/-- Both host inequalities in Proposition 3.7, in the explicit uniform power
formulation of the upper bound. The cylinder `M + L` contains every vertex
of the macroscopic pair mask, so the start-relation count is the actual
one for these windows. -/
theorem proposition_three_seven
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ k : ℕ, 0 < k → ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      ∀ δ : ℝ, 0 < δ →
      (FullHostComparison.startRelationHosts (M + L) L
        (separatedPairs (MacroscopicGeometry.macroscopicStarts M δ) L)).card ≤
        (squareProductHosts L
          (separatedPairs (MacroscopicGeometry.macroscopicStarts M δ) L)).card ∧
      ((squareProductHosts L
        (separatedPairs (MacroscopicGeometry.macroscopicStarts M δ) L)).card : ℝ) ^
        (2 * k) ≤ (M : ℝ) ^ (3 * k + 1) := by
  intro k hk
  obtain ⟨Mcore, hcore⟩ := proposition_three_seven_full_hosts C hC k hk
  refine ⟨max Mcore 2, ?_⟩
  intro M hM L hlog δ hδ
  have hsubset := MacroscopicGeometry.separatedPairs_macroscopicStarts_subset_Icc_product
    ((le_max_right _ _).trans hM) hδ L
  refine ⟨?_, hcore M ((le_max_left _ _).trans hM) L hlog δ hδ⟩
  apply FullHostComparison.card_startRelationHosts_le_squareProductHosts
  · intro xy hxy
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hsubset hxy)
    exact ⟨(Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp hy).1⟩
  · intro xy hxy
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hsubset hxy)
    have hxM := (Finset.mem_Icc.mp hx).2
    have hyM := (Finset.mem_Icc.mp hy).2
    constructor <;> omega

end
end PaperC.V282.FullIntervalHostAsymptotics
