import PaperCV282.FullHostCounting
import PaperC.Asymptotics.RelationalHostsThreeHalves

/-!
# Uniform dyadic estimates for unrestricted square-product hosts

The full prime equations give the retained congruence cover without block
parity restrictions. Its weighted kernel sum has an elementary Euler-product
majorant. The same explicit majorant works for every mask inside the dyadic
square, and is `N^(3/2+o(1))` uniformly when `L + 1 ≤ C log N`.
This is the dyadic host-count component of Proposition 3.7, not the complete
macroscopic rank-profile assertion.
-/

namespace PaperC.V282.FullHostAsymptotics

open Affine TwoWindowParity TwoWindowSquareHosts
open RelationalHostBound RelationalHostsThreeHalves
open scoped BigOperators

noncomputable section

/-- Real-valued finite kernel-sum bound, for any mask in the dyadic square. -/
theorem card_squareProductHosts_cast_le_kernelSum
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ dyadicBlock N ×ˢ dyadicBlock N) :
    ((squareProductHosts L s).card : ℝ) ≤
      8 * (L + 1 : ℝ) * (N : ℝ) *
        ∑ n ∈ Finset.Icc 1 (3 * N),
          LargeKernelWeightedCounting.largeKernelWeight (L + 1) n := by
  have hq := FullHostCounting.card_squareProductHosts_cast_le_kernelSumQ hN hL s hs
  have hcast := (Rat.cast_le (K := ℝ)).2 hq
  simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_sum, cast_largeKernelWeightQ] using hcast

/-- An explicit majorant independent of the chosen pair mask. -/
theorem card_squareProductHosts_cast_le_exp_bound
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ dyadicBlock N ×ˢ dyadicBlock N) :
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

/-- The bound holds for every dyadic mask, with thresholds independent of it.
The power formulation means: for each positive integer `k`, eventually
`card^(2*k) ≤ N^(3*k+1)` throughout the admissible length range. -/
theorem card_squareProductHosts_uniformThreeHalves
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      Admissible C N L → ∀ s : Finset (ℕ × ℕ),
      s ⊆ dyadicBlock N ×ˢ dyadicBlock N →
      ((squareProductHosts L s).card : ℝ) ^ (2 * k) ≤ (N : ℝ) ^ (3 * k + 1) := by
  classical
  have hfull : UniformThreeHalvesSubpolynomialOn (Admissible C)
      (fun N L => ((squareProductHosts L (dyadicBlock N ×ˢ dyadicBlock N)).card : ℝ)) := by
    apply UniformThreeHalves.of_linear_sqrt_mul_subpolynomial
      (relationalHostResidual_uniformSubpolynomial C hC)
    refine ⟨2, ?_⟩
    intro N _ L hNL
    have hfinite := card_squareProductHosts_cast_le_exp_bound hNL.1 hNL.2.1
      (dyadicBlock N ×ˢ dyadicBlock N) (fun _ h => h)
    rw [abs_of_nonneg (by positivity :
      0 ≤ ((squareProductHosts L (dyadicBlock N ×ˢ dyadicBlock N)).card : ℝ))]
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
      squareProductHosts L (dyadicBlock N ×ˢ dyadicBlock N) :=
    Finset.filter_subset_filter _ hs
  have hcard : ((squareProductHosts L s).card : ℝ) ≤
      ((squareProductHosts L (dyadicBlock N ×ˢ dyadicBlock N)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hbound := hN₀ N hN L hNL
  rw [abs_of_nonneg (by positivity)] at hbound
  exact (pow_le_pow_left₀ (by positivity) hcard _).trans hbound

/-- Uniform dyadic `N^(3/2+o(1))` bound for the actual separated full hosts. -/
theorem card_separated_squareProductHosts_uniformThreeHalves
    (C : ℝ) (hC : 0 ≤ C) :
    UniformThreeHalvesSubpolynomialOn (Admissible C)
      (fun N L => ((squareProductHosts L (separatedPairs (dyadicBlock N) L)).card : ℝ)) := by
  intro k hk
  obtain ⟨N₀, hN₀⟩ := card_squareProductHosts_uniformThreeHalves C hC k hk
  refine ⟨N₀, ?_⟩
  intro N hN L hNL
  rw [abs_of_nonneg (by positivity)]
  exact hN₀ N hN L hNL _ (Finset.filter_subset _ _)

end
end PaperC.V282.FullHostAsymptotics
