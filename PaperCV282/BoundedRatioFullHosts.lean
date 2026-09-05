import PaperCV282.FullIntervalHostAsymptotics

/-!
# Full hosts at the lower scale of a bounded-ratio interval

The global host bound at the upper endpoint transfers to the lower scale
by reserving one power of the lower endpoint to absorb the fixed ratio.
The threshold is chosen before the upper endpoint, the window length and
the pair mask. The argument retains all pairs, including different scales.
-/

namespace PaperC.V282.BoundedRatioFullHosts

open TwoWindowParity TwoWindowSquareHosts

noncomputable section

/-- Uniform full-host bound at scale `N` when the upper endpoint is at most `κ*N`.
No lower bound on `κ` is necessary: impossible endpoint conditions are allowed. -/
theorem card_squareProductHosts_uniformThreeHalves_boundedRatio
    (C : ℝ) (hC : 0 ≤ C) (κ : ℕ) :
    ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ,
      N ≤ M → M ≤ κ * N → ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ Finset.Icc 2 M ×ˢ Finset.Icc 2 M →
      ((squareProductHosts L s).card : ℝ) ^ (2 * k) ≤ (N : ℝ) ^ (3 * k + 1) := by
  intro k hk
  obtain ⟨Ncore, hcore⟩ :=
    FullIntervalHostAsymptotics.card_squareProductHosts_uniformThreeHalves_logarithmic
      C hC (2 * k) (by omega)
  refine ⟨max 2 (max Ncore (κ ^ (6 * k + 1))), ?_⟩
  intro N hN M hNM hMκ L hlog s hs
  have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
  have hNrest : max Ncore (κ ^ (6 * k + 1)) ≤ N := (le_max_right _ _).trans hN
  have hNcore : Ncore ≤ N := (le_max_left _ _).trans hNrest
  have hκN : κ ^ (6 * k + 1) ≤ N := (le_max_right _ _).trans hNrest
  have hlogNM : Real.log N ≤ Real.log M :=
    Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by exact_mod_cast hNM)
  have hlogM : ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M :=
    hlog.trans (mul_le_mul_of_nonneg_left hlogNM hC)
  have hglobal := hcore M (hNcore.trans hNM) L hlogM s hs
  have hglobal' :
      ((squareProductHosts L s).card : ℝ) ^ (4 * k) ≤ (M : ℝ) ^ (6 * k + 1) := by
    simpa only [show 2 * (2 * k) = 4 * k by omega,
      show 3 * (2 * k) + 1 = 6 * k + 1 by omega] using hglobal
  have hκcast : (κ : ℝ) ^ (6 * k + 1) ≤ (N : ℝ) := by
    exact_mod_cast hκN
  have hMcast : (M : ℝ) ≤ (κ : ℝ) * (N : ℝ) := by
    exact_mod_cast hMκ
  have hscaled :
      ((squareProductHosts L s).card : ℝ) ^ (4 * k) ≤ (N : ℝ) ^ (6 * k + 2) := by
    calc
      _ ≤ (M : ℝ) ^ (6 * k + 1) := hglobal'
      _ ≤ ((κ : ℝ) * (N : ℝ)) ^ (6 * k + 1) :=
        pow_le_pow_left₀ (by positivity) hMcast _
      _ = (κ : ℝ) ^ (6 * k + 1) * (N : ℝ) ^ (6 * k + 1) := mul_pow _ _ _
      _ ≤ (N : ℝ) * (N : ℝ) ^ (6 * k + 1) :=
        mul_le_mul_of_nonneg_right hκcast (by positivity)
      _ = (N : ℝ) ^ (6 * k + 2) := by
        rw [← pow_succ']
  have hsquare :
      (((squareProductHosts L s).card : ℝ) ^ (2 * k)) ^ 2 ≤
        ((N : ℝ) ^ (3 * k + 1)) ^ 2 := by
    simpa only [← pow_mul, show (2 * k) * 2 = 4 * k by omega,
      show (3 * k + 1) * 2 = 6 * k + 2 by omega] using hscaled
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare

/-- Both host inequalities on `[N,M)`, with the upper bound normalized at scale `N`. -/
theorem proposition_three_seven_boundedRatio
    (C : ℝ) (hC : 0 ≤ C) (κ : ℕ) :
    ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ,
      N ≤ M → M ≤ κ * N → ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log N →
      (FullHostComparison.startRelationHosts (M + L) L
        (separatedPairs (Finset.Ico N M) L)).card ≤
        (squareProductHosts L (separatedPairs (Finset.Ico N M) L)).card ∧
      ((squareProductHosts L (separatedPairs (Finset.Ico N M) L)).card : ℝ) ^
        (2 * k) ≤ (N : ℝ) ^ (3 * k + 1) := by
  intro k hk
  obtain ⟨Ncore, hcore⟩ :=
    card_squareProductHosts_uniformThreeHalves_boundedRatio C hC κ k hk
  refine ⟨max Ncore 2, ?_⟩
  intro N hN M hNM hMκ L hlog
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hN
  have hsubset : separatedPairs (Finset.Ico N M) L ⊆
      Finset.Icc 2 M ×ˢ Finset.Icc 2 M := by
    intro xy hxy
    have hpair := (mem_separatedPairs (Finset.Ico N M) L xy.1 xy.2).mp hxy
    have hx := Finset.mem_Ico.mp hpair.1
    have hy := Finset.mem_Ico.mp hpair.2.1
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hNtwo.trans hx.1, hx.2.le⟩,
        Finset.mem_Icc.mpr ⟨hNtwo.trans hy.1, hy.2.le⟩⟩
  refine ⟨?_, hcore N ((le_max_left _ _).trans hN) M hNM hMκ L hlog _ hsubset⟩
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
end PaperC.V282.BoundedRatioFullHosts
