import PaperC.Asymptotics.TheoremEightAlignedClosure

set_option maxHeartbeats 1800000

/-!
# Aligned deep-core exclusion above a common lower endpoint

The closed dyadic theorem asks that both starts lie in `[N,2N)`.  Inspection
of its finite assembly shows that the upper endpoint is not used: the
Hamming estimates depend only on `N` and `L`, while both Runge inequalities
are monotone in the first start.  We make that observation explicit here.

The numerical Runge package is evaluated at the witness `N ∈ [N,2N)` and
then transported to the actual start `x ≥ N`.  Consequently the resulting
exclusion applies, in particular, to every bounded-ratio block `[N,M)`,
including pairs crossing dyadic subblocks.
-/

namespace PaperC
namespace BoundedRatioSectorAligned

open Affine.CanonicalRationalCode
open AlignedCoreExclusion
open AlignedDeepCoreExtraction
open CanonicalResidualComponents
open TheoremEightHammingBudget

noncomputable section

/--
Uniform exclusion of an aligned deep core when the two starts merely share
the lower bound `N`.

This strengthens `TheoremEightAlignedClosure.no_aligned_deep_core_eventually`
in its geometric range while using exactly the same finite and asymptotic
ingredients.  No bounded-ratio constant is needed.
-/
theorem no_aligned_deep_core_of_lower_bounds_eventually
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ H, 1 ≤ H → H ≤ (L + 1) ^ A →
      ∀ x : ℕ, N ≤ x →
      ∀ y : ℕ, N ≤ y →
      ∀ c : ReducedCandidate x y (L + 1) H,
        3 * (L + 1) <
          16 *
            (residualComponents x y L c.1.1 c.1.2
              (pairChannelError x y c.1.1 c.1.2)).card →
        False := by
  obtain ⟨Nhamming, hHamming⟩ :=
    TheoremEightAlignedClosure.alignedHammingNumerics_eventually hC
  obtain ⟨Nrunge, hRunge⟩ :=
    AlignedRungeGrowth.rungeNumerics_eventually
      hC (by norm_num : (0 : ℝ) ≤ 65) A
  refine ⟨max 2 (max Nhamming Nrunge), ?_⟩
  intro N hN L hwindow H hH hHupper x hx y hy c hdensity
  have hNtwo : 2 ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail : max Nhamming Nrunge ≤ N :=
    (le_max_right _ _).trans hN
  have hNhamming : Nhamming ≤ N :=
    (le_max_left _ _).trans hNtail
  have hNrunge : Nrunge ≤ N :=
    (le_max_right _ _).trans hNtail
  have hxTwo : 2 ≤ x := hNtwo.trans hx
  have hyTwo : 2 ≤ y := hNtwo.trans hy
  obtain ⟨_hB64, htReal, hconditions⟩ :=
    hHamming N hNhamming L hwindow
  have hfamily :=
    one_sixteenth_le_card_smallExactFreeResidualComponents_of_candidate
      c hxTwo hyTwo (by omega) hdensity
  obtain ⟨ht, hmt, hrows, hvolume⟩ :=
    hconditions
      (smallExactFreeResidualComponents
        x y L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2) 43).card
      hfamily
  have hNmem : N ∈ dyadicBlock N := by
    simp only [dyadicBlock, Finset.mem_Ico]
    omega
  obtain ⟨hRungeAtN, hbaseAtN⟩ :=
    hRunge N hNrunge L hwindow H hH hHupper
      (componentHammingRadius (L + 1)) htReal
      c.1.1 (candidate_fst_pos c) N hNmem
  have hmonotone :
      c.1.1 * N ≤ c.1.1 * x :=
    Nat.mul_le_mul_left c.1.1 hx
  have hRungeRange :
      ∀ k : ℕ, 1 ≤ k → k ≤ 43 * componentHammingRadius (L + 1) →
        (128 * (2 * k) * (3 * H * (L + 1))) ^ (4 * k) <
          c.1.1 * x := by
    intro k hk hkt
    exact (hRungeAtN k hk hkt).trans_le hmonotone
  have hbase :
      2 * (3 * H * (L + 1)) ≤ c.1.1 * x :=
    hbaseAtN.trans hmonotone
  exact
    no_candidate_aligned_core_of_finite_conditions
      (K := 43) c hxTwo hyTwo ht hmt hrows hvolume
      hbase hRungeRange

end

end BoundedRatioSectorAligned
end PaperC
