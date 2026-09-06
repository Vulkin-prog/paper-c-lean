import PaperCV282.SaddlePoissonScales
import PaperCV282.BadStartRankinAsymptotics
import PaperCV282.CutoffGraphFreeCutoff

/-!
# Arithmetic deletion and graph budgets at the actual cutoff saddles

The same natural threshold works before every logarithmic window and mask.
Only deletion uses the previously declared ordinary PNT premise; the graph
bounds and scalar admissibility contain no prime-counting input.
-/

namespace PaperC.V282.SaddleArithmeticBounds

open Set Filter Topology SaddleParameters SaddleScales SaddleCutoffAdmissibility SaddlePoissonScales
open PrimeEulerPNT BadStartRankinAsymptotics MaskedArithmeticGeometry
open CutoffGraphDegree CutoffGraphFreeCutoff MaskedPairGeometry

noncomputable section

/-- The actual masked bad-start fraction has exponent -w/a+eta*nu at the true saddle. -/
theorem normalized_fullBadMask_saddle_cost_le_eventually
    (hPNT : PrimeNumberTheoremRemainder) (a betaMax eta : ℝ)
    (ha : 0 < a) (hbeta : 0 < betaMax) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N → ∀ mask : Finset ℕ,
      ((fullBadMask N L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask).card : ℝ) / N ≤
        Real.exp (-saddleCutoff a (Real.log N) / a + eta * saddleNu a (Real.log N)) := by
  obtain ⟨Nbad, hbad⟩ := normalized_fullBadMask_saddle_le_eventually hPNT ha betaMax eta hbeta heta
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ndomain, hdomain⟩ := eventually_atTop.1
    (hnatlog.eventually (eventually_ge_atTop (saddleThreshold a)))
  refine ⟨max Nbad Ndomain, ?_⟩
  intro N hN L hL mask
  have hH := hdomain N (by omega)
  have hcost : saddleCost (saddleNu a (Real.log N)) = saddleCutoff a (Real.log N) / a := by
    have h := saddleCutoff_equation ha hH
    change saddleCutoff a (Real.log N) = a * saddleCost (saddleNu a (Real.log N)) at h
    rw [h]
    field_simp [ha.ne']
  have h := hbad N (by omega) L hL mask
  simpa only [hcost, neg_div] using h

/-- Both actual all-site graph budgets at the true saddle, with no PNT premise. -/
theorem normalized_degree_and_edges_saddle_le_eventually
    (a betaMax eta : ℝ) (ha : 0 < a) (hbeta : 0 < betaMax) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
      (cutoffMaxDegree L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask : ℝ) / N ≤
        Real.exp (-saddleCutoff a (Real.log N) + eta * saddleNu a (Real.log N)) ∧
      ((maskedSupportEdges L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask).card : ℝ) / (N : ℝ) ^ 2 ≤
        Real.exp (-saddleCutoff a (Real.log N) + eta * saddleNu a (Real.log N)) := by
  obtain ⟨c, C, hc, hC, Hband, hband⟩ := saddleCutoff_sqrt_log_band_eventually ha
  obtain ⟨Ngraph, hgraph⟩ := normalized_degree_and_edges_free_cutoff_le_eventually
    c C betaMax eta hc hC hbeta heta
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nband, hNband⟩ := eventually_atTop.1 (hnatlog.eventually (eventually_ge_atTop Hband))
  refine ⟨max Ngraph Nband, ?_⟩
  intro N hN L hL mask hmask
  obtain ⟨hlo, hhi⟩ := hband (Real.log N) (hNband N (by omega))
  exact hgraph N (by omega) (saddleCutoff a (Real.log N)) hlo hhi L hL mask hmask

/-- Uniform eventual deletion of at most half the ambient block.
This supplies comparability of the retained full-block mean, without claiming it for sparse masks. -/
theorem fullBadStarts_fraction_le_half_eventually
    (hPNT : PrimeNumberTheoremRemainder) (a betaMax : ℝ)
    (ha : 0 < a) (hbeta : 0 < betaMax) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ((fullBadStarts N L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊).card : ℝ) / N ≤ 1 / 2 := by
  obtain ⟨Nbad, hbad⟩ := normalized_fullBadMask_saddle_cost_le_eventually
    hPNT a betaMax 1 ha hbeta (by norm_num)
  obtain ⟨Nsmall, hsmall⟩ := saddle_exponential_le_eventually a (1 / a) 1 (1 / 2)
    ha (by positivity) (by norm_num)
  refine ⟨max Nbad Nsmall, ?_⟩
  intro N hN L hL
  have h := hbad N (by omega) L hL (dyadicBlock N)
  have hmask : fullBadMask N L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ (dyadicBlock N) =
      fullBadStarts N L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ :=
    Finset.inter_eq_right.mpr (fullBadStarts_subset_block N L _)
  rw [hmask] at h
  apply h.trans
  have heq : -saddleCutoff a (Real.log N) / a + 1 * saddleNu a (Real.log N) =
      -(1 / a) * saddleCutoff a (Real.log N) + 1 * saddleNu a (Real.log N) := by ring
  rw [heq]
  exact hsmall N (by omega)

end
end PaperC.V282.SaddleArithmeticBounds
