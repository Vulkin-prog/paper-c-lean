import PaperCV282.DensityAlignedRunge

/-!
# Article Proposition 3.19 at every fixed positive density

The actual corrected canonical residual count is o(B), uniformly on the
macroscopic logarithmic band. Component extraction, the finite Hamming
volume bound and Runge's contradiction are all proved internally.
-/

namespace PaperC.V282.DensityAlignedExclusion

open DensityAlignedRunge DensityHammingBudget MacroscopicAlignedRunge MacroscopicGeometry
open Affine.CanonicalRationalCode AlignedCoreExclusion CanonicalResidualComponents
open ResidualComponentCounts TheoremEightHammingBudget SectionElevenPartition TwoWindowParity

noncomputable section

/-- No candidate has residual density at least the reciprocal of a fixed positive integer. -/
theorem no_candidate_eventually
    (betaMin betaMax delta : ℝ) (hmin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (A D : ℕ) (hD : 0 < D) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ H : ℕ, 1 ≤ H → H ≤ (L + 1) ^ A →
      ∀ x ∈ macroscopicStarts M delta, ∀ y ∈ macroscopicStarts M delta,
      ∀ c : ReducedCandidate x y (L + 1) H,
        L + 1 ≤ D * (residualComponents x y L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2)).card → False := by
  obtain ⟨Mh, hh⟩ := conditions_eventually (4 * D) (by positivity) betaMin hmin
  obtain ⟨Mr, hr⟩ := runge_general_cutoff_eventually betaMin betaMax delta hmin hbeta hdelta A (8 * D)
  obtain ⟨Mt, ht⟩ := translationRange_macroscopic_eventually betaMin betaMax delta hmin hbeta hdelta A
  obtain ⟨Mb, hb⟩ := height_ge_eventually betaMin hmin (4 * D)
  refine ⟨max 2 (max Mh (max Mr (max Mt Mb))), ?_⟩
  intro M hM L hlo hhi H hH hHB x hx y hy c hdense
  have hMtwo : 2 ≤ M := by omega
  have hxTwo := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hx)).1
  have hyTwo := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hy)).1
  have hB : 4 * D ≤ L + 1 := hb M (by omega) (L + 1) (by simpa using hlo)
  obtain ⟨_, htReal, hconditions⟩ := hh M (by omega) (L + 1) (by simpa using hlo)
  have hfamily := density_small_components c hxTwo hyTwo hD hB hdense
  obtain ⟨htPos, hmt, hrows, hvolume⟩ := hconditions _ hfamily
  have hbase := ht M (by omega) (L + 1) (by simpa using hlo) (by simpa using hhi)
    H hHB c.1.1 (candidate_fst_pos c) x hx
  have hrunge : ∀ k : ℕ, 1 ≤ k → k ≤ (8 * D) * componentHammingRadius (L + 1) →
      (128 * (2 * k) * (3 * H * (L + 1))) ^ (4 * k) < c.1.1 * x := by
    intro k hk hkt
    exact hr M (by omega) (L + 1) (by simpa using hlo) (by simpa using hhi)
      H hH hHB (componentHammingRadius (L + 1)) htReal k hk hkt
      c.1.1 (candidate_fst_pos c) x hx
  exact no_candidate_aligned_core_of_finite_conditions
    (K := 8 * D) c hxTwo hyTwo htPos hmt hrows hvolume hbase hrunge

/-- Uniform reciprocal-integer density exclusion for the actual canonical channel. -/
theorem canonical_count_small_eventually
    (betaMin betaMax delta : ℝ) (hmin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (A D : ℕ) (hD : 0 < D) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ x ∈ macroscopicStarts M delta, ∀ y ∈ macroscopicStarts M delta,
        IsCanonicallyAligned A L x y → D * canonicalResidualComponentCount A x y L < L + 1 := by
  obtain ⟨Mcore, hcore⟩ := no_candidate_eventually betaMin betaMax delta hmin hbeta hdelta A D hD
  refine ⟨max 2 Mcore, ?_⟩
  intro M hM L hlo hhi x hx y hy haligned
  have hMtwo : 2 ≤ M := by omega
  have hxTwo := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hx)).1
  have hyTwo := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hy)).1
  obtain ⟨c, hchoice⟩ := haligned
  have hcard := card_residualComponents (L := L)
    (candidate_fst_pos c) (candidate_snd_pos c) (candidate_coprime c) hxTwo hyTwo
    (show pairChannelError x y c.1.1 c.1.2 = (c.1.2 : ℤ) * y - (c.1.1 : ℤ) * x by rfl)
  by_contra hbad
  have hc : L + 1 ≤ D * (residualComponents x y L c.1.1 c.1.2
      (pairChannelError x y c.1.1 c.1.2)).card := by
    rw [hcard]
    have hn : L + 1 ≤ D * canonicalResidualComponentCount A x y L := by omega
    simpa only [canonicalResidualComponentCount, hchoice] using hn
  exact hcore M (by omega) L hlo hhi ((L + 1) ^ A)
    (Nat.one_le_pow _ _ (by omega)) le_rfl x hx y hy c hc

/-- Literal Proposition 3.19: every fixed real positive density is eventually excluded. -/
theorem proposition_three_nineteen
    (betaMin betaMax delta alpha : ℝ) (hmin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (halpha : 0 < alpha) (A : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ x ∈ macroscopicStarts M delta, ∀ y ∈ macroscopicStarts M delta,
        IsCanonicallyAligned A L x y →
          (canonicalResidualComponentCount A x y L : ℝ) < alpha * (L + 1 : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt halpha
  obtain ⟨Mzero, hsmall⟩ := canonical_count_small_eventually
    betaMin betaMax delta hmin hbeta hdelta A (n + 1) (by omega)
  refine ⟨Mzero, ?_⟩
  intro M hM L hlo hhi x hx y hy ha
  have hc : (n + 1 : ℝ) * (canonicalResidualComponentCount A x y L : ℝ) < L + 1 := by
    exact_mod_cast hsmall M hM L hlo hhi x hx y hy ha
  have hD : (0 : ℝ) < n + 1 := by positivity
  have hscale : 1 < alpha * (n + 1) := (div_lt_iff₀ hD).mp hn
  have hB : (0 : ℝ) < L + 1 := by positivity
  have hmul := mul_lt_mul_of_pos_right hscale hB
  nlinarith

end
end PaperC.V282.DensityAlignedExclusion
