import PaperCV282.MacroscopicAlignedRunge
import PaperCV282.TwoWindowParity
import PaperC.Combinatorics.AlignedDeepCoreExtraction
import PaperC.Combinatorics.SectionElevenPartition

/-!
# Exclusion of aligned residual cores above one sixth

The exact test needed for the fourth v2.8.2 sector is `B < 6*c#`.
The old component cutoff 43 still leaves at least `floor(B/16)` exact-free
components at this lower density. The new counting budget below proves
that fact directly, and the macroscopic Hamming/Runge package then excludes
every such aligned pair.
-/

namespace PaperC.V282.MacroscopicAlignedExclusion

open Affine.CanonicalRationalCode MacroscopicGeometry MacroscopicAlignedRunge
open AlignedCoreExclusion CanonicalResidualComponents ResidualComponentCounts
open TheoremEightHammingBudget SectionElevenPartition TwoWindowParity

noncomputable section

/-- The cutoff 43 also pays the two exceptional components at density greater than one sixth. -/
theorem sixth_cutoff_counting_budget {B residualCount : ℕ}
    (hB : 48 ≤ B) (hdensity : B < 6 * residualCount) :
    B / 16 + 2 + (2 * B) / (43 + 1) ≤ residualCount := by
  have htail : (2 * B) / (43 + 1) ≤ B / 16 := by
    calc
      (2 * B) / (43 + 1) = B / 22 := by
        simpa using Nat.mul_div_mul_left B 22 (by norm_num : 0 < (2 : ℕ))
      _ ≤ B / 16 := Nat.div_le_div_left (by norm_num) (by norm_num)
  have hquotient := Nat.div_mul_le_self B 16
  have hscaled : 6 * (B / 16 + 2 + (2 * B) / (43 + 1)) ≤ B := by omega
  omega

/-- A one-sixth dense candidate exposes the same small-component family used by Hamming. -/
theorem one_sixteenth_le_small_components_of_sixth_density
    {x y L H : ℕ} (c : ReducedCandidate x y (L + 1) H)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hB : 48 ≤ L + 1)
    (hdensity : L + 1 < 6 * (residualComponents x y L c.1.1 c.1.2
      (pairChannelError x y c.1.1 c.1.2)).card) :
    (L + 1) / 16 ≤ (smallExactFreeResidualComponents x y L c.1.1 c.1.2
      (pairChannelError x y c.1.1 c.1.2) 43).card := by
  apply target_le_card_smallExactFreeResidualComponents_of_candidate c hx hy
  exact sixth_cutoff_counting_budget hB hdensity

/-- No candidate with residual density greater than one sixth survives in the macroscopic band. -/
theorem no_dense_candidate_eventually
    (betaMin betaMax delta : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (A : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ H : ℕ, 1 ≤ H → H ≤ (L + 1) ^ A →
      ∀ x ∈ macroscopicStarts M delta, ∀ y ∈ macroscopicStarts M delta,
      ∀ c : ReducedCandidate x y (L + 1) H,
        L + 1 < 6 * (residualComponents x y L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2)).card → False := by
  obtain ⟨Mhamming, hhamming⟩ := hamming_numerics_eventually betaMin hbetaMin
  obtain ⟨Mrunge, hrunge⟩ := rungeScale_lt_macroscopic_eventually
    betaMin betaMax delta 65 hbetaMin hbeta hdelta (by norm_num) A
  obtain ⟨Mtranslation, htranslation⟩ := translationRange_macroscopic_eventually
    betaMin betaMax delta hbetaMin hbeta hdelta A
  refine ⟨max 2 (max Mhamming (max Mrunge Mtranslation)), ?_⟩
  intro M hM L hLmin hLmax H hH hHupper x hx y hy c hdensity
  have hMtwo : 2 ≤ M := (le_max_left _ _).trans hM
  have htail : max Mhamming (max Mrunge Mtranslation) ≤ M := (le_max_right _ _).trans hM
  have hMhamming : Mhamming ≤ M := (le_max_left _ _).trans htail
  have htail' : max Mrunge Mtranslation ≤ M := (le_max_right _ _).trans htail
  have hMrunge : Mrunge ≤ M := (le_max_left _ _).trans htail'
  have hMtranslation : Mtranslation ≤ M := (le_max_right _ _).trans htail'
  have hxTwo := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hx)).1
  have hyTwo := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hy)).1
  obtain ⟨hB64, htReal, hconditions⟩ :=
    hhamming M hMhamming (L + 1) (by exact_mod_cast hLmin)
  have hfamily := one_sixteenth_le_small_components_of_sixth_density
    c hxTwo hyTwo (by omega) hdensity
  obtain ⟨ht, hmt, hrows, hvolume⟩ := hconditions _ hfamily
  have hbase := htranslation M hMtranslation (L + 1)
    (by exact_mod_cast hLmin) (by exact_mod_cast hLmax)
    H hHupper c.1.1 (candidate_fst_pos c) x hx
  have hRungeRange : ∀ k : ℕ, 1 ≤ k → k ≤ 43 * componentHammingRadius (L + 1) →
      (128 * (2 * k) * (3 * H * (L + 1))) ^ (4 * k) < c.1.1 * x := by
    intro k hk hkt
    exact hrunge M hMrunge (L + 1) (by exact_mod_cast hLmin) (by exact_mod_cast hLmax)
      H hH hHupper (componentHammingRadius (L + 1)) htReal
      k hk hkt c.1.1 (candidate_fst_pos c) x hx
  exact no_candidate_aligned_core_of_finite_conditions
    (K := 43) c hxTwo hyTwo ht hmt hrows hvolume hbase hRungeRange

/-- Every aligned macroscopic pair has corrected residual density at most one sixth. -/
theorem aligned_component_count_le_sixth_eventually
    (betaMin betaMax delta : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (A : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ x ∈ macroscopicStarts M delta, ∀ y ∈ macroscopicStarts M delta,
        IsCanonicallyAligned A L x y →
          6 * canonicalResidualComponentCount A x y L ≤ L + 1 := by
  obtain ⟨Mcore, hcore⟩ := no_dense_candidate_eventually
    betaMin betaMax delta hbetaMin hbeta hdelta A
  refine ⟨max Mcore 2, ?_⟩
  intro M hM L hLmin hLmax x hx y hy haligned
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hM
  have hxTwo := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hx)).1
  have hyTwo := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hy)).1
  obtain ⟨c, hchoice⟩ := haligned
  have hcard := card_residualComponents (L := L)
    (candidate_fst_pos c) (candidate_snd_pos c) (candidate_coprime c) hxTwo hyTwo
    (show pairChannelError x y c.1.1 c.1.2 = (c.1.2 : ℤ) * y - (c.1.1 : ℤ) * x by rfl)
  by_contra hdensity
  have hcount : L + 1 < 6 * (residualComponents x y L c.1.1 c.1.2
      (pairChannelError x y c.1.1 c.1.2)).card := by
    rw [hcard]
    have hcanonical : L + 1 < 6 * canonicalResidualComponentCount A x y L := by omega
    simpa only [canonicalResidualComponentCount, hchoice] using hcanonical
  exact hcore M ((le_max_left _ _).trans hM) L hLmin hLmax
    ((L + 1) ^ A) (Nat.one_le_pow _ _ (by omega)) le_rfl x hx y hy c hcount

instance instDecidableAlignedDeepPredicate (A L : ℕ) :
    DecidablePred (fun xy : ℕ × ℕ => IsCanonicallyAligned A L xy.1 xy.2 ∧
      L + 1 < 6 * canonicalResidualComponentCount A xy.1 xy.2 L) :=
  fun _ => Classical.propDecidable _

/-- The aligned part left after the one-sixth test is eventually empty on the literal pair mask. -/
theorem aligned_deep_pairs_empty_eventually
    (betaMin betaMax delta : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (A : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
        ((separatedPairs (macroscopicStarts M delta) L).filter fun xy =>
          IsCanonicallyAligned A L xy.1 xy.2 ∧
            L + 1 < 6 * canonicalResidualComponentCount A xy.1 xy.2 L) = ∅ := by
  classical
  obtain ⟨Mzero, hbound⟩ := aligned_component_count_le_sixth_eventually
    betaMin betaMax delta hbetaMin hbeta hdelta A
  refine ⟨Mzero, ?_⟩
  intro M hM L hLmin hLmax
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro xy hxy
  obtain ⟨hsep, haligned, hdense⟩ := Finset.mem_filter.mp hxy
  have hp := Finset.mem_product.mp (Finset.mem_filter.mp hsep).1
  have hle := hbound M hM L hLmin hLmax xy.1 hp.1 xy.2 hp.2 haligned
  omega

end
end PaperC.V282.MacroscopicAlignedExclusion
