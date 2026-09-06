import PaperCV282.SectorEightSliceMass
import PaperCV282.MacroscopicDyadicSlices

/-!
# The terminal sector on the full macroscopic interval

Every pair is sliced by its larger start, and both orientations survive.
The logarithmic band transports uniformly to all nonempty slices. The
exceptional one-kernel branch is retained at the stronger three-quarter
ambient exponent before being absorbed in the middle profile monomial.
-/

namespace PaperC.V282.SectorEightProfile

open PropositionSixteenOne ResidualSectorPartition ResidualSectorMass CappedSectorMass
open SectorEightGeometry SectorEightWeights SectorEightSliceMass MacroscopicDyadicSlices
open MacroscopicGeometry
open scoped BigOperators

noncomputable section

/-- The actual larger coordinate is itself in the macroscopic interval. -/
theorem larger_start_mem_macroscopic {M L : ℕ} {delta : ℝ}
    (p : SeparatedBoundedRatioPair ⌈(M : ℝ) ^ delta⌉₊ M L) :
    max p.1.1 p.1.2 ∈ macroscopicStarts M delta := by
  have hgeo := mem_separatedBoundedRatioPairs.mp p.2
  rcases le_total p.1.1 p.1.2 with h | h
  · rw [max_eq_right h]
    exact hgeo.2.1
  · rw [max_eq_left h]
    exact hgeo.1

/-- Exact dyadic summation of the two terminal weight envelopes, uniformly before the weight. -/
theorem sum_sector_eight_macroscopic_le_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ A : ℕ, ∀ hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊, 1 ≤ A →
      ∀ U V : ℝ, 0 ≤ U → 0 ≤ V →
      ∀ w : SeparatedBoundedRatioPair ⌈(M : ℝ) ^ delta⌉₊ M L → ℝ,
      (∀ p ∈ sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 7, w p ≤ 4 * U) →
      (∀ p ∈ sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 7,
        L + 1 - 3 * terminalIndex A p - 1 ≤ 1 → w p ≤ 8 * V) →
      (∑ p ∈ sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 7, w p) ≤
        (M : ℝ) ^ epsilon *
          ((M : ℝ) ^ (2 / (3 : ℝ)) * U + (M : ℝ) ^ (3 / (4 : ℝ)) * V) := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Xslice, hslice⟩ := sum_sector_eight_slice_le_eventually
    betaMin (2 * betaMax / delta) (epsilon / 2) hbetaMin (by positivity) heps
  obtain ⟨Mtransport, htransport⟩ := dyadic_transport_eventually delta hdelta Xslice
  obtain ⟨Mnumber, hnumber⟩ := number_of_dyadicSlices_le_rpow_eventually (epsilon / 2) heps
  refine ⟨max Mtransport (max Mnumber 2), ?_⟩
  intro M hM L hlower hupper A hN hA U V hU hV w hweight hexception
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let s := sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 7
  let f : SeparatedBoundedRatioPair ⌈(M : ℝ) ^ delta⌉₊ M L → ℕ :=
    fun p => max p.1.1 p.1.2
  let P : ℝ := (M : ℝ) ^ (2 / (3 : ℝ)) * U + (M : ℝ) ^ (3 / (4 : ℝ)) * V
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hbound : ∀ p ∈ s, f p ≤ M := by
    intro p _
    exact ((mem_macroscopicStarts M delta (f p)).mp (larger_start_mem_macroscopic p)).2.le
  have hlocal : ∀ j ∈ Finset.range (Nat.log 2 M + 1),
      (dyadicSlice s f j).Nonempty →
      (∑ p ∈ dyadicSlice s f j, w p) ≤ (M : ℝ) ^ (epsilon / 2) * P := by
    intro j hj hnonempty
    obtain ⟨p0, hp0⟩ := hnonempty
    have hscale : ∀ p ∈ dyadicSlice s f j,
        2 ^ j ≤ f p ∧ f p < 2 * 2 ^ j := by
      intro p hp
      have hmacro := (mem_macroscopicStarts M delta (f p)).mp (larger_start_mem_macroscopic p)
      exact bounds_of_mem_dyadicSlice hp (by omega)
    obtain ⟨hXslice, hXtwo, hXM, hlogLower, hlogUpper⟩ :=
      htransport M (by omega) (f p0) (larger_start_mem_macroscopic p0) (2 ^ j)
        (hscale p0 hp0).1 (hscale p0 hp0).2
    obtain ⟨hLlower, hLupper⟩ := logarithmic_band_on_slice hbetaMin hbetaMax hdelta
      hlogLower hlogUpper hlower hupper
    have hh := hslice (2 ^ j) hXslice L hLlower hLupper _ M A hN hA
      (dyadicSlice s f j) (Finset.filter_subset _ _) hscale U V hU hV w
      (fun p hp => hweight p (Finset.mem_filter.mp hp).1)
      (fun p hp => hexception p (Finset.mem_filter.mp hp).1)
    have hXMreal : ((2 ^ j : ℕ) : ℝ) ≤ M := by exact_mod_cast hXM
    have hXnonneg : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by positivity
    have hpowE := Real.rpow_le_rpow hXnonneg hXMreal (le_of_lt heps)
    have hpowTwo := Real.rpow_le_rpow hXnonneg hXMreal (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have hpowThree := Real.rpow_le_rpow hXnonneg hXMreal (by norm_num : (0 : ℝ) ≤ 3 / 4)
    refine hh.trans ?_
    exact mul_le_mul hpowE (add_le_add (mul_le_mul_of_nonneg_right hpowTwo hU)
      (mul_le_mul_of_nonneg_right hpowThree hV)) (by positivity) (by positivity)
  have hfinite := sum_le_number_of_slices_mul s f w M (by positivity : 0 ≤ (M : ℝ) ^ (epsilon / 2) * P)
    hbound hlocal
  calc
    _ ≤ _ := hfinite
    _ ≤ (M : ℝ) ^ (epsilon / 2) * ((M : ℝ) ^ (epsilon / 2) * P) :=
      mul_le_mul_of_nonneg_right (hnumber M (by omega)) (by positivity)
    _ = _ := by rw [← mul_assoc, ← Real.rpow_add hMpos,
      show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- Proposition 3.25 with the literal three-quarter ambient exponent retained. -/
theorem proposition_three_twenty_five
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ A : ℕ, 1 ≤ A →
      sectorMass A 7 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ epsilon *
        ((M : ℝ) ^ (2 / (3 : ℝ)) * (2 : ℝ) ^ (L + 1) +
          (M : ℝ) ^ (3 / (4 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  obtain ⟨Msum, hsum⟩ := sum_sector_eight_macroscopic_le_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Msum 2, ?_⟩
  intro M hM L hlower hupper A hA
  have hN := two_le_macroscopic_lowerEndpoint (by omega : 2 ≤ M) hdelta
  have hh := hsum M (by omega) L hlower hupper A hN hA
    ((2 : ℝ) ^ (L + 1)) (((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)))
    (by positivity) (by positivity) (fun p => (residualWeight A hN p : ℝ))
    (fun p hp => residualWeight_cast_le_four_wordCount hN p (mem_sectorPairs.mp hp))
    (fun p hp he => exceptional_residualWeight_cast_le_eight_wordCount_two_thirds
      hN p (mem_sectorPairs.mp hp) he)
  simpa only [sectorMass, dif_pos hN, sectorMassNat, Nat.cast_sum] using hh

/-- The exact terminal envelope also retains a common real ceiling before assembly. -/
theorem proposition_three_twenty_five_capped
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 0 ≤ T →
      cappedSectorMass A 7 T ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ epsilon *
        ((M : ℝ) ^ (2 / (3 : ℝ)) * min T ((2 : ℝ) ^ (L + 1)) +
          (M : ℝ) ^ (3 / (4 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  obtain ⟨Msum, hsum⟩ := sum_sector_eight_macroscopic_le_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Msum 2, ?_⟩
  intro M hM L hlower hupper A hA T hT
  have hN := two_le_macroscopic_lowerEndpoint (by omega : 2 ≤ M) hdelta
  have hh := hsum M (by omega) L hlower hupper A hN hA
    (min T ((2 : ℝ) ^ (L + 1))) (((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)))
    (le_min hT (by positivity)) (by positivity) (fun p => min T (residualWeight A hN p : ℝ))
    (fun p hp => capped_residualWeight_le_four_min_wordCount hN p (mem_sectorPairs.mp hp) hT)
    (fun p hp he => (min_le_right _ _).trans
      (exceptional_residualWeight_cast_le_eight_wordCount_two_thirds hN p (mem_sectorPairs.mp hp) he))
  simpa only [cappedSectorMass, dif_pos hN] using hh

/-- The full actual terminal mass, with the same fixed coding parameter used in the paper. -/
theorem macroscopic_sector_eight_le_profile_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ A : ℕ, 1 ≤ A →
      sectorMass A 7 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ epsilon *
        ((M : ℝ) ^ (2 / (3 : ℝ)) * (2 : ℝ) ^ (L + 1) +
          (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  obtain ⟨Msum, hsum⟩ := sum_sector_eight_macroscopic_le_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Msum 2, ?_⟩
  intro M hM L hlower hupper A hA
  have hMtwo : 2 ≤ M := by omega
  have hN := two_le_macroscopic_lowerEndpoint hMtwo hdelta
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hpower : (M : ℝ) ^ (3 / (4 : ℝ)) ≤ M := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hMone (by norm_num : (3 / (4 : ℝ)) ≤ 1)
  have hh := hsum M (by omega) L hlower hupper A hN hA
    ((2 : ℝ) ^ (L + 1)) (((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)))
    (by positivity) (by positivity) (fun p => (residualWeight A hN p : ℝ))
    (fun p hp => residualWeight_cast_le_four_wordCount hN p (mem_sectorPairs.mp hp))
    (fun p hp he => exceptional_residualWeight_cast_le_eight_wordCount_two_thirds
      hN p (mem_sectorPairs.mp hp) he)
  simp only [sectorMass, dif_pos hN, sectorMassNat, Nat.cast_sum]
  exact hh.trans (by gcongr)

/-- The terminal cap is kept literally and uniformly before choosing any nonnegative ceiling. -/
theorem capped_sector_eight_le_profile_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 0 ≤ T →
      cappedSectorMass A 7 T ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ epsilon *
        ((M : ℝ) ^ (2 / (3 : ℝ)) * min T ((2 : ℝ) ^ (L + 1)) +
          (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  obtain ⟨Msum, hsum⟩ := sum_sector_eight_macroscopic_le_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Msum 2, ?_⟩
  intro M hM L hlower hupper A hA T hT
  have hMtwo : 2 ≤ M := by omega
  have hN := two_le_macroscopic_lowerEndpoint hMtwo hdelta
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hpower : (M : ℝ) ^ (3 / (4 : ℝ)) ≤ M := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hMone (by norm_num : (3 / (4 : ℝ)) ≤ 1)
  have hh := hsum M (by omega) L hlower hupper A hN hA
    (min T ((2 : ℝ) ^ (L + 1))) (((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)))
    (le_min hT (by positivity)) (by positivity) (fun p => min T (residualWeight A hN p : ℝ))
    (fun p hp => capped_residualWeight_le_four_min_wordCount hN p (mem_sectorPairs.mp hp) hT)
    (fun p hp he => (min_le_right _ _).trans
      (exceptional_residualWeight_cast_le_eight_wordCount_two_thirds hN p (mem_sectorPairs.mp hp) he))
  simp only [cappedSectorMass, dif_pos hN]
  exact hh.trans (by gcongr)

end
end PaperC.V282.SectorEightProfile
