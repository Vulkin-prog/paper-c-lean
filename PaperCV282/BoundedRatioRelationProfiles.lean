import PaperCV282.WholeRelationProfile
import PaperCV282.RelationProfileRestriction

/-!
# Complete profiles at the lower scale of bounded-ratio intervals

The upper endpoint, arbitrary separated mask, adequate cylinder and real
ceiling are all chosen after the threshold. A fixed natural ratio bounds
any fixed real ratio from above. The actual interval may be empty.
-/

namespace PaperC.V282.BoundedRatioRelationProfiles

open Affine WholeRelationProfile RelationProfileRestriction ProfileMonomials
open CappedRelationMass TwoWindowParity MacroscopicGeometry HostRankMass
open LogarithmicWordPowers

noncomputable section

/-- Fixed bounded ratios preserve logarithmic bands, with a factor two on the lower endpoint. -/
theorem logarithmic_band_at_multiple {N c L : ℕ} {betaMin betaMax : ℝ}
    (hN : 2 ≤ N) (hc : 1 ≤ c) (hcN : c ≤ N)
    (hbetaMin : 0 ≤ betaMin) (hbetaMax : 0 ≤ betaMax)
    (hlower : betaMin * Real.log N ≤ (L + 1 : ℝ))
    (hupper : (L + 1 : ℝ) ≤ betaMax * Real.log N) :
    (betaMin / 2) * Real.log (c * N : ℕ) ≤ (L + 1 : ℝ) ∧
      (L + 1 : ℝ) ≤ betaMax * Real.log (c * N : ℕ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcr : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcNr : (c : ℝ) ≤ N := by exact_mod_cast hcN
  have hloglow : Real.log N ≤ Real.log (c * N : ℕ) :=
    Real.log_le_log hNr (by push_cast; nlinarith)
  have hloghigh : Real.log (c * N : ℕ) ≤ 2 * Real.log N := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (c * N : ℕ))
      (show ((c * N : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 by push_cast; nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  exact ⟨(mul_le_mul_of_nonneg_left hloghigh (by positivity : 0 ≤ betaMin / 2)).trans
    (by nlinarith), hupper.trans (mul_le_mul_of_nonneg_left hloglow hbetaMax)⟩

/-- Every capped profile monomial has scale exponent at most two. -/
theorem cappedProfile_mul_le_square {c N Q T : ℝ}
    (hc : 1 ≤ c) (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hT : 0 ≤ T) :
    cappedProfile (c * N) Q T ≤ c ^ 2 * cappedProfile N Q T := by
  have hp (a : ℝ) (ha : a ≤ 2) : (c * N) ^ a ≤ c ^ 2 * N ^ a := by
    rw [Real.mul_rpow (by linarith) hN]
    exact mul_le_mul_of_nonneg_right
      (by simpa using Real.rpow_le_rpow_of_exponent_le hc ha) (Real.rpow_nonneg hN _)
  have ha := mul_le_mul_of_nonneg_right (hp (3 / (2 : ℝ)) (by norm_num))
    (Real.rpow_nonneg hQ (1 / (6 : ℝ)))
  have hb : c * N * Q ^ (2 / (3 : ℝ)) ≤ c ^ 2 * (N * Q ^ (2 / (3 : ℝ))) := by
    have hh : c ≤ c ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hh (mul_nonneg hN (Real.rpow_nonneg hQ (2 / (3 : ℝ))))
    nlinarith
  have hd := mul_le_mul_of_nonneg_right (hp (2 / (3 : ℝ)) (by norm_num)) (le_min hT hQ)
  unfold cappedProfile
  nlinarith

/-- Both literal capped masses on every bounded-ratio interval and every separated submask.
The common ceiling and cylinder are arbitrary after the common threshold. -/
theorem capped_masses_le_profile_boundedRatio_eventually
    (kappa : ℕ) (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ M : ℕ, M ≤ kappa * N → ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedPairs (Finset.Ico N M) L →
      ∀ K : ℕ, (∀ p ∈ s, p.1 + L ≤ K ∧ p.2 + L ≤ K) →
      ∀ T : ℝ, 0 ≤ T →
      cappedStartMass K L T s ≤ (N : ℝ) ^ epsilon * cappedProfile N ((2 : ℝ) ^ (L + 1)) T ∧
      cappedValueMass K L T s ≤ (N : ℝ) ^ epsilon * cappedProfile N ((2 : ℝ) ^ (L + 1)) T := by
  let c := max kappa 2
  have hc : 2 ≤ c := le_max_right _ _
  have hcr : (1 : ℝ) ≤ c := by exact_mod_cast (show 1 ≤ c by omega)
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Ns, hstart⟩ := proposition_three_twenty_seven_start_macroscopic
    (betaMin / 2) betaMax (1 / (2 : ℝ)) (epsilon / 2) (by positivity)
    (by linarith) (by norm_num) heps
  obtain ⟨Nv, hvalue⟩ := proposition_three_twenty_seven_value_macroscopic
    (betaMin / 2) betaMax (1 / (2 : ℝ)) (epsilon / 2) (by positivity)
    (by linarith) (by norm_num) heps
  obtain ⟨Nc, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le ((c : ℝ) ^ 2 * (c : ℝ) ^ (epsilon / 2)) 0
    (epsilon / 2) heps
  refine ⟨max Ns (max Nv (max Nc c)), ?_⟩
  intro N hN M hM L hlower hupper s hs K hK T hT
  have hNc : c ≤ N := by omega
  have hNtwo : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNZ : N ≤ c * N := by nlinarith
  have hMZ : M ≤ c * N := hM.trans (Nat.mul_le_mul_right N (le_max_left kappa 2))
  obtain ⟨hl, hu⟩ := logarithmic_band_at_multiple hNtwo (by omega) hNc
    hbetaMin.le (hbetaMin.trans hbeta).le hlower hupper
  have hpairs (p : ℕ × ℕ) (hp : p ∈ s) :
      p.1 ∈ Finset.Ico N (c * N) ∧ p.2 ∈ Finset.Ico N (c * N) ∧ L < Nat.dist p.1 p.2 := by
    obtain ⟨hx, hy, hd⟩ := (mem_separatedPairs _ _ _ _).mp (hs hp)
    obtain ⟨hxN, hxM⟩ := Finset.mem_Ico.mp hx
    obtain ⟨hyN, hyM⟩ := Finset.mem_Ico.mp hy
    exact ⟨Finset.mem_Ico.mpr ⟨hxN, hxM.trans_le hMZ⟩,
      Finset.mem_Ico.mpr ⟨hyN, hyM.trans_le hMZ⟩, hd⟩
  have hsub : s ⊆ separatedPairs (macroscopicStarts (c * N) (1 / (2 : ℝ))) L := by
    intro p hp
    obtain ⟨hx, hy, hd⟩ := hpairs p hp
    exact (mem_separatedPairs _ _ _ _).mpr
      ⟨boundedRatioBlock_subset_macroscopic hNc hx,
       boundedRatioBlock_subset_macroscopic hNc hy, hd⟩
  have hpos : ∀ p ∈ s, 2 ≤ p.1 ∧ 2 ≤ p.2 := by
    intro p hp
    obtain ⟨hx, hy, _⟩ := hpairs p hp
    exact ⟨hNtwo.trans (Finset.mem_Ico.mp hx).1, hNtwo.trans (Finset.mem_Ico.mp hy).1⟩
  have hcut : ∀ p ∈ s, p.1 + L ≤ c * N + L ∧ p.2 + L ≤ c * N + L := by
    intro p hp
    obtain ⟨hx, hy, _⟩ := hpairs p hp
    have hxZ := (Finset.mem_Ico.mp hx).2
    have hyZ := (Finset.mem_Ico.mp hy).2
    constructor <;> omega
  have hscale : ((c * N : ℕ) : ℝ) ^ (epsilon / 2) =
      (c : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (epsilon / 2) := by
    push_cast
    exact Real.mul_rpow (by positivity) hNpos.le
  have hprof : cappedProfile (c * N : ℕ) ((2 : ℝ) ^ (L + 1)) T ≤
      (c : ℝ) ^ 2 * cappedProfile N ((2 : ℝ) ^ (L + 1)) T := by
    simpa only [Nat.cast_mul] using cappedProfile_mul_le_square hcr hNpos.le (by positivity) hT
  have hconstant' : (c : ℝ) ^ 2 * (c : ℝ) ^ (epsilon / 2) ≤ (N : ℝ) ^ (epsilon / 2) := by
    simpa only [pow_zero, mul_one, abs_of_nonneg (by positivity :
      0 ≤ (c : ℝ) ^ 2 * (c : ℝ) ^ (epsilon / 2))]
      using hconstant N (by omega) L (by simpa using hupper)
  have hP := cappedProfile_nonneg hNpos.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1)) hT
  have hbound : ((c * N : ℕ) : ℝ) ^ (epsilon / 2) * cappedProfile (c * N : ℕ) ((2 : ℝ) ^ (L + 1)) T ≤
      (N : ℝ) ^ epsilon * cappedProfile N ((2 : ℝ) ^ (L + 1)) T := by
    calc
      _ ≤ ((c * N : ℕ) : ℝ) ^ (epsilon / 2) *
          ((c : ℝ) ^ 2 * cappedProfile N ((2 : ℝ) ^ (L + 1)) T) := by gcongr
      _ = ((c : ℝ) ^ 2 * (c : ℝ) ^ (epsilon / 2)) *
          (N : ℝ) ^ (epsilon / 2) * cappedProfile N ((2 : ℝ) ^ (L + 1)) T := by rw [hscale]; ring
      _ ≤ ((N : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (epsilon / 2)) *
          cappedProfile N ((2 : ℝ) ^ (L + 1)) T := by gcongr
      _ = _ := by rw [← Real.rpow_add hNpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]
  constructor
  · rw [cappedStartMass_cutoff_eq T s hpos hK hcut]
    exact (cappedStartMass_mono_mask _ _ hT hsub).trans
      ((hstart (c * N) (by omega) L hl hu T hT).trans hbound)
  · rw [cappedValueMass_cutoff_eq T s hpos
      (fun p hp => ⟨(hK p hp).1.trans (Nat.le_succ K), (hK p hp).2.trans (Nat.le_succ K)⟩)
      (fun p hp => ⟨(hcut p hp).1.trans (Nat.le_succ _), (hcut p hp).2.trans (Nat.le_succ _)⟩)]
    exact (cappedValueMass_mono_mask _ _ hT hsub).trans
      ((hvalue (c * N) (by omega) L hl hu T hT).trans hbound)

/-- The uncapped start and full-value profiles, on the same arbitrary masks and cylinders. -/
theorem raw_masses_le_profile_boundedRatio_eventually
    (kappa : ℕ) (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ M : ℕ, M ≤ kappa * N → ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedPairs (Finset.Ico N M) L →
      ∀ K : ℕ, (∀ p ∈ s, p.1 + L ≤ K ∧ p.2 + L ≤ K) →
      (relationWeightMass K L s : ℝ) ≤ (N : ℝ) ^ epsilon * rawProfile N ((2 : ℝ) ^ (L + 1)) ∧
      (valueWeightMass K L s : ℝ) ≤ (N : ℝ) ^ epsilon * rawProfile N ((2 : ℝ) ^ (L + 1)) := by
  obtain ⟨Nzero, hcap⟩ := capped_masses_le_profile_boundedRatio_eventually
    kappa betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨Nzero, ?_⟩
  intro N hN M hM L hl hu s hs K hK
  constructor
  · have h := (hcap N hN M hM L hl hu s hs K hK (relationWeightMass K L s) (by positivity)).1
    rw [cappedStartMass_self] at h
    exact h.trans (mul_le_mul_of_nonneg_left (cappedProfile_le_rawProfile (by positivity)) (by positivity))
  · have h := (hcap N hN M hM L hl hu s hs K hK (valueWeightMass K L s) (by positivity)).2
    rw [cappedValueMass_self] at h
    exact h.trans (mul_le_mul_of_nonneg_left (cappedProfile_le_rawProfile (by positivity)) (by positivity))

/-- The two interpolation bounds in the same lower-scale normalization. -/
theorem coarse_masses_le_profile_boundedRatio_eventually
    (kappa : ℕ) (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ M : ℕ, M ≤ kappa * N → ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedPairs (Finset.Ico N M) L →
      ∀ K : ℕ, (∀ p ∈ s, p.1 + L ≤ K ∧ p.2 + L ≤ K) →
      (relationWeightMass K L s : ℝ) ≤ (N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1)) ∧
      (valueWeightMass K L s : ℝ) ≤ (N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Nr, hraw⟩ := raw_masses_le_profile_boundedRatio_eventually
    kappa betaMin betaMax (epsilon / 2) hbetaMin hbeta heps
  obtain ⟨Nc, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le 2 0 (epsilon / 2) heps
  refine ⟨max Nr (max Nc 1), ?_⟩
  intro N hN M hM L hl hu s hs K hK
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hstart, hvalue⟩ := hraw N (by omega) M hM L hl hu s hs K hK
  have htwo : (2 : ℝ) ≤ (N : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant N (by omega) L (by simpa using hu)
  have hcoarse := rawProfile_le_two_coarseProfile hNpos
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  have hP := coarseProfile_nonneg hNpos.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  have hbound : (N : ℝ) ^ (epsilon / 2) * rawProfile N ((2 : ℝ) ^ (L + 1)) ≤
      (N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by
    calc
      _ ≤ (N : ℝ) ^ (epsilon / 2) * (2 * coarseProfile N ((2 : ℝ) ^ (L + 1))) := by gcongr
      _ ≤ ((N : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (epsilon / 2)) *
          coarseProfile N ((2 : ℝ) ^ (L + 1)) := by nlinarith [mul_nonneg hP (Real.rpow_nonneg hNpos.le (epsilon / 2))]
      _ = _ := by rw [← Real.rpow_add hNpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]
  exact ⟨hstart.trans hbound, hvalue.trans hbound⟩

/-- The capped dyadic profiles with their exact cutoff and with an arbitrary separated mask. -/
theorem capped_masses_le_profile_dyadic_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedPairs (Finset.Ico N (2 * N)) L →
      ∀ T : ℝ, 0 ≤ T →
      cappedStartMass (2 * N + L) L T s ≤ (N : ℝ) ^ epsilon * cappedProfile N ((2 : ℝ) ^ (L + 1)) T ∧
      cappedValueMass (2 * N + L) L T s ≤ (N : ℝ) ^ epsilon * cappedProfile N ((2 : ℝ) ^ (L + 1)) T := by
  obtain ⟨Nzero, hcap⟩ := capped_masses_le_profile_boundedRatio_eventually
    2 betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨Nzero, ?_⟩
  intro N hN L hl hu s hs T hT
  apply hcap N hN (2 * N) le_rfl L hl hu s hs (2 * N + L) ?_ T hT
  intro p hp
  obtain ⟨hx, hy, _⟩ := (mem_separatedPairs _ _ _ _).mp (hs hp)
  have hxZ := (Finset.mem_Ico.mp hx).2
  have hyZ := (Finset.mem_Ico.mp hy).2
  constructor <;> omega

/-- The uncapped dyadic start and full-value profiles on every separated mask. -/
theorem raw_masses_le_profile_dyadic_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedPairs (Finset.Ico N (2 * N)) L →
      (relationWeightMass (2 * N + L) L s : ℝ) ≤ (N : ℝ) ^ epsilon * rawProfile N ((2 : ℝ) ^ (L + 1)) ∧
      (valueWeightMass (2 * N + L) L s : ℝ) ≤ (N : ℝ) ^ epsilon * rawProfile N ((2 : ℝ) ^ (L + 1)) := by
  obtain ⟨Nzero, hraw⟩ := raw_masses_le_profile_boundedRatio_eventually
    2 betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨Nzero, ?_⟩
  intro N hN L hl hu s hs
  apply hraw N hN (2 * N) le_rfl L hl hu s hs (2 * N + L) ?_
  intro p hp
  obtain ⟨hx, hy, _⟩ := (mem_separatedPairs _ _ _ _).mp (hs hp)
  have hxZ := (Finset.mem_Ico.mp hx).2
  have hyZ := (Finset.mem_Ico.mp hy).2
  constructor <;> omega

/-- The interpolated dyadic start and full-value profiles on every separated mask. -/
theorem coarse_masses_le_profile_dyadic_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedPairs (Finset.Ico N (2 * N)) L →
      (relationWeightMass (2 * N + L) L s : ℝ) ≤ (N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1)) ∧
      (valueWeightMass (2 * N + L) L s : ℝ) ≤ (N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by
  obtain ⟨Nzero, hcoarse⟩ := coarse_masses_le_profile_boundedRatio_eventually
    2 betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨Nzero, ?_⟩
  intro N hN L hl hu s hs
  apply hcoarse N hN (2 * N) le_rfl L hl hu s hs (2 * N + L) ?_
  intro p hp
  obtain ⟨hx, hy, _⟩ := (mem_separatedPairs _ _ _ _).mp (hs hp)
  have hxZ := (Finset.mem_Ico.mp hx).2
  have hyZ := (Finset.mem_Ico.mp hy).2
  constructor <;> omega

end
end PaperC.V282.BoundedRatioRelationProfiles
