import PaperCV282.TouchingPairGeometry
import PaperCV282.MacroscopicPointwiseDefects
import PaperCV282.LogarithmicWordPowers
import PaperCV282.MacroscopicCanonicalCode

/-!
# The homogeneous touching-pair mass on logarithmic bands

The sum uses the actual two-start relation dimension and includes the
baseline weight one. The dyadic and macroscopic estimates are uniform in
the full logarithmic length band; no balance between word count and scale
is assumed.
-/

namespace PaperC.V282.TouchingPairMass

open Affine TouchingPairGeometry MacroscopicGeometry MacroscopicPointwiseDefects
open MacroscopicCanonicalCode LogarithmicWordPowers
open scoped BigOperators

noncomputable section

def homogeneousTouchingMass (K L : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ p ∈ touchingPairsOn s L, (2 : ℝ) ^ relationRho (twoStartSystem K p.1 p.2 L)

theorem homogeneousTouchingMass_le {K L : ℕ} {s : Finset ℕ} {W : ℝ} (hW : 0 ≤ W)
    (hweight : ∀ p ∈ touchingPairsOn s L,
      (2 : ℝ) ^ relationRho (twoStartSystem K p.1 p.2 L) ≤ W) :
    homogeneousTouchingMass K L s ≤ 2 * (s.card : ℝ) * W := by
  calc
    _ ≤ ∑ _p ∈ touchingPairsOn s L, W := Finset.sum_le_sum hweight
    _ = ((touchingPairsOn s L).card : ℝ) * W := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_touchingPairsOn_le s L) hW

theorem length_pos_eventually (betaMin : ℝ) (hbetaMin : 0 < betaMin) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → 0 < L := by
  obtain ⟨Nzero, hzero⟩ := exists_nat_gt (Real.exp (2 / betaMin))
  refine ⟨Nzero, ?_⟩
  intro N hN L hL
  have hcast : (Nzero : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_lt_log (Real.exp_pos (2 / betaMin))
    (hzero.trans_le hcast)
  rw [Real.log_exp] at hlog
  have hh := (div_lt_iff₀ hbetaMin).mp hlog
  have hpos : (0 : ℝ) < L := by linarith
  exact_mod_cast hpos

theorem two_pow_le_rpow_of_log_bound_eventually (D epsilon : ℝ)
    (hD : 0 ≤ D) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ r : ℕ,
      (r : ℝ) ≤ D * (Real.log N / Real.log (Real.log N)) →
      (2 : ℝ) ^ r ≤ (N : ℝ) ^ epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hepsilon
  obtain ⟨Npower, hpower⟩ := ExpSqrtLog.two_pow_log_div_loglog_pow_le_nat_eventually
    D hD (n + 1) (by omega)
  refine ⟨max Npower 1, ?_⟩
  intro N hN r hr
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp : ((2 : ℝ) ^ r) ^ (n + 1) ≤ N := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      hpower N (by omega) r (by simpa only [mul_div_assoc] using hr)
  have hroot : (2 : ℝ) ^ r ≤ (N : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (by positivity : (0 : ℝ) < n + 1)).mpr
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
    exact hp
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hNreal hn.le)

theorem dyadic_relationRho_log_bound_eventually (betaMin betaMax : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ K : ℕ, (∀ x ∈ dyadicBlock N, x + L ≤ K) →
      ∀ p ∈ touchingPairsOn (dyadicBlock N) L,
        (relationRho (twoStartSystem K p.1 p.2 L) : ℝ) ≤
          D * (Real.log N / Real.log (Real.log N)) := by
  have hmax : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨D, hD, Npoint, hpoint⟩ := CriticalPointwiseIntervals.pointwise_all_intervals_on_window
    (by positivity : 0 < 2 * betaMin) (by linarith : 2 * betaMin < 2 * betaMax)
  obtain ⟨Nlen, hlen⟩ := logarithmic_power_lt_rpow_eventually
    (2 * betaMax) 1 (by positivity) (by norm_num) 1 (by omega)
  obtain ⟨Npos, hpos⟩ := length_pos_eventually betaMin hbetaMin
  refine ⟨D, hD, max Npoint (max Nlen (max Npos 2)), ?_⟩
  intro N hN L hlo hhi K hcut p hp
  obtain ⟨hx, hy, hd⟩ := mem_touchingPairsOn.mp hp
  have hxrange := Finset.mem_Ico.mp hx
  have hyrange := Finset.mem_Ico.mp hy
  have hHhi : ((2 * (L + 1) : ℕ) : ℝ) ≤ 2 * betaMax * Real.log N := by
    push_cast
    linarith
  have hHbound := hlen N (by omega) (2 * (L + 1)) hHhi
  simp only [pow_one, Real.rpow_one] at hHbound
  push_cast at hHbound
  have hH : 2 * (L + 1) ≤ N := by exact_mod_cast (by linarith : (2 * (L + 1) : ℝ) ≤ N)
  have hrho := relationRho_touching_le_root_defects (by omega) (by omega)
    (hpos N (by omega) L hlo) hd ⟨hcut p.1 hx, hcut p.2 hy⟩
  have hwindow : CriticalWindowParameters.InCriticalWindow (2 * betaMin) (2 * betaMax) N
      (2 * (L + 1)) := ⟨by positivity, by linarith, by push_cast; linarith, hHhi⟩
  exact (show (relationRho (twoStartSystem K p.1 p.2 L) : ℝ) ≤
      ((IntervalDefectBound.defectsInInterval (2 * (L + 1)) (min p.1 p.2 - 1)).card : ℝ)
      by exact_mod_cast hrho).trans
    (hpoint N (by omega) _ hwindow _ (by omega) (by omega))

theorem macroscopic_relationRho_log_bound_eventually (betaMin betaMax delta : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hdelta : 0 < delta) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ K : ℕ, (∀ x ∈ macroscopicStarts M delta, x + L ≤ K) →
      ∀ p ∈ touchingPairsOn (macroscopicStarts M delta) L,
        (relationRho (twoStartSystem K p.1 p.2 L) : ℝ) ≤
          D * (Real.log M / Real.log (Real.log M)) := by
  obtain ⟨D, hD, Mpoint, hpoint⟩ := root_defects_log_bound_eventually
    (2 * betaMin) (2 * betaMax) delta (by positivity) (by linarith) hdelta
  obtain ⟨Mpos, hpos⟩ := length_pos_eventually betaMin hbetaMin
  refine ⟨D, hD, max Mpoint (max Mpos 2), ?_⟩
  intro M hM L hlo hhi K hcut p hp
  obtain ⟨hx, hy, hd⟩ := mem_touchingPairsOn.mp hp
  have hx2 := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc (by omega) hdelta hx)).1
  have hy2 := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc (by omega) hdelta hy)).1
  have hmin : min p.1 p.2 ∈ macroscopicStarts M delta := by
    rcases le_total p.1 p.2 with h | h
    · simpa only [min_eq_left h] using hx
    · simpa only [min_eq_right h] using hy
  have hrho := relationRho_touching_le_root_defects hx2 hy2 (hpos M (by omega) L hlo)
    hd ⟨hcut p.1 hx, hcut p.2 hy⟩
  exact (show (relationRho (twoStartSystem K p.1 p.2 L) : ℝ) ≤
      ((IntervalDefectBound.defectsInInterval (2 * (L + 1)) (min p.1 p.2 - 1)).card : ℝ)
      by exact_mod_cast hrho).trans
    (hpoint M (by omega) (2 * (L + 1)) (by push_cast; linarith)
      (by push_cast; linarith) _ hmin)

theorem mass_le_rpow_of_pointwise {K L M : ℕ} {s : Finset ℕ} {epsilon : ℝ}
    (hM : 0 < M) (hcard : s.card ≤ M)
    (hfactor : (2 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2))
    (hpoint : ∀ p ∈ touchingPairsOn s L,
      (2 : ℝ) ^ relationRho (twoStartSystem K p.1 p.2 L) ≤ (M : ℝ) ^ (epsilon / 2)) :
    homogeneousTouchingMass K L s ≤ (M : ℝ) ^ (1 + epsilon) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    _ ≤ 2 * (s.card : ℝ) * (M : ℝ) ^ (epsilon / 2) := homogeneousTouchingMass_le (by positivity) hpoint
    _ ≤ 2 * (M : ℝ) * (M : ℝ) ^ (epsilon / 2) := by gcongr
    _ ≤ (M : ℝ) ^ (epsilon / 2) * M * (M : ℝ) ^ (epsilon / 2) := by gcongr
    _ = (M : ℝ) * ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) := by ring
    _ = (M : ℝ) ^ (1 + epsilon) := by
      rw [Real.rpow_add hMpos (1 : ℝ) epsilon, Real.rpow_one, ← Real.rpow_add hMpos]
      congr 1
      congr 1
      ring

theorem dyadic_homogeneousTouchingMass_le_eventually (betaMin betaMax epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ K : ℕ, (∀ x ∈ dyadicBlock N, x + L ≤ K) →
        homogeneousTouchingMass K L (dyadicBlock N) ≤ (N : ℝ) ^ (1 + epsilon) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨D, hD, Npoint, hpoint⟩ := dyadic_relationRho_log_bound_eventually betaMin betaMax hbetaMin hbeta
  obtain ⟨Npower, hpower⟩ := two_pow_le_rpow_of_log_bound_eventually D (epsilon / 2) hD heps
  obtain ⟨Nfactor, hfactor⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le 2 0 (epsilon / 2) heps
  refine ⟨max Npoint (max Npower (max Nfactor 1)), ?_⟩
  intro N hN L hlo hhi K hcut
  apply mass_le_rpow_of_pointwise (by omega) (by rw [TouchingPairs.card_dyadicBlock])
  · simpa only [pow_zero, mul_one, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      hfactor N (by omega) L (by simpa using hhi)
  · intro p hp
    exact hpower N (by omega) _ (hpoint N (by omega) L hlo hhi K hcut p hp)

theorem macroscopic_homogeneousTouchingMass_le_eventually (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ K : ℕ, (∀ x ∈ macroscopicStarts M delta, x + L ≤ K) →
        homogeneousTouchingMass K L (macroscopicStarts M delta) ≤ (M : ℝ) ^ (1 + epsilon) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨D, hD, Mpoint, hpoint⟩ := macroscopic_relationRho_log_bound_eventually
    betaMin betaMax delta hbetaMin hbeta hdelta
  obtain ⟨Mpower, hpower⟩ := two_pow_le_rpow_of_log_bound_eventually D (epsilon / 2) hD heps
  obtain ⟨Mfactor, hfactor⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le 2 0 (epsilon / 2) heps
  refine ⟨max Mpoint (max Mpower (max Mfactor 1)), ?_⟩
  intro M hM L hlo hhi K hcut
  have hcard : (macroscopicStarts M delta).card ≤ M := by
    simp only [macroscopicStarts, Nat.card_Ico]
    omega
  apply mass_le_rpow_of_pointwise (by omega) hcard
  · simpa only [pow_zero, mul_one, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      hfactor M (by omega) L (by simpa using hhi)
  · intro p hp
    exact hpower M (by omega) _ (hpoint M (by omega) L hlo hhi K hcut p hp)

theorem lemma_two_eight_dyadic (betaMin betaMax epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      homogeneousTouchingMass (dyadicCutoff N (2 * L)) L (dyadicBlock N) ≤ (N : ℝ) ^ (1 + epsilon) := by
  obtain ⟨Nzero, hzero⟩ := dyadic_homogeneousTouchingMass_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨Nzero, fun N hN L hlo hhi => hzero N hN L hlo hhi _ ?_⟩
  intro x hx
  have hr := Finset.mem_Ico.mp hx
  unfold dyadicCutoff
  omega

theorem lemma_two_eight_macroscopic (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      homogeneousTouchingMass (M + L) L (macroscopicStarts M delta) ≤ (M : ℝ) ^ (1 + epsilon) := by
  obtain ⟨Mzero, hzero⟩ := macroscopic_homogeneousTouchingMass_le_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨Mzero, fun M hM L hlo hhi => hzero M hM L hlo hhi _ ?_⟩
  intro x hx
  have hr := Finset.mem_Ico.mp hx
  omega

theorem lemma_two_eight_overlap {g : ℕ → Bit} {x y L : ℕ}
    (hpositive : 0 < Nat.dist x y) (hoverlap : Nat.dist x y < L) :
    ¬(StartEvent g x L ∧ StartEvent g y L) := by
  apply startEvents_disjoint_of_dist_lt _ hoverlap
  intro h
  simp only [h, Nat.dist_self, lt_self_iff_false] at hpositive

theorem historical_touchingRho_eq {N L : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ TouchingPairs.touchingPairs N L) :
    TouchingMass.touchingRho N L p =
      relationRho (twoStartSystem (dyadicCutoff N (2 * L)) p.1 p.2 L) := by
  have hd := (TouchingPairs.mem_touchingPairs.mp hp).2.2
  rw [TouchingMass.touchingRho, TouchingMass.touchingLower,
    SectionTwelveMoments.touchingSystem_eq_twoStartSystem]
  rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq hd with h | h
  · rw [min_eq_left (by omega : p.1 ≤ p.2), ← h]
  · rw [min_eq_right (by omega : p.2 ≤ p.1), ← h]
    exact relationRho_comm _ _ _ _

theorem historical_touchingMass_le_homogeneous (N L : ℕ) :
    (TouchingMass.touchingMass N L : ℝ) ≤
      homogeneousTouchingMass (dyadicCutoff N (2 * L)) L (dyadicBlock N) := by
  unfold TouchingMass.touchingMass homogeneousTouchingMass
  rw [Nat.cast_sum]
  change (∑ p ∈ TouchingPairs.touchingPairs N L, (TouchingMass.touchingWeight N L p : ℝ)) ≤
    ∑ p ∈ TouchingPairs.touchingPairs N L,
      (2 : ℝ) ^ relationRho (twoStartSystem (dyadicCutoff N (2 * L)) p.1 p.2 L)
  apply Finset.sum_le_sum
  intro p hp
  have hn : TouchingMass.touchingWeight N L p ≤
      2 ^ relationRho (twoStartSystem (dyadicCutoff N (2 * L)) p.1 p.2 L) := by
    rw [TouchingMass.touchingWeight, historical_touchingRho_eq hp]
    exact Nat.sub_le _ _
  exact_mod_cast hn

theorem historical_touchingMass_le_eventually (betaMin betaMax epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      (TouchingMass.touchingMass N L : ℝ) ≤ (N : ℝ) ^ (1 + epsilon) := by
  obtain ⟨Nzero, hzero⟩ := lemma_two_eight_dyadic betaMin betaMax epsilon hbetaMin hbeta hepsilon
  exact ⟨Nzero, fun N hN L hlo hhi =>
    (historical_touchingMass_le_homogeneous N L).trans (hzero N hN L hlo hhi)⟩

end

end PaperC.V282.TouchingPairMass
