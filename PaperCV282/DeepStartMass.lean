import PaperCV282.PostQuadraticGap
import PaperCV282.PostQuadraticDecay
import PaperCV282.IntermediateDefectCount

/-! # Actual deep-start masses, with one global exceptional population -/
namespace PaperC.V282.DeepStartMass

open Filter Finset WindowValues InfiniteStartProbabilityTransfer
open PointwiseStartBounds PostQuadraticStartBounds PostQuadraticLiterature
open BalasubramanianShoreyInput IntermediateDefectCount
open scoped BigOperators

noncomputable section

/-- At most one complete-window defect gives the exact baseline upper bound. -/
theorem start_probability_le_baseline {x L : ℕ} (hx : 2 ≤ x) (hL : 0 < L)
    (hm : (defectIndices (L + 1) x (L + 1)).card ≤ 1) :
    infiniteStartProbability x L ≤ 1 / (2 : ℝ) ^ L := by
  have h := (corollary_two_five_start_bounds hx hL).2
  have hmzero : (defectIndices (L + 1) x (L + 1)).card - 1 = 0 := by omega
  simpa only [hmzero, pow_zero] using h

/-- The actual first moment splits into baseline starts and the two-defect population. -/
theorem finite_mass_split {L : ℕ} {s : Finset ℕ} {g R : ℝ} (hL : 0 < L)
    (hx : ∀ x ∈ s, 2 ≤ x)
    (hp : ∀ x ∈ s, infiniteStartProbability x L ≤ (2 : ℝ) ^ (-g))
    (hcard : ((s.filter (fun x => 2 ≤ (defectIndices (L + 1) x (L + 1)).card)).card : ℝ) ≤ R) :
    (∑ x ∈ s, infiniteStartProbability x L) ≤
      (s.card : ℝ) / (2 : ℝ) ^ L + R * (2 : ℝ) ^ (-g) := by
  classical
  let bad := s.filter (fun x => 2 ≤ (defectIndices (L + 1) x (L + 1)).card)
  have hpoint : ∀ x ∈ s, infiniteStartProbability x L ≤
      1 / (2 : ℝ) ^ L + if x ∈ bad then (2 : ℝ) ^ (-g) else 0 := by
    intro x hxs
    by_cases hb : x ∈ bad
    · rw [if_pos hb]
      have hnonneg : 0 ≤ 1 / (2 : ℝ) ^ L := by positivity
      linarith [hp x hxs]
    · rw [if_neg hb, add_zero]
      apply start_probability_le_baseline (hx x hxs) hL
      have hsmall : ¬ 2 ≤ (defectIndices (L + 1) x (L + 1)).card := by
        intro hd
        exact hb (Finset.mem_filter.mpr ⟨hxs, hd⟩)
      omega
  have hsum : (∑ x ∈ s, if x ∈ bad then (2 : ℝ) ^ (-g) else 0) =
      (bad.card : ℝ) * (2 : ℝ) ^ (-g) := by
    rw [← Finset.sum_filter]
    have hfilter : s.filter (fun x => x ∈ bad) = bad := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · exact And.right
      · intro hb
        exact ⟨(Finset.mem_filter.mp hb).1, hb⟩
    rw [hfilter]
    simp
  calc
    _ ≤ ∑ x ∈ s, (1 / (2 : ℝ) ^ L + if x ∈ bad then (2 : ℝ) ^ (-g) else 0) :=
      Finset.sum_le_sum hpoint
    _ = (s.card : ℝ) / (2 : ℝ) ^ L + (bad.card : ℝ) * (2 : ℝ) ^ (-g) := by
      rw [Finset.sum_add_distrib, hsum]
      simp [div_eq_mul_inv]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard (by positivity))

/-- A band-uniform deep first-moment estimate on every finite submask.
One Pell box controls the entire mask, so no dyadic multiplicity is needed. -/
theorem deep_mass_bound_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ theta K : ℝ, 0 ≤ K ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℕ) →
      (L + 1 : ℕ) ≤ betaMax * Real.log M →
      ∀ s : Finset ℕ, (∀ x ∈ s, (L + 1) ^ 2 + 2 < x ∧ x ≤ 2 * M) →
      (∑ x ∈ s, infiniteStartProbability x L) ≤
        (s.card : ℝ) / (2 : ℝ) ^ L +
        Real.exp (K * ((L : ℝ) / Real.log L)) * (2 : ℝ) ^ (-gap (L + 1) theta) := by
  classical
  obtain ⟨theta, Lzero, hp⟩ := postquadratic_start_probability hShorey
  obtain ⟨K, hK, Mc, hc⟩ := global_two_defect_count_eventually
    betaMin betaMax hbetaMin hbeta hPNT hNR
  obtain ⟨Ma, ha⟩ := CriticalWeightedDefect.admissible_eventually hbetaMin hbeta
  obtain ⟨Mh, hh⟩ := CriticalWeightedDefect.height_tends_to_infinity
    (c₂ := betaMax) hbetaMin (Lzero + 2)
  refine ⟨theta, K, hK, max Mc (max Ma Mh), ?_⟩
  intro M hM L hlo hup s hs
  have hLlarge := hh M (by omega) (L + 1) (ha M (by omega) (L + 1) ⟨hbetaMin,hbeta,hlo,hup⟩)
  apply finite_mass_split (by omega : 0 < L)
  · intro x hx
    have := hs x hx
    omega
  · intro x hx
    exact hp L (by omega) x (hs x hx).1
  · apply hc M (by omega) L hlo hup
    intro x hx
    obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx
    exact ⟨(hs x hxs).1, (hs x hxs).2, hd⟩

/-- The deep contribution in (7.7), uniformly for every finite mask in the full
post-quadratic range.  Microscopic starts are handled separately by Theorem 7.1. -/
theorem deep_mass_ambient_scale_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℕ) →
      (L + 1 : ℕ) ≤ betaMax * Real.log M →
      ∀ s : Finset ℕ, (∀ x ∈ s, (L + 1) ^ 2 + 2 < x ∧ x ≤ 2 * M) →
      (∑ x ∈ s, infiniteStartProbability x L) ≤
        (s.card : ℝ) / (2 : ℝ) ^ L +
        Real.exp (-(betaMin / 4) * (Real.log M / Real.log (Real.log M))) := by
  obtain ⟨theta, K, hK, Mc, hc⟩ := deep_mass_bound_eventually
    betaMin betaMax hbetaMin hbeta hShorey hPNT hNR
  obtain ⟨Ms, hs⟩ := IntermediateDefectScales.logarithmic_scales_eventually
    betaMin betaMax hbetaMin hbeta
  obtain ⟨Le, he⟩ := eventually_atTop.mp
    (PostQuadraticDecay.exceptional_envelope_le_eventually theta K 1 hK (by norm_num))
  obtain ⟨Ma, ha⟩ := CriticalWeightedDefect.admissible_eventually hbetaMin hbeta
  obtain ⟨Mh, hh⟩ := CriticalWeightedDefect.height_tends_to_infinity
    (c₂ := betaMax) hbetaMin (Le + 1)
  refine ⟨max Mc (max Ms (max Ma Mh)), ?_⟩
  intro M hM L hlo hup s hmask
  have hLlarge := hh M (by omega) (L + 1) (ha M (by omega) (L + 1) ⟨hbetaMin,hbeta,hlo,hup⟩)
  apply (hc M (by omega) L hlo hup s hmask).trans
  refine add_le_add le_rfl ((he L (by omega)).trans ?_)
  apply Real.exp_le_exp.mpr
  have hh := (hs M (by omega) L hlo hup).1
  linarith

end
end PaperC.V282.DeepStartMass
