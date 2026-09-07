import PaperCV282.MicroscopicInteriorBounds
import PaperCV282.DeepStartMass

/-! # The full prefix first moment in Proposition 7.3 -/
namespace PaperC.V282.MesoscopicPrefixMass

open Filter Finset InfiniteStartProbabilityTransfer
open MicroscopicInteriorBounds DeepStartMass IntermediateDefectScales
open PostQuadraticPrimeBounds PostQuadraticLiterature PrimeEulerPNT
open LaishramUniformInput HarmonicIncidenceSurplus
open scoped BigOperators

noncomputable section

/-- A band-uniform exponential bound on the exact border mass. -/
theorem border_mass_ambient_scale_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hPNT : PrimeNumberTheoremRemainder) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℕ) →
      (L + 1 : ℕ) ≤ betaMax * Real.log M →
      ((2 : ℝ)⁻¹) ^ Nat.primeCounting L ≤
        Real.exp (-(betaMin * Real.log 2 / 8) * (Real.log M / Real.log (Real.log M))) := by
  have hp := (primeCounting_normalized_tendsto_one hPNT).eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨Lp, hp⟩ := eventually_atTop.mp hp
  obtain ⟨Ms, hs⟩ := logarithmic_scales_eventually betaMin betaMax hbetaMin hbeta
  obtain ⟨Ma, ha⟩ := CriticalWeightedDefect.admissible_eventually hbetaMin hbeta
  obtain ⟨Mh, hh⟩ := CriticalWeightedDefect.height_tends_to_infinity
    (c₂ := betaMax) hbetaMin (max Lp 2 + 1)
  refine ⟨max Ms (max Ma Mh), ?_⟩
  intro M hM L hlo hup
  have hLlarge := hh M (by omega) (L + 1) (ha M (by omega) (L + 1) ⟨hbetaMin,hbeta,hlo,hup⟩)
  have hL : 2 ≤ L := by omega
  have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast hL)
  have hLp : 0 < (L : ℝ) := by positivity
  have hhalf := hp L (by omega)
  have hmul := (lt_div_iff₀ hLp).mp hhalf
  have hprime : (1 / 2 : ℝ) * ((L : ℝ) / Real.log L) ≤ Nat.primeCounting L := by
    rw [← mul_div_assoc, div_le_iff₀ hlogL]
    linarith
  have hscale := (hs M (by omega) L hlo hup).1
  have hplower : (betaMin / 8) * (Real.log M / Real.log (Real.log M)) ≤
      Nat.primeCounting L := by linarith
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 2⁻¹), Real.log_inv]
  apply Real.exp_le_exp.mpr
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  nlinarith

/-- Full masked first-moment estimate, with both microscopic and deep sites actual.
The mask may vary freely after the common scale/length threshold. -/
theorem masked_prefix_mass_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℕ) →
      (L + 1 : ℕ) ≤ betaMax * Real.log M →
      ∀ s : Finset ℕ, (∀ x ∈ s, 2 ≤ x ∧ x ≤ 2 * M) →
      (∑ x ∈ s, infiniteStartProbability x L) ≤ (s.card : ℝ) / (2 : ℝ) ^ L +
        2 * Real.exp (-(betaMin * Real.log 2 / 8) * (Real.log M / Real.log (Real.log M))) := by
  classical
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  have hstar : (1 / 12 : ℝ) < (surplus 11 : ℝ) := by rw [surplus_eleven_eq]; norm_num
  obtain ⟨Li, hi⟩ := theorem_seven_one_interior_sum hLS hShorey hPNT
    (by norm_num : (0 : ℝ) < 1 / 12) hstar
  obtain ⟨Md, hd⟩ := deep_mass_ambient_scale_eventually
    betaMin betaMax hbetaMin hbeta hShorey hPNT hNR
  obtain ⟨Mb, hb⟩ := border_mass_ambient_scale_eventually betaMin betaMax hbetaMin hbeta hPNT
  obtain ⟨Ma, ha⟩ := CriticalWeightedDefect.admissible_eventually hbetaMin hbeta
  obtain ⟨Mh, hh⟩ := CriticalWeightedDefect.height_tends_to_infinity
    (c₂ := betaMax) hbetaMin (max Li 4 + 1)
  obtain ⟨Mlog, hlog⟩ := LemmaFifteenThree.log_const_le_loglog_eventually hbetaMax
  refine ⟨max 2 (max Md (max Mb (max Ma (max Mh Mlog)))), ?_⟩
  intro M hM L hlo hup s hmask
  have hLlarge := hh M (by omega) (L + 1) (ha M (by omega) (L + 1) ⟨hbetaMin,hbeta,hlo,hup⟩)
  have hLfour : 4 ≤ L := by omega
  let u := s.filter (fun x => x ≤ 2 * L ^ 2)
  let v := s.filter (fun x => ¬x ≤ 2 * L ^ 2)
  have hu : u ⊆ Icc 2 (2 * L ^ 2) := by
    intro x hx
    obtain ⟨hxs,hxL⟩ := mem_filter.mp hx
    exact mem_Icc.mpr ⟨(hmask x hxs).1,hxL⟩
  have hmic : (∑ x ∈ u, infiniteStartProbability x L) ≤ ((2 : ℝ)⁻¹) ^ Nat.primeCounting L := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hu (fun x _ _ => by exact ENNReal.toReal_nonneg)).trans
    apply (hi L (by omega)).trans
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hp : (0 : ℝ) ≤ Nat.primeCounting L := by positivity
    nlinarith
  have hdeep := hd M (by omega) L hlo hup v (by
    intro x hx
    obtain ⟨hxs,hxl⟩ := mem_filter.mp hx
    have hlocal : (L + 1) ^ 2 + 2 < 2 * L ^ 2 := by nlinarith
    exact ⟨by omega, (hmask x hxs).2⟩)
  have hloglog := (hlog M (by omega)).1
  have hS : 0 ≤ Real.log M / Real.log (Real.log M) := by
    apply div_nonneg _ hloglog.le
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hsmall : Real.exp (-(betaMin / 4) * (Real.log M / Real.log (Real.log M))) ≤
      Real.exp (-(betaMin * Real.log 2 / 8) * (Real.log M / Real.log (Real.log M))) := by
    apply Real.exp_le_exp.mpr
    have hlogTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hc : betaMin * Real.log 2 / 8 ≤ betaMin / 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right (neg_le_neg hc) hS
  have hcard : (v.card : ℝ) ≤ s.card := by exact_mod_cast card_filter_le s (fun x => ¬x ≤ 2 * L ^ 2)
  have hsplit : (∑ x ∈ s, infiniteStartProbability x L) =
      (∑ x ∈ u, infiniteStartProbability x L) + ∑ x ∈ v, infiniteStartProbability x L := by
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  have hm := hmic.trans (hb M (by omega) L hlo hup)
  have hv := hdeep.trans (add_le_add (div_le_div_of_nonneg_right hcard (by positivity)) hsmall)
  linarith

/-- The exact finite set of starts in the open real prefix. -/
def realPrefix (M : ℕ) (delta : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊(M : ℝ) ^ delta⌋₊).filter (fun x => (x : ℝ) < (M : ℝ) ^ delta)

theorem mem_realPrefix {M x : ℕ} {delta : ℝ} :
    x ∈ realPrefix M delta ↔ 2 ≤ x ∧ (x : ℝ) < (M : ℝ) ^ delta := by
  rw [realPrefix, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hx,_⟩,hxM⟩; exact ⟨hx,hxM⟩
  · rintro ⟨hx,hxM⟩
    exact ⟨⟨hx,(Nat.le_floor_iff (Real.rpow_nonneg (by positivity) _)).mpr hxM.le⟩,hxM⟩

theorem card_realPrefix_le (M : ℕ) (delta : ℝ) :
    ((realPrefix M delta).card : ℝ) ≤ (M : ℝ) ^ delta := by
  have hc : (realPrefix M delta).card ≤ ⌊(M : ℝ) ^ delta⌋₊ := by
    apply (card_filter_le _ _).trans
    simp only [Nat.card_Icc]
    omega
  exact (show ((realPrefix M delta).card : ℝ) ≤ (⌊(M : ℝ) ^ delta⌋₊ : ℝ) by exact_mod_cast hc).trans
    (Nat.floor_le (Real.rpow_nonneg (by positivity) _))

/-- Equation (7.7), including every true start in the prefix; the threshold precedes delta. -/
theorem equation_seven_seven
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℕ) →
      (L + 1 : ℕ) ≤ betaMax * Real.log M →
      ∀ delta : ℝ, 0 < delta → delta < 1 →
      (∑ x ∈ realPrefix M delta, infiniteStartProbability x L) ≤
        (M : ℝ) ^ delta / (2 : ℝ) ^ L +
        2 * Real.exp (-(betaMin * Real.log 2 / 8) * (Real.log M / Real.log (Real.log M))) := by
  obtain ⟨Mzero,h⟩ := masked_prefix_mass_eventually betaMin betaMax hbetaMin hbeta hLS hShorey hPNT hNR
  refine ⟨max Mzero 1, ?_⟩
  intro M hM L hlo hup delta _hdelta hdeltaOne
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hp : (M : ℝ) ^ delta ≤ M := by
    simpa using Real.rpow_le_rpow_of_exponent_le hMone hdeltaOne.le
  have hh := h M (by omega) L hlo hup (realPrefix M delta) (by
    intro x hx
    obtain ⟨hx,hxm⟩ := mem_realPrefix.mp hx
    have hxn : x ≤ M := by exact_mod_cast (hxm.le.trans hp)
    exact ⟨hx,by omega⟩)
  exact hh.trans (add_le_add (div_le_div_of_nonneg_right (card_realPrefix_le M delta) (by positivity)) le_rfl)

/-- The displayed bulk term is precisely lambda_M times M^(delta-1). -/
theorem prefix_bulk_term_eq (M L : ℕ) (delta : ℝ) (hM : 0 < M) :
    (M : ℝ) ^ delta / (2 : ℝ) ^ L =
      ((M : ℝ) / (2 : ℝ) ^ L) * (M : ℝ) ^ (delta - 1) := by
  rw [Real.rpow_sub (by exact_mod_cast hM), Real.rpow_one]
  field_simp

end
end PaperC.V282.MesoscopicPrefixMass
