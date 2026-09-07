import PaperCV282.PostQuadraticGap
import PaperC.Asymptotics.LemmaFifteenThree

/-! # Quantitative absorption by the post-quadratic gap -/
namespace PaperC.V282.PostQuadraticDecay

open Filter BalasubramanianShoreyInput PropositionFifteenFiveDecay
open PostQuadraticPrimeBounds
open scoped Topology

noncomputable section

/-- Every fixed exponential counting cost is absorbed with any fixed positive margin. -/
theorem exceptional_envelope_le_eventually (theta K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) :
    ∀ᶠ L : ℕ in atTop,
      Real.exp (K * ((L : ℝ) / Real.log L)) * (2 : ℝ) ^ (-gap (L + 1) theta) ≤
        Real.exp (-A * ((L : ℝ) / Real.log L)) := by
  obtain ⟨Lzero, hgap⟩ := gap_ge_pell_and_log_eventually theta (K + A) (by positivity)
  filter_upwards [eventually_ge_atTop (max Lzero 2)] with L hL
  have hLp : 0 < (L : ℝ) := by
    exact_mod_cast (show 0 < L by omega)
  have hlog : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (show 2 ≤ L by omega))
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h := mul_le_mul_of_nonneg_right (hgap L (by omega)) hlogTwo.le
  have he : K * ((L : ℝ) / Real.log L) - Real.log 2 * gap (L + 1) theta ≤
      -A * ((L : ℝ) / Real.log L) := by
    have hc : 0 ≤ (K + A) * ((L : ℝ) / Real.log L) := by positivity
    have hh : ((2 * (K + A) / Real.log 2) * ((L : ℝ) / Real.log L) +
        3 * Real.log L / Real.log 2) * Real.log 2 =
        2 * (K + A) * ((L : ℝ) / Real.log L) + 3 * Real.log L := by field_simp
    rw [hh] at h
    nlinarith
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- A prime-count upper bound is derived from the same ordinary PNT input. -/
theorem primeCounting_le_two_scale_eventually (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder) :
    ∀ᶠ L : ℕ in atTop,
      (Nat.primeCounting L : ℝ) ≤ 2 * ((L : ℝ) / Real.log L) := by
  filter_upwards [(primeCounting_normalized_tendsto_one hPNT).eventually
    (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)), eventually_ge_atTop 2] with L hp hL
  have hLp : 0 < (L : ℝ) := by positivity
  have hlog : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast hL)
  have ht := (div_lt_iff₀ hLp).mp hp
  rw [← mul_div_assoc, le_div_iff₀ hlog]
  linarith

/-- The exceptional envelope is negligible even relative to the exact border probability. -/
theorem exceptional_relative_to_border_le_eventually
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (theta K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) :
    ∀ᶠ L : ℕ in atTop,
      (Real.exp (K * ((L : ℝ) / Real.log L)) * (2 : ℝ) ^ (-gap (L + 1) theta)) /
          ((2 : ℝ)⁻¹) ^ Nat.primeCounting L ≤
        Real.exp (-A * ((L : ℝ) / Real.log L)) := by
  have hlogTwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  filter_upwards [primeCounting_le_two_scale_eventually hPNT,
    exceptional_envelope_le_eventually theta (K + 2 * Real.log 2) A (by positivity) hA]
    with L hp he
  have hprime : (2 : ℝ) ^ Nat.primeCounting L ≤
      Real.exp ((2 * Real.log 2) * ((L : ℝ) / Real.log L)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ = Real.exp (K * ((L : ℝ) / Real.log L)) * (2 : ℝ) ^ Nat.primeCounting L *
        (2 : ℝ) ^ (-gap (L + 1) theta) := by rw [inv_pow, div_inv_eq_mul]; ring
    _ ≤ Real.exp (K * ((L : ℝ) / Real.log L)) *
        Real.exp ((2 * Real.log 2) * ((L : ℝ) / Real.log L)) *
        (2 : ℝ) ^ (-gap (L + 1) theta) := by gcongr
    _ = Real.exp ((K + 2 * Real.log 2) * ((L : ℝ) / Real.log L)) *
        (2 : ℝ) ^ (-gap (L + 1) theta) := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ _ := he

/-- The real B/log B scale diverges. -/
theorem nat_div_log_tendsto_atTop :
    Tendsto (fun L : ℕ => (L : ℝ) / Real.log L) atTop atTop := by
  have hi := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hp : ∀ᶠ L : ℕ in atTop, 0 < Real.log (L : ℝ) / L := by
    filter_upwards [eventually_ge_atTop 2] with L hL
    exact div_pos (Real.log_pos (by exact_mod_cast hL)) (by positivity)
  have hpos := tendsto_nhdsWithin_iff.mpr ⟨hi, hp⟩
  have h := tendsto_inv_nhdsGT_zero.comp hpos
  simpa only [Function.comp_def, id_eq, one_div, inv_div] using h

/-- Negligibility relative to the genuine border scale, with no restriction on upper heights. -/
theorem exceptional_relative_to_border_tendsto_zero
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder) (theta K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun L : ℕ =>
      (Real.exp (K * ((L : ℝ) / Real.log L)) * (2 : ℝ) ^ (-gap (L + 1) theta)) /
          ((2 : ℝ)⁻¹) ^ Nat.primeCounting L) atTop (𝓝 0) := by
  have he := exceptional_relative_to_border_le_eventually hPNT theta K 1 hK (by norm_num)
  have hl : Tendsto (fun L : ℕ => Real.exp (-1 * ((L : ℝ) / Real.log L))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_one_mul] using Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp nat_div_log_tendsto_atTop)
  exact squeeze_zero' (Eventually.of_forall (fun L => by positivity)) he hl

end
end PaperC.V282.PostQuadraticDecay
