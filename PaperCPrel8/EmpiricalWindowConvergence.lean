import PaperCPrel8.EmpiricalWindowLaw
import PaperCPrel8.EmpiricalTransfer

/-! # From summable field errors and window ratios to empirical convergence

This endpoint proves the probabilistic completion for actual window
frequencies. Its remaining numerical hypotheses are explicit: a summable
field-TV bound, a summable h/N ratio, and convergence of the target means.
No source tail probability or independence across scales is assumed.
-/
namespace PaperC.Prel8.EmpiricalWindowConvergence
open MeasureTheory ProbabilityTheory Filter Topology
open PaperC.V282.PoissonFieldMeasure PaperC.V282.SharpConditioning
open PaperC.V282.FiniteFieldTotalVariation
open PaperC.Prel8.EmpiricalWindowVariance PaperC.Prel8.EmpiricalWindowLaw
open PaperC.Prel8.EmpiricalTransfer
open scoped BigOperators NNReal
noncomputable section

/-- The frequencies are nonnegative for every deterministic field. -/
theorem frequency_nonneg {n : ℕ} (N h r : ℕ) (x : Fin n → ℕ) :
    0 ≤ frequency N h r x := by
  unfold frequency
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro u _
  unfold hit
  split <;> norm_num

/-- The empirical frequencies sum to one, even for arbitrary truncated windows. -/
theorem frequency_hasSum {n N : ℕ} (hN : 0 < N) (h : ℕ) (x : Fin n → ℕ) :
    HasSum (fun r => frequency N h r x) 1 := by
  have hs (u : Fin N) : HasSum (fun r => hit h u.val r x) (1:ℝ) := by
    simpa only [hit, eq_comm] using hasSum_ite_eq (windowCount h u.val x) (1:ℝ)
  have ht := (hasSum_sum (s := Finset.univ) (fun u _ => hs u)).div_const (N:ℝ)
  simpa only [frequency, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, div_self (show (N:ℝ) ≠ 0 by positivity)] using ht

/-- Summable field-TV errors and overlap ratios imply summable frequency tails. -/
theorem summable_source_frequency_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n N h : ℕ → ℕ)
    (X : (k : ℕ) → Ω → Fin (n k) → ℕ) (hX : ∀ k, Measurable (X k))
    (p : ℕ → ℝ≥0) (delta : ℕ → ℝ)
    (hN : ∀ k, 0 < N k) (hh : ∀ᶠ k in atTop, 0 < h k)
    (hfit : ∀ᶠ k in atTop, N k+h k ≤ n k+1)
    (hTV : ∀ᶠ k in atTop, measureTotalVariation (μ.map (X k))
      (fieldMeasure (fun _ : Fin (n k) => p k)) ≤ delta k)
    (hd : Summable delta) (hratio : Summable (fun k => (h k:ℝ)/(N k)))
    (r : ℕ) {eta : ℝ} (heta : 0 < eta) :
    Summable (fun k => μ.real {ω |
      eta < |frequency (N k) (h k) r (X k ω)-(poissonMeasure (h k*p k)).real {r}|}) := by
  apply (hd.add (hratio.mul_right (1/(2*eta^2)))).of_norm_bounded_eventually_nat
  filter_upwards [hh,hfit,hTV] with k hk hfk htk
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  have hb := source_frequency_tail_le μ (X k) (hX k) (p k) (hN k) hk hfk (delta k) htk r heta
  have hn : (0:ℝ)<N k := Nat.cast_pos.mpr (hN k)
  have he : (0:ℝ)<eta^2 := sq_pos_of_pos heta
  calc
    _ ≤ delta k+(2*(h k:ℝ)-1)/(4*N k*eta^2) := hb
    _ ≤ delta k+((h k:ℝ)/(N k))*(1/(2*eta^2)) := by
      apply add_le_add_right
      field_simp
      nlinarith

/-- Almost-sure total variation of actual empirical count frequencies.
The target means may vary with k; only their coordinate limit is required. -/
theorem ae_empirical_variation_convergence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n N h : ℕ → ℕ)
    (X : (k : ℕ) → Ω → Fin (n k) → ℕ) (hX : ∀ k, Measurable (X k))
    (p : ℕ → ℝ≥0) (delta : ℕ → ℝ)
    (hN : ∀ k, 0 < N k) (hh : ∀ᶠ k in atTop, 0 < h k)
    (hfit : ∀ᶠ k in atTop, N k+h k ≤ n k+1)
    (hTV : ∀ᶠ k in atTop, measureTotalVariation (μ.map (X k))
      (fieldMeasure (fun _ : Fin (n k) => p k)) ≤ delta k)
    (hd : Summable delta) (hratio : Summable (fun k => (h k:ℝ)/(N k)))
    (limit : ℕ → ℝ) (hl : HasSum limit 1) (hl0 : ∀ r, 0 ≤ limit r)
    (hq : ∀ r, Tendsto (fun k => (poissonMeasure (h k*p k)).real {r}) atTop (𝓝 (limit r))) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => massTotalVariation
      (fun r => frequency (N k) (h k) r (X k ω)) limit) atTop (𝓝 0) := by
  apply ae_variation_convergence μ _ _ limit
    (fun k ω => frequency_hasSum (hN k) (h k) (X k ω))
    (fun k ω r => frequency_nonneg _ _ _ _) hl hl0 hq
  intro r m
  exact summable_source_frequency_tails μ n N h X hX p delta hN hh hfit hTV hd hratio r
    (by positivity)

end
end PaperC.Prel8.EmpiricalWindowConvergence
