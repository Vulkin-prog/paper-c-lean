import PaperCPrel8.TypicalDictionaryTheorem

/-! # Turning uniform arbitrary-slack bounds into one deterministic little-oh remainder -/
namespace PaperC.Prel8.UniformExponentialEnvelope
open Filter Topology
noncomputable section

/-- Positive envelope after subtracting the separately controlled polynomial error. -/
def remainder (V P R : ℕ → ℝ) (C : ℝ) (N : ℕ) : ℝ :=
  Real.log (max (R N/C-P N) (Real.exp (-V N)))+V N

/-- The chosen remainder is nonnegative at every index, including initial ones. -/
theorem remainder_nonneg (V P R : ℕ → ℝ) (C : ℝ) (N : ℕ) :
    0 ≤ remainder V P R C N := by
  have h := Real.log_le_log (Real.exp_pos (-V N)) (le_max_right (R N/C-P N) (Real.exp (-V N)))
  rw [Real.log_exp] at h
  unfold remainder
  linarith

/-- The same deterministic envelope bounds every original error at every index. -/
theorem remainder_bound (V P R : ℕ → ℝ) {C : ℝ} (hC : 0 < C) (N : ℕ) :
    R N ≤ C*(Real.exp (-V N+remainder V P R C N)+P N) := by
  have hp : 0 < max (R N/C-P N) (Real.exp (-V N)) := lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  have he : -V N+remainder V P R C N=Real.log (max (R N/C-P N) (Real.exp (-V N))) := by unfold remainder; ring
  rw [he,Real.exp_log hp]
  have h := (div_le_iff₀ hC).mp (show R N/C ≤ max (R N/C-P N) (Real.exp (-V N))+P N by linarith [le_max_left (R N/C-P N) (Real.exp (-V N))])
  nlinarith

/-- Uniform bounds for every positive slack yield a single o(nu) remainder. -/
theorem remainder_div_tendsto_zero (V nu P R : ℕ → ℝ) {C : ℝ} (hC : 0 < C)
    (hnu : Tendsto nu atTop atTop)
    (hbound : ∀ eta : ℝ, 0 < eta → ∀ᶠ N in atTop,
      R N ≤ C*(Real.exp (-V N+eta*nu N)+P N)) :
    Tendsto (fun N => remainder V P R C N/nu N) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_,?_⟩
  · intro a ha
    filter_upwards [hnu.eventually (eventually_gt_atTop (0:ℝ))] with N hn
    exact lt_of_lt_of_le ha (div_nonneg (remainder_nonneg V P R C N) hn.le)
  · intro b hb
    filter_upwards [hnu.eventually (eventually_gt_atTop (0:ℝ)),hbound (b/2) (by linarith)] with N hn hR
    have hr : R N/C-P N ≤ Real.exp (-V N+(b/2)*nu N) := by
      have h : R N/C ≤ Real.exp (-V N+(b/2)*nu N)+P N := by
        apply (div_le_iff₀ hC).mpr
        nlinarith [hR]
      linarith
    have he : Real.exp (-V N) ≤ Real.exp (-V N+(b/2)*nu N) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hmax := max_le hr he
    have hp : 0 < max (R N/C-P N) (Real.exp (-V N)) :=
      lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
    have hl := Real.log_le_log hp hmax
    rw [Real.log_exp] at hl
    have hrem : remainder V P R C N ≤ (b/2)*nu N := by unfold remainder; linarith
    have hd := (div_le_iff₀ hn).mpr hrem
    exact hd.trans_lt (by linarith)

end
end PaperC.Prel8.UniformExponentialEnvelope
