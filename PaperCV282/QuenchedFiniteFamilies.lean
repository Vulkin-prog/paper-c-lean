import PaperCV282.QuenchedBorelCantelli

/-!
# Almost-sure simultaneous control of logarithmically many conditional laws

The finite union is paid before Borel--Cantelli. Its cardinality is absorbed
by an arbitrarily small part of the fixed saddle margin; no independence of
the scales, environments or members of the family is used.
-/

namespace PaperC.V282.QuenchedFiniteFamilies

open MeasureTheory Filter Topology GeometricSaddleSummability QuenchedBorelCantelli
open SaddleScales SaddleCutoffAdmissibility

noncomputable section

/-- A logarithmic multiplicity costs arbitrarily little of a positive saddle margin. -/
theorem log_weight_le_exp_nu {sizes : ℕ → ℕ} (hg : GeometricLowerGrowth sizes)
    (C a eta : ℝ) (ha : 0 < a) (heta : 0 < eta) :
    ∀ᶠ k in atTop, C * Real.log (sizes k) ≤
      Real.exp (eta * saddleNu a (Real.log (sizes k))) := by
  have hlog := log_sizes_tendsto_atTop hg
  have hnu := (tendsto_saddleNu_atTop ha).comp hlog
  have hsmall : Tendsto (fun k =>
      (Real.log (|C| + 1) + Real.log (Real.log (sizes k))) /
        saddleNu a (Real.log (sizes k))) atTop (𝓝 0) := by
    simpa only [add_div, add_zero, Function.comp_def] using
      ((tendsto_const_nhds (x := Real.log (|C| + 1))).div_atTop hnu).add
        ((tendsto_log_div_saddleNu ha).comp hlog)
  filter_upwards [hsmall.eventually (gt_mem_nhds heta),
    hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hnu.eventually (eventually_gt_atTop (0 : ℝ))] with k hs hl hn
  have hcost := ((div_lt_iff₀ hn).mp hs).le
  calc
    _ ≤ (|C| + 1) * Real.log (sizes k) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hl.le
    _ = Real.exp (Real.log (|C| + 1) + Real.log (Real.log (sizes k))) := by
      rw [Real.exp_add, Real.exp_log (by positivity), Real.exp_log hl]
    _ ≤ _ := Real.exp_le_exp.mpr hcost

/-- Exact algebra for the Markov amplification and the multiplicity cost. -/
theorem amplification_identity (K z c beta eta nu : ℝ) :
    Real.exp (eta * nu) * ((K * Real.exp (-c * nu) + z) / Real.exp (-beta * nu)) =
      K * Real.exp (-(c - beta - eta) * nu) + Real.exp ((beta + eta) * nu) * z := by
  have hi : (Real.exp (-beta * nu))⁻¹ = Real.exp (beta * nu) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have he1 : Real.exp (eta * nu) * Real.exp (-c * nu) * Real.exp (beta * nu) =
      Real.exp (-(c - beta - eta) * nu) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (eta * nu) * Real.exp (beta * nu) =
      Real.exp ((beta + eta) * nu) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [div_eq_mul_inv, hi]
  calc
    _ = K * (Real.exp (eta * nu) * Real.exp (-c * nu) * Real.exp (beta * nu)) +
        (Real.exp (eta * nu) * Real.exp (beta * nu)) * z := by ring
    _ = _ := by rw [he1, he2]

/-- The full Markov series is summable for a logarithmic finite family. -/
theorem summable_family_ratios {sizes : ℕ → ℕ} (hg : GeometricLowerGrowth sizes)
    (w : ℕ → ℝ) (hw0 : ∀ k, 0 ≤ w k) (C a c beta delta K : ℝ)
    (ha : 0 < a) (hbc : beta < c) (hd : 0 < delta) (hK : 0 ≤ K)
    (hw : ∀ᶠ k in atTop, w k ≤ C * Real.log (sizes k)) :
    Summable (fun k => w k *
      ((K * Real.exp (-c * saddleNu a (Real.log (sizes k))) + (sizes k : ℝ)^(-delta)) /
        Real.exp (-beta * saddleNu a (Real.log (sizes k))))) := by
  let eta := (c - beta) / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hleft : 0 < c - beta - eta := by dsimp [eta]; linarith
  have hs := ((summable_exp_neg_nu hg ha hleft).mul_left K).add
    (summable_exp_nu_mul_size_rpow hg ha hd (beta + eta))
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hw, log_weight_le_exp_nu hg C a eta ha heta] with k hw he
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 k) (by positivity))]
  calc
    _ ≤ Real.exp (eta * saddleNu a (Real.log (sizes k))) *
        ((K * Real.exp (-c * saddleNu a (Real.log (sizes k))) + (sizes k : ℝ)^(-delta)) /
          Real.exp (-beta * saddleNu a (Real.log (sizes k)))) :=
      mul_le_mul_of_nonneg_right (hw.trans he) (by positivity)
    _ = _ := amplification_identity _ _ _ _ _ _

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- Simultaneous almost-sure control of every member of the actual finite family. -/
theorem ae_eventually_uniform_saddle_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (indices : ℕ → Finset ι) (f : ℕ → ι → Ω → ℝ)
    (hf : ∀ k i, Integrable (f k i) μ) (hf0 : ∀ k i omega, 0 ≤ f k i omega)
    (sizes : ℕ → ℕ) (hg : GeometricLowerGrowth sizes)
    (C a c beta delta K : ℝ) (ha : 0 < a) (hbc : beta < c) (hd : 0 < delta) (hK : 0 ≤ K)
    (hcard : ∀ᶠ k in atTop, ((indices k).card : ℝ) ≤ C * Real.log (sizes k))
    (hmean : ∀ᶠ k in atTop, ∀ i ∈ indices k,
      (∫ omega, f k i omega ∂μ) ≤
        K * Real.exp (-c * saddleNu a (Real.log (sizes k))) + (sizes k : ℝ)^(-delta)) :
    ∀ᵐ omega ∂μ, ∀ᶠ k in atTop, ∀ i ∈ indices k,
      f k i omega ≤ Real.exp (-beta * saddleNu a (Real.log (sizes k))) := by
  let F := fun k omega => ∑ i ∈ indices k, f k i omega
  have hF : ∀ k, Integrable (F k) μ := fun k =>
    integrable_finsetSum (indices k) (fun i _ => hf k i)
  have hF0 : ∀ k omega, 0 ≤ F k omega := fun k omega =>
    Finset.sum_nonneg (fun i _ => hf0 k i omega)
  have hsum := summable_family_ratios hg (fun k => ((indices k).card : ℝ))
    (fun _ => Nat.cast_nonneg _) C a c beta delta K ha hbc hd hK hcard
  have hresult := ae_eventually_le_of_summable_ratios μ F hF hF0
    (fun k => ((indices k).card : ℝ) *
      (K * Real.exp (-c * saddleNu a (Real.log (sizes k))) + (sizes k : ℝ)^(-delta)))
    (fun k => Real.exp (-beta * saddleNu a (Real.log (sizes k))))
    (fun _ => Real.exp_pos _) ?_ (by simpa only [mul_div_assoc] using hsum)
  · filter_upwards [hresult] with omega h
    filter_upwards [h] with k hk
    intro i hi
    exact (Finset.single_le_sum (fun j _ => hf0 k j omega) hi).trans hk
  · filter_upwards [hmean] with k hk
    rw [show (∫ omega, F k omega ∂μ) = ∑ i ∈ indices k, ∫ omega, f k i omega ∂μ from
      integral_finsetSum _ (fun i _ => hf k i)]
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hk

end
end PaperC.V282.QuenchedFiniteFamilies
