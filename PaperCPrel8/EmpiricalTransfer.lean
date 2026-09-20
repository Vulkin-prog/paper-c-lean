import PaperCV282.QuenchedBorelCantelli
import PaperCV282.FiniteFieldTotalVariation
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Summable frequency errors and discrete total variation

Probabilistic completion used by 3PREL8 7.8a: coordinate convergence of
probability masses implies total variation, and summable frequency tail
errors hold simultaneously almost surely for all count values. No
independence between scales or coupling of all target scales is assumed.
The arithmetic microscopic bound and moving-window variance are separate.
-/
namespace PaperC.Prel8.EmpiricalTransfer
open MeasureTheory Filter Topology
open PaperC.V282.FiniteFieldTotalVariation
open scoped BigOperators ENNReal
noncomputable section

/-- Exact overlap identity for two normalized countable mass functions. -/
theorem variation_eq_one_sub_overlap {α : Type*} {p q : α → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1) (hp0 : ∀ a, 0≤p a) (hq0 : ∀ a, 0≤q a) :
    massTotalVariation p q = 1-∑' a, min (p a) (q a) := by
  have hm : Summable (fun a => min (p a) (q a)) :=
    hq.summable.of_nonneg_of_le (fun a => le_min (hp0 a) (hq0 a)) (fun a => min_le_right _ _)
  have hid (a : α) : |p a-q a|=p a+q a-2*min (p a) (q a) := by
    rcases le_total (p a) (q a) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  unfold massTotalVariation
  simp_rw [hid]
  rw [(hp.summable.add hq.summable).tsum_sub (hm.mul_left 2),
    hp.summable.tsum_add hq.summable, tsum_mul_left, hp.tsum_eq, hq.tsum_eq]
  ring

/-- Discrete Scheffe argument: no uniform tail assumption on the source is needed. -/
theorem variation_tendsto_zero {α : Type*} (p : ℕ → α → ℝ) (q : α → ℝ)
    (hp : ∀ n, HasSum (p n) 1) (hq : HasSum q 1)
    (hp0 : ∀ n a, 0≤p n a) (hq0 : ∀ a, 0≤q a)
    (hlim : ∀ a, Tendsto (fun n => p n a) atTop (𝓝 (q a))) :
    Tendsto (fun n => massTotalVariation (p n) q) atTop (𝓝 0) := by
  have hmin : ∀ a, Tendsto (fun n => min (p n a) (q a)) atTop (𝓝 (q a)) := by
    intro a
    simpa using (hlim a).min (tendsto_const_nhds (x := q a))
  have hb : ∀ᶠ n in atTop, ∀ a, ‖min (p n a) (q a)‖ ≤ q a := by
    exact Eventually.of_forall fun n a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp0 n a) (hq0 a))]
      exact min_le_right _ _
  have h := tendsto_tsum_of_dominated_convergence hq.summable hmin hb
  rw [hq.tsum_eq] at h
  have hout := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simp only [sub_self] at hout
  convert hout using 1
  ext n
  exact variation_eq_one_sub_overlap (hp n) hq (hp0 n) hq0

/-- Summable real event masses imply that their events occur only finitely often. -/
theorem ae_eventually_avoid {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (E : ℕ → Set Ω) (hs : Summable (fun n => μ.real (E n))) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ E n := by
  have h := ENNReal.ofReal_tsum_of_nonneg (fun n => measureReal_nonneg (μ := μ) (s := E n)) hs
  simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  apply ae_eventually_notMem
  rw [← h]
  exact ENNReal.ofReal_ne_top

/-- A countable intersection gives one full-measure set for all count values. -/
theorem ae_frequency_convergence {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f : ℕ → Ω → ℕ → ℝ) (q : ℕ → ℕ → ℝ)
    (hs : ∀ r m : ℕ, Summable (fun n => μ.real
      {ω | (1 : ℝ)/(m+1) < |f n ω r-q n r|})) :
    ∀ᵐ ω ∂μ, ∀ r, Tendsto (fun n => f n ω r-q n r) atTop (𝓝 0) := by
  have hall : ∀ᵐ ω ∂μ, ∀ r m : ℕ, ∀ᶠ n in atTop,
      |f n ω r-q n r| ≤ (1 : ℝ)/(m+1) := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro m
    filter_upwards [ae_eventually_avoid μ _ (hs r m)] with ω h
    filter_upwards [h] with n hn
    exact le_of_not_gt hn
  filter_upwards [hall] with ω h r
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hepsilon
  obtain ⟨N,hN⟩ := eventually_atTop.mp (h r m)
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Real.dist_eq, sub_zero] using (hN n hn).trans_lt hm

/-- From the frequency tail bounds to almost-sure total variation convergence. -/
theorem ae_variation_convergence {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f : ℕ → Ω → ℕ → ℝ) (q : ℕ → ℕ → ℝ) (limit : ℕ → ℝ)
    (hsource : ∀ n ω, HasSum (f n ω) 1) (hsource0 : ∀ n ω r, 0≤f n ω r)
    (hlimit : HasSum limit 1) (hlimit0 : ∀ r, 0≤limit r)
    (hq : ∀ r, Tendsto (fun n => q n r) atTop (𝓝 (limit r)))
    (hs : ∀ r m : ℕ, Summable (fun n => μ.real
      {ω | (1 : ℝ)/(m+1) < |f n ω r-q n r|})) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => massTotalVariation (f n ω) limit) atTop (𝓝 0) := by
  filter_upwards [ae_frequency_convergence μ f q hs] with ω hω
  apply variation_tendsto_zero _ limit (fun n => hsource n ω) hlimit
    (fun n r => hsource0 n ω r) hlimit0
  intro r
  have h := (hω r).add (hq r)
  simpa using h

end
end PaperC.Prel8.EmpiricalTransfer
