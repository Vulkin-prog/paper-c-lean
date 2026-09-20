import PaperCPrel8.TiltedVoidDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The tilted identity integrated to the void endpoint, including a zero void -/
namespace PaperC.Prel8.TiltedVoidIntegral
open Finset Filter Topology MeasureTheory TiltedVoidDerivative
open ArratiaGoldsteinGordonInput IndependentThinning V282.SteinFiniteExpectation
noncomputable section
variable {Ω : Type*} [Fintype Ω]

def integrand (mu : FinitePMF Ω) (N : Ω → ℕ) (m : ℕ) (p t : ℝ) : ℝ :=
  tiltedMean mu N t/(1-t)-(m:ℝ)*p/(1-t*p)

theorem generating_continuous (mu : FinitePMF Ω) (N : Ω → ℕ) : Continuous (generating mu N) := by
  unfold generating finitePMFExpectation
  fun_prop

theorem generating_one (mu : FinitePMF Ω) (N : Ω → ℕ) :
    generating mu N 1=eventProbability mu (fun w ↦ N w=0) := by
  unfold generating finitePMFExpectation eventProbability
  apply sum_congr rfl
  intro w hw
  by_cases hn : N w=0 <;> simp [hn]

theorem normalized_zero (mu : FinitePMF Ω) (N : Ω → ℕ) (m : ℕ) (p : ℝ) :
    normalized mu N m p 0=1 := by
  simp [normalized,generating,expectation_const]

theorem integrand_continuousOn (mu : FinitePMF Ω) (N : Ω → ℕ) (m : ℕ)
    {p : ℝ} (hp : 0≤p) (hp1 : p<1) : ContinuousOn (integrand mu N m p) (Set.Iio 1) := by
  have hg := generating_continuous mu N
  have hw : Continuous (fun t : ℝ ↦ finitePMFExpectation mu (fun w ↦ (1-t)^N w*(N w:ℝ))) := by
    unfold finitePMFExpectation
    fun_prop
  intro t ht
  have ht' : t<1 := ht
  have hb : 1-t*p≠0 := by nlinarith
  have hden : 1-t≠0 := by linarith
  unfold integrand tiltedMean
  exact (((hw.continuousAt.div hg.continuousAt (generating_pos mu N ht').ne').div
    (continuous_const.sub continuous_id).continuousAt hden).sub
      (continuous_const.continuousAt.div
        (continuous_const.sub (continuous_id.mul continuous_const)).continuousAt hb)).continuousWithinAt

/-- No smallness estimate is asserted: this is the exact finite-interval identity. -/
theorem integral_identity (mu : FinitePMF Ω) (N : Ω → ℕ) (m : ℕ)
    {p s : ℝ} (hp : 0≤p) (hp1 : p<1) (hs : 0≤s) (hs1 : s<1) :
    (∫ t in (0:ℝ)..s, integrand mu N m p t) = -Real.log (normalized mu N m p s) := by
  have hsub : Set.uIcc (0:ℝ) s⊆Set.Iio 1 := by
    rw [Set.uIcc_of_le hs]
    intro t ht
    exact lt_of_le_of_lt ht.2 hs1
  have hi : IntervalIntegrable (integrand mu N m p) volume 0 s :=
    ((integrand_continuousOn mu N m hp hp1).mono hsub).intervalIntegrable
  have hd : ∀ t∈Set.uIcc (0:ℝ) s,
      HasDerivAt (fun t ↦ -Real.log (normalized mu N m p t)) (integrand mu N m p t) t := by
    intro t ht
    convert (log_normalized_derivative mu N m hp hp1 (hsub ht)).neg using 1
    unfold integrand
    ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simpa only [normalized_zero,Real.log_one,neg_zero,sub_zero] using hh

theorem endpoint_limit (mu : FinitePMF Ω) (N : Ω → ℕ) (m : ℕ) {p : ℝ} (hp1 : p<1) :
    Tendsto (normalized mu N m p) (𝓝[<] (1:ℝ))
      (𝓝 (eventProbability mu (fun w ↦ N w=0)/(1-p)^m)) := by
  have hh := (generating_continuous mu N).continuousAt.div
    ((continuous_const.sub (continuous_id.mul continuous_const)).pow m).continuousAt
    (pow_ne_zero m (show 1-(1:ℝ)*p≠0 by linarith))
  have ht := hh.tendsto.mono_left (nhdsWithin_le_nhds (s:=Set.Iio (1:ℝ)))
  convert ht using 1
  · funext t
    simp [normalized]
  · simp [generating_one]

/-- A positive endpoint void gives the ordinary finite logarithmic limit. -/
theorem integral_limit_positive (mu : FinitePMF Ω) (N : Ω → ℕ) (m : ℕ)
    {p : ℝ} (hp : 0≤p) (hp1 : p<1)
    (hv : 0<eventProbability mu (fun w ↦ N w=0)) :
    Tendsto (fun s ↦ ∫ t in (0:ℝ)..s, integrand mu N m p t) (𝓝[<] (1:ℝ))
      (𝓝 (-Real.log (eventProbability mu (fun w ↦ N w=0)/(1-p)^m))) := by
  have ht := ((endpoint_limit mu N m hp1).log (div_pos hv (pow_pos (by linarith) _)).ne').neg
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0:ℝ)<1))] with s hs hs0
  exact (integral_identity mu N m hp hp1 hs0.le hs).symm

/-- If the void is zero, the improper identity has value +infinity, not Real.log 0. -/
theorem integral_limit_zero (mu : FinitePMF Ω) (N : Ω → ℕ) (m : ℕ)
    {p : ℝ} (hp : 0≤p) (hp1 : p<1)
    (hv : eventProbability mu (fun w ↦ N w=0)=0) :
    Tendsto (fun s ↦ ∫ t in (0:ℝ)..s, integrand mu N m p t) (𝓝[<] (1:ℝ)) atTop := by
  have ht : Tendsto (normalized mu N m p) (𝓝[<] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [hv,zero_div] using endpoint_limit mu N m hp1
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_pos (generating_pos mu N ht) (pow_pos (by have ht' : t<1 := ht; nlinarith : 0<1-t*p) _)
  have hl := tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp ht)
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0:ℝ)<1))] with s hs hs0
  exact (integral_identity mu N m hp hp1 hs0.le hs).symm

end
end PaperC.Prel8.TiltedVoidIntegral
