import PaperCV282.ConstantWindowRates
import PaperCV282.ExactMarkedSourceTail
import PaperCV282.ExactMarkedClusterTransfer
import PaperCV282.ExactMarkedCritical

/-!
# Corollary 5.7 for the actual count of all constant windows

The source has no left-maximality restriction. Its law approaches the
actual compound Poisson random sum with intensity N/2^L and positive
geometric marks. We first fix the mark cutoff, then let that cutoff grow;
no unproved passage from finite-dimensional laws is used for this scalar statistic.
-/
namespace PaperC.V282.ConstantWindowCompoundConvergence

open MeasureTheory InfiniteRademacher ConstantWindowBoundary ConstantWindowRates
open ExactMarkedSourceTail ExactMarkedClusterTransfer ExactMarkedCritical ExactMarkedFieldBounds
open MarkedDetruncation InfiniteMassCoupling FiniteFieldTotalVariation GeometricClusterTarget
open AllStartSoftPoisson CriticalRunWindow ProcessAGGInput PrimeEulerPNT
open Filter Topology

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instIsProbabilityMeasureInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Actual half-L1 distance, with the varying intensity kept in the true compound target. -/
def constantWindowCompoundDistance (N L : ℕ) : ℝ :=
  massTotalVariation (observableLaw infiniteRademacherMeasure (infiniteConstantWindowCount N L))
    (fun n => (geometricCompoundMeasure (fullRate N L)).real {n})

theorem constantWindowCompoundDistance_nonneg (N L : ℕ) :
    0 ≤ constantWindowCompoundDistance N L := massTotalVariation_nonneg _ _

/-- Boundary, source tail, finite marked field, and target tail are all actual law comparisons. -/
theorem constantWindowCompoundDistance_le {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) (E : ℕ) :
    constantWindowCompoundDistance N L ≤
      infiniteRademacherMeasure.real (boundaryWindowEvent N L)+infiniteMarkTailProbability N L E+
        exactSignedDistance N L E (dyadicBlock N)+(fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  have hcount := hasSum_observableLaw infiniteRademacherMeasure (measurable_infiniteConstantWindowCount N L)
  have hcluster := hasSum_observableLaw infiniteRademacherMeasure (measurable_infiniteExactClusterCount N L)
  have htrunc := hasSum_observableLaw infiniteRademacherMeasure (measurable_truncatedExactClusterCount N L E)
  have htarget : HasSum (fun n => (geometricCompoundMeasure (fullRate N L)).real {n}) 1 :=
    hasSum_observableLaw (geometricCompoundMeasure (fullRate N L)) measurable_id
  have hfirst := massTotalVariation_triangle hcount.summable hcluster.summable htarget.summable
    (observableLaw_nonneg _ _) (observableLaw_nonneg _ _) (fun n => measureReal_nonneg)
  have hsecond := massTotalVariation_triangle hcluster.summable htrunc.summable htarget.summable
    (observableLaw_nonneg _ _) (observableLaw_nonneg _ _) (fun n => measureReal_nonneg)
  have hmiddle := hsecond.trans (add_le_add (source_cluster_truncation_tv_le N L E)
    (truncated_source_to_compound_tv_le N L E))
  have hfinal := hfirst.trans (add_le_add (constantWindow_cluster_law_distance_le_boundary hN hL) hmiddle)
  simpa only [constantWindowCompoundDistance,exactSignedDistance,add_assoc] using hfinal

/-- A uniform vanishing tail permits taking the cutoff limit after the source limit. -/
theorem tendsto_zero_of_vanishing_approximants (f : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (r : ℕ → ℝ)
    (hf : ∀ N, 0 ≤ f N) (hg : ∀ E, Tendsto (g E) atTop (𝓝 0))
    (hr : Tendsto r atTop (𝓝 0))
    (hbound : ∀ E, ∀ᶠ N in atTop, f N≤g E N+r E) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun N => ha.trans_le (hf N))
  · intro b hb
    obtain ⟨E,hE⟩ := (hr.eventually (eventually_lt_nhds (by linarith : (0 : ℝ)<b/2))).exists
    filter_upwards [hbound E,(hg E).eventually (eventually_lt_nhds (by linarith : (0 : ℝ)<b/2))]
      with N hN hgN
    linarith

/-- For each fixed cutoff the two tails are uniformly bounded by their geometric mass. -/
theorem fixed_truncation_comparison_eventually (C : ℝ) (hC : 0 ≤ C)
    (L : ℕ → ℕ) (hwindow : ∀ᶠ N in atTop, InRunLengthWindow C N (L N)) (E : ℕ) :
    ∀ᶠ N in atTop, constantWindowCompoundDistance N (L N) ≤
      (infiniteRademacherMeasure.real (boundaryWindowEvent N (L N))+
        exactSignedDistance N (L N) E (dyadicBlock N))+
          3*balanceConstant C/(2 : ℝ)^(E+1) := by
  obtain ⟨Nb,hb⟩ := fixed_mark_band_eventually C hC E
  have hbeta : lowerConstant < 2*upperConstant := by
    have hu := lowerConstant_pos.trans lowerConstant_lt_upperConstant
    linarith [lowerConstant_lt_upperConstant]
  obtain ⟨Nt,ht⟩ := source_mark_tail_le_eventually lowerConstant (2*upperConstant) (1/4)
    lowerConstant_pos hbeta (by norm_num)
  filter_upwards [hwindow,eventually_ge_atTop (max 1 (max Nb Nt))] with N hw hN
  obtain ⟨hL,hlo,hhi,hrate⟩ := hb N (by omega) (L N) hw
  have hlonglow : lowerConstant*Real.log N ≤ (L N+E+2 : ℝ) := by
    have he : (0 : ℝ)≤E := by positivity
    linarith
  have htail := ht N (by omega) (L N) E hlonglow hhi
  have hone : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hpow : (N : ℝ)^(-(1/(2 : ℝ))+(1/4))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hone (by norm_num)
  have hk : 0≤balanceConstant C := balanceConstant_nonneg C
  have htail' : infiniteMarkTailProbability N (L N) E≤2*balanceConstant C/(2 : ℝ)^(E+1) := by
    apply htail.trans
    calc
      _ ≤ (balanceConstant C/(2 : ℝ)^(E+1))*2 := by gcongr;linarith
      _ = _ := by ring
  have htarget : (fullRate N (L N) : ℝ)/(2 : ℝ)^(E+1)≤balanceConstant C/(2 : ℝ)^(E+1) :=
    div_le_div_of_nonneg_right hrate (by positivity)
  have hbound := constantWindowCompoundDistance_le (N := N) (by omega) hL E
  calc
    _ ≤ infiniteRademacherMeasure.real (boundaryWindowEvent N (L N))+
        infiniteMarkTailProbability N (L N) E+exactSignedDistance N (L N) E (dyadicBlock N)+
        (fullRate N (L N) : ℝ)/(2 : ℝ)^(E+1) := hbound
    _ ≤ infiniteRademacherMeasure.real (boundaryWindowEvent N (L N))+
        2*balanceConstant C/(2 : ℝ)^(E+1)+exactSignedDistance N (L N) E (dyadicBlock N)+
        balanceConstant C/(2 : ℝ)^(E+1) := by gcongr
    _ = _ := by ring

/-- Corollary 5.7: all constant windows converge to the genuine geometric compound-Poisson target. -/
theorem corollary_five_seven (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (C : ℝ) (hC : 0 ≤ C) (L : ℕ → ℕ)
    (hwindow : ∀ᶠ N in atTop, InRunLengthWindow C N (L N)) :
    Tendsto (fun N => constantWindowCompoundDistance N (L N)) atTop (𝓝 0) := by
  have hL : ∀ᶠ N in atTop, 1 ≤ L N := by
    obtain ⟨Nb,hb⟩ := fixed_mark_band_eventually C hC 0
    filter_upwards [hwindow,eventually_ge_atTop Nb] with N hw hN
    exact (hb N hN (L N) hw).1
  have hboundary := boundary_probability_tendsto_zero C L hL hwindow
  have hr : Tendsto (fun E : ℕ => 3*balanceConstant C/(2 : ℝ)^(E+1)) atTop (𝓝 0) := by
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2)
      (by norm_num : (1/(2 : ℝ))<1)
    convert hg.const_mul (3*balanceConstant C/2) using 1
    · funext E
      rw [pow_succ]
      simp only [div_pow,one_pow]
      ring
    · simp
  apply tendsto_zero_of_vanishing_approximants _
    (fun E N => infiniteRademacherMeasure.real (boundaryWindowEvent N (L N))+
      exactSignedDistance N (L N) E (dyadicBlock N)) _
    (fun N => constantWindowCompoundDistance_nonneg _ _) _ hr
    (fixed_truncation_comparison_eventually C hC L hwindow)
  intro E
  simpa only [add_zero] using hboundary.add
    (exact_signed_fixed_truncation_tendsto_zero hAGG hPNT C hC L hwindow E)

end
end PaperC.V282.ConstantWindowCompoundConvergence
