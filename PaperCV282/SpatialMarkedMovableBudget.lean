import PaperCV282.SpatialMarkedEventComparison
import PaperCV282.MovableMarkedBudget
import PaperCV282.ExactMarkedMovableRates
import PaperCV282.GrowingLevelParameters
import PaperCV282.RareConditioningRates

/-!
# The movable labelled growing-field conclusion of Theorem 5.8(i)

The source is the genuine full spatial configuration, the conditioning is
an actual positive arithmetic event, and the depth is o(log N).
-/
namespace PaperC.V282.SpatialMarkedMovableBudget

open Filter Topology MeasureTheory InfiniteRademacher InfiniteCylinderTransfer
open SpatialMarkedEventComparison MovableMarkedBudget ExactMarkedMovableRates
open GrowingLevelParameters RareConditioningRates SoftRateAssembly SaddleParameters SaddleScales
open PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson ExactMarkedRates

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The freely chosen cutoff retains both intensity powers for the actual complete field. -/
theorem spatial_event_free_band (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (c C betaMin betaMax epsilon eta : ℝ) (hc : 0<c) (hC : 0<C)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ w : ℝ,
      c*Real.sqrt (Real.log N*Real.log (Real.log N))≤w →
      w≤C*Real.sqrt (Real.log N*Real.log (Real.log N)) → ∀ L E : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+E+2 : ℝ)≤betaMax*Real.log N →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite ⌊Real.exp w⌋₊) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      spatialEventDistance N L A ≤
        (freeMarkedRate N L w epsilon eta+
          ((fullRate N L : ℝ)/(2 : ℝ)^(E+1))*(1+(N : ℝ)^(-(1/(2 : ℝ))+epsilon)))/
            infiniteRademacherMeasure.real A+(fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  obtain ⟨Nf,hf⟩ := signed_free_field_rate_eventually hAGG hPNT c C betaMin betaMax epsilon eta
    hc hC hbetaMin hbeta hepsilon heta
  obtain ⟨Nt,ht⟩ := ExactMarkedSourceTail.source_mark_tail_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max Nf Nt,?_⟩
  intro N hN w hwlo hwhi L E hlo hhi A hA hpos
  have hlo' : betaMin*Real.log N≤(L+E+2 : ℝ) := by
    have he : (0 : ℝ)≤E := by positivity
    linarith
  have hfin := (hf N (by omega) w hwlo hwhi L E hlo hhi).2.1
  have htail := ht N (by omega) L E hlo' hhi
  have h := spatial_event_tv_le_finite_and_tails
    (C := max ⌊Real.exp w⌋₊ (dyadicCutoff N (L+E+1)))
    (Y := ⌊Real.exp w⌋₊) (le_max_left _ _) N L E A hA hpos
  apply h.trans
  refine add_le_add ?_ le_rfl
  apply div_le_div_of_nonneg_right _ hpos.le
  linarith

/-- The three terms of (5.20), before removing the exact source and target tails. -/
theorem spatial_event_movable_band (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L E : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+E+2 : ℝ)≤betaMax*Real.log N →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      spatialEventDistance N L A ≤
        (movableMarkedRate N L epsilon eta+
          ((fullRate N L : ℝ)/(2 : ℝ)^(E+1))*(1+(N : ℝ)^(-(1/(2 : ℝ))+epsilon)))/
            infiniteRademacherMeasure.real A+(fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  obtain ⟨Nf,hf⟩ := signed_movable_field_rate_eventually hAGG hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  obtain ⟨Nt,ht⟩ := ExactMarkedSourceTail.source_mark_tail_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max Nf Nt,?_⟩
  intro N hN L E hlo hhi A hA hpos
  have hlo' : betaMin*Real.log N≤(L+E+2 : ℝ) := by
    have he : (0 : ℝ)≤E := by positivity
    linarith
  have hfin := (hf N (by omega) L E hlo hhi).2.1
  have htail := ht N (by omega) L E hlo' hhi
  have h := spatial_event_tv_le_finite_and_tails
    (C := max (softCutoff N) (dyadicCutoff N (L+E+1)))
    (Y := softCutoff N) (le_max_left _ _) N L E A hA hpos
  simp only [softCutoff] at h
  apply h.trans
  refine add_le_add ?_ le_rfl
  apply div_le_div_of_nonneg_right _ hpos.le
  linarith

/-- The complete-field three-term bound (5.20), with all mark tails absorbed. -/
theorem spatial_event_movable_rate (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (hepsUpper : epsilon<1/3) (heta : 0<eta) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      spatialEventDistance N L A≤2*Real.exp (eventInformation A)*movableMarkedRate N L epsilon eta := by
  have hbmax := hbetaMin.trans hbeta
  obtain ⟨Ne,he⟩ := movable_mark_band_eventually betaMax hbmax
  obtain ⟨Nf,hf⟩ := spatial_event_movable_band hAGG hPNT betaMin (2*betaMax) epsilon eta
    hbetaMin (by linarith) hepsilon heta
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns,hs⟩ := eventually_atTop.1 (hlog.eventually (eventually_ge_atTop (saddleThreshold 2)))
  refine ⟨max Ne (max Nf (max Ns 2)),?_⟩
  intro N hN L hlo hhi A hA hpos
  have hraw := hf N (by omega) L (movableMarkCutoff N) hlo (he N (by omega) L hhi) A hA hpos
  have hv := saddleCutoff_pos (a := 2) (by norm_num) (hs N (by omega))
  have hn : 1≤(N : ℝ) := by exact_mod_cast (show 1≤N by omega)
  have hnu : 0≤saddleNu 2 (Real.log N) := by
    unfold saddleNu
    exact div_nonneg (Real.log_nonneg hn) hv.le
  have heI : 1≤Real.exp (eventInformation A) := Real.one_le_exp_iff.mpr (eventInformation_nonneg A hpos)
  have hpow : (N : ℝ)^(-(1/(2 : ℝ))+epsilon)≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
  have ht : (fullRate N L : ℝ)/(2 : ℝ)^(movableMarkCutoff N+1)≤
      (fullRate N L : ℝ)*Real.exp (-saddleCutoff 2 (Real.log N)/2+eta*saddleNu 2 (Real.log N)) := by
    have h := mul_le_mul_of_nonneg_left (movableMarkCutoff_geometric_tail N)
      (show 0≤(fullRate N L : ℝ) by positivity)
    simp only [mul_one_div] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg heta.le hnu]
  have ht0 : 0≤(fullRate N L : ℝ)/(2 : ℝ)^(movableMarkCutoff N+1) := by positivity
  have hf0 : 0≤(fullRate N L : ℝ)*Real.exp
      (-saddleCutoff 2 (Real.log N)/2+eta*saddleNu 2 (Real.log N)) := by positivity
  have hR : 32*((fullRate N L : ℝ)*Real.exp
      (-saddleCutoff 2 (Real.log N)/2+eta*saddleNu 2 (Real.log N)))≤movableMarkedRate N L epsilon eta := by
    unfold movableMarkedRate
    have h1 : 0≤(fullRate N L : ℝ)^2*Real.exp
      (-saddleCutoff 2 (Real.log N)+eta*saddleNu 2 (Real.log N)) := by positivity
    have h2 : 0≤(fullRate N L : ℝ)*(1+(fullRate N L : ℝ))*(N : ℝ)^(-(1/(3 : ℝ))+epsilon) := by positivity
    linarith
  rw [div_eq_mul_inv,← exp_eventInformation A hpos] at hraw
  have hp := mul_nonneg ht0 (sub_nonneg.mpr hpow)
  have hh := mul_nonneg (sub_nonneg.mpr heI) ht0
  have htI := mul_le_mul_of_nonneg_left ht (Real.exp_nonneg (eventInformation A))
  have hRI := mul_le_mul_of_nonneg_left hR (Real.exp_nonneg (eventInformation A))
  have hpI := mul_nonneg (Real.exp_nonneg (eventInformation A)) hp
  nlinarith

/-- A uniform complete-field estimate under the literal movable labelled information margin. -/
theorem movable_labelled_event_bound (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hc : 0 < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin*Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ betaMax*Real.log N →
      1 ≤ (fullRate N L : ℝ) → ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      movableLogCost (eventInformation A) (fullRate N L) ≤
        saddleCutoff 2 (Real.log N)/2-c*saddleNu 2 (Real.log N) →
      spatialEventDistance N L A ≤
        64*Real.exp (-(c/2)*saddleNu 2 (Real.log N))+
        64*(N : ℝ)^(-(1/(12 : ℝ)))+3*Real.exp (-saddleCutoff 2 (Real.log N)) := by
  have hbmax := hbetaMin.trans hbeta
  obtain ⟨Ne,he⟩ := movable_mark_band_eventually betaMax hbmax
  obtain ⟨Nf,hf⟩ := spatial_event_movable_band hAGG hPNT betaMin (2*betaMax) (1/6) (c/2)
    hbetaMin (by linarith) (by norm_num) (by positivity)
  obtain ⟨Nr,hr⟩ := movable_budget_bound_eventually c hc
  refine ⟨max Ne (max Nf Nr),?_⟩
  intro N hN L hlo hhi hrate A hA hpos hbudget
  have hraw := hf N (by omega) L (movableMarkCutoff N) hlo (he N (by omega) L hhi) A hA hpos
  have hb := hr N (by omega) (eventInformation A) (fullRate N L) (eventInformation_nonneg A hpos) hrate hbudget
  have heI : 1 ≤ Real.exp (eventInformation A) := Real.one_le_exp_iff.mpr (eventInformation_nonneg A hpos)
  have ht0 : 0 ≤ (fullRate N L : ℝ)/(2 : ℝ)^(movableMarkCutoff N+1) := by positivity
  have htailmul := mul_nonneg (sub_nonneg.mpr heI) ht0
  have hpow1 : -(1/(3 : ℝ))+1/6= -(1/(6 : ℝ)) := by norm_num
  have hpow2 : -(1/(2 : ℝ))+1/6= -(1/(3 : ℝ)) := by norm_num
  unfold movableMarkedRate at hraw
  rw [hpow1,hpow2,div_eq_mul_inv,← exp_eventInformation A hpos] at hraw
  apply le_trans _ hb
  nlinarith

/-- Equation (5.19) implies a full signed spatial comparison tending to zero at growing depth. -/
theorem theorem_five_eight_labelled_movable (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (c : ℝ) (hc : 0 < c)
    (d : ℕ → ℕ) (hd : Tendsto (fun N : ℕ => (d N : ℝ)/Real.log N) atTop (𝓝 0))
    (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ N in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance] (A N))
    (hpos : ∀ᶠ N in atTop, 0 < infiniteRademacherMeasure.real (A N))
    (hbudget : ∀ᶠ N in atTop,
      movableLogCost (eventInformation (A N)) (fullRate N (movingLength N (d N))) ≤
        saddleCutoff 2 (Real.log N)/2-c*saddleNu 2 (Real.log N)) :
    Tendsto (fun N => spatialEventDistance N (movingLength N (d N)) (A N)) atTop (𝓝 0) := by
  have hlog2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let lo : ℝ := (1/Real.log 2)/2
  let hi : ℝ := 2*(1/Real.log 2)
  have hlo : 0<lo := by dsimp [lo]; positivity
  have hlo' : lo<1/Real.log 2 := by
    dsimp [lo]
    have hh : 0<1/Real.log (2 : ℝ) := by positivity
    linarith
  have hhi : 1/Real.log 2<hi := by
    dsimp [hi]
    have hh : 0<1/Real.log (2 : ℝ) := by positivity
    linarith
  obtain ⟨Nb,hb⟩ := growing_length_band_eventually d hd lo hi hlo' hhi
  obtain ⟨Nd,hdep⟩ := growing_intensity_eventually d hd 1 (by norm_num)
  obtain ⟨Nr,hr⟩ := movable_labelled_event_bound hAGG hPNT lo hi c hlo (hlo'.trans hhi) hc
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => spatialEventDistance_nonneg _ _ _)) _
    (movable_budget_error_tendsto_zero c hc)
  filter_upwards [hA,hpos,hbudget,eventually_ge_atTop (max Nb (max Nd (max Nr 2)))] with N hA hpos hbudget hN
  have hdepth : d N ≤ criticalBase N := by have hh := (hdep N (by omega)).1;omega
  have hrate := (fullRate_depth_bounds (by omega : 1≤N) hdepth).1
  have hpow : (1 : ℝ) ≤ 2^(d N) := one_le_pow₀ (by norm_num)
  exact hr N (by omega) (movingLength N (d N)) (hb N (by omega)).1 (hb N (by omega)).2
    (hpow.trans hrate) (A N) hA hpos hbudget

end
end PaperC.V282.SpatialMarkedMovableBudget
