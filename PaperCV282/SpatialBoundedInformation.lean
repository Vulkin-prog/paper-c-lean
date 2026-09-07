import PaperCV282.SpatialMarkedHardBudget

/-! # Full spatial comparison at every bounded intensity under the critical information budget -/
namespace PaperC.V282.SpatialBoundedInformation

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open SpatialMarkedEventComparison LabelledInformationBudget GrowingMarkedTruncation
open AllStartSoftPoisson ExactMarkedRates HardPoissonRates SaddleParameters SaddleScales
open SaddleCutoffAdmissibility RareConditioningRates PrimeEulerPNT ProcessAGGInput

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- A fixed upper bound on intensity consumes only a vanishing fraction of the saddle margin. -/
theorem bounded_cost_eventually (K c : ℝ) (hc : 0<c) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ rate I : ℝ,
      0≤rate → rate≤K → I≤saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      labelledLogCost I (max 1 rate)≤
        saddleCutoff 1 (Real.log N)-(c/2)*saddleNu 1 (Real.log N) := by
  have hl : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hn := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp hl
  let cost := Real.log (max 1 K)+Real.log (1+max 1 K)
  have hh := ((tendsto_const_nhds (x := cost)).div_atTop hn).eventually
    (gt_mem_nhds (by linarith : (0 : ℝ)<c/2))
  apply eventually_atTop.1
  filter_upwards [hh,hn.eventually (eventually_gt_atTop (0 : ℝ))] with N hh hn
  intro rate I _hr hK hI
  have hcost := ((div_lt_iff₀ hn).mp hh).le
  have hmax : max 1 rate≤max 1 K := max_le_max_left _ hK
  have h1 := Real.log_le_log (by have := le_max_left (1 : ℝ) rate;linarith) hmax
  have h2 := Real.log_le_log (by have := le_max_left (1 : ℝ) rate;linarith)
    (add_le_add_left hmax 1)
  rw [add_comm (max 1 rate) 1,add_comm (max 1 K) 1] at h2
  unfold labelledLogCost
  dsimp [cost] at hcost
  linarith

/-- The full actual field, uniformly for bounded lambda; intensities below one are included. -/
theorem spatial_event_bound (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (lo hi K c : ℝ) (hlo : 0<lo) (hhi : lo<hi) (hc : 0<c) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      lo*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤hi*Real.log N →
      (fullRate N L : ℝ)≤K → ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      eventInformation A≤saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      spatialEventDistance N L A≤
        32*Real.exp (-(c/4)*saddleNu 1 (Real.log N))+
        32*(N : ℝ)^(-(1/(12 : ℝ)))+3*Real.exp (-saddleCutoff 1 (Real.log N)) := by
  obtain ⟨Ne,he⟩ := growing_mark_band_eventually hi (hlo.trans hhi)
  obtain ⟨Nf,hf⟩ := spatial_event_full_band hAGG hPNT lo (2*hi) (1/6) (c/4)
    hlo (by linarith) (by norm_num) (by linarith)
  obtain ⟨Nc,hcost⟩ := bounded_cost_eventually K c hc
  obtain ⟨Nb,hb⟩ := labelled_budget_bound_eventually (c/2) (by linarith)
  refine ⟨max Ne (max Nf (max Nc Nb)),?_⟩
  intro N hN L hL hL' hK A hA hp hI
  have hraw := hf N (by omega) L (growingMarkCutoff N) hL (he N (by omega) L hL') A hA hp
  have hR0 : 0≤(fullRate N L : ℝ) := (fullRate N L).coe_nonneg
  have hcost' := hcost N (by omega) (fullRate N L) (eventInformation A) hR0 hK hI
  have hbound := hb N (by omega) (eventInformation A) (max 1 (fullRate N L)) (le_max_left _ _) hcost'
  have hhalf : c/2/2=c/4 := by ring
  rw [hhalf] at hbound
  have heI : 1≤Real.exp (eventInformation A) := Real.one_le_exp_iff.mpr (eventInformation_nonneg A hp)
  have ht0 : 0≤(fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1) := by positivity
  have htailmul := mul_nonneg (sub_nonneg.mpr heI) ht0
  unfold exactMarkedRate at hraw
  rw [show -(1/(3 : ℝ))+1/6= -(1/(6 : ℝ)) by norm_num,
    show -(1/(2 : ℝ))+1/6= -(1/(3 : ℝ)) by norm_num,
    div_eq_mul_inv,← exp_eventInformation A hp] at hraw
  have hraw' : spatialEventDistance N L A≤
      Real.exp (eventInformation A)*(32*(fullRate N L : ℝ)*(1+(fullRate N L : ℝ))*
        (Real.exp (-saddleCutoff 1 (Real.log N)+(c/4)*saddleNu 1 (Real.log N))+
          (N : ℝ)^(-(1/(6 : ℝ))))+
        ((fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1))*(2+(N : ℝ)^(-(1/(3 : ℝ))))) := by
    nlinarith
  apply hraw'.trans
  apply le_trans _ hbound
  gcongr <;> exact le_max_right _ _

/-- Along any sequence in the common band the true conditional spatial distance tends to zero. -/
theorem spatial_event_tendsto_zero (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (lo hi K c : ℝ) (hlo : 0<lo) (hhi : lo<hi) (hc : 0<c)
    (A : ℕ → Set InfiniteSample)
    (hband : ∀ᶠ k in atTop,lo*Real.log (sizes k)≤(lengths k+1 : ℝ) ∧
      (lengths k+1 : ℝ)≤hi*Real.log (sizes k))
    (hK : ∀ᶠ k in atTop,(fullRate (sizes k) (lengths k) : ℝ)≤K)
    (hA : ∀ᶠ k in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance] (A k))
    (hpos : ∀ᶠ k in atTop,0 < infiniteRademacherMeasure.real (A k))
    (hbudget : ∀ᶠ k in atTop,eventInformation (A k)≤
      saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    Tendsto (fun k => spatialEventDistance (sizes k) (lengths k) (A k)) atTop (𝓝 0) := by
  obtain ⟨Nzero,hzero⟩ := spatial_event_bound hAGG hPNT lo hi K c hlo hhi hc
  have ht := (labelled_budget_error_tendsto_zero (c/2) (by linarith)).comp hsizes
  have hh : c/2/2=c/4 := by ring
  simp only [hh,Function.comp_def] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => spatialEventDistance_nonneg _ _ _) _ ht
  filter_upwards [hsizes.eventually (eventually_ge_atTop Nzero),hband,hK,hA,hpos,hbudget]
    with k hk hb hK hA hp hbu
  exact hzero (sizes k) hk (lengths k) hb.1 hb.2 hK (A k) hA hp hbu

end
end PaperC.V282.SpatialBoundedInformation
