import PaperCV282.MesoscopicCutoff
import PaperCV282.MicroscopicNonvacancy

/-! # Stability of the genuine conditioned microscopic configurations

All records use the common space Nat -> Bool, with the border at coordinate
one and zeros beyond their integer cutoff. The enlarged event is actual
non-vacancy, not a conditioning event of an auxiliary model.
-/
namespace PaperC.V282.MesoscopicStability

open MeasureTheory ProbabilityTheory Filter Set InfiniteRademacher
open InfiniteStartProbabilityTransfer MicroscopicBorderEvents MicroscopicNonvacancy
open SharpConditioning MesoscopicCutoff PostQuadraticLiterature
open scoped BigOperators Topology Classical

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def extraEvent (L T : ℕ) : Set InfiniteSample :=
  ⋃ x ∈ Finset.Ioc (2 * L ^ 2) T, infiniteStartEvent x L

def enlargedEvent (L T : ℕ) : Set InfiniteSample := microscopicEvent L ∪ extraEvent L T

def microscopicRecord (L T : ℕ) (omega : InfiniteSample) (x : ℕ) : Bool :=
  if x=1 then if omega∈borderEvent L then true else false
  else if x∈Finset.Icc 2 (max (2 * L ^ 2) T) then
    if omega∈infiniteStartEvent x L then true else false
  else false

theorem measurableSet_extraEvent (L T : ℕ) : MeasurableSet (extraEvent L T) := by
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ =>
    measurableSet_infiniteStartEvent x L

theorem measurableSet_enlargedEvent (L T : ℕ) : MeasurableSet (enlargedEvent L T) :=
  (measurableSet_microscopicEvent L).union (measurableSet_extraEvent L T)

theorem enlargedEvent_probability_pos (L T : ℕ) :
    0 < infiniteRademacherMeasure.real (enlargedEvent L T) :=
  (microscopicProbability_pos L).trans_le (measureReal_mono subset_union_left)

theorem measurable_microscopicRecord (L T : ℕ) : Measurable (microscopicRecord L T) := by
  apply measurable_pi_lambda
  intro x
  by_cases hx : x=1
  · simp only [microscopicRecord,hx,ite_true]
    exact Measurable.ite (measurableSet_borderEvent L) measurable_const measurable_const
  · by_cases hm : x∈Finset.Icc 2 (max (2 * L ^ 2) T)
    · simp only [microscopicRecord,hx,ite_false,hm,ite_true]
      exact Measurable.ite (measurableSet_infiniteStartEvent x L) measurable_const measurable_const
    · simp only [microscopicRecord,hx,ite_false,hm]
      exact measurable_const

/-- The two records coincide unless there is an actual added start. -/
theorem records_eq_off_extra (L T : ℕ) {omega : InfiniteSample}
    (h : omega∉extraEvent L T) : microscopicRecord L T omega=microscopicRecord L 0 omega := by
  funext x
  by_cases hx : x=1
  · simp only [microscopicRecord,hx,ite_true]
  · by_cases hb : x∈Finset.Icc 2 (2 * L ^ 2)
    · have hm : x∈Finset.Icc 2 (max (2 * L ^ 2) T) :=
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hb).1,(Finset.mem_Icc.mp hb).2.trans (le_max_left _ _)⟩
      simp only [microscopicRecord,hx,ite_false,max_eq_left (Nat.zero_le _),hb,hm,ite_true]
    · by_cases hm : x∈Finset.Icc 2 (max (2 * L ^ 2) T)
      · have hi : x∈Finset.Ioc (2 * L ^ 2) T := by
          have := Finset.mem_Icc.mp hm
          have hb' := hb
          simp only [Finset.mem_Icc] at hb'
          apply Finset.mem_Ioc.mpr
          omega
        have hn : omega∉infiniteStartEvent x L := by
          intro ho
          exact h (Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hi,ho⟩⟩)
        simp only [microscopicRecord,hx,ite_false,max_eq_left (Nat.zero_le _),hb,hm,ite_true,hn,ite_false]
      · simp only [microscopicRecord,hx,ite_false,max_eq_left (Nat.zero_le _),hb,hm,ite_false]

/-- Coupling on one arbitrary probability space; no countability assumption on the target. -/
theorem map_tv_le_of_eq_off {Omega Alpha : Type*} [MeasurableSpace Omega] [MeasurableSpace Alpha]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (E : Set Omega)
    {f g : Omega → Alpha} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ omega, omega∉E → f omega=g omega) :
    measureTotalVariation (mu.map f) (mu.map g) ≤ mu.real E := by
  letI instProbabilityMapF : IsProbabilityMeasure (mu.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI instProbabilityMapG : IsProbabilityMeasure (mu.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro A hA
  simp only [Measure.real,Measure.map_apply hf hA,Measure.map_apply hg hA]
  apply (abs_measureReal_sub_le_measureReal_symmDiff (hf hA).nullMeasurableSet
    (hg hA).nullMeasurableSet).trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro omega ho
  by_contra he
  have hh := h omega he
  simp [Set.mem_symmDiff,hh] at ho

/-- The two true source conditionings differ by at most the relative extra-start mass. -/
theorem conditional_source_tv_le (L T : ℕ) :
    measureTotalVariation (cond infiniteRademacherMeasure (enlargedEvent L T))
      (cond infiniteRademacherMeasure (microscopicEvent L)) ≤
      infiniteRademacherMeasure.real (extraEvent L T) / ((2 : ℝ)⁻¹)^Nat.primeCounting L := by
  have hn := nested_conditioning_le infiniteRademacherMeasure (microscopicEvent L) (enlargedEvent L T)
    (measurableSet_microscopicEvent L) (measurableSet_enlargedEvent L T) subset_union_left
    (microscopicProbability_pos L)
  have hp := enlargedEvent_probability_pos L T
  have ha : 0 < ((2 : ℝ)⁻¹)^Nat.primeCounting L := by positivity
  have hlo : ((2 : ℝ)⁻¹)^Nat.primeCounting L ≤ infiniteRademacherMeasure.real (enlargedEvent L T) :=
    (border_probability_le_microscopic_probability L).trans (measureReal_mono subset_union_left)
  apply hn.trans
  apply (div_le_div_of_nonneg_right (measureReal_mono (show
    enlargedEvent L T \ microscopicEvent L ⊆ extraEvent L T by
      intro omega ho;exact ho.1.resolve_left ho.2)) hp.le).trans
  exact div_le_div_of_nonneg_left (by positivity) ha hlo

/-- The actual two conditional configurations, on a common space and padded by zeros. -/
theorem conditional_record_tv_le (L T : ℕ) :
    measureTotalVariation
      ((cond infiniteRademacherMeasure (enlargedEvent L T)).map (microscopicRecord L T))
      ((cond infiniteRademacherMeasure (microscopicEvent L)).map (microscopicRecord L 0)) ≤
      2 * (infiniteRademacherMeasure.real (extraEvent L T) / ((2 : ℝ)⁻¹)^Nat.primeCounting L) := by
  let mu := cond infiniteRademacherMeasure (enlargedEvent L T)
  let nu := cond infiniteRademacherMeasure (microscopicEvent L)
  letI instProbabilityEnlarged : IsProbabilityMeasure mu := cond_isProbabilityMeasure
    (ConditionedCountableLaw.measure_ne_zero_of_real_pos _ (enlargedEvent_probability_pos L T))
  letI instProbabilityMicro : IsProbabilityMeasure nu := cond_isProbabilityMeasure
    (ConditionedCountableLaw.measure_ne_zero_of_real_pos _ (microscopicProbability_pos L))
  letI instProbabilityRecordT : IsProbabilityMeasure (mu.map (microscopicRecord L T)) :=
    Measure.isProbabilityMeasure_map (measurable_microscopicRecord L T).aemeasurable
  letI instProbabilityRecordZeroMu : IsProbabilityMeasure (mu.map (microscopicRecord L 0)) :=
    Measure.isProbabilityMeasure_map (measurable_microscopicRecord L 0).aemeasurable
  letI instProbabilityRecordZeroNu : IsProbabilityMeasure (nu.map (microscopicRecord L 0)) :=
    Measure.isProbabilityMeasure_map (measurable_microscopicRecord L 0).aemeasurable
  have hc := map_tv_le_of_eq_off mu (extraEvent L T) (measurable_microscopicRecord L T)
    (measurable_microscopicRecord L 0) (fun _ h => records_eq_off_extra L T h)
  have hmass : mu.real (extraEvent L T) ≤
      infiniteRademacherMeasure.real (extraEvent L T) / ((2 : ℝ)⁻¹)^Nat.primeCounting L := by
    rw [show mu=cond infiniteRademacherMeasure (enlargedEvent L T) from rfl,
      cond_real_apply _ _ (measurableSet_enlargedEvent L T),inter_eq_right.mpr (show extraEvent L T ⊆ enlargedEvent L T from subset_union_right)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      ((border_probability_le_microscopic_probability L).trans (measureReal_mono subset_union_left))
  have ht := (measureTotalVariation_map_le mu nu (measurable_microscopicRecord L 0)).trans
    (conditional_source_tv_le L T)
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro A hA
  have h1 := (discrepancy_le _ _ A hA).trans (hc.trans hmass)
  have h2 := (discrepancy_le _ _ A hA).trans ht
  exact (abs_sub_le _ ((mu.map (microscopicRecord L 0)).real A) _).trans (by linarith)

/-- The cutoff condition gives convergence of the genuine zero-padded configurations. -/
theorem cutoff_conditioned_stability (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) (cutoffs : ℕ → ℕ)
    (hcutoff : ∀ᶠ L : ℕ in atTop, cutoffs L ≤ 2 ^ L)
    (hsmall : Tendsto (fun L : ℕ => (cutoffs L : ℝ) /
      (2 : ℝ)^((L : ℝ)-(Nat.primeCounting L : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun L : ℕ => measureTotalVariation
      ((cond infiniteRademacherMeasure (enlargedEvent L (cutoffs L))).map (microscopicRecord L (cutoffs L)))
      ((cond infiniteRademacherMeasure (microscopicEvent L)).map (microscopicRecord L 0))) atTop (𝓝 0) := by
  have hh := cutoff_probability_negligible hShorey hPNT hNR cutoffs hcutoff hsmall
  apply squeeze_zero _ _ (show Tendsto (fun L : ℕ =>
    2 * (infiniteRademacherMeasure.real (extraEvent L (cutoffs L)) / ((2 : ℝ)⁻¹)^Nat.primeCounting L))
    atTop (𝓝 0) from by simpa only [extraEvent,mul_zero] using hh.const_mul 2)
  · intro L
    letI instProbabilityEnlarged : IsProbabilityMeasure (cond infiniteRademacherMeasure (enlargedEvent L (cutoffs L))) :=
      cond_isProbabilityMeasure (ConditionedCountableLaw.measure_ne_zero_of_real_pos _ (enlargedEvent_probability_pos L _))
    letI instProbabilityMicro : IsProbabilityMeasure (cond infiniteRademacherMeasure (microscopicEvent L)) :=
      cond_isProbabilityMeasure (ConditionedCountableLaw.measure_ne_zero_of_real_pos _ (microscopicProbability_pos L))
    letI instProbabilityRecordT : IsProbabilityMeasure
        ((cond infiniteRademacherMeasure (enlargedEvent L (cutoffs L))).map (microscopicRecord L (cutoffs L))) :=
      Measure.isProbabilityMeasure_map (measurable_microscopicRecord L _).aemeasurable
    letI instProbabilityRecordZero : IsProbabilityMeasure
        ((cond infiniteRademacherMeasure (microscopicEvent L)).map (microscopicRecord L 0)) :=
      Measure.isProbabilityMeasure_map (measurable_microscopicRecord L 0).aemeasurable
    exact measureTotalVariation_nonneg _ _
  · intro L
    exact conditional_record_tv_le L (cutoffs L)

/-- The literal cutoff hypothesis alone suffices: its upper ambient bound is derived. -/
theorem cutoff_conditioned_stability_of_littleO (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) (cutoffs : ℕ → ℕ)
    (hsmall : Tendsto (fun L : ℕ => (cutoffs L : ℝ) /
      (2 : ℝ)^((L : ℝ)-(Nat.primeCounting L : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun L : ℕ => measureTotalVariation
      ((cond infiniteRademacherMeasure (enlargedEvent L (cutoffs L))).map (microscopicRecord L (cutoffs L)))
      ((cond infiniteRademacherMeasure (microscopicEvent L)).map (microscopicRecord L 0))) atTop (𝓝 0) := by
  apply cutoff_conditioned_stability hShorey hPNT hNR cutoffs _ hsmall
  filter_upwards [hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with L hL
  have hpositive : 0 < (2 : ℝ)^((L : ℝ)-(Nat.primeCounting L : ℝ)) := by positivity
  have hbound := ((div_lt_one hpositive).mp hL).le
  have hpower : (2 : ℝ)^((L : ℝ)-(Nat.primeCounting L : ℝ)) ≤ (2 : ℝ)^L := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (sub_le_self _ (by positivity))
  have hreal := hbound.trans hpower
  exact_mod_cast hreal

end
end PaperC.V282.MesoscopicStability
