import PaperCV282.BulkMarkedConvergence
import PaperCV282.MesoscopicStability

/-! # The real microscopic record belongs to the full bulk conditioning algebra -/
namespace PaperC.V282.BulkMicroscopicRecord

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open InfiniteStartProbabilityTransfer MicroscopicBorderEvents MesoscopicStability
open BulkMarkedRates BulkMarkedStable BulkMarkedConvergence BulkStartFieldComparison BulkMarkedGeometry
open BulkMarkedAggregation PoissonFieldMeasure SharpConditioning
open HardPoissonRates AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput
open SaddleParameters SaddleScales SaddleCutoffAdmissibility SaddleAsymptotics SaddleExpansion PrimeEulerSaddle

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- A cylinder representative of the genuine border and all starts through 2 L squared. -/
def finiteMicroscopicRecord (Y L : ℕ) (sigma : SampleSpace Y) (x : ℕ) : Bool :=
  if x=1 then if (∀ n : ℕ,1≤n→n≤L→valueBit sigma n=0) then true else false
  else if x∈Finset.Icc 2 (2*L^2) then if startAt sigma x L then true else false
  else false

theorem microscopicRecord_restrict_eq {Y L : ℕ} (hcut : 2*L^2+L≤Y) (omega : InfiniteSample) :
    finiteMicroscopicRecord Y L (restrictToFinite Y omega)=microscopicRecord L 0 omega := by
  funext x
  have hb : (∀n : ℕ,1≤n→n≤L→valueBit (restrictToFinite Y omega) n=0) ↔ omega∈borderEvent L := by
    constructor <;> intro h n hn hnL
    · rw [← valueBit_restrictToFinite_eq_infiniteValueBit omega (show n≤Y by omega)]
      exact h n hn hnL
    · rw [valueBit_restrictToFinite_eq_infiniteValueBit omega (show n≤Y by omega)]
      exact h n hn hnL
  by_cases hx : x=1
  · simp only [finiteMicroscopicRecord,microscopicRecord,hx,ite_true,hb]
  · by_cases hm : x∈Finset.Icc 2 (2*L^2)
    · have hc : x+L≤Y := by have := (Finset.mem_Icc.mp hm).2;omega
      have hs := startAt_restrictToFinite_iff omega hc
      simp only [finiteMicroscopicRecord,microscopicRecord,hx,ite_false,hm,ite_true,
        max_eq_left (Nat.zero_le _),hs,infiniteStartEvent,Set.mem_setOf_eq]
    · simp only [finiteMicroscopicRecord,microscopicRecord,hx,ite_false,hm,
        max_eq_left (Nat.zero_le _)]

/-- No measurability premise on the final microscopic record is assumed. -/
theorem measurable_microscopicRecord_fullFY {Y L : ℕ} (hcut : 2*L^2+L≤Y) :
    Measurable[MeasurableSpace.comap (restrictToFinite Y) inferInstance] (microscopicRecord L 0) := by
  have h := (measurable_of_countable (finiteMicroscopicRecord Y L)).comp (comap_measurable (restrictToFinite Y))
  have heq : finiteMicroscopicRecord Y L ∘ restrictToFinite Y = microscopicRecord L 0 :=
    funext (microscopicRecord_restrict_eq hcut)
  rw [← heq]
  exact h

/-- The rounded hard cutoff contains the complete microscopic cylinder, uniformly before L. -/
theorem microscopic_cylinder_le_hardCutoff_eventually (beta : ℝ) (hbeta : 0<beta) :
    ∃ Mzero : ℕ, ∀M≥Mzero, ∀ L : ℕ, (L+1 : ℝ)≤beta*Real.log M → 2*L^2+L≤hardCutoff M := by
  let K : ℝ := 3*beta^2
  have hK : 0<K := by dsimp [K];positivity
  have hcost : Tendsto (fun H => (|Real.log K|+2*Real.log H)/saddleCutoff 1 H) atTop (𝓝 0) := by
    simpa only [add_div,mul_div_assoc,mul_zero,add_zero] using
      ((tendsto_const_nhds (x := |Real.log K|)).div_atTop (tendsto_saddleCutoff_atTop (a := 1) (by norm_num))).add
        ((tendsto_log_div_saddleCutoff (a := 1) (by norm_num)).const_mul 2)
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ M : ℕ in atTop, ∀ L : ℕ, (L+1 : ℝ)≤beta*Real.log M → 2*L^2+L≤hardCutoff M := by
    filter_upwards [hlog.eventually (hcost.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))),
      hlog.eventually (eventually_ge_atTop (saddleThreshold 1)),
      hlog.eventually (eventually_gt_atTop (0 : ℝ))] with M hc hth hpos
    intro L hL
    have hw := saddleCutoff_pos (a := 1) (by norm_num) hth
    have hh := (div_le_iff₀ hw).mp hc.le
    have hexp : K*(Real.log M)^2 ≤Real.exp (saddleCutoff 1 (Real.log M)) := by
      have he := Real.exp_le_exp.mpr (show Real.log K+Real.log (Real.log M)+Real.log (Real.log M)≤
          saddleCutoff 1 (Real.log M) by linarith [le_abs_self (Real.log K)])
      simpa only [Real.exp_add,Real.exp_log hK,Real.exp_log hpos,pow_two,mul_assoc] using he
    apply (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
    push_cast
    have hl0 : (0 : ℝ)≤L := by positivity
    have hb0 : 0≤beta*Real.log M := by positivity
    have hs := sq_le_sq₀ (by positivity : 0≤(L : ℝ)+1) hb0 |>.mpr hL
    dsimp [K] at hexp
    nlinarith
  exact eventually_atTop.1 hevent

/-- The true joint law keeps the entire microscopic configuration; its target is the actual product. -/
def microscopicJointDistance (M L : ℕ) (delta : ℝ) : ℝ :=
  measureTotalVariation
    (infiniteRademacherMeasure.map (fun omega =>
      (microscopicRecord L 0 omega,startField (bulkStarts M L delta) L omega)))
    ((infiniteRademacherMeasure.map (microscopicRecord L 0)).prod
      (fieldMeasure (startFieldRates (bulkStarts M L delta) L)))

theorem microscopic_joint_le_start_conditional {M L : ℕ} (delta : ℝ)
    (hcut : 2*L^2+L≤hardCutoff M) :
    microscopicJointDistance M L delta≤bulkStartConditionalDistance M L delta :=
  recorded_start_joint_le_conditional M L delta (microscopicRecord L 0)
    (measurable_microscopicRecord_fullFY hcut)

theorem microscopicJointDistance_nonneg (M L : ℕ) (delta : ℝ) :
    0≤microscopicJointDistance M L delta := by
  letI instProbabilityJoint : IsProbabilityMeasure
      (infiniteRademacherMeasure.map (fun omega =>
        (microscopicRecord L 0 omega,startField (bulkStarts M L delta) L omega))) :=
    Measure.isProbabilityMeasure_map ((measurable_microscopicRecord L 0).prodMk
      (measurable_startField _ _)).aemeasurable
  letI instProbabilityRecord : IsProbabilityMeasure (infiniteRademacherMeasure.map (microscopicRecord L 0)) :=
    Measure.isProbabilityMeasure_map (measurable_microscopicRecord L 0).aemeasurable
  exact measureTotalVariation_nonneg _ _

/-- Equation (7.17), in the stronger relative form o(lambda), for the actual microscopic record. -/
theorem equation_seven_seventeen (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (L : ℕ→ℕ) (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta)
    (hupper : ∀ᶠ M in atTop,(L M : ℝ)≤beta*Real.log M)
    (hrare : Tendsto (fun M => (fullRate M (L M) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun M => microscopicJointDistance M (L M) delta/(fullRate M (L M) : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun M => div_nonneg (microscopicJointDistance_nonneg M (L M) delta) (by positivity)) ?_
    (equation_seven_sixteen hAGG hPNT L beta delta hbeta hdelta hupper hrare)
  obtain ⟨Mzero,hzero⟩ := microscopic_cylinder_le_hardCutoff_eventually (beta+1) (by linarith)
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hupper,hlog.eventually (eventually_ge_atTop (1 : ℝ)),eventually_ge_atTop Mzero] with M hu hl hM
  have hc := hzero M hM (L M) (by nlinarith)
  exact div_le_div_of_nonneg_right (microscopic_joint_le_start_conditional delta hc) (by positivity)

/-- The exact scale printed in (7.17), with the actual microscopic non-vacancy probability. -/
theorem equation_seven_seventeen_total_scale (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (L : ℕ→ℕ) (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta)
    (hupper : ∀ᶠ M in atTop,(L M : ℝ)≤beta*Real.log M)
    (hrare : Tendsto (fun M => (fullRate M (L M) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun M => microscopicJointDistance M (L M) delta/
      (MicroscopicNonvacancy.microscopicProbability (L M)+(fullRate M (L M) : ℝ))) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun M => div_nonneg (microscopicJointDistance_nonneg M (L M) delta)
    (add_nonneg (MicroscopicNonvacancy.microscopicProbability_pos _).le (by positivity))) ?_
    (equation_seven_seventeen hAGG hPNT L beta delta hbeta hdelta hupper hrare)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have hp : (0 : ℝ)<(fullRate M (L M) : ℝ) := by
    change 0<(M : ℝ)/2^(L M)
    positivity
  exact div_le_div_of_nonneg_left (microscopicJointDistance_nonneg M (L M) delta) hp
    (by linarith [(MicroscopicNonvacancy.microscopicProbability_pos (L M)).le])

end
end PaperC.V282.BulkMicroscopicRecord
