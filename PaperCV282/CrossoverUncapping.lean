import PaperCV282.CrossoverSourceCoupling
import PaperCV282.CrossoverClockRecordMass
import PaperCV282.CrossoverSparseSource

/-! # Exact geometric removal of the prime-clock cap -/
namespace PaperC.V282.CrossoverUncapping

open MeasureTheory ProbabilityTheory Set Filter Topology InfiniteRademacher
open CrossoverMarkedModel CrossoverMarkedCandidate CrossoverMarkedTarget CrossoverPrimeClockLaw
open CrossoverSourceCoupling CrossoverClockRecordMass CrossoverBulkOnePoint
open RarePrefixGeometry MicroscopicBorderEvents PrimeClockDistribution SharpConditioning ConditionedCountableLaw
open CrossoverSparseSource
open scoped NNReal ENNReal

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem hit_probability_pos {M L : ℕ} (hLM : L≤M) :
    0 < infiniteRademacherMeasure.real (hitEvent M L) := by
  apply (borderEvent_probability_pos L).trans_le
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  rw [hitEvent_eq_union hLM]
  exact subset_union_left

def borderTail (K : ℕ) : Set Record := {r | ∃G : ℕ, K<G ∧ r=borderLabel G}

theorem capBorder_eq_off_tail (K : ℕ) (r : Record) (hr : r∉borderTail K) : capBorder K r=r := by
  cases r with
  | none => rfl
  | some r =>
    cases r with
    | inl G =>
      have hG : G≤K := by by_contra hn; exact hr ⟨G,by omega,rfl⟩
      simp only [capBorder,borderLabel,min_eq_left hG]
    | inr j => rfl

theorem gamma_cap_eq_off_prime_tail {M L K : ℕ} {delta : ℝ} (hLM : L≤M) (omega : InfiniteSample)
    (h : omega∉borderEvent L ∩ {omega | K+1≤primeOvershoot L omega}) :
    gamma M L delta omega=capBorder K (gamma M L delta omega) := by
  by_cases hx : firstStart M L omega=1
  · have hb := (firstStart_eq_one_iff hLM omega).mp hx
    have hg : primeOvershoot L omega≤K := by
      by_contra hn
      exact h ⟨hb,by change K+1≤primeOvershoot L omega; omega⟩
    rw [gamma_on_border hLM hb]
    simp only [capBorder,borderLabel,min_eq_left hg]
  · unfold gamma recordFromValues
    rw [if_neg hx]
    cases hp : pointAtSite (BulkMarkedGeometry.bulkStarts M L delta) (firstStart M L omega)
        (BulkMarkedSource.spatialMarkedSource _ L omega) <;> rfl

/-- The source tail is paid by its exact border mass before rare-event normalization. -/
theorem conditionalGamma_cap_tv_le {M L : ℕ} (delta : ℝ) (hLM : L≤M) (K : ℕ) :
    measureTotalVariation (conditionalGammaLaw M L delta)
      ((conditionalGammaLaw M L delta).map (capBorder K)) ≤ 1/(2 : ℝ)^(K+1) := by
  let H := hitEvent M L
  let E := borderEvent L ∩ {omega | K+1≤primeOvershoot L omega}
  have hp : 0 < infiniteRademacherMeasure.real H := hit_probability_pos hLM
  letI instProbabilityHit : IsProbabilityMeasure (cond infiniteRademacherMeasure H) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hp)
  have hb : infiniteRademacherMeasure.real (borderEvent L) ≤ infiniteRademacherMeasure.real H := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    rw [show H=hitEvent M L from rfl,hitEvent_eq_union hLM]
    exact subset_union_left
  have hc := map_tv_le_of_ae_eq_off (cond infiniteRademacherMeasure H) E
    (measurable_gamma M L delta) (measurable_capGamma M L K delta)
    (Eventually.of_forall (gamma_cap_eq_off_prime_tail hLM))
  change measureTotalVariation ((cond infiniteRademacherMeasure H).map (gamma M L delta)) _ ≤ _
  rw [conditionalGammaLaw,Measure.map_map (measurable_of_countable _) (measurable_gamma M L delta)]
  apply hc.trans
  rw [cond_real_apply _ H (measurableSet_hitEvent M L)]
  apply (div_le_div_of_nonneg_right (measureReal_mono inter_subset_right) hp.le).trans
  rw [show E=borderEvent L ∩ {omega | K+1≤primeOvershoot L omega} from rfl,border_prime_clock_tail]
  apply (div_le_iff₀ hp).mpr
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<2^(K+1))).mpr
  have he : (1/(2 : ℝ)^(K+1)*infiniteRademacherMeasure.real H)*(2 : ℝ)^(K+1)=
      infiniteRademacherMeasure.real H := by field_simp
  rw [he]
  exact hb

theorem border_tail_mass (K : ℕ) : borderLaw.real (borderTail K)=1/(2 : ℝ)^(K+1) := by
  rw [borderLaw,map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  have he : borderLabel ⁻¹' borderTail K={G : ℕ | K<G} := by
    ext G
    simp [borderTail,borderLabel]
  rw [he,geometric_strict_tail]

theorem borderLaw_cap_tv_le (K : ℕ) :
    measureTotalVariation borderLaw (borderLaw.map (capBorder K)) ≤ 1/(2 : ℝ)^(K+1) := by
  have hc := map_tv_le_of_ae_eq_off borderLaw (borderTail K) measurable_id
    (measurable_of_countable (capBorder K))
    (Eventually.of_forall fun r hr => (capBorder_eq_off_tail K r hr).symm)
  simpa only [Measure.map_id,border_tail_mass] using hc

theorem mixed_border_tail_mass (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) :
    (mixedLaw sites hs L).real (borderTail K)=(borderWeight sites L : ℝ)/(2 : ℝ)^(K+1) := by
  have hb := border_tail_mass K
  have hm : (bulkLaw sites hs).real (borderTail K)=0 := by
    rw [bulkLaw,map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    have he : bulkLabel sites ⁻¹' borderTail K=∅ := by
      ext j
      simp [borderTail,borderLabel,bulkLabel]
    rw [he,measureReal_empty]
  rw [mixedLaw_real,hb,hm,mul_zero,add_zero]
  ring

theorem mixedLaw_cap_tv_le (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) :
    measureTotalVariation (mixedLaw sites hs L) ((mixedLaw sites hs L).map (capBorder K)) ≤
      1/(2 : ℝ)^(K+1) := by
  have hc := map_tv_le_of_ae_eq_off (mixedLaw sites hs L) (borderTail K) measurable_id
    (measurable_of_countable (capBorder K))
    (Eventually.of_forall fun r hr => (capBorder_eq_off_tail K r hr).symm)
  rw [Measure.map_id,mixed_border_tail_mass] at hc
  apply hc.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := congrArg (fun a : ℝ≥0 => (a : ℝ)) (weights_sum sites L)
  push_cast at h
  linarith [show (0 : ℝ)≤(bulkWeight sites L : ℝ) by positivity]

end
end PaperC.V282.CrossoverUncapping
