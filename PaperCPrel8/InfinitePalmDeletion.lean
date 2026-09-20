import PaperCPrel8.PalmDeletionIdentity
import PaperCV282.InfiniteMassCoupling
import PaperCV282.SharpConditioning

/-! # Ordinary Palm deletion on the genuine infinite probability space

The configuration space may be countable with unbounded marks. Every sum is
an actual measure of disjoint configuration fibres; no finite-source premise
or exponential amplification is needed.
-/
namespace PaperC.Prel8.InfinitePalmDeletion
open MeasureTheory ProbabilityTheory
open V282.InfiniteMassCoupling V282.SharpConditioning
noncomputable section
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] [Countable Z]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Countably many disjoint retained configurations sum to the original
outside-event probability, restricted to the regular retained configurations. -/
theorem sum_deleted_configurations (mu : Measure Ω) [IsFiniteMeasure mu]
    (f : Ω → Z) (hf : Measurable f) (regular : Z → Prop) (outside : Set Ω) :
    (∑' z, if regular z then mu.real ({w | f w=z} ∩ outside) else 0) =
      mu.real ({w | regular (f w)} ∩ outside) := by
  have h := restricted_observableLaw_eq_event (mu.restrict outside) hf {z | regular z}
  have he (z : Z) : observableLaw (mu.restrict outside) f z = mu.real ({w | f w=z} ∩ outside) := by
    unfold observableLaw
    exact measureReal_restrict_apply (hf (measurableSet_singleton z))
  simp_rw [he] at h
  rw [measureReal_restrict_apply (hf ((Set.to_countable {z | regular z}).measurableSet))] at h
  exact h

/-- The sum is bounded by the ordinary probability of an outside occurrence. -/
theorem sum_deleted_le (mu : Measure Ω) [IsFiniteMeasure mu]
    (f : Ω → Z) (hf : Measurable f) (regular : Z → Prop) (outside : Set Ω) :
    (∑' z, if regular z then mu.real ({w | f w=z} ∩ outside) else 0) ≤ mu.real outside := by
  rw [sum_deleted_configurations mu f hf]
  exact measureReal_mono Set.inter_subset_right

/-- Exact conditional-mass cancellation, valid directly for the infinite source. -/
theorem palm_deleted_mass (mu : Measure Ω) [IsFiniteMeasure mu]
    (f : Ω → Z) (hf : Measurable f) (outside presence : Set Ω)
    (houtside : MeasurableSet outside) (hpresence : MeasurableSet presence)
    (z : Z) (hp : 0<mu.real presence) (himp : {w | f w=z} ⊆ presence) :
    mu.real presence * ((cond mu presence).real {w | f w=z}-
      (cond mu presence).real ({w | f w=z} \ outside)) =
      mu.real ({w | f w=z} ∩ outside) := by
  rw [cond_real_apply mu presence hpresence,cond_real_apply mu presence hpresence]
  rw [Set.inter_eq_right.mpr himp,Set.inter_eq_right.mpr (Set.Subset.trans Set.sdiff_subset himp)]
  rw [← sub_div,mul_div_cancel₀ _ hp.ne']
  have hsplit := measureReal_inter_add_sdiff (μ := mu) (s := {w | f w=z}) houtside
  linarith

/-- After weighting exact Palm probabilities by target masses exp(-mu)*lambda,
the exponential factors cancel before summing. -/
theorem weighted_deleted_average (mu : Measure Ω) [IsFiniteMeasure mu]
    (f : Ω → Z) (hf : Measurable f) (regular : Z → Prop) (outside : Set Ω)
    (houtside : MeasurableSet outside) (presence : Z → Set Ω)
    (hpresence : ∀ z, MeasurableSet (presence z))
    (hp : ∀ z, regular z → 0<mu.real (presence z))
    (himp : ∀ z, {w | f w=z} ⊆ presence z)
    (rate : ℝ) (q : Z → ℝ)
    (hq : ∀ z, regular z → q z=Real.exp (-rate)*mu.real (presence z)) :
    (∑' z, if regular z then q z*Real.exp rate*
      ((cond mu (presence z)).real {w | f w=z}-
        (cond mu (presence z)).real ({w | f w=z} \ outside)) else 0) =
      mu.real ({w | regular (f w)} ∩ outside) := by
  rw [← sum_deleted_configurations mu f hf regular outside]
  apply tsum_congr
  intro z
  by_cases hz : regular z
  · simp only [hz,ite_true,hq z hz]
    have he : (Real.exp (-rate)*mu.real (presence z))*Real.exp rate=mu.real (presence z) := by
      rw [mul_right_comm,← Real.exp_add]
      simp
    rw [he]
    exact palm_deleted_mass mu f hf outside (presence z) houtside (hpresence z) z (hp z hz) (himp z)
  · simp [hz]

end
end PaperC.Prel8.InfinitePalmDeletion
