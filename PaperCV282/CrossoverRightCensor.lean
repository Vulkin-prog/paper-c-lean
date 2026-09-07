import PaperCV282.CrossoverMarkedTarget
import PaperCV282.CrossoverPrimeClockLaw
import Mathlib.Algebra.BigOperators.Intervals

/-! # The exact one-point target loses at most one over its population under right censoring -/
namespace PaperC.V282.CrossoverRightCensor

open MeasureTheory ProbabilityTheory BulkMarkedTypes CrossoverBulkOnePoint CrossoverMarkedModel
open CrossoverPrimeClockLaw GeometricClusterTarget SpatialDiffuseMarks SharpConditioning InfiniteMassCoupling
open scoped BigOperators

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- R is the last allowed base start M-L+1. Only the excess is censored. -/
def censorLabel (sites : Finset ℕ) (R : ℕ) (j : SpatialMarkedIndex sites) : SpatialMarkedIndex sites :=
  (j.1,(min j.2.1 (R-j.1.val),j.2.2))

theorem censorLabel_eq_iff (sites : Finset ℕ) (R : ℕ) (j : SpatialMarkedIndex sites) :
    censorLabel sites R j=j ↔ j.2.1 ≤ R-j.1.val := by
  simp [censorLabel,Prod.ext_iff]

theorem geometric_reflected_sum_le_one (R : ℕ) :
    (∑ x ∈ Finset.range (R+1),1/(2 : ℝ)^(R-x+1)) ≤ 1 := by
  have he := Finset.sum_range_reflect (fun k => 1/(2 : ℝ)^(k+1)) (R+1)
  simp only [Nat.add_sub_cancel] at he
  rw [he]
  have hp := geometric_partial_mass (R+1)
  simp only [geometric_excess_real] at hp
  rw [hp]
  linarith [show (0 : ℝ) ≤ 1/(2 : ℝ)^(R+1) by positivity]

theorem geometric_site_tail_sum_le_one (sites : Finset ℕ) (R : ℕ)
    (hsites : ∀ x ∈ sites, x ≤ R) :
    (∑ x ∈ sites,1/(2 : ℝ)^(R-x+1)) ≤ 1 := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (geometric_reflected_sum_le_one R)
  · intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hsites x hx))
  · intro x _ _
    positivity

theorem censor_disagreement_probability_le (sites : Finset ℕ) (hs : sites.Nonempty) (R : ℕ)
    (hsites : ∀ x ∈ sites, x ≤ R) :
    (labelMeasure sites hs).real {j | censorLabel sites R j≠j} ≤ 1/(sites.card : ℝ) := by
  have he : {j : SpatialMarkedIndex sites | censorLabel sites R j≠j}=
      ⋃ x : sites, ({x} ×ˢ ({e : ℕ | R-x.val < e} ×ˢ (Set.univ : Set F₂))) := by
    ext j
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_prod,
      Set.mem_singleton_iff,Set.mem_univ,and_true]
    change ¬(censorLabel sites R j=j) ↔ _
    rw [censorLabel_eq_iff,not_le]
    exact ⟨fun h => ⟨j.1,rfl,h⟩,fun ⟨x,hx,h⟩ => hx ▸ h⟩
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  have hm (x : sites) : (labelMeasure sites hs).real
      ({x} ×ˢ ({e : ℕ | R-x.val < e} ×ˢ (Set.univ : Set F₂)))=
      (1/(sites.card : ℝ))*(1/(2 : ℝ)^(R-x.val+1)) := by
    rw [labelMeasure,measureReal_prod_prod,measureReal_prod_prod,uniformSiteMeasure_real_singleton,
      geometric_strict_tail,probReal_univ,mul_one]
  simp_rw [hm]
  rw [← Finset.mul_sum]
  have heq : (∑ x : sites,1/(2 : ℝ)^(R-x.val+1))=∑ x ∈ sites,1/(2 : ℝ)^(R-x+1) := by
    exact Finset.sum_coe_sort sites (fun x : ℕ => 1/(2 : ℝ)^(R-x+1))
  rw [heq]
  exact (mul_le_mul_of_nonneg_left (geometric_site_tail_sum_le_one sites R hsites) (by positivity)).trans_eq (mul_one _)

/-- This bound concerns the complete position/sign/excess law, not merely its excess marginal. -/
theorem censor_target_tv_le (sites : Finset ℕ) (hs : sites.Nonempty) (R : ℕ)
    (hsites : ∀ x ∈ sites, x ≤ R) :
    measureTotalVariation ((labelMeasure sites hs).map (censorLabel sites R))
      (labelMeasure sites hs) ≤ 1/(sites.card : ℝ) := by
  letI instProbabilityCensored : IsProbabilityMeasure ((labelMeasure sites hs).map (censorLabel sites R)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro A hA
  rw [map_measureReal_apply (measurable_of_countable _) hA]
  have hh := event_discrepancy_le_disagreement (labelMeasure sites hs) (censorLabel sites R) id A
  exact hh.trans (censor_disagreement_probability_le sites hs R hsites)

theorem censor_keeps_site (sites : Finset ℕ) (R : ℕ) (j : SpatialMarkedIndex sites) :
    (censorLabel sites R j).1=j.1 := rfl

theorem censor_keeps_sign (sites : Finset ℕ) (R : ℕ) (j : SpatialMarkedIndex sites) :
    (censorLabel sites R j).2.2=j.2.2 := rfl

end
end PaperC.V282.CrossoverRightCensor
