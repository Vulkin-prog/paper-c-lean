import PaperCV282.SpatialMarkedTarget
import PaperCV282.GeometricConfigurationCounts
import PaperCV282.AllStartSoftPoisson

/-! # A genuine geometric tail bound for the complete spatial configuration -/
namespace PaperC.V282.SpatialMarkedTargetTail

open MeasureTheory ProbabilityTheory SpatialMarkedTypes SpatialMarkedTarget
open GeometricMarkedConfiguration GeometricConfigurationCounts AllStartSoftPoisson
open InfiniteMassCoupling FiniteFieldTotalVariation
open scoped BigOperators NNReal ENNReal

noncomputable section

def spatialTargetTail (N E : ℕ) : Set (SpatialMarkedConfig N) :=
  {config | ∃ j : SpatialMarkedIndex N, E < j.2.1 ∧ config j ≠ 0}

theorem flattenRows_preimage_tail (N E : ℕ) :
    flattenRows N ⁻¹' spatialTargetTail N E =
      ⋃ i : Fin N × F₂, {rows | rows i ∈ configurationTail E} := by
  ext rows
  constructor
  · rintro ⟨⟨x,e,s⟩,he,hne⟩
    exact Set.mem_iUnion.mpr ⟨(x,s),e,he,hne⟩
  · intro h
    obtain ⟨⟨x,s⟩,e,he,hne⟩ := Set.mem_iUnion.mp h
    exact ⟨(x,e,s),he,hne⟩

theorem sum_signedSiteRate (N L : ℕ) :
    (∑ _ : Fin N × F₂, (signedSiteRate L : ℝ)) = (fullRate N L : ℝ) := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,ZMod.card,
    nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  change (N : ℝ)*2*((1 : ℝ)/2^(L+1)) = (N : ℝ)/2^L
  rw [pow_succ]
  field_simp

/-- The total target tail includes every site and both signs, with its exact geometric scale. -/
theorem spatial_target_tail_probability_le (N L E : ℕ) :
    (spatialTargetMeasure N L).real (spatialTargetTail N E) ≤
      (fullRate N L : ℝ) / (2 : ℝ) ^ (E+1) := by
  have hmap := (hasLaw_flattenRows N L).measureReal_eq
    ((Set.to_countable (spatialTargetTail N E)).measurableSet)
  change (spatialRowsMeasure N L).real (flattenRows N ⁻¹' spatialTargetTail N E) =
    (spatialTargetMeasure N L).real (spatialTargetTail N E) at hmap
  rw [← hmap,flattenRows_preimage_tail]
  calc
    _ ≤ ∑ i : Fin N × F₂, (spatialRowsMeasure N L).real {rows | rows i ∈ configurationTail E} :=
      measureReal_iUnion_fintype_le _
    _ = ∑ _ : Fin N × F₂, (configurationMeasure (signedSiteRate L)).real (configurationTail E) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hasLaw_spatial_row N L i).measureReal_eq
        ((Set.to_countable (configurationTail E)).measurableSet)
    _ ≤ ∑ _ : Fin N × F₂, (signedSiteRate L : ℝ)/(2 : ℝ)^(E+1) :=
      Finset.sum_le_sum (fun i hi => configuration_tail_probability_le _ E)
    _ = _ := by rw [← Finset.sum_div,sum_signedSiteRate]

theorem spatial_truncation_eq_outside_tail (N E : ℕ) (config : SpatialMarkedConfig N)
    (h : config ∉ spatialTargetTail N E) : truncateConfiguration N E config = config := by
  apply (truncate_configuration_eq_self_iff N E config).mpr
  intro j hj
  by_contra hn
  exact h ⟨j,hj,hn⟩

/-- The two actual laws are coupled by erasing precisely the excesses above the cutoff. -/
theorem spatial_target_truncation_tv_le (N L E : ℕ) :
    massTotalVariation (observableLaw (spatialTargetMeasure N L) id)
      (observableLaw (spatialTargetMeasure N L) (truncateConfiguration N E)) ≤
        (fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  apply (massTotalVariation_observableLaw_le_event (spatialTargetMeasure N L)
    measurable_id (measurable_of_countable _) (fun config h =>
      (spatial_truncation_eq_outside_tail N E config h).symm)).trans
  exact spatial_target_tail_probability_le N L E

end
end PaperC.V282.SpatialMarkedTargetTail
