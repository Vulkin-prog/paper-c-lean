import PaperCV282.BulkMarkedTarget
import PaperCV282.FiniteStartMaskAverages
import PaperCV282.GeometricConfigurationCounts
import PaperCV282.AllStartSoftPoisson

/-! # A genuine geometric tail bound for the complete spatial configuration -/
namespace PaperC.V282.BulkMarkedTargetTail

open MeasureTheory ProbabilityTheory BulkMarkedTypes BulkMarkedTarget
open SpatialMarkedTarget (signedSiteRate)
open FiniteStartMaskAverages (maskRate)
open GeometricMarkedConfiguration GeometricConfigurationCounts AllStartSoftPoisson
open InfiniteMassCoupling FiniteFieldTotalVariation
open scoped BigOperators NNReal ENNReal

noncomputable section

def spatialTargetTail (sites : Finset ℕ) (E : ℕ) : Set (SpatialMarkedConfig sites) :=
  {config | ∃ j : SpatialMarkedIndex sites, E < j.2.1 ∧ config j ≠ 0}

theorem flattenRows_preimage_tail (sites : Finset ℕ) (E : ℕ) :
    flattenRows sites ⁻¹' spatialTargetTail sites E =
      ⋃ i : {x : ℕ // x∈sites} × F₂, {rows | rows i ∈ configurationTail E} := by
  ext rows
  constructor
  · rintro ⟨⟨x,e,s⟩,he,hne⟩
    exact Set.mem_iUnion.mpr ⟨(x,s),e,he,hne⟩
  · intro h
    obtain ⟨⟨x,s⟩,e,he,hne⟩ := Set.mem_iUnion.mp h
    exact ⟨(x,e,s),he,hne⟩

theorem sum_signedSiteRate (sites : Finset ℕ) (L : ℕ) :
    (∑ _ : {x : ℕ // x∈sites} × F₂, (signedSiteRate L : ℝ)) = (maskRate L sites : ℝ) := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_coe,ZMod.card,
    nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  change (sites.card : ℝ)*2*((1 : ℝ)/2^(L+1)) = (sites.card : ℝ)/2^L
  rw [pow_succ]
  field_simp

/-- The total target tail includes every site and both signs, with its exact geometric scale. -/
theorem spatial_target_tail_probability_le (sites : Finset ℕ) (L E : ℕ) :
    (spatialTargetMeasure sites L).real (spatialTargetTail sites E) ≤
      (maskRate L sites : ℝ) / (2 : ℝ) ^ (E+1) := by
  have hmap := (hasLaw_flattenRows sites L).measureReal_eq
    ((Set.to_countable (spatialTargetTail sites E)).measurableSet)
  change (spatialRowsMeasure sites L).real (flattenRows sites ⁻¹' spatialTargetTail sites E) =
    (spatialTargetMeasure sites L).real (spatialTargetTail sites E) at hmap
  rw [← hmap,flattenRows_preimage_tail]
  calc
    _ ≤ ∑ i : {x : ℕ // x∈sites} × F₂, (spatialRowsMeasure sites L).real {rows | rows i ∈ configurationTail E} :=
      measureReal_iUnion_fintype_le _
    _ = ∑ _ : {x : ℕ // x∈sites} × F₂, (configurationMeasure (signedSiteRate L)).real (configurationTail E) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hasLaw_spatial_row sites L i).measureReal_eq
        ((Set.to_countable (configurationTail E)).measurableSet)
    _ ≤ ∑ _ : {x : ℕ // x∈sites} × F₂, (signedSiteRate L : ℝ)/(2 : ℝ)^(E+1) :=
      Finset.sum_le_sum (fun i hi => configuration_tail_probability_le _ E)
    _ = _ := by rw [← Finset.sum_div,sum_signedSiteRate]

theorem spatial_truncation_eq_outside_tail (sites : Finset ℕ) (E : ℕ) (config : SpatialMarkedConfig sites)
    (h : config ∉ spatialTargetTail sites E) : truncateConfiguration sites E config = config := by
  apply (truncate_configuration_eq_self_iff sites E config).mpr
  intro j hj
  by_contra hn
  exact h ⟨j,hj,hn⟩

/-- The two actual laws are coupled by erasing precisely the excesses above the cutoff. -/
theorem spatial_target_truncation_tv_le (sites : Finset ℕ) (L E : ℕ) :
    massTotalVariation (observableLaw (spatialTargetMeasure sites L) id)
      (observableLaw (spatialTargetMeasure sites L) (truncateConfiguration sites E)) ≤
        (maskRate L sites : ℝ)/(2 : ℝ)^(E+1) := by
  apply (massTotalVariation_observableLaw_le_event (spatialTargetMeasure sites L)
    measurable_id (measurable_of_countable _) (fun config h =>
      (spatial_truncation_eq_outside_tail sites E config h).symm)).trans
  exact spatial_target_tail_probability_le sites L E

end
end PaperC.V282.BulkMarkedTargetTail
