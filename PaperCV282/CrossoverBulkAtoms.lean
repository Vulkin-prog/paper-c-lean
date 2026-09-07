import PaperCV282.CrossoverConfigurationAtoms
import PaperCV282.BulkMarkedAggregation

/-! # Empty and one-point atoms of the actual complete signed bulk target -/
namespace PaperC.V282.CrossoverBulkAtoms

open MeasureTheory ProbabilityTheory BulkMarkedTypes BulkMarkedTarget BulkMarkedAggregation
open GeometricMarkedConfiguration GeometricConfigurationCounts CrossoverConfigurationAtoms
open SpatialMarkedTarget (signedSiteRate)
open PoissonFieldMeasure
open scoped BigOperators NNReal ENNReal

noncomputable section
local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def totalRate (sites : Finset ℕ) (L : ℕ) : ℝ≥0 := sites.card/(2 : ℝ≥0)^L

def totalSize (sites : Finset ℕ) (c : SpatialMarkedConfig sites) : ℕ := c.sum (fun _ n => n)

theorem row_rate_sum (sites : Finset ℕ) (L : ℕ) :
    (∑ _ : sites × F₂, signedSiteRate L)=totalRate sites L := by
  apply NNReal.coe_injective
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_coe,ZMod.card,nsmul_eq_mul]
  change ((sites.card*2 : ℕ) : ℝ)*(1/(2 : ℝ)^(L+1))=(sites.card : ℝ)/(2 : ℝ)^L
  push_cast
  rw [pow_succ]
  field_simp

theorem totalSize_flattenRows (sites : Finset ℕ) (rows : sites × F₂ → (ℕ →₀ ℕ)) :
    totalSize sites (flattenRows sites rows)=∑ i : sites × F₂, configurationSize (rows i) :=
  sum_flattenRows sites rows _ (fun _ => rfl) (fun _ _ _ => rfl)

theorem hasLaw_totalSize (sites : Finset ℕ) (L : ℕ) :
    HasLaw (totalSize sites) (poissonMeasure (totalRate sites L)) (spatialTargetMeasure sites L) := by
  have h := (hasLaw_coordinate_sum (fun _ : sites × F₂ => signedSiteRate L) Finset.univ).fun_comp
    (hasLaw_rowCounts sites L)
  simp only [row_rate_sum] at h
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  rw [spatialTargetMeasure,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have he : (totalSize sites) ∘ (flattenRows sites)=
      fun rows : sites × F₂ → (ℕ →₀ ℕ) => ∑ i : sites × F₂, configurationSize (rows i) :=
    funext (totalSize_flattenRows sites)
  rw [he]
  exact h.map_eq

theorem flattenRows_injective (sites : Finset ℕ) : Function.Injective (flattenRows sites) := by
  intro f g h
  funext i
  ext e
  exact congrArg (fun c : SpatialMarkedConfig sites => c (i.1,e,i.2)) h

theorem flattenRows_zero (sites : Finset ℕ) : flattenRows sites (fun _ => 0)=0 := by
  ext j
  rfl

def onePointRows (sites : Finset ℕ) (j : SpatialMarkedIndex sites) : sites × F₂ → (ℕ →₀ ℕ) :=
  Function.update (fun _ => 0) (j.1,j.2.2) (Finsupp.single j.2.1 1)

theorem flattenRows_onePointRows (sites : Finset ℕ) (j : SpatialMarkedIndex sites) :
    flattenRows sites (onePointRows sites j)=Finsupp.single j 1 := by
  ext k
  simp only [flattenRows_apply,onePointRows,Function.update_apply]
  split_ifs with h
  · have hx : k.1=j.1 := congrArg (fun i : sites × F₂ => i.1) h
    have hs : k.2.2=j.2.2 := congrArg (fun i : sites × F₂ => i.2) h
    simp [Finsupp.single_apply,Prod.ext_iff,hx,hs]
  · have hn : k≠j := by intro hk;subst k;exact h rfl
    simp [hn]

theorem spatial_atom_eq_rows (sites : Finset ℕ) (L : ℕ) (rows : sites × F₂ → (ℕ →₀ ℕ)) :
    (spatialTargetMeasure sites L).real {flattenRows sites rows}=
      ∏ i : sites × F₂, (configurationMeasure (signedSiteRate L)).real {rows i} := by
  rw [spatialTargetMeasure,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : flattenRows sites ⁻¹' {flattenRows sites rows}={rows} := by
    ext f
    exact (flattenRows_injective sites).eq_iff
  rw [he,spatialRowsMeasure,Measure.pi_singleton,ENNReal.toReal_prod]
  rfl

theorem spatial_zero_mass (sites : Finset ℕ) (L : ℕ) :
    (spatialTargetMeasure sites L).real {0}=Real.exp (-(totalRate sites L : ℝ)) := by
  rw [← flattenRows_zero sites,spatial_atom_eq_rows]
  simp_rw [configuration_zero_mass]
  rw [Finset.prod_const,← Real.exp_nat_mul]
  congr 1
  have h := congrArg (fun r : ℝ≥0 => (r : ℝ)) (row_rate_sum sites L)
  simp only [Finset.sum_const,nsmul_eq_mul] at h
  push_cast at h
  simpa only [mul_neg] using congrArg Neg.neg h

theorem spatial_single_mass (sites : Finset ℕ) (L : ℕ) (j : SpatialMarkedIndex sites) :
    (spatialTargetMeasure sites L).real {Finsupp.single j 1}=
      Real.exp (-(totalRate sites L : ℝ))/(2 : ℝ)^(L+j.2.1+2) := by
  rw [← flattenRows_onePointRows sites j,spatial_atom_eq_rows]
  have hr : 0<signedSiteRate L := by unfold signedSiteRate;positivity
  have he (i : sites × F₂) :
      (configurationMeasure (signedSiteRate L)).real {onePointRows sites j i}=
      Real.exp (-(signedSiteRate L : ℝ)) *
        (if i=(j.1,j.2.2) then (signedSiteRate L : ℝ)/(2 : ℝ)^(j.2.1+1) else 1) := by
    by_cases hi : i=(j.1,j.2.2)
    · subst i
      simp only [onePointRows,Function.update_self,if_true,configuration_single_mass _ hr]
      ring
    · simp only [onePointRows,Function.update_of_ne hi,configuration_zero_mass,if_neg hi,mul_one]
  simp_rw [he]
  rw [Finset.prod_mul_distrib,Fintype.prod_ite_eq',Finset.prod_const,← Real.exp_nat_mul]
  have hh : (Fintype.card (sites × F₂) : ℝ)*(-(signedSiteRate L : ℝ))=-(totalRate sites L : ℝ) := by
    have h := congrArg (fun r : ℝ≥0 => (r : ℝ)) (row_rate_sum sites L)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
    push_cast at h
    linarith
  simp only [Finset.card_univ,hh]
  change Real.exp (-(totalRate sites L : ℝ))*((1/(2 : ℝ)^(L+1))/(2 : ℝ)^(j.2.1+1))=_
  rw [show L+j.2.1+2=(L+1)+(j.2.1+1) by omega,pow_add]
  ring

end
end PaperC.V282.CrossoverBulkAtoms
