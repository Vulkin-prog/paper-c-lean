import PaperCPrel8.InfinitePlantMass

/-! # Complete Poisson atom formula for the same enumerated regular plants -/
namespace PaperC.Prel8.EnumeratedTargetAtoms
open Finset MeasureTheory ProbabilityTheory
open V282.BulkMarkedTypes V282.BulkMarkedTarget V282.CrossoverBulkAtoms
open V282.CrossoverConfigurationAtoms V282.GeometricMarkedConfiguration V282.ExactMarkedModel
open V282.SpatialMarkedTarget (signedSiteRate)
open InfinitePlantMass
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {k : ℕ} {sites : Finset ℕ}

def rowKey (labels : Fin k → SpatialMarkedIndex sites) (i : Fin k) : sites × F₂ :=
  ((labels i).1,(labels i).2.2)

def rows (labels : Fin k → SpatialMarkedIndex sites) (r : sites × F₂) : ℕ →₀ ℕ :=
  ∑ i, if rowKey labels i=r then Finsupp.single (labels i).2.1 1 else 0

/-- The raw enumeration and its row decomposition are literally the same configuration. -/
theorem flatten_rows (labels : Fin k → SpatialMarkedIndex sites) :
    flattenRows sites (rows labels)=enumeratedConfiguration sites labels := by
  ext j
  simp only [flattenRows_apply,rows,enumeratedConfiguration,Finsupp.finsetSum_apply]
  apply sum_congr rfl
  intro i hi
  rcases h : labels i with ⟨x,e,s⟩
  rcases j with ⟨y,f,t⟩
  by_cases hr : rowKey labels i=(y,t)
  · have hh : x=y ∧ s=t := by simpa [rowKey,h] using hr
    rcases hh with ⟨rfl,rfl⟩
    simp [hr,Finsupp.single_apply,Prod.ext_iff]
  · have hh : ¬(x=y ∧ s=t) := by simpa [rowKey,h] using hr
    simp only [hr,ite_false,Finsupp.zero_apply,Finsupp.single_apply]
    symm
    apply ite_eq_right
    intro he
    have ht := Prod.mk.inj he
    exact hh ⟨ht.1,(Prod.mk.inj ht.2).2⟩

/-- Private sites give injective row labels. -/
theorem rowKey_injective (labels : Fin k → SpatialMarkedIndex sites)
    (hinj : Function.Injective (fun i ↦ (labels i).1)) : Function.Injective (rowKey labels) := by
  intro i j h
  exact hinj (congrArg (fun r : sites × F₂ ↦ r.1) h)

/-- At an occupied row there is exactly the displayed single excess. -/
theorem rows_at (labels : Fin k → SpatialMarkedIndex sites)
    (hinj : Function.Injective (rowKey labels)) (i : Fin k) :
    rows labels (rowKey labels i)=Finsupp.single (labels i).2.1 1 := by
  unfold rows
  rw [sum_eq_single i]
  · simp
  · intro j hj hji
    exact ite_eq_right (fun h ↦ hji (hinj h))
  · simp

/-- Every remaining row is exactly empty. -/
theorem rows_outside (labels : Fin k → SpatialMarkedIndex sites) (r : sites × F₂)
    (hr : r∉Finset.univ.image (rowKey labels)) : rows labels r=0 := by
  apply sum_eq_zero
  intro i hi
  exact ite_eq_right (fun h ↦ hr (mem_image.mpr ⟨i,mem_univ _,h⟩))

/-- Complete atom formula for any finite enumeration with distinct sites. The
same product of signed-mark intensities occurs in the arithmetic Palm mass. -/
theorem enumerated_target_mass (sites : Finset ℕ) (L : ℕ)
    (labels : Fin k → SpatialMarkedIndex sites)
    (hinj : Function.Injective (fun i ↦ (labels i).1)) :
    (spatialTargetMeasure sites L).real {enumeratedConfiguration sites labels} =
      Real.exp (-(totalRate sites L:ℝ))*∏ i, (signedMarkRate L (labels i).2.1:ℝ) := by
  let R := Finset.univ.image (rowKey labels)
  let factor : sites × F₂ → ℝ := fun r ↦
    (configurationMeasure (signedSiteRate L)).real {rows labels r}/Real.exp (-(signedSiteRate L:ℝ))
  have hfactor (i : Fin k) : factor (rowKey labels i)=(signedMarkRate L (labels i).2.1:ℝ) := by
    dsimp [factor]
    rw [rows_at labels (rowKey_injective labels hinj)]
    have hm := RegularConfigurationAtoms.row_mass L (some (labels i).2.1)
    change (configurationMeasure (signedSiteRate L)).real {Finsupp.single (labels i).2.1 1}=
      Real.exp (-(signedSiteRate L:ℝ))*(signedMarkRate L (labels i).2.1:ℝ) at hm
    rw [hm,mul_div_cancel_left₀ _ (Real.exp_ne_zero _)]
  have hout (r : sites × F₂) (hr : r∉R) : factor r=1 := by
    dsimp [factor]
    rw [rows_outside labels r hr,configuration_zero_mass,div_self (Real.exp_ne_zero _)]
  have hprod : (∏ r : sites × F₂, factor r)=∏ i, (signedMarkRate L (labels i).2.1:ℝ) := by
    rw [← prod_subset (subset_univ R) (fun r hr hnot ↦ hout r hnot)]
    dsimp [R]
    rw [prod_image (fun i _ j _ h ↦ rowKey_injective labels hinj h)]
    simp_rw [hfactor]
  rw [← flatten_rows labels,spatial_atom_eq_rows]
  have hrow (r : sites × F₂) : (configurationMeasure (signedSiteRate L)).real {rows labels r}=
      Real.exp (-(signedSiteRate L:ℝ))*factor r := by dsimp [factor]; field_simp
  simp_rw [hrow]
  rw [prod_mul_distrib,hprod]
  have hzero := spatial_zero_mass sites L
  rw [← flattenRows_zero sites,spatial_atom_eq_rows] at hzero
  simp_rw [configuration_zero_mass] at hzero
  rw [hzero]

end
end PaperC.Prel8.EnumeratedTargetAtoms
