import PaperCPrel8.SaddleScaleMonotonicity
import PaperCPrel8.MarkovReadouts

/-! # Exact integer-site restriction and enlargement of the prime conditioning field -/
namespace PaperC.Prel8.DyadicRestriction
open MeasureTheory ProbabilityTheory PaperC.InfiniteRademacher PaperC.InfiniteCylinderTransfer
open PaperC.Prel8.MicroscopicSiteRestoration PaperC.Prel8.MicroscopicValueProfile
open PaperC.V282.BulkMarkedSource PaperC.V282.BulkMarkedTarget PaperC.V282.BulkMarkedComparison
open PaperC.V282.MacroTransportRestriction PaperC.V282.ConditionedCountableLaw
open PaperC.V282.CountableLawTransfer PaperC.V282.InfiniteMassCoupling
open PaperC.V282.FiniteFieldTotalVariation
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Full prime sigma-algebras increase with the literal integer cutoff. -/
theorem prime_sigma_mono {Y Z : ℕ} (hYZ : Y ≤ Z) :
    MeasurableSpace.comap (restrictToFinite Y) inferInstance ≤
      MeasurableSpace.comap (restrictToFinite Z) inferInstance := by
  let projection : PaperC.SampleSpace Z → PaperC.SampleSpace Y := fun σ p =>
    σ ⟨⟨p.1.val,lt_of_lt_of_le p.1.isLt (Nat.succ_le_succ hYZ)⟩,p.2⟩
  apply MeasurableSpace.comap_le_comap_of_eq_comp projection (measurable_of_finite _)
  rfl

/-- Every dyadic start is a genuine interior start of the larger prefix. -/
theorem dyadic_subset_prefix {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) :
    Finset.Ico N (2*N) ⊆ interiorStarts (4*N) L := by
  intro x hx
  have hx := Finset.mem_Ico.mp hx
  change x ∈ (Finset.Icc 1 (4*N-L)).image (fun j => j+1)
  exact Finset.mem_image.mpr ⟨x-1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩

/-- Both source and target restrict exactly, retaining integer positions, signs and full excesses. -/
theorem spatial_restriction_tv_le {s t : Finset ℕ} (hst : s ⊆ t) (L : ℕ)
    (A : Set InfiniteSample) (hpos : 0 < infiniteRademacherMeasure.real A) :
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (spatialMarkedSource s L))
      (spatialTargetLaw s L) ≤
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (spatialMarkedSource t L))
      (spatialTargetLaw t L) := by
  have h := conditional_statistic_tv_le infiniteRademacherMeasure A hpos (spatialTargetMeasure t L)
    (measurable_spatialMarkedSource t L) measurable_id (restrictSites hst)
  have hs : restrictSites hst ∘ spatialMarkedSource t L = spatialMarkedSource s L :=
    funext (restrict_spatialMarkedSource hst L)
  have ht : observableLaw (spatialTargetMeasure t L) (restrictSites hst ∘ id) = spatialTargetLaw s L :=
    observableLaw_of_hasLaw _ _ (hasLaw_restrictSites hst L)
  rwa [hs,ht] at h

end
end PaperC.Prel8.DyadicRestriction
