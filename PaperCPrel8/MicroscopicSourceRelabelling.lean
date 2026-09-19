import PaperCPrel8.MicroscopicRetainedTheorem
import PaperCV282.BulkMarkedComparison
import PaperCV282.MovingMarkedLevels

/-! # Exact relabelling to the existing countable spatial source and target

The map changes left boundaries j to starts j+1. It is bijective and retains
every excess and sign, so it does not incur a total-variation error.
-/
namespace PaperC.Prel8.MicroscopicSourceRelabelling
open PaperC.Prel8.MicroscopicValueProfile PaperC.Prel8.ActualSignedPalm
open PaperC.Prel8.MicroscopicInfiniteField
open PaperC.V282.BulkSupportGraph
open PaperC.V282.BulkMarkedInfinite PaperC.V282.BulkMarkedTransfer
open PaperC.V282.ExactMarkedModel PaperC.V282.FiniteFieldPoissonCoupling
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.MovingMarkedLevels
open PaperC.InfiniteRademacher
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Boundary-to-start translation on the actual finite site sets. -/
def startEquiv (G : Finset ℕ) : {j // j ∈ G} ≃ {x // x ∈ retainedStarts G} where
  toFun j := ⟨j.val+1,Finset.mem_image.mpr ⟨j.val,j.property,rfl⟩⟩
  invFun x := ⟨x.val-1,by
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp x.property
    have hx : x.val-1=j := by omega
    rw [hx]
    exact hj⟩
  left_inv j := by apply Subtype.ext; simp
  right_inv x := by
    apply Subtype.ext
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp x.property
    dsimp
    omega

def indexEquiv (G : Finset ℕ) (E : ℕ) :
    Index G E ≃ LabelledIndex (retainedStarts G) (Fin (E+1) × PaperC.F₂) :=
  Equiv.prodCongr (startEquiv G) (Equiv.refl _)

def vectorEquiv (G : Finset ℕ) (E : ℕ) :
    (Index G E → ℕ) ≃ (LabelledIndex (retainedStarts G) (Fin (E+1) × PaperC.F₂) → ℕ) :=
  Equiv.arrowCongr (indexEquiv G E) (Equiv.refl ℕ)

/-- The old spatial source coordinate is exactly the new boundary-indexed indicator. -/
theorem infinite_coordinate_eq (G : Finset ℕ) (L E : ℕ) (ω : InfiniteSample) (i : Index G E) :
    PaperC.V282.BulkMarkedInfinite.infiniteSignedField (retainedStarts G) L E (retainedStarts G)
      ω (indexEquiv G E i) = infiniteField L E G ω i := by
  have hi := (indexEquiv G E i).1.property
  simp only [PaperC.V282.BulkMarkedInfinite.infiniteSignedField,hi,true_and]
  rfl

/-- Equality of the entire finite marked vector after exact relabelling. -/
theorem infinite_vector_eq (G : Finset ℕ) (L E : ℕ) (ω : InfiniteSample) :
    PaperC.V282.BulkMarkedInfinite.infiniteSignedField (retainedStarts G) L E (retainedStarts G) ω =
      vectorEquiv G E (infiniteField L E G ω) := by
  funext j
  obtain ⟨i,rfl⟩ := (indexEquiv G E).surjective j
  simpa only [vectorEquiv,Equiv.arrowCongr_apply,Function.comp_apply,Equiv.symm_apply_apply,Equiv.refl_apply] using
    infinite_coordinate_eq G L E ω i

/-- The full-mask Poisson product is exactly the retained product after relabelling. -/
theorem poisson_vector_eq (G : Finset ℕ) (L E : ℕ) (z : Index G E → ℕ) :
    poissonFieldMass (allSignedRates (retainedStarts G) L E (retainedStarts G)) (vectorEquiv G E z) =
      poissonFieldMass (rate L) z := by
  unfold poissonFieldMass
  apply (Fintype.prod_equiv (indexEquiv G E) _ _ ?_).symm
  intro i
  have hi := (indexEquiv G E i).1.property
  simp only [allSignedRates,hi,ite_true,vectorEquiv,Equiv.arrowCongr_apply,Function.comp_apply,
    Equiv.symm_apply_apply,Equiv.refl_apply]
  rfl

end
end PaperC.Prel8.MicroscopicSourceRelabelling
