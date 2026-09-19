import PaperCPrel8.PullSiteTarget
import PaperCPrel8.ArithmeticPalmNormalization
import PaperCPrel8.RegularTargetCompletion
import PaperCPrel8.MicroscopicValueProfile

/-! # Exact boundary/start and retained-mask transfer of regular target configurations -/
namespace PaperC.Prel8.RetainedRegularTarget
open Finset MeasureTheory ProbabilityTheory V282.BulkMarkedTypes V282.BulkMarkedTarget
open RegularTargetCloud MicroscopicValueProfile InfinitePlantMass ArithmeticPalmMass ArithmeticPalmNormalization
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {n C L E Y K : ℕ} {G : Finset ℕ}

def boundaryEmbedding (hG : G⊆Icc 1 n) : retainedStarts G ↪ Icc 1 n where
  toFun x := ⟨x.val-1,by
    obtain ⟨j,hj,hx⟩ := mem_image.mp x.property
    have hh := hG hj
    simp only [retainedStarts] at hx
    rw [← hx,Nat.add_sub_cancel]
    exact hh⟩
  inj' := by
    intro x y h
    have hx : 1≤x.val := by obtain ⟨j,hj,hx⟩ := mem_image.mp x.property; omega
    have hy : 1≤y.val := by obtain ⟨j,hj,hy⟩ := mem_image.mp y.property; omega
    apply Subtype.ext
    have he := congrArg Subtype.val h
    change x.val-1=y.val-1 at he
    omega

def shiftedLabel {k : ℕ} (labels : Fin k → SpatialMarkedIndex (Icc 1 n))
    (hgood : ∀ i, (labels i).1.val∈G) (i : Fin k) : SpatialMarkedIndex (retainedStarts G) :=
  (⟨(labels i).1.val+1,mem_image.mpr ⟨_,hgood i,rfl⟩⟩,(labels i).2)

theorem boundary_shiftedLabel {k : ℕ} (hG : G⊆Icc 1 n)
    (labels : Fin k → SpatialMarkedIndex (Icc 1 n)) (hgood : ∀ i, (labels i).1.val∈G) (i : Fin k) :
    PullSiteTarget.labelEmbedding (boundaryEmbedding hG) (shiftedLabel labels hgood i)=labels i := by
  apply Prod.ext
  · apply Subtype.ext
    change (labels i).1.val+1-1=(labels i).1.val
    omega
  · rfl

/-- All labels are preserved, with their full multiplicities, signs and unbounded excesses. -/
theorem pull_enumeration {k : ℕ} (hG : G⊆Icc 1 n)
    (labels : Fin k → SpatialMarkedIndex (Icc 1 n)) (hgood : ∀ i, (labels i).1.val∈G) :
    PullSiteTarget.pull (boundaryEmbedding hG) (enumeratedConfiguration (Icc 1 n) labels)=
      enumeratedConfiguration (retainedStarts G) (shiftedLabel labels hgood) := by
  ext a
  simp only [PullSiteTarget.pull_apply,enumeratedConfiguration,Finsupp.finsetSum_apply]
  apply sum_congr rfl
  intro i hi
  rw [← boundary_shiftedLabel hG labels hgood i]
  simp only [Finsupp.single_apply,(PullSiteTarget.labelEmbedding (boundaryEmbedding hG)).injective.eq_iff]

/-- The paper's same-grid regularity implies the actual arithmetic regularity after restriction. -/
theorem boundedRegular_of_regular (hG : G⊆Icc 1 n) (hC : n+(L+E+1)≤C)
    (c : SpatialMarkedConfig (Icc 1 n))
    (hc : RegularConfiguration (Icc 1 n) (L+E+1) Y K E G c) :
    boundedRegular (retainedStarts G) C L E Y K (PullSiteTarget.pull (boundaryEmbedding hG) c) := by
  obtain ⟨k,hk,labels,rfl,hgood,hreg,he⟩ := hc
  change boundedRegular _ _ _ _ _ _ (PullSiteTarget.pull _ (enumeratedConfiguration _ labels))
  rw [pull_enumeration hG labels hgood]
  constructor
  · refine ⟨k,shiftedLabel labels hgood,rfl,?_,?_,?_,?_⟩
    · intro i
      have h := (mem_Icc.mp (labels i).1.property).1
      change 2≤(labels i).1.val+1
      omega
    · exact he
    · intro i
      have h := (mem_Icc.mp (labels i).1.property).2
      change (labels i).1.val+1-1+(L+E+1)≤C
      omega
    · simpa only [shiftedLabel,Nat.add_sub_cancel] using hreg
  · rw [enumerated_size]
    exact hk

/-- The named retained target exception is bounded by the complete G.3 target exception. -/
theorem exceptional_probability_le (hG : G⊆Icc 1 n) (hC : n+(L+E+1)≤C) :
    (spatialTargetMeasure (retainedStarts G) L).real
      {z | ¬boundedRegular (retainedStarts G) C L E Y K z}≤
    (spatialTargetMeasure (Icc 1 n) L).real
      {z | ¬RegularConfiguration (Icc 1 n) (L+E+1) Y K E G z} := by
  have hlaw := PullSiteTarget.hasLaw_pull (boundaryEmbedding hG) L
  rw [← hlaw.measureReal_eq (Set.to_countable _).measurableSet]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro c hc hreg
  exact hc (boundedRegular_of_regular hG hC c hreg)

end
end PaperC.Prel8.RetainedRegularTarget
