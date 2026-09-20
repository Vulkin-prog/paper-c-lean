import PaperCPrel8.ActualSignedPalm
import PaperCPrel8.RoughKernelCloudBound
import PaperCPrel8.MicroscopicConditionalSpatial

/-! # Ordinary deletion of base starts on good sites, without an exponential Palm penalty -/
namespace PaperC.Prel8.GoodStartDeletion
open Finset ActualSignedPalm PrimeForcing PivotGeometry HardConditionalForcing OddPrimePivot
open RoughKernelCloudBound ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
open V282.PrescribedValues MicroscopicConditionalSpatial MicroscopicInfiniteField
open MeasureTheory InfiniteRademacher InfiniteCylinderTransfer IndependentScalarTail
noncomputable section
local instance : MeasurableSpace F₂ := ⊤
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E : ℕ} {G D : Finset ℕ}

/-- A constant-word union suffices for deletion; its harmless factor two avoids any sign convention. -/
theorem start_mass_le (h : GoodGeometry C Y L E G) (j : ℕ) (hj : j∈G)
    (A : SmallSample C Y → Prop) :
    eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun w ↦ A (restrictSmall C Y w) ∧ StartEvent (valueBit w) (j+1) L)≤
    eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w))*(2/(2:ℝ)^L) := by
  have hC : j+1+L≤C+1 := by have := h.cylinder_le j hj; omega
  have hgood (a : Fin L) : Y<largestOddPrime (j+1+a.val) := by
    have hg := h.good j hj ⟨a.val+1,by have := a.isLt; omega⟩
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg
  let q := cylinderPivot (show 0<j+1 by omega) hC (fun a ↦ h.cutoff_pos.trans_lt (hgood a))
  have hq := cylinderPivot_basis (show 0<j+1 by omega) hC
    (fun a ↦ h.cutoff_pos.trans_lt (hgood a)) (fun a ↦ (show L≤Y by have := h.support_le; omega).trans (hgood a).le)
  have hb := probability_cover (FinitePMF.uniform (SampleSpace C))
    (fun w ↦ A (restrictSmall C Y w) ∧ StartEvent (valueBit w) (j+1) L)
    (fun s : F₂ ↦ fun w ↦ A (restrictSmall C Y w) ∧ valueSystem C (fun a : Fin L ↦ j+1+a.val) w=fun _ ↦ s)
    (fun w hw ↦ ⟨valueBit w (j+1),hw.1,(valueSystem_eq_iff _ _ _ _).mpr (fun a ↦ hw.2.2 a.val a.isLt)⟩)
  have he (s : F₂) := word_small_event_probability (fun a : Fin L ↦ j+1+a.val) q hq hgood (fun _ ↦ s) A
  simp_rw [he] at hb
  simpa [Fintype.card_fun,Fintype.card_fin,ZMod.card,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hb

theorem mask_mass_le (h : GoodGeometry C Y L E G) (hD : D⊆G) (A : SmallSample C Y → Prop) :
    eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun w ↦ A (restrictSmall C Y w) ∧ ∃ j∈D, StartEvent (valueBit w) (j+1) L)≤
    eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w))*
      (2*(D.card:ℝ)/(2:ℝ)^L) := by
  have hb := probability_cover (FinitePMF.uniform (SampleSpace C))
    (fun w ↦ A (restrictSmall C Y w) ∧ ∃ j∈D, StartEvent (valueBit w) (j+1) L)
    (fun j : D ↦ fun w ↦ A (restrictSmall C Y w) ∧ StartEvent (valueBit w) (j.val+1) L)
    (fun w hw ↦ by obtain ⟨j,hj,hs⟩ := hw.2; exact ⟨⟨j,hj⟩,hw.1,hs⟩)
  have hs := sum_le_sum (s:=univ) (fun (j:D) _ ↦ start_mass_le h j.val (hD j.property) A)
  apply hb.trans (hs.trans_eq ?_)
  simp only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul]
  ring

/-- The original infinite-source intersection has exactly the same bound. -/
theorem infinite_mask_mass_le (h : GoodGeometry C Y L E G) (hD : D⊆G) (A : SmallSample C Y → Prop) :
    infiniteRademacherMeasure.real (traceEvent C Y A∩hitEvent L (D.image (fun j ↦ j+1)))≤
      infiniteRademacherMeasure.real (traceEvent C Y A)*(2*(D.card:ℝ)/(2:ℝ)^L) := by
  have he : traceEvent C Y A∩hitEvent L (D.image (fun j ↦ j+1))=
      {w | A (restrictSmall C Y (restrictToFinite C w)) ∧
        ∃ j∈D, StartEvent (valueBit (restrictToFinite C w)) (j+1) L} := by
    ext w
    simp only [Set.mem_inter_iff,traceEvent,Set.mem_setOf_eq,hitEvent_iff]
    apply and_congr_right
    intro hA
    constructor
    · rintro ⟨x,hx,hs⟩
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
      have hc : j+1+L≤C := by have := h.cylinder_le j (hD hj); omega
      exact ⟨j,hj,(startAt_restrictToFinite_iff w hc).mpr hs⟩
    · rintro ⟨j,hj,hs⟩
      have hc : j+1+L≤C := by have := h.cylinder_le j (hD hj); omega
      exact ⟨j+1,mem_image.mpr ⟨j,hj,rfl⟩,(startAt_restrictToFinite_iff w hc).mp hs⟩
  rw [he,show infiniteRademacherMeasure.real _=(infiniteRademacherMeasure _).toReal from rfl,
    cylinder_probability C (fun w ↦ A (restrictSmall C Y w) ∧
      ∃ j∈D, StartEvent (valueBit w) (j+1) L),traceEvent_probability]
  exact mask_mass_le h hD A

end
end PaperC.Prel8.GoodStartDeletion
