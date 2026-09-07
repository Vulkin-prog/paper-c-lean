import PaperCV282.CrossoverMovingTarget

/-! # The recorded bulk sign is the sign at the true least departure -/
namespace PaperC.V282.CrossoverSourceSigns

open MeasureTheory InfiniteRademacher InfiniteCylinderTransfer RarePrefixGeometry MicroscopicBorderEvents
open CrossoverMarkedModel CrossoverMarkedTarget CrossoverSparseSource BulkMarkedSource BulkMarkedGeometry

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

theorem gamma_bulk_sign {M L : ℕ} {delta : ℝ} {omega : InfiniteSample} {x e : ℕ} {s : F₂}
    (hg : gamma M L delta omega=some (Sum.inr (x,(e,s)))) : infiniteValueBit omega x=s := by
  unfold gamma recordFromValues at hg
  split_ifs at hg with hx
  · simp [borderLabel] at hg
  · cases hp : pointAtSite (bulkStarts M L delta) (firstStart M L omega)
        (spatialMarkedSource (bulkStarts M L delta) L omega) with
    | none => simp [hp] at hg
    | some j =>
      have hj := pointAtSite_some_property hp
      have hmark := (spatialMarkedValue_ne_zero_iff _ _ _ j).mp hj.2
      simp only [hp,Option.map_some,Option.some.injEq,Sum.inr.injEq,Prod.mk.injEq] at hg
      have hs := congrArg (fun z : ℕ × F₂ => z.2) hg.2
      simpa only [hg.1,hs] using hmark.2

theorem gamma_border_position {M L G : ℕ} {delta : ℝ} {omega : InfiniteSample}
    (hg : gamma M L delta omega=borderLabel G) : firstStart M L omega=1 := by
  unfold gamma recordFromValues at hg
  split_ifs at hg with hx
  · exact hx
  · cases hp : pointAtSite (bulkStarts M L delta) (firstStart M L omega)
        (spatialMarkedSource (bulkStarts M L delta) L omega) <;> simp [hp,borderLabel] at hg

def positiveSource (M L : ℕ) (omega : InfiniteSample) : Bool :=
  if infiniteValueBit omega (firstStart M L omega)=0 then true else false

theorem firstStart_le_cutoff (M L : ℕ) (omega : InfiniteSample) : firstStart M L omega≤M+1 := by
  by_cases hh : omega∈hitEvent M L
  · have hm := (mem_containedStarts M L _ omega).mp (firstStart_mem hh)
    omega
  · rw [(firstStart_eq_zero_iff M L omega).mpr hh]
    omega

theorem measurable_positiveSource (M L : ℕ) : Measurable (positiveSource M L) := by
  let f : SampleSpace (M+1) × ℕ → Bool := fun z => if valueBit z.1 z.2=0 then true else false
  have hr : Measurable (restrictToFinite (M+1)) :=
    measurable_pi_lambda _ fun p => measurable_pi_apply (finitePrimeCoordinate (M+1) p)
  have hm := (measurable_of_countable f).comp (hr.prodMk (measurable_firstStart M L))
  have he : f ∘ (fun omega : InfiniteSample => (restrictToFinite (M+1) omega,firstStart M L omega))=
      positiveSource M L := by
    funext omega
    simp only [f,Function.comp_apply,positiveSource,
      valueBit_restrictToFinite_eq_infiniteValueBit omega (firstStart_le_cutoff M L omega)]
  rw [← he]
  exact hm

theorem positiveSign_eq_source_off_cemetery {M L : ℕ} {delta : ℝ} {omega : InfiniteSample}
    (hg : gamma M L delta omega≠none) : positiveSign (gamma M L delta omega)=positiveSource M L omega := by
  cases he : gamma M L delta omega with
  | none => exact False.elim (hg he)
  | some r =>
    cases r with
    | inl G =>
      have hx := gamma_border_position he
      simp [positiveSign,positiveSource,hx,infiniteValueBit_one]
    | inr j =>
      rcases j with ⟨x,e,s⟩
      have hx := gamma_bulk_position he
      have hs := gamma_bulk_sign he
      simp [positiveSign,positiveSource,hx,hs]

end
end PaperC.V282.CrossoverSourceSigns
