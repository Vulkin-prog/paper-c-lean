import PaperCV282.IidWordField
import PaperCV282.DictionaryFieldInfinite

/-!
# The word field of the genuine iid sequence on all integer coordinates

The existing infinite product consists of independent fair coordinate bits.
Here the sequence is the coordinates omega n themselves, rather than the
multiplicative parity function built from those bits. Its finite prefix law
and the complete iid word field are identified exactly.
-/
namespace PaperC.V282.IidWordInfinite

open MeasureTheory Set InfiniteRademacher InfiniteFieldTransfer
open IidWordField WordOverlap WindowValues DictionaryFieldModel DictionaryFieldInfinite
open SectionTwelveMoments ArratiaGoldsteinGordonInput ConditionalDependencyGraph
open FiniteFieldTotalVariation ProcessAGGInput
open scoped BigOperators ENNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Restriction of the genuine iid sequence to its first C integer coordinates. -/
def iidPrefix (C : ℕ) (omega : InfiniteSample) : IidSample C := fun i => omega i.val

def iidPrefixMeasure (C : ℕ) : Measure (IidSample C) :=
  (PMF.uniformOfFintype (IidSample C)).toMeasure

theorem measurable_iidPrefix (C : ℕ) : Measurable (iidPrefix C) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.val

/-- Every prefix assignment has mass 2^(-C) in the actual independent-bit source. -/
theorem measure_iidPrefix_singleton (C : ℕ) (sigma : IidSample C) :
    infiniteRademacherMeasure (iidPrefix C ⁻¹' {sigma}) = ((2 : ℝ≥0∞)⁻¹)^C := by
  have hset : iidPrefix C ⁻¹' {sigma} =
      Set.pi (Finset.range C) (fun n => {iidSequence C sigma n}) := by
    ext omega
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_pi,Finset.mem_coe,Finset.mem_range]
    constructor
    · intro h n hn
      have hi := congrFun h (⟨n,hn⟩ : Fin C)
      simpa [iidPrefix,iidSequence,hn] using hi
    · intro h
      funext i
      simpa [iidPrefix,iidSequence,i.isLt] using h i.val i.isLt
  rw [hset,infiniteRademacherMeasure,Measure.infinitePi_pi]
  · simp
  · intro n hn
    exact MeasurableSet.singleton _

/-- The finite product distribution is the exact image of all iid integer bits. -/
theorem map_iidPrefix (C : ℕ) :
    Measure.map (iidPrefix C) infiniteRademacherMeasure = iidPrefixMeasure C := by
  apply Measure.ext_of_singleton
  intro sigma
  rw [Measure.map_apply (measurable_iidPrefix C) (MeasurableSet.singleton _),
    measure_iidPrefix_singleton,iidPrefixMeasure,PMF.toMeasure_uniformOfFintype_apply {sigma} (MeasurableSet.singleton _)]
  simp only [Fintype.card_unique,Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat]
  norm_num only [Nat.cast_one,one_div]
  exact (ENNReal.inv_pow).symm

/-- Finite iid event probabilities are actual real masses of the uniform prefix law. -/
theorem iidPrefixMeasure_event (C : ℕ) (P : IidSample C → Prop) :
    (iidPrefixMeasure C {omega | P omega}).toReal = eventProbability (iidUniformPMF C) P := by
  rw [iidPrefixMeasure,PMF.toMeasure_uniformOfFintype_apply {omega | P omega} (Set.toFinite _ |>.measurableSet),
    eventProbability_iidUniformPMF_eq]
  unfold finiteUniformProbability
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype]

/-- The full iid word field reads direct independent coordinates of the source sequence. -/
def infiniteIidField (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (omega : InfiniteSample) (i : DictionaryIndex N L W) : ℕ :=
  if Occurs omega i.1.val i.2.val then 1 else 0

def infiniteIidFieldLaw (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (k : DictionaryIndex N L W → ℕ) : ℝ :=
  (infiniteRademacherMeasure {omega | infiniteIidField N L W omega = k}).toReal

/-- An adequate prefix preserves all letters of the genuine infinite iid occurrence. -/
theorem occurs_iidPrefix_iff {C x B : ℕ} (hcut : x-1+B ≤ C)
    (b : Fin B → F₂) (omega : InfiniteSample) :
    Occurs (iidSequence C (iidPrefix C omega)) x b ↔ Occurs omega x b := by
  have hi (i : Fin B) : vertex x B i < C := by have h := i.isLt; unfold vertex; omega
  simp only [Occurs,iidSequence,dif_pos (hi _),iidPrefix]

/-- Exact field equality on the actual iid prefix. -/
theorem indicatorField_iidPrefix_eq (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (omega : InfiniteSample) :
    indicatorField (iidFieldIndicator N L W) (iidPrefix (dyadicCutoff N L + 1) omega) =
      infiniteIidField N L W omega := by
  funext i
  simp only [indicatorField,iidFieldIndicator,iidWordIndicator_eq_true,
    occurs_iidPrefix_iff (dictionary_vertex_cutoff N L i.1),infiniteIidField]

theorem infiniteIidField_event_eq_preimage (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (k : DictionaryIndex N L W → ℕ) :
    {omega | infiniteIidField N L W omega = k} =
      iidPrefix (dyadicCutoff N L + 1) ⁻¹'
        {sigma | indicatorField (iidFieldIndicator N L W) sigma = k} := by
  ext omega
  simp only [Set.mem_preimage,Set.mem_setOf_eq,indicatorField_iidPrefix_eq]

theorem measurableSet_infiniteIidField_event (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (k : DictionaryIndex N L W → ℕ) :
    MeasurableSet {omega | infiniteIidField N L W omega = k} := by
  rw [infiniteIidField_event_eq_preimage]
  exact (measurable_iidPrefix _) (Set.toFinite _ |>.measurableSet)

/-- The finite iid comparison law is exactly the full integer-sequence field law. -/
theorem infiniteIidFieldLaw_eq_iidFieldLaw (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    infiniteIidFieldLaw N L W = iidFieldLaw N L W := by
  funext k
  unfold infiniteIidFieldLaw
  rw [infiniteIidField_event_eq_preimage,
    ← Measure.map_apply (measurable_iidPrefix _) (Set.toFinite _ |>.measurableSet),
    map_iidPrefix,iidPrefixMeasure_event]
  exact (finiteFieldLaw_eq_eventProbability _ _ _).symm

theorem hasSum_infiniteIidFieldLaw (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    HasSum (infiniteIidFieldLaw N L W) 1 := by
  rw [infiniteIidFieldLaw_eq_iidFieldLaw]
  exact hasSum_iidFieldLaw N L W

end
end PaperC.V282.IidWordInfinite
