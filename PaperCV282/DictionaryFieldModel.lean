import PaperCV282.InfiniteConditionalWords
import PaperCV282.AllStartConditionalDependency
import PaperCV282.ProcessAGGInput

/-!
# The complete site-and-word field

A word prescribes all L+1 values, including the left root x-1. Coordinates
retain both their site and their dictionary label. Empty dictionaries and
empty masks are allowed; no independence of arithmetic values is assumed.
-/

namespace PaperC.V282.DictionaryFieldModel

open Affine ConditionalStartProbability ConditionalDependencyGraph ConditionalAGGInstantiation
open ConditionalAGGAverage ArratiaGoldsteinGordonInput LargePrimeDependencyGraph
open SectionTwelveMoments SectionThirteenFiniteBound DefectivePredicate PrescribedValues WindowValues InfiniteWordTransfer
open MaskedArithmeticGeometry FiniteFieldPoissonCoupling ProcessAGGInput
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

@[reducible]
def DictionaryIndex (N L : ℕ) (W : Finset (Fin (L + 1) → F₂)) :=
  {x : ℕ // x ∈ dyadicBlock N} × {b : Fin (L + 1) → F₂ // b ∈ W}

def wordRate (L : ℕ) : ℝ≥0 := ⟨1 / (2 : ℝ) ^ (L + 1), by positivity⟩

def dictionaryRate (L : ℕ) (W : Finset (Fin (L + 1) → F₂)) : ℝ≥0 :=
  W.card * wordRate L

theorem wordRate_coe (L : ℕ) : (wordRate L : ℝ) = 1 / (2 : ℝ) ^ (L + 1) := rfl

theorem dictionaryRate_coe (L : ℕ) (W : Finset (Fin (L + 1) → F₂)) :
    (dictionaryRate L W : ℝ) = W.card / (2 : ℝ) ^ (L + 1) := by
  change (W.card : ℝ) * (1 / (2 : ℝ) ^ (L + 1)) = _
  ring

def finiteWordIndicator (M x B : ℕ) (b : Fin B → F₂) (omega : SampleSpace M) : Bool := by
  classical
  exact decide (omega ∈ finiteWordEvent M x B b)

@[simp]
theorem finiteWordIndicator_eq_true_iff (M x B : ℕ) (b : Fin B → F₂) (omega : SampleSpace M) :
    finiteWordIndicator M x B b omega = true ↔ omega ∈ finiteWordEvent M x B b := by
  classical
  simp [finiteWordIndicator]

def conditionedWordIndicator (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    DictionaryIndex N L W → LargeSample (dyadicCutoff N L) Y → Bool :=
  fun i eta => finiteWordIndicator (dyadicCutoff N L) i.1.val (L + 1) i.2.val
    (assemble (dyadicCutoff N L) Y sigma eta)

def maskedWordIndicator (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    DictionaryIndex N L W → LargeSample (dyadicCutoff N L) Y → Bool := by
  classical
  exact fun i eta => if i.1.val ∈ mask then conditionedWordIndicator N L Y W sigma i eta else false

@[simp]
theorem conditionedWordIndicator_eq_true_iff (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (sigma : SmallSample (dyadicCutoff N L) Y) (i : DictionaryIndex N L W)
    (eta : LargeSample (dyadicCutoff N L) Y) :
    conditionedWordIndicator N L Y W sigma i eta = true ↔
      assemble (dyadicCutoff N L) Y sigma eta ∈ finiteWordEvent (dyadicCutoff N L) i.1.val (L + 1) i.2.val :=
  finiteWordIndicator_eq_true_iff _ _ _ _ _

@[simp]
theorem maskedWordIndicator_eq_true_iff (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (mask : Finset ℕ) (sigma : SmallSample (dyadicCutoff N L) Y) (i : DictionaryIndex N L W)
    (eta : LargeSample (dyadicCutoff N L) Y) :
    maskedWordIndicator N L Y W mask sigma i eta = true ↔ i.1.val ∈ mask ∧
      assemble (dyadicCutoff N L) Y sigma eta ∈ finiteWordEvent (dyadicCutoff N L) i.1.val (L + 1) i.2.val := by
  classical
  simp [maskedWordIndicator]

/-- The word vertex set is exactly the complete support convention. -/
theorem vertex_mem_startTreeSupport {x L : ℕ} (hx : 1 ≤ x) (j : Fin (L + 1)) :
    vertex x (L + 1) j ∈ startTreeSupport x L := by
  rw [mem_startTreeSupport]
  by_cases hj : j.val = 0
  · left
    simp [vertex,hj]
  · right
    refine ⟨j.val - 1, by omega, ?_⟩
    unfold vertex
    omega

/-- Event probabilities in the large-coordinate cylinder equal their affine fibre probabilities. -/
theorem finiteUniformProbability_conditionedWord_eq (M Y x B : ℕ)
    (b : Fin B → F₂) (sigma : SmallSample M Y) :
    finiteUniformProbability (fun eta : LargeSample M Y =>
      assemble M Y sigma eta ∈ finiteWordEvent M x B b) =
      uniformSolutionProbability (largeValueSystem M Y (vertex x B))
        (conditionedValueRhs M Y (vertex x B) b sigma) := by
  classical
  unfold finiteUniformProbability uniformSolutionProbability
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have e : {eta : LargeSample M Y // assemble M Y sigma eta ∈ finiteWordEvent M x B b} ≃
      Solution (largeValueSystem M Y (vertex x B)) (conditionedValueRhs M Y (vertex x B) b sigma) :=
    Equiv.subtypeEquivRight fun eta => by
      change (∀ j, valueBit (assemble M Y sigma eta) (vertex x B j) = b j) ↔ _
      rw [← valueSystem_eq_iff]
      exact assemble_solves_values_iff M Y (vertex x B) b sigma eta
  rw [Fintype.card_congr e]
  congr 1
  norm_cast
  simp only [← Nat.card_eq_fintype_card]

/-- Exact word marginal at a genuine nondefective full support. -/
theorem marginal_conditionedWordIndicator_of_not_fullBad {N L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (hN : 2 ≤ N) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) (i : DictionaryIndex N L W)
    (hgood : i.1.val ∉ fullBadStarts N L Y) :
    marginal (largeUniformPMF (dyadicCutoff N L) Y)
      (conditionedWordIndicator N L Y W sigma) i = wordRate L := by
  classical
  have hx : 2 ≤ i.1.val := two_le_of_mem_dyadicBlock hN i.1.property
  have hcut : i.1.val - 1 + (L + 1) ≤ dyadicCutoff N L + 1 := by
    have hb := Finset.mem_Ico.mp i.1.property
    unfold dyadicCutoff
    omega
  have hvertices (j : Fin (L + 1)) : ¬HDefective Y (vertex i.1.val (L + 1) j) := by
    intro hd
    exact hgood (mem_fullBadStarts.mpr ⟨i.1.property,_,vertex_mem_startTreeSupport (by omega) j,hd⟩)
  rw [marginal,eventProbability_largeUniformPMF_eq]
  simp_rw [conditionedWordIndicator_eq_true_iff]
  rw [finiteUniformProbability_conditionedWord_eq,
    corollary_two_six_conditioned hx hcut hLY hvertices]
  rw [wordRate_coe]
  push_cast
  rfl

/-- Masking retains the true marginal and gives exact zero outside the mask. -/
theorem marginal_maskedWordIndicator (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (mask : Finset ℕ) (sigma : SmallSample (dyadicCutoff N L) Y) (i : DictionaryIndex N L W) :
    marginal (largeUniformPMF (dyadicCutoff N L) Y) (maskedWordIndicator N L Y W mask sigma) i =
      if i.1.val ∈ mask then marginal (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedWordIndicator N L Y W sigma) i else 0 := by
  classical
  by_cases hi : i.1.val ∈ mask
  · simp [marginal,maskedWordIndicator,hi]
  · simp [marginal,eventProbability,maskedWordIndicator,hi]

/-- Different dictionary labels at one site cannot both occur. -/
theorem finiteWordIndicator_same_site_disjoint {M x B : ℕ} {b c : Fin B → F₂}
    (hne : b ≠ c) (omega : SampleSpace M) :
    ¬(finiteWordIndicator M x B b omega = true ∧ finiteWordIndicator M x B c omega = true) := by
  simp only [finiteWordIndicator_eq_true_iff,finiteWordEvent,Set.mem_setOf_eq]
  rintro ⟨hb,hc⟩
  exact hne (funext fun j => (hb j).symm.trans (hc j))

/-- Average true marginals retain the actual unconditional word probabilities. -/
theorem average_marginal_conditionedWordIndicator (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (sigmaIndex : DictionaryIndex N L W) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      marginal (largeUniformPMF (dyadicCutoff N L) Y) (conditionedWordIndicator N L Y W sigma) sigmaIndex) =
      ((uniformEventProbability (fun omega : SampleSpace (dyadicCutoff N L) =>
        omega ∈ finiteWordEvent (dyadicCutoff N L) sigmaIndex.1.val (L + 1) sigmaIndex.2.val) : ℚ) : ℝ) := by
  classical
  simpa only [marginal,conditionedWordIndicator_eq_true_iff] using
    finiteUniformAverage_largeEventProbability_eq_full (dyadicCutoff N L) Y
      (fun omega => omega ∈ finiteWordEvent (dyadicCutoff N L) sigmaIndex.1.val (L + 1) sigmaIndex.2.val)

end
end PaperC.V282.DictionaryFieldModel
