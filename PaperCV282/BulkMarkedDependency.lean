import PaperCV282.BulkProcessCosts
import PaperCV282.ExactMarkedDependency
import PaperCV282.MacroscopicMaskGeometry

/-! # Actual signed marks on an arbitrary finite population -/
namespace PaperC.V282.BulkMarkedDependency

open ExactMarkedModel ExactMarkedDependency SignedExactMarks BulkSupportGraph BulkProcessCosts
open ConditionalStartProbability ConditionalDependencyGraph ConditionalAGGInstantiation
open ConditionalAGGAverage ArratiaGoldsteinGordonInput LargePrimeDependencyGraph
open SectionThirteenFiniteBound DictionaryFieldModel PrescribedValues WindowValues InfiniteWordTransfer
open MacroscopicMaskGeometry DefectivePredicate Affine

noncomputable section
local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Locality is tested on the complete maximal support, including both boundaries. -/
theorem conditionedSignedAt_locality {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L)
    (sigma : SmallSample C Y) (i : LabelledIndex sites (Fin (E+1) × F₂))
    (eta theta : LargeSample C Y)
    (heq : ∀ q : LargePrimeCoordinate C Y,
      largeCoordinatePrime q ∈ largePrimeCoordinates i.1.val (L+E+1) Y → eta q = theta q) :
    labelledFamily sites (conditionedSignedAt C L E Y sigma) i eta =
      labelledFamily sites (conditionedSignedAt C L E Y sigma) i theta := by
  unfold labelledFamily conditionedSignedAt signedAt
  apply Bool.decide_congr
  have hx : 1 ≤ i.1.val := by have h := hsite i.1.val i.1.property; omega
  rw [signedExactMark_iff_finiteWordEvent hx hL,signedExactMark_iff_finiteWordEvent hx hL]
  have hb (j : Fin (L+i.2.1.val+2)) :
      valueBit (assemble C Y sigma eta) (vertex i.1.val (L+i.2.1.val+2) j) =
      valueBit (assemble C Y sigma theta) (vertex i.1.val (L+i.2.1.val+2) j) := by
    have hlarge := valueBit_extendLarge_eq_of_eqOn_largePrimeCoordinates
      (marked_vertex_mem_max hx (by have h := i.2.1.isLt; omega) j) eta theta heq
    unfold assemble
    simp only [← valueLinear_apply,map_add]
    simpa only [valueLinear_apply] using congrArg (fun z =>
      valueBit (extendSmall C Y sigma) (vertex i.1.val (L+i.2.1.val+2) j) + z) hlarge
  simp only [finiteWordEvent,Set.mem_setOf_eq]
  simp_rw [hb]

theorem hasExactDependencyGraph_signed {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L)
    (mask : Finset ℕ) (sigma : SmallSample C Y) :
    HasExactDependencyGraph (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) mask)
      (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂)) := by
  apply hasExactDependencyGraph_of_labelled_locality
  apply maskedLabelIndicator_locality
  exact conditionedSignedAt_locality hsite hL sigma

/-- Goodness is a statement about every value in the actual maximal support. -/
theorem signedAt_marginal_good {C L E Y : ℕ} {sites mask : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L)
    (hC : ∀ x ∈ sites, x+L+E+1 ≤ C) (hY : L+E+2 ≤ Y)
    (sigma : SmallSample C Y) (i : LabelledIndex sites (Fin (E+1) × F₂))
    (hgood : i.1.val ∈ goodMask (L+E+1) Y mask) :
    marginal (largeUniformPMF C Y) (labelledFamily sites (conditionedSignedAt C L E Y sigma)) i =
      (signedMarkRate L i.2.1.val : ℝ) := by
  have hx : 2 ≤ i.1.val := hsite i.1.val i.1.property
  have hcut : i.1.val-1+(L+E+2) ≤ C+1 := by
    have hc := hC i.1.val i.1.property
    omega
  have hg (j : Fin (L+E+2)) : ¬HDefective Y (vertex i.1.val (L+E+2) j) := by
    exact not_defective_of_good hgood (marked_vertex_mem_max (by omega) (le_refl E) j)
  simp only [marginal,labelledFamily,conditionedSignedAt,signedAt,decide_eq_true_eq]
  exact conditioned_signedMark_probability hx hL (by have hi := i.2.1.isLt; omega) hcut hY hg _ sigma

/-- All actual good-site marginals equal their geometric signed rates. -/
theorem signedAt_marginal_masked_good {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L)
    (hC : ∀ x ∈ sites, x+L+E+1 ≤ C) (hY : L+E+2 ≤ Y)
    (mask : Finset ℕ) (sigma : SmallSample C Y)
    (i : LabelledIndex sites (Fin (E+1) × F₂)) :
    marginal (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask)) i =
      if i.1.val ∈ goodMask (L+E+1) Y mask then (signedMarkRate L i.2.1.val : ℝ) else 0 := by
  by_cases hi : i.1.val ∈ goodMask (L+E+1) Y mask
  · simp only [marginal,maskedLabelledFamily,maskedLabelIndicator,if_pos hi]
    exact signedAt_marginal_good hsite hL hC hY sigma i hi
  · simp [marginal,maskedLabelledFamily,maskedLabelIndicator,hi,eventProbability]

end
end PaperC.V282.BulkMarkedDependency
