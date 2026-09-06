import PaperCV282.SignedExactMarks
import PaperCV282.LabelledProcessCosts

/-!
# Actual signed exact marks on the maximal-support dependency graph

The cylinder cutoff is independent of both the base length and the maximal
excess. The graph keeps every sign and excess at every site.
-/
namespace PaperC.V282.ExactMarkedDependency

open ExactMarkedModel SignedExactMarks LabelledSupportGraph LabelledProcessCosts
open ConditionalStartProbability ConditionalDependencyGraph ConditionalAGGInstantiation
open ConditionalAGGAverage ArratiaGoldsteinGordonInput LargePrimeDependencyGraph
open SectionThirteenFiniteBound DictionaryFieldModel PrescribedValues WindowValues InfiniteWordTransfer
open MaskedArithmeticGeometry DefectivePredicate Affine

noncomputable section
local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The actual signed event as a site-and-label family. -/
def signedAt (C L E : ℕ) (x : ℕ) (a : Fin (E+1) × F₂) (omega : SampleSpace C) : Bool :=
  decide (SignedExactMark (valueBit omega) x L a.1.val a.2)

def conditionedSignedAt (C L E Y : ℕ) (sigma : SmallSample C Y)
    (x : ℕ) (a : Fin (E+1) × F₂) (eta : LargeSample C Y) : Bool :=
  signedAt C L E x a (assemble C Y sigma eta)

theorem labelledFamily_signedAt (C N L E : ℕ) :
    labelledFamily N (signedAt C L E) = signedMarkedIndicator C N L E := rfl

theorem labelledFamily_conditionedSignedAt (C N L E Y : ℕ) (sigma : SmallSample C Y) :
    labelledFamily N (conditionedSignedAt C L E Y sigma) =
      conditionedSignedMarkedIndicator C N L E Y sigma := rfl

/-- Every actual marked vertex belongs to the maximal whole support. -/
theorem marked_vertex_mem_max {x L E e : ℕ} (hx : 1 ≤ x) (he : e ≤ E)
    (j : Fin (L+e+2)) : vertex x (L+e+2) j ∈ startTreeSupport x (L+E+1) := by
  exact vertex_mem_startTreeSupport hx (⟨j.val,by have hj := j.isLt; omega⟩ : Fin (L+E+1+1))

/-- Equality on all large primes of the maximal support fixes the actual signed event. -/
theorem conditionedSignedAt_locality {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (sigma : SmallSample C Y) (i : LabelledIndex N (Fin (E+1) × F₂))
    (eta theta : LargeSample C Y)
    (heq : ∀ q : LargePrimeCoordinate C Y,
      largeCoordinatePrime q ∈ largePrimeCoordinates i.1.val (L+E+1) Y → eta q = theta q) :
    labelledFamily N (conditionedSignedAt C L E Y sigma) i eta =
      labelledFamily N (conditionedSignedAt C L E Y sigma) i theta := by
  unfold labelledFamily conditionedSignedAt signedAt
  apply Bool.decide_congr
  have hx : 1 ≤ i.1.val := by have h := two_le_of_mem_dyadicBlock hN i.1.property; omega
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

/-- Exact full-pattern dependency for the actual signed field, with any deterministic mask. -/
theorem hasExactDependencyGraph_signed {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (mask : Finset ℕ) (sigma : SmallSample C Y) :
    HasExactDependencyGraph (largeUniformPMF C Y)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) mask)
      (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂)) := by
  apply hasExactDependencyGraph_of_labelled_locality
  apply maskedLabelIndicator_locality
  exact conditionedSignedAt_locality hN hL sigma

/-- Mutual exclusion at one site is an event theorem, with no probabilistic premise. -/
theorem signedAt_disjoint {C L E : ℕ} (hL : 1 ≤ L) (x : ℕ)
    (a b : Fin (E+1) × F₂) (hne : a ≠ b) (omega : SampleSpace C) :
    ¬(signedAt C L E x a omega = true ∧ signedAt C L E x b omega = true) := by
  simp only [signedAt,decide_eq_true_eq]
  rintro ⟨ha,hb⟩
  obtain ⟨he,hs⟩ := signedExactMark_unique hL ha hb
  exact hne (Prod.ext (Fin.ext he) hs)

/-- Goodness is tested on the maximal support, including its left boundary. -/
theorem signedAt_marginal_good {C N L E Y : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : L+E+2 ≤ Y) (sigma : SmallSample C Y)
    (i : LabelledIndex N (Fin (E+1) × F₂)) (hgood : i.1.val ∉ fullBadStarts N (L+E+1) Y) :
    marginal (largeUniformPMF C Y) (labelledFamily N (conditionedSignedAt C L E Y sigma)) i =
      (signedMarkRate L i.2.1.val : ℝ) := by
  have hx : 2 ≤ i.1.val := two_le_of_mem_dyadicBlock hN i.1.property
  have hcut : i.1.val-1+(L+E+2) ≤ C+1 := by
    have hb := Finset.mem_Ico.mp i.1.property
    unfold dyadicCutoff at hC
    omega
  have hg (j : Fin (L+E+2)) : ¬HDefective Y (vertex i.1.val (L+E+2) j) := by
    intro hd
    exact hgood (mem_fullBadStarts.mpr ⟨i.1.property,_,marked_vertex_mem_max (by omega) (le_refl E) j,hd⟩)
  simp only [marginal,labelledFamily,conditionedSignedAt,signedAt,decide_eq_true_eq]
  exact conditioned_signedMark_probability hx hL (by have hi := i.2.1.isLt; omega) hcut hY hg _ sigma

/-- Masked good marginals retain their true excess-dependent geometric rates. -/
theorem signedAt_marginal_masked_good {C N L E Y : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (sigma : SmallSample C Y)
    (i : LabelledIndex N (Fin (E+1) × F₂)) :
    marginal (largeUniformPMF C Y)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask)) i =
      if i.1.val ∈ fullGoodMask N (L+E+1) Y mask then (signedMarkRate L i.2.1.val : ℝ) else 0 := by
  by_cases hi : i.1.val ∈ fullGoodMask N (L+E+1) Y mask
  · simp only [marginal,maskedLabelledFamily,maskedLabelIndicator,if_pos hi]
    exact signedAt_marginal_good hN hL hC hY sigma i (mem_fullGoodMask.mp hi).2
  · simp [marginal,maskedLabelledFamily,maskedLabelIndicator,hi,eventProbability]

end
end PaperC.V282.ExactMarkedDependency
