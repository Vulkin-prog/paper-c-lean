import PaperCV282.ConstantWindowClusters
import PaperCV282.PointwiseStartBounds
import PaperCV282.InfiniteMassCoupling
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The actual source count and its two boundary-window errors

The two windows have starts N and 2*N-1. A window has L values and imposes
L-1 zero affine equations; the affine center is t+1, not t.
-/

namespace PaperC.V282.ConstantWindowBoundary

open MeasureTheory InfiniteRademacher InfiniteExactLengthProbabilityTransfer
open ConstantWindowClusters PointwiseStartBounds WindowValues ExactLengthDecomposition
open MixedLengthAffine SectionTwelveMoments InfiniteMassCoupling FiniteFieldTotalVariation
open scoped BigOperators

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instIsProbabilityMeasureInfiniteRademacher :
    IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The genuine constant-window event in the infinite multiplicative model. -/
def infiniteConstantWindowEvent (t L : ℕ) : Set InfiniteSample :=
  {omega | ConstantWindow (infiniteValueBit omega) t L}

/-- The actual number of all constant windows in the dyadic block. -/
def infiniteConstantWindowCount (N L : ℕ) (omega : InfiniteSample) : ℕ :=
  constantWindowCount (infiniteValueBit omega) N L

/-- The actual weighted count of all exact-run marks, with no truncation. -/
def infiniteExactClusterCount (N L : ℕ) (omega : InfiniteSample) : ℕ :=
  exactClusterCount (infiniteValueBit omega) N L

/-- Precisely the two windows which can cross the counting interval's boundary. -/
def boundaryWindowEvent (N L : ℕ) : Set InfiniteSample :=
  infiniteConstantWindowEvent N L ∪ infiniteConstantWindowEvent (2*N-1) L

theorem infiniteConstantWindowEvent_eq_affine {t L : ℕ} (hL : 1 ≤ L) :
    infiniteConstantWindowEvent t L = infiniteAffineStartEvent (t+1) (L-1) (fun _ => 0) := by
  ext omega
  simp only [infiniteConstantWindowEvent,infiniteAffineStartEvent,Set.mem_setOf_eq]
  constructor
  · intro h i
    have hi := i.isLt
    split_ifs with hz
    · simp only [Nat.add_sub_cancel]
      exact (Affine.add_eq_zero_iff_eq _ _).mpr (h 1 (by omega)).symm
    · apply (Affine.add_eq_zero_iff_eq _ _).mpr
      exact (h 1 (by omega)).trans (by simpa only [Nat.add_assoc] using (h (1+i.val) (by omega)).symm)
  · intro h j hj
    by_cases hjzero : j=0
    · simp [hjzero]
    have hl2 : 2 ≤ L := by omega
    have hfirst := h ⟨0,by omega⟩
    simp only [Nat.add_sub_cancel] at hfirst
    have hbase := (Affine.add_eq_zero_iff_eq _ _).mp hfirst
    by_cases hjone : j=1
    · simpa only [hjone] using hbase.symm
    have hi := h ⟨j-1,by omega⟩
    dsimp only at hi
    rw [if_neg (show j-1 ≠ 0 by omega)] at hi
    have hvalue := (Affine.add_eq_zero_iff_eq _ _).mp hi
    have hindex : t+1+(j-1)=t+j := by omega
    rw [hindex] at hvalue
    exact hvalue.symm.trans hbase.symm

theorem measurableSet_infiniteConstantWindowEvent (t L : ℕ) :
    MeasurableSet (infiniteConstantWindowEvent t L) := by
  by_cases hL : 1 ≤ L
  · rw [infiniteConstantWindowEvent_eq_affine hL]
    exact measurableSet_infiniteAffineStartEvent _ _ _
  · have hzero : L=0 := by omega
    simp [infiniteConstantWindowEvent,ConstantWindow,hzero]

theorem measurable_infiniteConstantWindowCount (N L : ℕ) :
    Measurable (infiniteConstantWindowCount N L) := by
  unfold infiniteConstantWindowCount constantWindowCount
  exact Finset.measurable_sum _ (fun t ht => measurable_const.ite
    (measurableSet_infiniteConstantWindowEvent t L) measurable_const)

theorem measurable_infiniteExactClusterCount (N L : ℕ) :
    Measurable (infiniteExactClusterCount N L) := by
  unfold infiniteExactClusterCount exactClusterCount
  apply Finset.measurable_sum
  intro x hx
  apply Measurable.tsum
  intro e
  exact measurable_const.ite (measurableSet_infiniteExactLengthEvent x (excessRowCount L e))
    measurable_const

theorem measurableSet_boundaryWindowEvent (N L : ℕ) :
    MeasurableSet (boundaryWindowEvent N L) :=
  (measurableSet_infiniteConstantWindowEvent N L).union
    (measurableSet_infiniteConstantWindowEvent (2*N-1) L)

/-- This is a pointwise rank estimate at the actual window, including its first vertex. -/
theorem constantWindow_probability_le_fullDefects {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L) :
    infiniteRademacherMeasure.real (infiniteConstantWindowEvent t L) ≤
      (2 : ℝ) ^ (defectIndices L (t+1) L).card / (2 : ℝ) ^ (L-1) := by
  rw [infiniteConstantWindowEvent_eq_affine hL]
  have h := corollary_two_five_upper_infinite (x := t+1) (L := L-1) (by omega) (fun _ => 0)
  have hlen : L-1+1=L := by omega
  rw [hlen] at h
  apply h.trans
  exact div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) (by positivity)

/-- No almost-sure run-termination assumption is needed outside the two endpoint events. -/
theorem infinite_counts_eq_off_boundary {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L)
    (omega : InfiniteSample) (h : omega ∉ boundaryWindowEvent N L) :
    infiniteConstantWindowCount N L omega = infiniteExactClusterCount N L omega := by
  apply constantWindowCount_eq_exactClusterCount hN hL
  · exact fun hleft => h (Or.inl hleft)
  · exact fun hright => h (Or.inr hright)

/-- The source coupling costs only the probability of the two endpoint windows. -/
theorem constantWindow_cluster_law_distance_le_boundary {N L : ℕ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) :
    massTotalVariation
      (observableLaw infiniteRademacherMeasure (infiniteConstantWindowCount N L))
      (observableLaw infiniteRademacherMeasure (infiniteExactClusterCount N L)) ≤
      infiniteRademacherMeasure.real (boundaryWindowEvent N L) := by
  exact massTotalVariation_observableLaw_le_event infiniteRademacherMeasure
    (measurable_infiniteConstantWindowCount N L) (measurable_infiniteExactClusterCount N L)
    (infinite_counts_eq_off_boundary hN hL)

/-- The two-endpoint error has an explicit, genuinely pointwise arithmetic bound. -/
theorem boundary_probability_le_fullDefects {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    infiniteRademacherMeasure.real (boundaryWindowEvent N L) ≤
      ((2 : ℝ) ^ (defectIndices L (N+1) L).card +
        (2 : ℝ) ^ (defectIndices L (2*N) L).card) / (2 : ℝ) ^ (L-1) := by
  apply (measureReal_union_le _ _).trans
  have hleft := constantWindow_probability_le_fullDefects hN hL
  have hright := constantWindow_probability_le_fullDefects (t := 2*N-1) (by omega) hL
  have hindex : 2*N-1+1=2*N := by omega
  rw [hindex] at hright
  simpa only [add_div] using add_le_add hleft hright

end
end PaperC.V282.ConstantWindowBoundary
