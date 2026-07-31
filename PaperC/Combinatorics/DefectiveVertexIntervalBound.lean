import PaperC.Analysis.CriticalPointwiseIntervals
import PaperC.Combinatorics.ResidualComponentCounts

set_option maxHeartbeats 1800000

/-!
# Interval bounds for the two-boundary defective vertices

The defective vertices of the concrete large-prime graph are the complete
boundary labels whose odd prime support lies below `B = L+1`.  This module
places the left and right boundary labels in the two concrete defect sets

`defectsInInterval (L+1) (x-1)` and
`defectsInInterval (L+1) (y-1)`.

Injectivity of the complete-boundary label in each block then bounds the
total defective-vertex count by the sum of those two interval counts.  The
same estimate holds for the canonical corrected count `D#`, since correction
only removes defective exact units.
-/

namespace PaperC
namespace DefectiveVertexIntervalBound

open Affine
open Affine.CanonicalRationalCode
open DefectCounting
open DefectivePredicate
open ExactUnitIsolation
open LargePrimeComponents
open LargePrimeGraph
open LargePrimeGraphResolution
open LargePrimeOccurrences
open ResidualComponentCounts

noncomputable section

/-! ## From the intrinsic defect predicate to the concrete interval set -/

/--
Every intrinsically `H`-defective value in `[U,U+H]` belongs to the finite
set used by the pointwise interval bound.  The separate zero branch makes
the statement valid even at the left endpoint `x-1=0`.
-/
theorem mem_defectsInInterval_of_hDefective
    {H U n : ℕ}
    (hdef : HDefective H n)
    (hlower : U ≤ n)
    (hupper : n ≤ U + H) :
    n ∈ IntervalDefectBound.defectsInInterval H U := by
  rw [IntervalDefectBound.mem_defectsInInterval]
  refine ⟨?_, hlower, hupper⟩
  by_cases hn : n = 0
  · subst n
    let rep : HDefectRepresentation H 0 :=
      { support := ∅
        support_subset := by simp
        squarePart := 0
        value_eq := by simp }
    exact
      mem_defectValues_of_HDefectRepresentation
        rep hupper
  · let rep : HDefectRepresentation H n :=
      Classical.choice
        ((hDefective_iff_exists_HDefectRepresentation hn).mp hdef)
    exact
      mem_defectValues_of_HDefectRepresentation
        rep hupper

/-! ## The canonical injection of defective occurrences -/

/--
A defective occurrence is sent to its integer label in the corresponding
left or right defect interval.
-/
noncomputable def defectiveVertexToIntervals
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    {v : Occurrence L // v ∈ defectiveVertices x y L} →
      Sum
        {n : ℕ //
          n ∈ IntervalDefectBound.defectsInInterval
            (L + 1) (x - 1)}
        {n : ℕ //
          n ∈ IntervalDefectBound.defectsInInterval
            (L + 1) (y - 1)} := by
  rintro ⟨v, hv⟩
  rcases v with i | j
  · apply Sum.inl
    refine ⟨startCompleteVertexLabel x L i, ?_⟩
    apply mem_defectsInInterval_of_hDefective
    · exact
        (isDefective_iff_hDefective
          x y L (Sum.inl i)).mp
          (mem_defectiveVertices.mp hv)
    · exact startCompleteVertexLabel_lower hx i
    · have hupper :=
        startCompleteVertexLabel_upper hx i
      omega
  · apply Sum.inr
    refine ⟨startCompleteVertexLabel y L j, ?_⟩
    apply mem_defectsInInterval_of_hDefective
    · exact
        (isDefective_iff_hDefective
          x y L (Sum.inr j)).mp
          (mem_defectiveVertices.mp hv)
    · exact startCompleteVertexLabel_lower hy j
    · have hupper :=
        startCompleteVertexLabel_upper hy j
      omega

/-- The map to the disjoint union of the two interval defect sets is injective. -/
theorem defectiveVertexToIntervals_injective
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Function.Injective
      (defectiveVertexToIntervals
        (x := x) (y := y) (L := L) hx hy) := by
  rintro ⟨v, hv⟩ ⟨w, hw⟩ hmap
  apply Subtype.ext
  cases v with
  | inl i =>
      cases w with
      | inl j =>
          apply congrArg Sum.inl
          apply
            RelationalPrimeAssignment.startCompleteVertexLabel_injective hx
          have hlabel :=
            congrArg
              (Sum.elim
                (fun n => n.1)
                (fun n => n.1))
              hmap
          simpa [defectiveVertexToIntervals] using hlabel
      | inr j =>
          have hblock :=
            congrArg
              (Sum.elim
                (fun _ => false)
                (fun _ => true))
              hmap
          simp [defectiveVertexToIntervals] at hblock
  | inr i =>
      cases w with
      | inl j =>
          have hblock :=
            congrArg
              (Sum.elim
                (fun _ => false)
                (fun _ => true))
              hmap
          simp [defectiveVertexToIntervals] at hblock
      | inr j =>
          apply congrArg Sum.inr
          apply
            RelationalPrimeAssignment.startCompleteVertexLabel_injective hy
          have hlabel :=
            congrArg
              (Sum.elim
                (fun n => n.1)
                (fun n => n.1))
              hmap
          simpa [defectiveVertexToIntervals] using hlabel

/--
The literal defective-vertex count is bounded by the two complete-boundary
defect intervals.
-/
theorem defectiveVertexCount_le_interval_sum
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    defectiveVertexCount x y L ≤
      (IntervalDefectBound.defectsInInterval
        (L + 1) (x - 1)).card +
      (IntervalDefectBound.defectsInInterval
        (L + 1) (y - 1)).card := by
  classical
  let leftDefects :=
    IntervalDefectBound.defectsInInterval
      (L + 1) (x - 1)
  let rightDefects :=
    IntervalDefectBound.defectsInInterval
      (L + 1) (y - 1)
  calc
    defectiveVertexCount x y L =
        Fintype.card
          {v : Occurrence L //
            v ∈ defectiveVertices x y L} := by
      exact
        (Fintype.card_coe
          (defectiveVertices x y L)).symm
    _ ≤
        Fintype.card
          (Sum
            {n : ℕ // n ∈ leftDefects}
            {n : ℕ // n ∈ rightDefects}) :=
      Fintype.card_le_of_injective
        (defectiveVertexToIntervals hx hy)
        (defectiveVertexToIntervals_injective hx hy)
    _ = leftDefects.card + rightDefects.card := by
      simp
    _ =
        (IntervalDefectBound.defectsInInterval
          (L + 1) (x - 1)).card +
        (IntervalDefectBound.defectsInInterval
          (L + 1) (y - 1)).card := by
      rfl

/-! ## Transfer to the corrected count `D#` -/

/-- Canonical correction never increases the literal defective count. -/
theorem canonicalCorrectedDefectCount_le_defectiveVertexCount
    (A x y L : ℕ) :
    canonicalCorrectedDefectCount A x y L ≤
      defectiveVertexCount x y L := by
  generalize hchoice :
      canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = choice
  cases choice with
  | none =>
      simp [canonicalCorrectedDefectCount, hchoice]
  | some c =>
      simpa [canonicalCorrectedDefectCount, hchoice] using
        correctedDefectCount_le
          x y L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2)

/--
The desired finite form of `(6.4)`: `D#` is bounded by the two local defect
sets of length `B=L+1`.
-/
theorem canonicalCorrectedDefectCount_le_interval_sum
    (A : ℕ)
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    canonicalCorrectedDefectCount A x y L ≤
      (IntervalDefectBound.defectsInInterval
        (L + 1) (x - 1)).card +
      (IntervalDefectBound.defectsInInterval
        (L + 1) (y - 1)).card :=
  (canonicalCorrectedDefectCount_le_defectiveVertexCount
    A x y L).trans
    (defectiveVertexCount_le_interval_sum hx hy)

/-! ## Uniform pointwise consequence in a critical window -/

/--
Uniform `O(log N / loglog N)` bound for the corrected count, provided both
complete-boundary intervals lie in the enlarged pointwise window.
-/
theorem canonicalCorrectedDefectCount_uniform_on_window
    {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁)
    (hc₁c₂ : c₁ < c₂) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
        CriticalWindowParameters.InCriticalWindow
          c₁ c₂ N (L + 1) →
        ∀ A x y,
          1 ≤ x → 1 ≤ y →
          N ≤ 2 * (x - 1) →
          (x - 1) + (L + 1) ≤ 3 * N →
          N ≤ 2 * (y - 1) →
          (y - 1) + (L + 1) ≤ 3 * N →
          ((canonicalCorrectedDefectCount A x y L : ℕ) : ℝ) ≤
            K *
              (Real.log N /
                Real.log (Real.log N)) := by
  obtain ⟨K, hK, N₀, hpoint⟩ :=
    CriticalPointwiseIntervals.pointwise_all_intervals_on_window
      hc₁ hc₁c₂
  refine ⟨2 * K, by positivity, N₀, ?_⟩
  intro N hN L hwindow A x y hx hy
      hNx hxContained hNy hyContained
  have hleft :=
    hpoint N hN (L + 1) hwindow
      (x - 1) hNx hxContained
  have hright :=
    hpoint N hN (L + 1) hwindow
      (y - 1) hNy hyContained
  have hfinite :=
    canonicalCorrectedDefectCount_le_interval_sum
      (L := L) A hx hy
  have hcast :
      ((canonicalCorrectedDefectCount A x y L : ℕ) : ℝ) ≤
        ((IntervalDefectBound.defectsInInterval
            (L + 1) (x - 1)).card : ℝ) +
        ((IntervalDefectBound.defectsInInterval
            (L + 1) (y - 1)).card : ℝ) := by
    exact_mod_cast hfinite
  calc
    ((canonicalCorrectedDefectCount A x y L : ℕ) : ℝ) ≤
        ((IntervalDefectBound.defectsInInterval
            (L + 1) (x - 1)).card : ℝ) +
        ((IntervalDefectBound.defectsInInterval
            (L + 1) (y - 1)).card : ℝ) :=
      hcast
    _ ≤
        K * (Real.log N / Real.log (Real.log N)) +
          K * (Real.log N / Real.log (Real.log N)) :=
      add_le_add hleft hright
    _ =
        (2 * K) *
          (Real.log N / Real.log (Real.log N)) := by
      ring

/--
Convenient geometric specialization: starts in the main dyadic block meet
the two interval-containment hypotheses as soon as `N≥2` and `L+1≤N`.
-/
theorem canonicalCorrectedDefectCount_uniform_on_dyadicBlock
    {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁)
    (hc₁c₂ : c₁ < c₂) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L,
        CriticalWindowParameters.InCriticalWindow
          c₁ c₂ N (L + 1) →
        L + 1 ≤ N →
        ∀ A x y,
          x ∈ dyadicBlock N →
          y ∈ dyadicBlock N →
          ((canonicalCorrectedDefectCount A x y L : ℕ) : ℝ) ≤
            K *
              (Real.log N /
                Real.log (Real.log N)) := by
  obtain ⟨K, hK, N₀, hbound⟩ :=
    canonicalCorrectedDefectCount_uniform_on_window
      hc₁ hc₁c₂
  refine ⟨K, hK, N₀, ?_⟩
  intro N hN L hwindow hL A x y hx hy
  have hN₀ : N₀ ≤ N :=
    (le_max_left N₀ 2).trans hN
  have hNtwo : 2 ≤ N :=
    (le_max_right N₀ 2).trans hN
  have hxIco :
      x ∈ Finset.Ico N (2 * N) := by
    simpa only [dyadicBlock] using hx
  have hyIco :
      y ∈ Finset.Ico N (2 * N) := by
    simpa only [dyadicBlock] using hy
  have hxBounds := Finset.mem_Ico.mp hxIco
  have hyBounds := Finset.mem_Ico.mp hyIco
  apply hbound N hN₀ L hwindow A x y
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-! ## Literal `B / log B` form of (6.4) -/

/--
Elementary comparison of the two equivalent critical scales.  The explicit
positivity hypotheses are separated from the asymptotic threshold so the
algebraic content is reusable:

`log N / loglog N ≤ (2/c₁) * (B/log B)`.
-/
theorem log_div_loglog_le_two_div_lower_mul_height_div_log
    {c₁ c₂ : ℝ} {N B : ℕ}
    (hc₁ : 0 < c₁)
    (hc₁c₂ : c₁ < c₂)
    (hwindow :
      CriticalWindowParameters.InCriticalWindow
        c₁ c₂ N B)
    (hlogNpos : 0 < Real.log N)
    (hloglogNpos : 0 < Real.log (Real.log N))
    (hBone : 1 < (B : ℝ))
    (hlogc₂ :
      Real.log c₂ ≤ Real.log (Real.log N)) :
    Real.log N / Real.log (Real.log N) ≤
      (2 / c₁) * ((B : ℝ) / Real.log B) := by
  have hc₂ : 0 < c₂ :=
    hc₁.trans hc₁c₂
  have hBpos : 0 < (B : ℝ) :=
    zero_lt_one.trans hBone
  have hlogBpos : 0 < Real.log B :=
    Real.log_pos hBone
  have hlogB_le_product :
      Real.log B ≤
        Real.log (c₂ * Real.log N) := by
    apply Real.log_le_log hBpos
    exact hwindow.2.2.2
  have hlogB_le_twice :
      Real.log B ≤
        2 * Real.log (Real.log N) := by
    calc
      Real.log B ≤
          Real.log (c₂ * Real.log N) :=
        hlogB_le_product
      _ =
          Real.log c₂ +
            Real.log (Real.log N) := by
        rw [Real.log_mul hc₂.ne' hlogNpos.ne']
      _ ≤
          2 * Real.log (Real.log N) := by
        linarith
  have hlogN_le_height :
      Real.log N ≤ (B : ℝ) / c₁ := by
    rw [le_div_iff₀ hc₁]
    nlinarith [hwindow.2.2.1]
  have hreciprocal :
      1 / Real.log (Real.log N) ≤
        2 / Real.log B := by
    rw [div_le_div_iff₀ hloglogNpos hlogBpos]
    simpa only [one_mul] using hlogB_le_twice
  calc
    Real.log N / Real.log (Real.log N) ≤
        ((B : ℝ) / c₁) /
          Real.log (Real.log N) :=
      div_le_div_of_nonneg_right
        hlogN_le_height hloglogNpos.le
    _ =
        ((B : ℝ) / c₁) *
          (1 / Real.log (Real.log N)) := by
      ring
    _ ≤
        ((B : ℝ) / c₁) *
          (2 / Real.log B) :=
      mul_le_mul_of_nonneg_left hreciprocal
        (div_nonneg (Nat.cast_nonneg B) hc₁.le)
    _ =
        (2 / c₁) *
          ((B : ℝ) / Real.log B) := by
      ring

/--
All positivity assumptions in the preceding comparison hold uniformly once
`N` exceeds a threshold depending only on the critical-window constants.
-/
theorem log_div_loglog_le_height_div_log_eventually
    {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁)
    (hc₁c₂ : c₁ < c₂) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B,
      CriticalWindowParameters.InCriticalWindow
        c₁ c₂ N B →
      Real.log N / Real.log (Real.log N) ≤
        (2 / c₁) * ((B : ℝ) / Real.log B) := by
  let T : ℝ :=
    max (Real.exp 1) (max c₂ (1 / c₁))
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (Real.exp T)
  refine ⟨N₀, ?_⟩
  intro N hN B hwindow
  have hNlarge :
      Real.exp T < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hT_lt_logN :
      T < Real.log N := by
    have hmono :=
      Real.log_lt_log (Real.exp_pos T) hNlarge
    simpa only [Real.log_exp] using hmono
  have hexpOne_le_T :
      Real.exp 1 ≤ T :=
    le_max_left _ _
  have hc₂_le_T :
      c₂ ≤ T :=
    (le_max_left c₂ (1 / c₁)).trans
      (le_max_right (Real.exp 1) _)
  have hreciprocal_le_T :
      1 / c₁ ≤ T :=
    (le_max_right c₂ (1 / c₁)).trans
      (le_max_right (Real.exp 1) _)
  have hexpOne_lt_logN :
      Real.exp 1 < Real.log N :=
    hexpOne_le_T.trans_lt hT_lt_logN
  have hexpOne_gt_one :
      (1 : ℝ) < Real.exp 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hlogNpos : 0 < Real.log N :=
    zero_lt_one.trans
      (hexpOne_gt_one.trans hexpOne_lt_logN)
  have hloglogNpos :
      0 < Real.log (Real.log N) :=
    Real.log_pos
      (hexpOne_gt_one.trans hexpOne_lt_logN)
  have hc₂ : 0 < c₂ :=
    hc₁.trans hc₁c₂
  have hc₂_lt_logN :
      c₂ < Real.log N :=
    hc₂_le_T.trans_lt hT_lt_logN
  have hlogc₂ :
      Real.log c₂ ≤ Real.log (Real.log N) :=
    Real.log_le_log hc₂ hc₂_lt_logN.le
  have hreciprocal_lt_logN :
      1 / c₁ < Real.log N :=
    hreciprocal_le_T.trans_lt hT_lt_logN
  have hone_lt_lower :
      (1 : ℝ) < c₁ * Real.log N := by
    rw [div_lt_iff₀ hc₁] at hreciprocal_lt_logN
    nlinarith
  have hBone : 1 < (B : ℝ) :=
    hone_lt_lower.trans_le hwindow.2.2.1
  exact
    log_div_loglog_le_two_div_lower_mul_height_div_log
      hc₁ hc₁c₂ hwindow
      hlogNpos hloglogNpos hBone hlogc₂

/--
Literal uniform form of `(6.4)`.  In the critical window `B=L+1`, for
dyadic starts and `B≤N`,

`D# ≪_{c₁,c₂} B / log B`.

The threshold internalizes every logarithmic positivity condition.
-/
theorem canonicalCorrectedDefectCount_uniform_B_div_log_B
    {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁)
    (hc₁c₂ : c₁ < c₂) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L,
        CriticalWindowParameters.InCriticalWindow
          c₁ c₂ N (L + 1) →
        L + 1 ≤ N →
        ∀ A x y,
          x ∈ dyadicBlock N →
          y ∈ dyadicBlock N →
          ((canonicalCorrectedDefectCount A x y L : ℕ) : ℝ) ≤
            K *
              (((L + 1 : ℕ) : ℝ) /
                Real.log (((L + 1 : ℕ) : ℝ))) := by
  obtain ⟨K, hK, Npoint, hpoint⟩ :=
    canonicalCorrectedDefectCount_uniform_on_dyadicBlock
      hc₁ hc₁c₂
  obtain ⟨Ncompare, hcompare⟩ :=
    log_div_loglog_le_height_div_log_eventually
      hc₁ hc₁c₂
  refine
    ⟨K * (2 / c₁),
      mul_nonneg hK (div_nonneg (by norm_num) hc₁.le),
      max Npoint Ncompare, ?_⟩
  intro N hN L hwindow hheight A x y hx hy
  have hNpoint : Npoint ≤ N :=
    (le_max_left Npoint Ncompare).trans
      ((le_max_left (max Npoint Ncompare) 2).trans hN)
  have hNcompare : Ncompare ≤ N :=
    (le_max_right Npoint Ncompare).trans
      ((le_max_left (max Npoint Ncompare) 2).trans hN)
  have hNtwo : 2 ≤ N :=
    (le_max_right (max Npoint Ncompare) 2).trans hN
  have hpointBound :=
    hpoint N (max_le hNpoint hNtwo)
      L hwindow hheight A x y hx hy
  have hscale :=
    hcompare N hNcompare (L + 1) hwindow
  calc
    ((canonicalCorrectedDefectCount A x y L : ℕ) : ℝ) ≤
        K *
          (Real.log N /
            Real.log (Real.log N)) :=
      hpointBound
    _ ≤
        K *
          ((2 / c₁) *
            (((L + 1 : ℕ) : ℝ) /
              Real.log (((L + 1 : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_left hscale hK
    _ =
        (K * (2 / c₁)) *
          (((L + 1 : ℕ) : ℝ) /
            Real.log (((L + 1 : ℕ) : ℝ))) := by
      ring

end

end DefectiveVertexIntervalBound
end PaperC
