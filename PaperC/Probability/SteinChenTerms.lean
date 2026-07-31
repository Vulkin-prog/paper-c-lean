import PaperC.Asymptotics.DependencyEdgesCritical
import PaperC.Probability.SectionTwelveMoments

set_option maxHeartbeats 1200000

/-!
# Finite Stein--Chen terms for the conditional dependency graph

This file formalizes the deterministic finite sums occurring in Lemma 13.8.
The vertices are the good starts `I_N \ D_Y`; the ordered edges are the
large-prime dependency edges constructed in
`LargePrimeDependencyGraph`.  Since every good conditional marginal is
`2⁻ᴸ`, the first Stein--Chen term is exactly the number of closed ordered
neighbour pairs divided by `2^(2L)`.

For the second term, averaging the conditional joint probabilities over the
fixed small-prime coordinates gives the unconditional joint probabilities
already defined in `SectionTwelveMoments`.  We partition the ordered edge set
into overlap, touching, and separated parts.  Overlap contributes exactly
zero.  The touching and separated pieces are bounded by the finite defect
masses proved in Sections 3 and 11.  This yields a fully proved finite
majorant; neither the Arratia--Goldstein--Gordon theorem nor a conditional
independence interface is used here.
-/

namespace PaperC
namespace SteinChenTerms

open scoped BigOperators

open LargePrimeDependencyGraph
open SectionTwelveMoments

noncomputable section

/-! ## Closed neighbourhood pairs and the first term -/

/--
Ordered closed-neighbourhood pairs: the diagonal of the good vertex set,
together with all ordered dependency edges.
-/
def closedDependencyPairs (N L Y : ℕ) : Finset (ℕ × ℕ) :=
  (goodStarts N L Y).diag ∪ orderedDependencyEdges N L Y

@[simp]
theorem mem_closedDependencyPairs
    {N L Y : ℕ} {pair : ℕ × ℕ} :
    pair ∈ closedDependencyPairs N L Y ↔
      (pair.1 ∈ goodStarts N L Y ∧ pair.1 = pair.2) ∨
        pair ∈ orderedDependencyEdges N L Y := by
  simp [closedDependencyPairs]

/-- The diagonal and the loopless ordered edge set are disjoint. -/
theorem disjoint_goodDiag_orderedDependencyEdges
    (N L Y : ℕ) :
    Disjoint (goodStarts N L Y).diag
      (orderedDependencyEdges N L Y) := by
  refine Finset.disjoint_left.mpr ?_
  intro pair hdiag hedge
  have heq : pair.1 = pair.2 :=
    (Finset.mem_diag.mp hdiag).2
  exact ne_of_mem_orderedDependencyEdges hedge heq

/-- Exact count of the closed ordered neighbourhood relation. -/
theorem card_closedDependencyPairs
    (N L Y : ℕ) :
    (closedDependencyPairs N L Y).card =
      (goodStarts N L Y).card +
        (orderedDependencyEdges N L Y).card := by
  rw [closedDependencyPairs,
    Finset.card_union_of_disjoint
      (disjoint_goodDiag_orderedDependencyEdges N L Y)]
  rw [Finset.diag_card]

/-- The good-start population is bounded by the length-`N` dyadic block. -/
theorem card_goodStarts_le
    (N L Y : ℕ) :
    (goodStarts N L Y).card ≤ N := by
  calc
    (goodStarts N L Y).card ≤ (dyadicBlock N).card :=
      Finset.card_le_card (Finset.sdiff_subset)
    _ = N := TouchingPairs.card_dyadicBlock N

/-- The common conditional marginal `p_N = 2⁻ᴸ`. -/
def conditionalMarginal (L : ℕ) : ℚ :=
  (1 : ℚ) / (2 : ℚ) ^ L

/-- First Stein--Chen term, written as its literal finite double sum. -/
def steinBOne (N L Y : ℕ) : ℚ :=
  ∑ _pair ∈ closedDependencyPairs N L Y,
    conditionalMarginal L * conditionalMarginal L

/-- Exact cardinal form of the first Stein--Chen term. -/
theorem steinBOne_eq_card_div
    (N L Y : ℕ) :
    steinBOne N L Y =
      ((closedDependencyPairs N L Y).card : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  unfold steinBOne conditionalMarginal
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [show 2 * L = L + L by omega, pow_add]
  ring

/-- Manuscript-facing finite estimate `b₁ ≤ (N+E_Y)2⁻²ᴸ`. -/
theorem steinBOne_le
    (N L Y : ℕ) :
    steinBOne N L Y ≤
      ((N + (orderedDependencyEdges N L Y).card : ℕ) : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  rw [steinBOne_eq_card_div, card_closedDependencyPairs]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast
      Nat.add_le_add_right (card_goodStarts_le N L Y)
        (orderedDependencyEdges N L Y).card
  · positivity

/-! ## The edge partition and the averaged second term -/

/-- Dependency edges at strict overlap distance. -/
def overlapDependencyEdges (N L Y : ℕ) : Finset (ℕ × ℕ) :=
  orderedDependencyEdges N L Y ∩ overlappingPairs N L

/-- Dependency edges at the touching distance. -/
def touchingDependencyEdges (N L Y : ℕ) : Finset (ℕ × ℕ) :=
  orderedDependencyEdges N L Y ∩ touchingOffDiagPairs N L

/-- Dependency edges beyond the touching distance. -/
def separatedDependencyEdges (N L Y : ℕ) : Finset (ℕ × ℕ) :=
  orderedDependencyEdges N L Y ∩ separatedOffDiagPairs N L

/-- Every ordered dependency edge belongs to the dyadic off-diagonal. -/
theorem orderedDependencyEdges_subset_offDiag
    (N L Y : ℕ) :
    orderedDependencyEdges N L Y ⊆ (dyadicBlock N).offDiag := by
  intro pair hedge
  have hmem := mem_orderedDependencyEdges.mp hedge
  exact Finset.mem_offDiag.mpr
    ⟨(mem_goodStarts.mp hmem.1).1,
      (mem_goodStarts.mp hmem.2.1).1,
      ne_of_mem_orderedDependencyEdges hedge⟩

/-- Exact overlap/touching/separated partition of the ordered edge set. -/
theorem orderedDependencyEdges_eq_three_parts
    (N L Y : ℕ) :
    orderedDependencyEdges N L Y =
      overlapDependencyEdges N L Y ∪
        (touchingDependencyEdges N L Y ∪
          separatedDependencyEdges N L Y) := by
  ext pair
  simp only [overlapDependencyEdges, touchingDependencyEdges,
    separatedDependencyEdges, Finset.mem_union, Finset.mem_inter]
  constructor
  · intro hedge
    have hoff :
        pair ∈ (dyadicBlock N).offDiag :=
      orderedDependencyEdges_subset_offDiag N L Y hedge
    rw [offDiag_eq_three_distance_populations] at hoff
    rcases Finset.mem_union.mp hoff with hover | hrest
    · exact Or.inl ⟨hedge, hover⟩
    · rcases Finset.mem_union.mp hrest with htouch | hsep
      · exact Or.inr (Or.inl ⟨hedge, htouch⟩)
      · exact Or.inr (Or.inr ⟨hedge, hsep⟩)
  · rintro (hover | htouch | hsep)
    · exact hover.1
    · exact htouch.1
    · exact hsep.1

theorem disjoint_overlapDependencyEdges_touching
    (N L Y : ℕ) :
    Disjoint (overlapDependencyEdges N L Y)
      (touchingDependencyEdges N L Y) := by
  refine Finset.disjoint_left.mpr ?_
  intro pair hover htouch
  exact (Finset.disjoint_left.mp
    (disjoint_overlapping_touching N L))
      (Finset.mem_inter.mp hover).2
      (Finset.mem_inter.mp htouch).2

theorem disjoint_overlapDependencyEdges_separated
    (N L Y : ℕ) :
    Disjoint (overlapDependencyEdges N L Y)
      (separatedDependencyEdges N L Y) := by
  refine Finset.disjoint_left.mpr ?_
  intro pair hover hsep
  exact (Finset.disjoint_left.mp
    (disjoint_overlapping_separated N L))
      (Finset.mem_inter.mp hover).2
      (Finset.mem_inter.mp hsep).2

theorem disjoint_touchingDependencyEdges_separated
    (N L Y : ℕ) :
    Disjoint (touchingDependencyEdges N L Y)
      (separatedDependencyEdges N L Y) := by
  refine Finset.disjoint_left.mpr ?_
  intro pair htouch hsep
  exact (Finset.disjoint_left.mp
    (disjoint_touching_separated N L))
      (Finset.mem_inter.mp htouch).2
      (Finset.mem_inter.mp hsep).2

/--
The averaged second Stein--Chen term.  This is exactly the unconditional
joint mass on the ordered dependency edges.
-/
def steinBTwoAverage (N L Y : ℕ) : ℚ :=
  jointPairMass N L (orderedDependencyEdges N L Y)

/-- Exact three-distance decomposition of the averaged second term. -/
theorem steinBTwoAverage_eq_three_parts
    (N L Y : ℕ) :
    steinBTwoAverage N L Y =
      jointPairMass N L (overlapDependencyEdges N L Y) +
        jointPairMass N L (touchingDependencyEdges N L Y) +
          jointPairMass N L (separatedDependencyEdges N L Y) := by
  rw [steinBTwoAverage, orderedDependencyEdges_eq_three_parts]
  rw [jointPairMass_union
    (Finset.disjoint_union_right.mpr
      ⟨disjoint_overlapDependencyEdges_touching N L Y,
        disjoint_overlapDependencyEdges_separated N L Y⟩)]
  rw [jointPairMass_union
    (disjoint_touchingDependencyEdges_separated N L Y)]
  ring

/-- Strict-overlap dependency edges carry no joint probability. -/
theorem jointPairMass_overlapDependencyEdges_eq_zero
    (N L Y : ℕ) :
    jointPairMass N L (overlapDependencyEdges N L Y) = 0 := by
  classical
  unfold jointPairMass
  apply Finset.sum_eq_zero
  intro pair hpair
  exact jointStartProbability_eq_zero_of_overlap
    (mem_overlappingPairs.mp
      (Finset.mem_inter.mp hpair).2).2.2.1
    (mem_overlappingPairs.mp
      (Finset.mem_inter.mp hpair).2).2.2.2

/-- Joint start probabilities are nonnegative rational numbers. -/
theorem jointStartProbability_nonneg
    (N L x y : ℕ) :
    0 ≤ jointStartProbability N L x y := by
  classical
  unfold jointStartProbability uniformEventProbability
  positivity

/-- Joint mass is monotone under inclusion of finite pair populations. -/
theorem jointPairMass_mono
    {N L : ℕ} {s t : Finset (ℕ × ℕ)}
    (hst : s ⊆ t) :
    jointPairMass N L s ≤ jointPairMass N L t := by
  unfold jointPairMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hst
    (fun pair _ht _hs =>
      jointStartProbability_nonneg N L pair.1 pair.2)

/-- Natural defect mass is monotone under inclusion. -/
theorem jointDefectMass_mono
    {N L : ℕ} {s t : Finset (ℕ × ℕ)}
    (hst : s ⊆ t) :
    jointDefectMass N L s ≤ jointDefectMass N L t := by
  unfold jointDefectMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hst
    (fun _pair _ht _hs => Nat.zero_le _)

/-- Touching edge mass is bounded by the complete touching population. -/
theorem jointPairMass_touchingDependencyEdges_le
    (N L Y : ℕ) :
    jointPairMass N L (touchingDependencyEdges N L Y) ≤
      jointPairMass N L (touchingOffDiagPairs N L) :=
  jointPairMass_mono Finset.inter_subset_right

/--
Separated edge mass is bounded by its independent baseline plus the complete
separated defect mass.
-/
theorem jointPairMass_separatedDependencyEdges_le
    {N L Y : ℕ} (hL : 0 < L) :
    jointPairMass N L (separatedDependencyEdges N L Y) ≤
      ((separatedDependencyEdges N L Y).card : ℚ) /
          (2 : ℚ) ^ (2 * L) +
        (jointDefectMass N L
          (separatedOffDiagPairs N L) : ℚ) /
          (2 : ℚ) ^ (2 * L) := by
  have habs :=
    abs_jointPairMass_sub_baseline_le
      N L hL (separatedDependencyEdges N L Y)
  have hpoint :
      jointPairMass N L (separatedDependencyEdges N L Y) -
          ((separatedDependencyEdges N L Y).card : ℚ) /
            (2 : ℚ) ^ (2 * L) ≤
        (jointDefectMass N L
          (separatedDependencyEdges N L Y) : ℚ) /
            (2 : ℚ) ^ (2 * L) :=
    le_trans (le_abs_self _) habs
  have hdefect :
      (jointDefectMass N L
          (separatedDependencyEdges N L Y) : ℚ) ≤
        (jointDefectMass N L
          (separatedOffDiagPairs N L) : ℚ) := by
    exact_mod_cast jointDefectMass_mono
      (N := N) (L := L) (s := separatedDependencyEdges N L Y)
      (t := separatedOffDiagPairs N L)
      Finset.inter_subset_right
  have hdiv :
      (jointDefectMass N L
          (separatedDependencyEdges N L Y) : ℚ) /
            (2 : ℚ) ^ (2 * L) ≤
        (jointDefectMass N L
          (separatedOffDiagPairs N L) : ℚ) /
            (2 : ℚ) ^ (2 * L) :=
    div_le_div_of_nonneg_right hdefect (by positivity)
  linarith

/--
Touching edge mass is bounded by the complete touching baseline and defect
mass.
-/
theorem jointPairMass_touchingDependencyEdges_le_complete
    {N L Y : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    jointPairMass N L (touchingDependencyEdges N L Y) ≤
      ((touchingOffDiagPairs N L).card : ℚ) /
          (2 : ℚ) ^ (2 * L) +
        (TouchingMass.touchingMass N L : ℚ) /
          (2 : ℚ) ^ (2 * L) := by
  have hsubset :=
    jointPairMass_touchingDependencyEdges_le N L Y
  have habs :=
    abs_touchingPairMass_sub_baseline_le hN hL
  have hpoint :
      jointPairMass N L (touchingOffDiagPairs N L) -
          ((touchingOffDiagPairs N L).card : ℚ) /
            (2 : ℚ) ^ (2 * L) ≤
        (TouchingMass.touchingMass N L : ℚ) /
          (2 : ℚ) ^ (2 * L) :=
    le_trans (le_abs_self _) habs
  linarith

/--
Fully proved finite majorant for the averaged second Stein--Chen term.
It has the same asymptotic strength as Lemma 13.8:

`E b₂ ≤ (T_N + E_Y + touchingMass + R₂) / 2^(2L)`,

where `T_N` is the number of ordered touching pairs.
-/
theorem steinBTwoAverage_le
    {N L Y : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    steinBTwoAverage N L Y ≤
      (((touchingOffDiagPairs N L).card +
          (orderedDependencyEdges N L Y).card +
          TouchingMass.touchingMass N L +
          jointDefectMass N L
            (separatedOffDiagPairs N L) : ℕ) : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  rw [steinBTwoAverage_eq_three_parts,
    jointPairMass_overlapDependencyEdges_eq_zero]
  have htouch :=
    jointPairMass_touchingDependencyEdges_le_complete
      (Y := Y) hN hL
  have hsep :=
    jointPairMass_separatedDependencyEdges_le
      (N := N) (Y := Y) hL
  have hcard :
      (separatedDependencyEdges N L Y).card ≤
        (orderedDependencyEdges N L Y).card :=
    Finset.card_le_card Finset.inter_subset_left
  have hcardQ :
      ((separatedDependencyEdges N L Y).card : ℚ) ≤
        ((orderedDependencyEdges N L Y).card : ℚ) := by
    exact_mod_cast hcard
  have hcardDiv :
      ((separatedDependencyEdges N L Y).card : ℚ) /
          (2 : ℚ) ^ (2 * L) ≤
        ((orderedDependencyEdges N L Y).card : ℚ) /
          (2 : ℚ) ^ (2 * L) :=
    div_le_div_of_nonneg_right hcardQ (by positivity)
  calc
    0 +
          jointPairMass N L (touchingDependencyEdges N L Y) +
          jointPairMass N L (separatedDependencyEdges N L Y) ≤
        (((touchingOffDiagPairs N L).card : ℚ) /
              (2 : ℚ) ^ (2 * L) +
            (TouchingMass.touchingMass N L : ℚ) /
              (2 : ℚ) ^ (2 * L)) +
          (((separatedDependencyEdges N L Y).card : ℚ) /
              (2 : ℚ) ^ (2 * L) +
            (jointDefectMass N L
              (separatedOffDiagPairs N L) : ℚ) /
              (2 : ℚ) ^ (2 * L)) := by
        linarith
    _ ≤
        (((touchingOffDiagPairs N L).card : ℚ) /
              (2 : ℚ) ^ (2 * L) +
            (TouchingMass.touchingMass N L : ℚ) /
              (2 : ℚ) ^ (2 * L)) +
          (((orderedDependencyEdges N L Y).card : ℚ) /
              (2 : ℚ) ^ (2 * L) +
            (jointDefectMass N L
              (separatedOffDiagPairs N L) : ℚ) /
              (2 : ℚ) ^ (2 * L)) := by
        gcongr
    _ =
        (((touchingOffDiagPairs N L).card +
            (orderedDependencyEdges N L Y).card +
            TouchingMass.touchingMass N L +
            jointDefectMass N L
              (separatedOffDiagPairs N L) : ℕ) : ℚ) /
          (2 : ℚ) ^ (2 * L) := by
        push_cast
        ring

end

end SteinChenTerms
end PaperC
