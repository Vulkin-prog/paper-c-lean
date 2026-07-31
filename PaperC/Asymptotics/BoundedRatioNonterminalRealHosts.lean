import PaperC.Asymptotics.BoundedRatioNonterminalHostCounts

set_option maxHeartbeats 3600000

/-!
# Real-valued host envelopes for Lemma 17.23

`BoundedRatioNonterminalHostCounts` gives the exact source disjunction for
bounded component hosts:

* support two, hence two singleton offset sets;
* support at least three, oriented so that one mobile offset set has degree
  at least two.

Its first finite interface uses natural-valued common bounds.  The arithmetic
degree-two and Evertse--Silverman sums naturally yield real asymptotic
envelopes, so this module repeats the last finite union bound after coercion
to `ℝ`.  No host-count hypothesis and no arithmetic bridge is introduced.
-/

namespace PaperC
namespace BoundedRatioNonterminalRealHosts

open BoundedRatioComponentHosts
open BoundedRatioManyDefectsFibers
open BoundedRatioNonterminalHostCounts

noncomputable section

/-! ## Fixed-shape disintegration -/

/-- Real-valued first-start disintegration of one fixed shape. -/
theorem card_boundedComponentHostsOfShape_cast_le_leftBaseFibers
    {N M A L K : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hfiber :
      ∀ base ∈ boundedStartBases N M,
        ((leftBaseShapeFiber
          N M A L K base shape).card : ℝ) ≤ Q) :
    ((boundedComponentHostsOfShape
        N M A L K shape).card : ℝ) ≤
      ((M - N : ℕ) : ℝ) * Q := by
  classical
  have hbase :
      ((boundedStartBases N M).card : ℝ) ≤
        ((M - N : ℕ) : ℝ) := by
    exact_mod_cast card_boundedStartBases_le N M
  calc
    ((boundedComponentHostsOfShape
        N M A L K shape).card : ℝ) ≤
        (((boundedStartBases N M).biUnion fun base =>
          leftBaseShapeFiber
            N M A L K base shape).card : ℝ) := by
      exact_mod_cast
        Finset.card_le_card
          (boundedComponentHostsOfShape_subset_leftBaseUnion
            shape)
    _ ≤
        ∑ base ∈ boundedStartBases N M,
          ((leftBaseShapeFiber
            N M A L K base shape).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _base ∈ boundedStartBases N M, Q :=
      Finset.sum_le_sum fun base hbaseMem =>
        hfiber base hbaseMem
    _ = ((boundedStartBases N M).card : ℝ) * Q := by
      simp
    _ ≤ ((M - N : ℕ) : ℝ) * Q :=
      mul_le_mul_of_nonneg_right hbase hQ

/-- Symmetric real-valued second-start disintegration. -/
theorem card_boundedComponentHostsOfShape_cast_le_rightBaseFibers
    {N M A L K : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hfiber :
      ∀ base ∈ boundedStartBases N M,
        ((rightBaseShapeFiber
          N M A L K base shape).card : ℝ) ≤ Q) :
    ((boundedComponentHostsOfShape
        N M A L K shape).card : ℝ) ≤
      ((M - N : ℕ) : ℝ) * Q := by
  classical
  have hbase :
      ((boundedStartBases N M).card : ℝ) ≤
        ((M - N : ℕ) : ℝ) := by
    exact_mod_cast card_boundedStartBases_le N M
  calc
    ((boundedComponentHostsOfShape
        N M A L K shape).card : ℝ) ≤
        (((boundedStartBases N M).biUnion fun base =>
          rightBaseShapeFiber
            N M A L K base shape).card : ℝ) := by
      exact_mod_cast
        Finset.card_le_card
          (boundedComponentHostsOfShape_subset_rightBaseUnion
            shape)
    _ ≤
        ∑ base ∈ boundedStartBases N M,
          ((rightBaseShapeFiber
            N M A L K base shape).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _base ∈ boundedStartBases N M, Q :=
      Finset.sum_le_sum fun base hbaseMem =>
        hfiber base hbaseMem
    _ = ((boundedStartBases N M).card : ℝ) * Q := by
      simp
    _ ≤ ((M - N : ℕ) : ℝ) * Q :=
      mul_le_mul_of_nonneg_right hbase hQ

/-! ## The exact source disjunction after coercion -/

/--
Real-valued form of the finite host disjunction of Lemma 17.23.

`Q₂` bounds every two-singleton fixed-shape population.  `Q` bounds every
fixed-base fibre in an orientation whose mobile degree is at least two.
The only remaining factors are the interval width and the explicit
polynomial number of offset shapes.
-/
theorem card_boundedComponentHosts_cast_le_sourceDisjunction
    {N M A L K : ℕ} (hN : 2 ≤ N)
    (Q₂ Q : ℝ) (hQ₂ : 0 ≤ Q₂) (hQ : 0 ≤ Q)
    (htwo :
      ∀ shape ∈ boundedOffsetShapes L K,
        shape.1.card + shape.2.card = 2 →
        ((boundedComponentHostsOfShape
          N M A L K shape).card : ℝ) ≤ Q₂)
    (hleft :
      ∀ shape ∈ boundedOffsetShapes L K,
        2 ≤ shape.2.card →
        ∀ base ∈ boundedStartBases N M,
          ((leftBaseShapeFiber
            N M A L K base shape).card : ℝ) ≤ Q)
    (hright :
      ∀ shape ∈ boundedOffsetShapes L K,
        2 ≤ shape.1.card →
        ∀ base ∈ boundedStartBases N M,
          ((rightBaseShapeFiber
            N M A L K base shape).card : ℝ) ≤ Q) :
    ((boundedComponentHosts N M A L K).card : ℝ) ≤
      ((((K + 1) * (L + 1) ^ K) ^ 2 : ℕ) : ℝ) *
        max Q₂ (((M - N : ℕ) : ℝ) * Q) := by
  classical
  let R : ℝ :=
    max Q₂ (((M - N : ℕ) : ℝ) * Q)
  have hRnonneg : 0 ≤ R := by
    dsimp only [R]
    exact le_max_of_le_left hQ₂
  have hshape :
      ∀ shape ∈ boundedOffsetShapes L K,
        ((boundedComponentHostsOfShape
          N M A L K shape).card : ℝ) ≤ R := by
    intro shape hshapeMem
    have hdata := mem_boundedOffsetShapes.mp hshapeMem
    have htotalPos :
        2 ≤ shape.1.card + shape.2.card := by
      have hleftPos : 0 < shape.1.card :=
        Finset.card_pos.mpr hdata.1
      have hrightPos : 0 < shape.2.card :=
        Finset.card_pos.mpr hdata.2.1
      omega
    by_cases htwoShape :
        shape.1.card + shape.2.card = 2
    · exact (htwo shape hshapeMem htwoShape).trans
        (le_max_left _ _)
    · have hthree :
          3 ≤ shape.1.card + shape.2.card := by
        omega
      rcases
          mobile_degree_dichotomy_of_three_le_total
            hshapeMem hthree with
        hmobile | hmobile
      · exact
          (card_boundedComponentHostsOfShape_cast_le_leftBaseFibers
            shape Q hQ
            (hleft shape hshapeMem hmobile)).trans
            (le_max_right _ _)
      · exact
          (card_boundedComponentHostsOfShape_cast_le_rightBaseFibers
            shape Q hQ
            (hright shape hshapeMem hmobile)).trans
            (le_max_right _ _)
  have hshapeCount :
      ((boundedOffsetShapes L K).card : ℝ) ≤
        ((((K + 1) * (L + 1) ^ K) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast card_boundedOffsetShapes_le L K
  calc
    ((boundedComponentHosts N M A L K).card : ℝ) ≤
        (((boundedOffsetShapes L K).biUnion fun shape =>
          boundedComponentHostsOfShape
            N M A L K shape).card : ℝ) := by
      exact_mod_cast
        Finset.card_le_card
          (boundedComponentHosts_subset_shapeUnion hN)
    _ ≤
        ∑ shape ∈ boundedOffsetShapes L K,
          ((boundedComponentHostsOfShape
            N M A L K shape).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _shape ∈ boundedOffsetShapes L K, R :=
      Finset.sum_le_sum fun shape hshapeMem =>
        hshape shape hshapeMem
    _ = ((boundedOffsetShapes L K).card : ℝ) * R := by
      simp
    _ ≤
        ((((K + 1) * (L + 1) ^ K) ^ 2 : ℕ) : ℝ) * R :=
      mul_le_mul_of_nonneg_right hshapeCount hRnonneg
    _ =
        ((((K + 1) * (L + 1) ^ K) ^ 2 : ℕ) : ℝ) *
          max Q₂ (((M - N : ℕ) : ℝ) * Q) := by
      rfl

end

end BoundedRatioNonterminalRealHosts
end PaperC
