import PaperC.Asymptotics.BoundedRatioManyDefectsFixedFibers
import PaperC.Asymptotics.BoundedRatioNonterminalCardinality

set_option maxHeartbeats 3600000

/-!
# Direct host-count reductions for the bounded-ratio nonterminal sector

This file isolates the exact finite disjunction used in Lemma 17.23.
For a fixed component offset shape there are two genuinely different
counting mechanisms.

* If the component has support two, both offset sets are singletons.  This
  is the two-singleton parametrization of Lemma 17.22.
* If its support is at least three, one of the two offset sets has
  cardinality at least two.  We fix the start in the other block and apply
  the one-sided count of Lemma 17.21 in the orientation in which the mobile
  degree is at least two.

The first-start and second-start disintegrations below are literal finite
covers.  They show that a uniform fixed-base/fixed-shape bound `Q` costs
only the interval width `M-N`.  The final theorem combines the two branches
before the polynomial number of offset shapes is summed.

No arithmetic statement or audit bridge is introduced.  The last section
also attaches the degree-two and degree-at-least-three fixed fibres to the
existing generalized-Pell and Evertse--Silverman inputs.  The downstream
modules `BoundedRatioTwoSingletonHosts`,
`BoundedRatioTwoSingletonCritical`,
`BoundedRatioNonterminalMobileAssembly` and
`BoundedRatioNonterminalAssembly` perform the explicit asymptotic summation,
choose the terminal threshold and close Lemma 17.28.
-/

namespace PaperC
namespace BoundedRatioNonterminalHostCounts

open BoundedRatioComponentHosts
open BoundedRatioGeometry
open BoundedRatioManyDefectsFibers
open BoundedRatioManyDefectsFixedFibers
open BoundedRatioNonterminalCardinality
open ComponentNormalization
open EvertseSilvermanInput
open PropositionSixteenOne
open SquarefreeSmoothCount

noncomputable section

/-! ## Exact disintegration by one fixed start -/

/-- The finite set of shifted first-start bases occurring in `[N,M)`. -/
noncomputable def boundedStartBases (N M : ℕ) : Finset ℕ :=
  (BoundedRatioGeometry.boundedRatioBlock N M).image fun x => x - 1

theorem card_boundedStartBases_le (N M : ℕ) :
    (boundedStartBases N M).card ≤ M - N := by
  unfold boundedStartBases
  exact (Finset.card_image_le.trans_eq
    (card_boundedRatioBlock N M))

theorem firstBase_mem_boundedStartBases
    {N M L : ℕ}
    (pair : SeparatedBoundedRatioPair N M L) :
    pair.1.1 - 1 ∈ boundedStartBases N M := by
  rw [boundedStartBases, Finset.mem_image]
  exact ⟨pair.1.1,
    (BoundedRatioGeometry.mem_separatedBoundedRatioPairs.mp pair.2).1,
    rfl⟩

theorem secondBase_mem_boundedStartBases
    {N M L : ℕ}
    (pair : SeparatedBoundedRatioPair N M L) :
    pair.1.2 - 1 ∈ boundedStartBases N M := by
  rw [boundedStartBases, Finset.mem_image]
  exact ⟨pair.1.2,
    (BoundedRatioGeometry.mem_separatedBoundedRatioPairs.mp pair.2).2.1,
    rfl⟩

/-- A fixed-shape host fibre is covered by its literal first-start fibres. -/
theorem boundedComponentHostsOfShape_subset_leftBaseUnion
    {N M A L K : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :
    boundedComponentHostsOfShape N M A L K shape ⊆
      (boundedStartBases N M).biUnion fun base =>
        leftBaseShapeFiber N M A L K base shape := by
  classical
  intro pair hpair
  apply Finset.mem_biUnion.mpr
  refine ⟨pair.1.1 - 1, firstBase_mem_boundedStartBases pair, ?_⟩
  exact mem_leftBaseShapeFiber.mpr ⟨hpair, rfl⟩

/-- Symmetric second-start cover. -/
theorem boundedComponentHostsOfShape_subset_rightBaseUnion
    {N M A L K : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :
    boundedComponentHostsOfShape N M A L K shape ⊆
      (boundedStartBases N M).biUnion fun base =>
        rightBaseShapeFiber N M A L K base shape := by
  classical
  intro pair hpair
  apply Finset.mem_biUnion.mpr
  refine ⟨pair.1.2 - 1, secondBase_mem_boundedStartBases pair, ?_⟩
  exact mem_rightBaseShapeFiber.mpr ⟨hpair, rfl⟩

/--
If every first-start fibre has at most `Q` elements, the entire fixed-shape
host population has at most `(M-N)Q` elements.
-/
theorem card_boundedComponentHostsOfShape_le_leftBaseFibers
    {N M A L K Q : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hfiber :
      ∀ base ∈ boundedStartBases N M,
        (leftBaseShapeFiber N M A L K base shape).card ≤ Q) :
    (boundedComponentHostsOfShape N M A L K shape).card ≤
      (M - N) * Q := by
  classical
  calc
    (boundedComponentHostsOfShape N M A L K shape).card ≤
        ((boundedStartBases N M).biUnion fun base =>
          leftBaseShapeFiber N M A L K base shape).card :=
      Finset.card_le_card
        (boundedComponentHostsOfShape_subset_leftBaseUnion shape)
    _ ≤
        ∑ base ∈ boundedStartBases N M,
          (leftBaseShapeFiber N M A L K base shape).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _base ∈ boundedStartBases N M, Q :=
      Finset.sum_le_sum fun base hbase => hfiber base hbase
    _ = (boundedStartBases N M).card * Q := by simp
    _ ≤ (M - N) * Q :=
      Nat.mul_le_mul_right Q (card_boundedStartBases_le N M)

/-- Symmetric fixed-second-start summation. -/
theorem card_boundedComponentHostsOfShape_le_rightBaseFibers
    {N M A L K Q : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hfiber :
      ∀ base ∈ boundedStartBases N M,
        (rightBaseShapeFiber N M A L K base shape).card ≤ Q) :
    (boundedComponentHostsOfShape N M A L K shape).card ≤
      (M - N) * Q := by
  classical
  calc
    (boundedComponentHostsOfShape N M A L K shape).card ≤
        ((boundedStartBases N M).biUnion fun base =>
          rightBaseShapeFiber N M A L K base shape).card :=
      Finset.card_le_card
        (boundedComponentHostsOfShape_subset_rightBaseUnion shape)
    _ ≤
        ∑ base ∈ boundedStartBases N M,
          (rightBaseShapeFiber N M A L K base shape).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _base ∈ boundedStartBases N M, Q :=
      Finset.sum_le_sum fun base hbase => hfiber base hbase
    _ = (boundedStartBases N M).card * Q := by simp
    _ ≤ (M - N) * Q :=
      Nat.mul_le_mul_right Q (card_boundedStartBases_le N M)

/-! ## The source disjunction: two singletons or mobile degree at least two -/

theorem shape_total_card_two_iff_singletons
    {L K : ℕ}
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    (hshape : shape ∈ boundedOffsetShapes L K)
    (htotal : shape.1.card + shape.2.card = 2) :
    shape.1.card = 1 ∧ shape.2.card = 1 := by
  have hdata := mem_boundedOffsetShapes.mp hshape
  have hleft : 0 < shape.1.card := Finset.card_pos.mpr hdata.1
  have hright : 0 < shape.2.card := Finset.card_pos.mpr hdata.2.1
  omega

theorem mobile_degree_dichotomy_of_three_le_total
    {L K : ℕ}
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    (hshape : shape ∈ boundedOffsetShapes L K)
    (htotal : 3 ≤ shape.1.card + shape.2.card) :
    2 ≤ shape.2.card ∨ 2 ≤ shape.1.card := by
  have hdata := mem_boundedOffsetShapes.mp hshape
  have hleft : 0 < shape.1.card := Finset.card_pos.mpr hdata.1
  have hright : 0 < shape.2.card := Finset.card_pos.mpr hdata.2.1
  omega

/--
Finite form of Lemma 17.23.  The size-two branch is counted globally at a
fixed shape by `Q₂`.  Every larger component is oriented so that the mobile
degree is at least two and then costs one interval width times `Q`.
-/
theorem card_boundedComponentHosts_le_sourceDisjunction
    {N M A L K Q₂ Q : ℕ} (hN : 2 ≤ N)
    (htwo :
      ∀ shape ∈ boundedOffsetShapes L K,
        shape.1.card + shape.2.card = 2 →
        (boundedComponentHostsOfShape
          N M A L K shape).card ≤ Q₂)
    (hleft :
      ∀ shape ∈ boundedOffsetShapes L K,
        2 ≤ shape.2.card →
        ∀ base ∈ boundedStartBases N M,
          (leftBaseShapeFiber
            N M A L K base shape).card ≤ Q)
    (hright :
      ∀ shape ∈ boundedOffsetShapes L K,
        2 ≤ shape.1.card →
        ∀ base ∈ boundedStartBases N M,
          (rightBaseShapeFiber
            N M A L K base shape).card ≤ Q) :
    (boundedComponentHosts N M A L K).card ≤
      ((K + 1) * (L + 1) ^ K) ^ 2 *
        max Q₂ ((M - N) * Q) := by
  apply card_boundedComponentHosts_le_of_shapeFibers hN
  intro shape hshape
  have hdata := mem_boundedOffsetShapes.mp hshape
  have htotalPos :
      2 ≤ shape.1.card + shape.2.card := by
    have hleftPos : 0 < shape.1.card :=
      Finset.card_pos.mpr hdata.1
    have hrightPos : 0 < shape.2.card :=
      Finset.card_pos.mpr hdata.2.1
    omega
  by_cases htwoShape :
      shape.1.card + shape.2.card = 2
  · exact (htwo shape hshape htwoShape).trans (Nat.le_max_left _ _)
  · have hthree :
        3 ≤ shape.1.card + shape.2.card := by omega
    rcases mobile_degree_dichotomy_of_three_le_total hshape hthree with
      hmobile | hmobile
    · exact
        (card_boundedComponentHostsOfShape_le_leftBaseFibers
          shape (hleft shape hshape hmobile)).trans
          (Nat.le_max_right _ _)
    · exact
        (card_boundedComponentHostsOfShape_le_rightBaseFibers
          shape (hright shape hshape hmobile)).trans
          (Nat.le_max_right _ _)

/-! ## Explicit attachment to Pell and Evertse--Silverman -/

/--
The explicit one-sided bound selected by the source proof.  Degree two
uses the exceptional signed-divisor term or generalized Pell; degree at
least three uses the literal Evertse--Silverman bound.
-/
noncomputable def leftMobileArithmeticBound
    {L : ℕ} (K : ℕ) (c : ℝ)
    (M base : ℕ)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))) : ℕ :=
  if hdegree : shape.2.card = 2 then
    ∑ d ∈ squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K),
      if leftNormalizedCoefficient shape base d = 1 then
        (Int.divisorsAntidiag
          ((offsetShiftOfCard shape.2 hdegree 0 -
            offsetShiftOfCard shape.2 hdegree 1) ^ 2)).card
      else
        ⌈PellInput.expLogLogBound c
          (boundedRatioCutoff M L)⌉₊
  else
    ∑ d ∈ squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K),
      (shape.2.card +
        explicitBound (offsetShift shape.2)
          (leftNormalizedCoefficient shape base d : ℤ))

/-- Symmetric explicit one-sided bound. -/
noncomputable def rightMobileArithmeticBound
    {L : ℕ} (K : ℕ) (c : ℝ)
    (M base : ℕ)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))) : ℕ :=
  if hdegree : shape.1.card = 2 then
    ∑ d ∈ squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K),
      if rightNormalizedCoefficient shape base d = 1 then
        (Int.divisorsAntidiag
          ((offsetShiftOfCard shape.1 hdegree 0 -
            offsetShiftOfCard shape.1 hdegree 1) ^ 2)).card
      else
        ⌈PellInput.expLogLogBound c
          (boundedRatioCutoff M L)⌉₊
  else
    ∑ d ∈ squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K),
      (shape.1.card +
        explicitBound (offsetShift shape.1)
          (rightNormalizedCoefficient shape base d : ℤ))

/--
Generalized Pell and Evertse--Silverman bound every left-oriented actual
fibre of mobile degree at least two by the explicit arithmetic expression
above, eventually in the common cutoff.
-/
theorem exists_card_leftBaseShapeFiber_le_mobileArithmeticBound
    (hES : EvertseSilvermanAbscissaStatement)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (K : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ X₀ : ℕ, ∀ (N M A L base : ℕ)
        (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
        2 ≤ N →
        2 ≤ shape.2.card →
        X₀ ≤ boundedRatioCutoff M L →
        (leftBaseShapeFiber N M A L K base shape).card ≤
          leftMobileArithmeticBound K c M base shape := by
  obtain ⟨c, hc, X₀, hdegreeTwo⟩ :=
    card_leftBaseShapeFiber_degree_two_polynomial_of_generalizedPell
      hPell (K := K) (E := max 4 (2 * K))
      (by omega) (le_max_left _ _) (le_max_right _ _)
  refine ⟨c, hc, X₀, ?_⟩
  intro N M A L base shape hN hdegree hcutoff
  by_cases htwo : shape.2.card = 2
  · unfold leftMobileArithmeticBound
    rw [dif_pos htwo]
    exact hdegreeTwo N M A L base shape hN htwo hcutoff
  · have hthree : 3 ≤ shape.2.card := by omega
    unfold leftMobileArithmeticBound
    rw [dif_neg htwo]
    by_cases hempty :
        leftBaseShapeFiber N M A L K base shape = ∅
    · simp [hempty]
    · obtain ⟨pair, hpair⟩ :=
        Finset.nonempty_iff_ne_empty.mpr hempty
      have hbaseEq :=
        (mem_leftBaseShapeFiber.mp hpair).2
      have hx := (pair_coordinates_two_le hN pair).1
      have hbase : 2 ≤ base + 1 := by omega
      exact
        card_leftBaseShapeFiber_degree_at_least_three
          hES hN shape hthree hbase

/-- Symmetric explicit arithmetic attachment. -/
theorem exists_card_rightBaseShapeFiber_le_mobileArithmeticBound
    (hES : EvertseSilvermanAbscissaStatement)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (K : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ X₀ : ℕ, ∀ (N M A L base : ℕ)
        (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
        2 ≤ N →
        2 ≤ shape.1.card →
        X₀ ≤ boundedRatioCutoff M L →
        (rightBaseShapeFiber N M A L K base shape).card ≤
          rightMobileArithmeticBound K c M base shape := by
  obtain ⟨c, hc, X₀, hdegreeTwo⟩ :=
    card_rightBaseShapeFiber_degree_two_polynomial_of_generalizedPell
      hPell (K := K) (E := max 4 (2 * K))
      (by omega) (le_max_left _ _) (le_max_right _ _)
  refine ⟨c, hc, X₀, ?_⟩
  intro N M A L base shape hN hdegree hcutoff
  by_cases htwo : shape.1.card = 2
  · unfold rightMobileArithmeticBound
    rw [dif_pos htwo]
    exact hdegreeTwo N M A L base shape hN htwo hcutoff
  · have hthree : 3 ≤ shape.1.card := by omega
    unfold rightMobileArithmeticBound
    rw [dif_neg htwo]
    by_cases hempty :
        rightBaseShapeFiber N M A L K base shape = ∅
    · simp [hempty]
    · obtain ⟨pair, hpair⟩ :=
        Finset.nonempty_iff_ne_empty.mpr hempty
      have hbaseEq :=
        (mem_rightBaseShapeFiber.mp hpair).2
      have hy := (pair_coordinates_two_le hN pair).2
      have hbase : 2 ≤ base + 1 := by omega
      exact
        card_rightBaseShapeFiber_degree_at_least_three
          hES hN shape hthree hbase

/-! ## One explicit combined finite envelope -/

/--
The largest literal two-singleton shape fibre.  This is exactly the finite
quantity to which the parametrization and Euler-product count of Lemma
17.22 must be applied; shapes of any other total cardinality contribute
zero to this maximum.
-/
noncomputable def twoSingletonShapeFiberMaximum
    (N M A L K : ℕ) : ℕ :=
  (boundedOffsetShapes L K).sup fun shape =>
    if shape.1.card + shape.2.card = 2 then
      (boundedComponentHostsOfShape
        N M A L K shape).card
    else 0

theorem card_twoSingletonShapeFiber_le_maximum
    {N M A L K : ℕ}
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    (hshape : shape ∈ boundedOffsetShapes L K)
    (htotal : shape.1.card + shape.2.card = 2) :
    (boundedComponentHostsOfShape N M A L K shape).card ≤
      twoSingletonShapeFiberMaximum N M A L K := by
  unfold twoSingletonShapeFiberMaximum
  have hle :=
    Finset.le_sup
      (s := boundedOffsetShapes L K)
      (f := fun shape =>
        if shape.1.card + shape.2.card = 2 then
          (boundedComponentHostsOfShape
            N M A L K shape).card
        else 0)
      hshape
  simpa only [if_pos htotal] using hle

/--
Maximum of the two explicit mobile arithmetic sums, over every actual base
and every admissible shape.  It contains no theorem-valued field: it is a
fully concrete finite expression built from divisors, the generalized-Pell
bound and the Evertse--Silverman bound.
-/
noncomputable def mobileArithmeticMaximum
    (K : ℕ) (cLeft cRight : ℝ)
    (N M L : ℕ) : ℕ :=
  (boundedStartBases N M).sup fun base =>
    (boundedOffsetShapes L K).sup fun shape =>
      max
        (leftMobileArithmeticBound K cLeft M base shape)
        (rightMobileArithmeticBound K cRight M base shape)

theorem leftMobileArithmeticBound_le_maximum
    {K N M L base : ℕ} {cLeft cRight : ℝ}
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    (hbase : base ∈ boundedStartBases N M)
    (hshape : shape ∈ boundedOffsetShapes L K) :
    leftMobileArithmeticBound K cLeft M base shape ≤
      mobileArithmeticMaximum K cLeft cRight N M L := by
  unfold mobileArithmeticMaximum
  have hmax :
      leftMobileArithmeticBound K cLeft M base shape ≤
        max
          (leftMobileArithmeticBound K cLeft M base shape)
          (rightMobileArithmeticBound K cRight M base shape) :=
    Nat.le_max_left _ _
  have hshapeSup :
      max
          (leftMobileArithmeticBound K cLeft M base shape)
          (rightMobileArithmeticBound K cRight M base shape) ≤
        (boundedOffsetShapes L K).sup fun shape =>
          max
            (leftMobileArithmeticBound K cLeft M base shape)
            (rightMobileArithmeticBound K cRight M base shape) :=
    Finset.le_sup
      (f := fun shape =>
        max
          (leftMobileArithmeticBound K cLeft M base shape)
          (rightMobileArithmeticBound K cRight M base shape))
      hshape
  exact hmax.trans
    (hshapeSup.trans
      (Finset.le_sup
        (f := fun base =>
          (boundedOffsetShapes L K).sup fun shape =>
            max
              (leftMobileArithmeticBound K cLeft M base shape)
              (rightMobileArithmeticBound K cRight M base shape))
        hbase))

theorem rightMobileArithmeticBound_le_maximum
    {K N M L base : ℕ} {cLeft cRight : ℝ}
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    (hbase : base ∈ boundedStartBases N M)
    (hshape : shape ∈ boundedOffsetShapes L K) :
    rightMobileArithmeticBound K cRight M base shape ≤
      mobileArithmeticMaximum K cLeft cRight N M L := by
  unfold mobileArithmeticMaximum
  have hmax :
      rightMobileArithmeticBound K cRight M base shape ≤
        max
          (leftMobileArithmeticBound K cLeft M base shape)
          (rightMobileArithmeticBound K cRight M base shape) :=
    Nat.le_max_right _ _
  have hshapeSup :
      max
          (leftMobileArithmeticBound K cLeft M base shape)
          (rightMobileArithmeticBound K cRight M base shape) ≤
        (boundedOffsetShapes L K).sup fun shape =>
          max
            (leftMobileArithmeticBound K cLeft M base shape)
            (rightMobileArithmeticBound K cRight M base shape) :=
    Finset.le_sup
      (f := fun shape =>
        max
          (leftMobileArithmeticBound K cLeft M base shape)
          (rightMobileArithmeticBound K cRight M base shape))
      hshape
  exact hmax.trans
    (hshapeSup.trans
      (Finset.le_sup
        (f := fun base =>
          (boundedOffsetShapes L K).sup fun shape =>
            max
              (leftMobileArithmeticBound K cLeft M base shape)
              (rightMobileArithmeticBound K cRight M base shape))
        hbase))

/--
Strongest finite consequence currently available for Lemma 17.23.
After generalized Pell and Evertse--Silverman, every bounded-component host
is bounded by one completely explicit expression:

* the maximum two-singleton fibre, or
* one interval width times the maximum displayed divisor/Pell/ES sum,

followed by the polynomial offset-shape factor.

Thus no unspecified fixed-fibre count remains in the size-at-least-three
branch.
-/
theorem exists_card_boundedComponentHosts_le_explicit_sourceEnvelope
    (hES : EvertseSilvermanAbscissaStatement)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (K : ℕ) :
    ∃ cLeft cRight : ℝ,
      0 ≤ cLeft ∧ 0 ≤ cRight ∧
      ∃ X₀ : ℕ, ∀ (N M A L : ℕ),
        2 ≤ N →
        X₀ ≤ boundedRatioCutoff M L →
        (boundedComponentHosts N M A L K).card ≤
          ((K + 1) * (L + 1) ^ K) ^ 2 *
            max
              (twoSingletonShapeFiberMaximum N M A L K)
              ((M - N) *
                mobileArithmeticMaximum
                  K cLeft cRight N M L) := by
  obtain ⟨cLeft, hcLeft, XLeft, hleft⟩ :=
    exists_card_leftBaseShapeFiber_le_mobileArithmeticBound
      hES hPell K
  obtain ⟨cRight, hcRight, XRight, hright⟩ :=
    exists_card_rightBaseShapeFiber_le_mobileArithmeticBound
      hES hPell K
  refine ⟨cLeft, cRight, hcLeft, hcRight, max XLeft XRight, ?_⟩
  intro N M A L hN hcutoff
  apply card_boundedComponentHosts_le_sourceDisjunction hN
  · intro shape hshape htotal
    exact card_twoSingletonShapeFiber_le_maximum hshape htotal
  · intro shape hshape hdegree base hbase
    exact
      (hleft N M A L base shape hN hdegree
        ((le_max_left _ _).trans hcutoff)).trans
        (leftMobileArithmeticBound_le_maximum hbase hshape)
  · intro shape hshape hdegree base hbase
    exact
      (hright N M A L base shape hN hdegree
        ((le_max_right _ _).trans hcutoff)).trans
        (rightMobileArithmeticBound_le_maximum hbase hshape)

end

end BoundedRatioNonterminalHostCounts
end PaperC
