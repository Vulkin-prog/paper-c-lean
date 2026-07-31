import PaperC.Asymptotics.BoundedRatioNonterminalHostCounts
import PaperC.Diophantine.SingletonProductParametrization
import PaperC.Analysis.PrimeReciprocalSqrtSum
import PaperC.Arithmetic.TerminalKernelCount
import Mathlib.NumberTheory.Harmonic.Bounds

set_option maxHeartbeats 3600000

/-!
# The two-singleton host reduction in Lemma 17.22

A component of support two has one offset in each block.  For fixed offsets
and fixed squarefree smooth component coefficient `d`, this file maps every
literal host injectively to the canonical parameters

`(e,c,u,v)` with

`X = e c u²`, `Y = (d/e)c v²`.

The target is a completely explicit finite set whose inequalities are the
ones summed in the paper.  Summing over `d` gives a finite upper bound for
`twoSingletonShapeFiberMaximum`; no component witness or host predicate is
left in that bound.

The last section records the exact powerset Euler product

`∏_{p≤B}(1+2/√p)`

and its already available prime-sensitive exponential majorant.  The
elementary `(e,c,u,v)` summation is carried out completely: one square
class costs `τ(d) T H_T / √d`, squarefreeness gives
`τ(d)=2^ω(d)`, and summing prime supports recovers the displayed Euler
product.  This yields explicit real bounds both for every fixed shape and
for the complete degree-two host population.  No bridge or opaque
arithmetic hypothesis is introduced.
-/

namespace PaperC
namespace BoundedRatioTwoSingletonHosts

open scoped BigOperators
open Affine
open BoundedRatioComponentHosts
open BoundedRatioComponentNormalization
open BoundedRatioManyDefectsFixedFibers
open BoundedRatioNonterminalHostCounts
open DefectCounting
open LargeOddKernel
open PropositionSixteenOne
open SingletonProductParametrization
open SquarefreeSmoothCount
open TerminalKernelCount
open WeightedDefectCounting

noncomputable section

/-! ## Fixed square class without fixing either start -/

/-- Hosts of one fixed shape carrying the specified component square class. -/
noncomputable def twoSingletonSquareClassFiber
    (N M A L K : ℕ)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (d : ℕ) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact
    (boundedComponentHostsOfShape N M A L K shape).filter
      (CarriesShapeSquareClass
        (N := N) (M := M) (A := A) (L := L) (K := K)
        shape d)

@[simp]
theorem mem_twoSingletonSquareClassFiber
    {N M A L K d : ℕ}
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ twoSingletonSquareClassFiber N M A L K shape d ↔
      pair ∈ boundedComponentHostsOfShape N M A L K shape ∧
      CarriesShapeSquareClass
        (N := N) (M := M) (A := A) (L := L) (K := K)
        shape d pair := by
  simp [twoSingletonSquareClassFiber]

/-- Every fixed-shape host is carried by one of its literal smooth classes. -/
theorem boundedComponentHostsOfShape_subset_squareClassUnion
    {N M A L K : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :
    boundedComponentHostsOfShape N M A L K shape ⊆
      (squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K)).biUnion fun d =>
          twoSingletonSquareClassFiber
            N M A L K shape d := by
  classical
  intro pair hpair
  rcases (mem_boundedComponentHostsOfShape.mp hpair).2 with
    ⟨C, hC, hcard, hleft, hright⟩
  obtain ⟨d, z, _e, _v, hd, hdsq, hdsmooth, hz,
      _he, _hesq, _hv, hwhole, _hrightEq, _heCanonical,
      hdBound, _hleftBound, _hrightBound, _heBound⟩ :=
    exists_normalized_component_equation_with_height
      hN pair hC hcard
  have hdMem :
      d ∈ squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K) := by
    rw [mem_squarefreeSmoothUpTo]
    refine ⟨hd, hdBound, hdsq, ?_⟩
    intro p hp
    exact hdsmooth p
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  apply Finset.mem_biUnion.mpr
  refine ⟨d, hdMem, ?_⟩
  rw [mem_twoSingletonSquareClassFiber]
  refine ⟨hpair, hd, hdsq, hdsmooth, hdBound, ?_⟩
  exact ⟨C, hC, hcard, hleft, hright, z, hz, hwhole⟩

/-! ## Canonical `(e,c,u,v)` container -/

/-- Tuple layout `(e,(c,(u,v)))`. -/
abbrev SingletonParameterTuple := ℕ × (ℕ × (ℕ × ℕ))

/--
The exact finite parameter container used after the canonical
two-singleton factorization.  Besides positivity and `e ∣ d`, the two
reconstructed labels are required to lie below the common cylinder cutoff.
-/
noncomputable def singletonParameterTuples
    (d T : ℕ) : Finset SingletonParameterTuple := by
  classical
  exact
    ((Finset.Icc 1 d).product
      ((Finset.Icc 1 T).product
        ((Finset.Icc 1 (Nat.sqrt T)).product
          (Finset.Icc 1 (Nat.sqrt T))))).filter fun t =>
      t.1 ∣ d ∧
      t.2.1.Coprime d ∧
      t.1 * t.2.1 * t.2.2.1 ^ 2 ≤ T ∧
      (d / t.1) * t.2.1 * t.2.2.2 ^ 2 ≤ T

/--
The root box above fixed divisor split `e` and common part `c`.  Its
cardinality is the product of the two integer square roots appearing in
the paper's harmonic summation.
-/
noncomputable def singletonRootBox
    (d T e c : ℕ) : Finset SingletonParameterTuple := by
  classical
  exact
    ({e} : Finset ℕ).product
      (({c} : Finset ℕ).product
        ((Finset.Icc 1 (Nat.sqrt (T / (e * c)))).product
          (Finset.Icc 1 (Nat.sqrt (T / ((d / e) * c))))))

/-- Union of all root boxes at one fixed divisor split. -/
noncomputable def singletonSummationContainerAt
    (d T e : ℕ) : Finset SingletonParameterTuple := by
  classical
  exact
    (Finset.Icc 1 T).biUnion fun c =>
      singletonRootBox d T e c

/-- The divisor/common-part summation container. -/
noncomputable def singletonSummationContainer
    (d T : ℕ) : Finset SingletonParameterTuple := by
  classical
  exact
    d.divisors.biUnion fun e =>
      singletonSummationContainerAt d T e

/--
Every tuple satisfying the two reconstructed-label inequalities belongs
to its corresponding divisor/common-part root box.
-/
theorem singletonParameterTuples_subset_summationContainer
    {d T : ℕ} (hd : 0 < d) :
    singletonParameterTuples d T ⊆
      singletonSummationContainer d T := by
  classical
  intro t ht
  rcases t with ⟨e, c, u, v⟩
  rw [singletonParameterTuples, Finset.mem_filter] at ht
  rcases ht with
    ⟨htRange, heDiv, _hcCoprime, huBound, hvBound⟩
  rcases Finset.mem_product.mp htRange with ⟨heRange, hcuvRange⟩
  rcases Finset.mem_product.mp hcuvRange with ⟨hcRange, huvRange⟩
  rcases Finset.mem_product.mp huvRange with ⟨huRange, hvRange⟩
  have hePos : 0 < e := (Finset.mem_Icc.mp heRange).1
  have hcPos : 0 < c := (Finset.mem_Icc.mp hcRange).1
  have hecPos : 0 < e * c := Nat.mul_pos hePos hcPos
  have hdePos : 0 < d / e := by
    exact Nat.div_pos (Nat.le_of_dvd hd heDiv) hePos
  have hdecPos : 0 < (d / e) * c :=
    Nat.mul_pos hdePos hcPos
  have huSq :
      u ^ 2 ≤ T / (e * c) := by
    apply (Nat.le_div_iff_mul_le hecPos).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using huBound
  have hvSq :
      v ^ 2 ≤ T / ((d / e) * c) := by
    apply (Nat.le_div_iff_mul_le hdecPos).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hvBound
  rw [singletonSummationContainer]
  apply Finset.mem_biUnion.mpr
  refine
    ⟨e, Nat.mem_divisors.mpr ⟨heDiv, hd.ne'⟩, ?_⟩
  rw [singletonSummationContainerAt]
  apply Finset.mem_biUnion.mpr
  refine ⟨c, hcRange, ?_⟩
  rw [singletonRootBox]
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_singleton.mpr rfl, ?_⟩
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_singleton.mpr rfl, ?_⟩
  apply Finset.mem_product.mpr
  exact
    ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp huRange).1,
          Nat.le_sqrt'.mpr huSq⟩,
      Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hvRange).1,
          Nat.le_sqrt'.mpr hvSq⟩⟩

@[simp]
theorem card_singletonRootBox
    (d T e c : ℕ) :
    (singletonRootBox d T e c).card =
      Nat.sqrt (T / (e * c)) *
        Nat.sqrt (T / ((d / e) * c)) := by
  classical
  simp [singletonRootBox, Nat.card_Icc]

theorem card_singletonSummationContainerAt_le
    (d T e : ℕ) :
    (singletonSummationContainerAt d T e).card ≤
      ∑ c ∈ Finset.Icc 1 T,
        Nat.sqrt (T / (e * c)) *
          Nat.sqrt (T / ((d / e) * c)) := by
  classical
  rw [singletonSummationContainerAt]
  calc
    ((Finset.Icc 1 T).biUnion fun c =>
        singletonRootBox d T e c).card ≤
        ∑ c ∈ Finset.Icc 1 T,
          (singletonRootBox d T e c).card :=
      Finset.card_biUnion_le
    _ =
        ∑ c ∈ Finset.Icc 1 T,
          Nat.sqrt (T / (e * c)) *
            Nat.sqrt (T / ((d / e) * c)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      exact card_singletonRootBox d T e c

theorem card_singletonSummationContainer_le
    (d T : ℕ) :
    (singletonSummationContainer d T).card ≤
      ∑ e ∈ d.divisors,
        ∑ c ∈ Finset.Icc 1 T,
          Nat.sqrt (T / (e * c)) *
            Nat.sqrt (T / ((d / e) * c)) := by
  classical
  rw [singletonSummationContainer]
  calc
    (d.divisors.biUnion fun e =>
        singletonSummationContainerAt d T e).card ≤
        ∑ e ∈ d.divisors,
          (singletonSummationContainerAt d T e).card :=
      Finset.card_biUnion_le
    _ ≤
        ∑ e ∈ d.divisors,
          ∑ c ∈ Finset.Icc 1 T,
            Nat.sqrt (T / (e * c)) *
              Nat.sqrt (T / ((d / e) * c)) :=
      Finset.sum_le_sum fun e _he =>
        card_singletonSummationContainerAt_le d T e

theorem card_singletonParameterTuples_le_rootSum
    {d T : ℕ} (hd : 0 < d) :
    (singletonParameterTuples d T).card ≤
      ∑ e ∈ d.divisors,
        ∑ c ∈ Finset.Icc 1 T,
          Nat.sqrt (T / (e * c)) *
            Nat.sqrt (T / ((d / e) * c)) := by
  calc
    (singletonParameterTuples d T).card ≤
        (singletonSummationContainer d T).card :=
      Finset.card_le_card
        (singletonParameterTuples_subset_summationContainer hd)
    _ ≤ _ := card_singletonSummationContainer_le d T

/-! ## Harmonic estimate for one square class -/

/-- The two root denominators recombine to `c √d`. -/
theorem sqrt_split_denominators
    {d e c : ℕ} (he : e ∣ d) :
    Real.sqrt ((e * c : ℕ) : ℝ) *
        Real.sqrt (((d / e) * c : ℕ) : ℝ) =
      (c : ℝ) * Real.sqrt d := by
  calc
    Real.sqrt ((e * c : ℕ) : ℝ) *
          Real.sqrt (((d / e) * c : ℕ) : ℝ) =
        (Real.sqrt (e : ℝ) * Real.sqrt (c : ℝ)) *
          (Real.sqrt ((d / e : ℕ) : ℝ) *
            Real.sqrt (c : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg e),
        Real.sqrt_mul (Nat.cast_nonneg (d / e))]
    _ =
        (Real.sqrt (e : ℝ) *
            Real.sqrt ((d / e : ℕ) : ℝ)) *
          (Real.sqrt (c : ℝ) * Real.sqrt (c : ℝ)) := by
      ring
    _ =
        Real.sqrt ((e * (d / e) : ℕ) : ℝ) *
          (c : ℝ) := by
      rw [Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg e),
        Real.mul_self_sqrt (Nat.cast_nonneg c)]
    _ = (c : ℝ) * Real.sqrt d := by
      rw [Nat.mul_div_cancel' he]
      ring

/--
One `(e,c)` root box costs at most `T/(c√d)` after casting to the
reals.
-/
theorem cast_rootPair_le_harmonicWeight
    {d T e c : ℕ} (hd : 0 < d)
    (he : e ∈ d.divisors)
    (hc : c ∈ Finset.Icc 1 T) :
    ((Nat.sqrt (T / (e * c)) *
        Nat.sqrt (T / ((d / e) * c)) : ℕ) : ℝ) ≤
      (T : ℝ) * (c : ℝ)⁻¹ * (Real.sqrt d)⁻¹ := by
  have heDiv : e ∣ d :=
    Nat.dvd_of_mem_divisors he
  have hePos : 0 < e :=
    Nat.pos_of_dvd_of_pos heDiv hd
  have hcPos : 0 < c :=
    (Finset.mem_Icc.mp hc).1
  have hdePos : 0 < d / e :=
    Nat.div_pos (Nat.le_of_dvd hd heDiv) hePos
  have hleft :=
    cast_sqrt_div_le T (e * c)
  have hright :=
    cast_sqrt_div_le T ((d / e) * c)
  have hsqrtT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hleftInv :
      0 ≤ (Real.sqrt ((e * c : ℕ) : ℝ))⁻¹ := by
    positivity
  have hrightInv :
      0 ≤ (Real.sqrt (((d / e) * c : ℕ) : ℝ))⁻¹ := by
    positivity
  rw [Nat.cast_mul]
  calc
    (Nat.sqrt (T / (e * c)) : ℝ) *
          (Nat.sqrt (T / ((d / e) * c)) : ℝ) ≤
        (Real.sqrt T *
            (Real.sqrt ((e * c : ℕ) : ℝ))⁻¹) *
          (Real.sqrt T *
            (Real.sqrt (((d / e) * c : ℕ) : ℝ))⁻¹) :=
      mul_le_mul hleft hright
        (Nat.cast_nonneg _)
        (mul_nonneg hsqrtT hleftInv)
    _ =
        (Real.sqrt T * Real.sqrt T) *
          (Real.sqrt ((e * c : ℕ) : ℝ) *
            Real.sqrt (((d / e) * c : ℕ) : ℝ))⁻¹ := by
      rw [mul_inv_rev]
      ring
    _ =
        (T : ℝ) *
          ((c : ℝ) * Real.sqrt d)⁻¹ := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg T),
        sqrt_split_denominators heDiv]
    _ = (T : ℝ) * (c : ℝ)⁻¹ * (Real.sqrt d)⁻¹ := by
      rw [mul_inv_rev]
      ring

/-- The common-part sum is exactly the rational harmonic number. -/
theorem sum_harmonicWeights
    (T d : ℕ) :
    (∑ c ∈ Finset.Icc 1 T,
        (T : ℝ) * (c : ℝ)⁻¹ *
          (Real.sqrt d)⁻¹) =
      (T : ℝ) * (harmonic T : ℝ) *
        (Real.sqrt d)⁻¹ := by
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum,
    Rat.cast_inv, Rat.cast_natCast]

/--
Harmonic estimate for the complete canonical parameter container of one
positive square class.
-/
theorem card_singletonParameterTuples_cast_le_harmonic
    {d T : ℕ} (hd : 0 < d) :
    ((singletonParameterTuples d T).card : ℝ) ≤
      (d.divisors.card : ℝ) *
        ((T : ℝ) * (harmonic T : ℝ) *
          (Real.sqrt d)⁻¹) := by
  have hroot :=
    card_singletonParameterTuples_le_rootSum
      (d := d) (T := T) hd
  calc
    ((singletonParameterTuples d T).card : ℝ) ≤
        (∑ e ∈ d.divisors,
          ∑ c ∈ Finset.Icc 1 T,
            Nat.sqrt (T / (e * c)) *
              Nat.sqrt (T / ((d / e) * c)) : ℕ) := by
      exact_mod_cast hroot
    _ =
        ∑ e ∈ d.divisors,
          ∑ c ∈ Finset.Icc 1 T,
            ((Nat.sqrt (T / (e * c)) *
              Nat.sqrt (T / ((d / e) * c)) : ℕ) : ℝ) := by
      norm_cast
    _ ≤
        ∑ e ∈ d.divisors,
          ∑ c ∈ Finset.Icc 1 T,
            (T : ℝ) * (c : ℝ)⁻¹ *
              (Real.sqrt d)⁻¹ := by
      exact Finset.sum_le_sum fun e he =>
        Finset.sum_le_sum fun c hc =>
          cast_rootPair_le_harmonicWeight hd he hc
    _ =
        ∑ _e ∈ d.divisors,
          ((T : ℝ) * (harmonic T : ℝ) *
            (Real.sqrt d)⁻¹) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact sum_harmonicWeights T d
    _ =
        (d.divisors.card : ℝ) *
          ((T : ℝ) * (harmonic T : ℝ) *
            (Real.sqrt d)⁻¹) := by
      simp

/-- A positive squarefree integer has exactly two divisor choices per prime. -/
theorem card_divisors_eq_two_pow_primeFactors_card
    {d : ℕ} (hd : Squarefree d) :
    d.divisors.card = 2 ^ d.primeFactors.card := by
  rw [Nat.card_divisors hd.ne_zero]
  calc
    ∏ p ∈ d.primeFactors,
          (d.factorization p + 1) =
        ∏ _p ∈ d.primeFactors, 2 := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree
        hd (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = 2 ^ d.primeFactors.card := by
      simp

/--
The divisor count divided by `√d` is exactly the support weight used in
the two-singleton Euler product.
-/
theorem squarefree_divisorWeight_eq_supportWeight
    {d : ℕ} (hd : Squarefree d) :
    (d.divisors.card : ℝ) * (Real.sqrt d)⁻¹ =
      ∏ p ∈ d.primeFactors,
        (2 * (Real.sqrt p)⁻¹) := by
  have hdProd :
      ∏ p ∈ d.primeFactors, p = d :=
    Nat.prod_primeFactors_of_squarefree hd
  have hsqrt :
      Real.sqrt (d : ℝ) =
        ∏ p ∈ d.primeFactors, Real.sqrt p := by
    calc
      Real.sqrt (d : ℝ) =
          Real.sqrt
            ((d.primeFactors.prod id : ℕ) : ℝ) := by
        congr 1
        norm_cast
        simpa only [id_eq] using hdProd.symm
      _ = ∏ p ∈ d.primeFactors, Real.sqrt p :=
        sqrt_natCast_prod d.primeFactors
  rw [card_divisors_eq_two_pow_primeFactors_card hd,
    Nat.cast_pow, Nat.cast_ofNat, hsqrt]
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_inv_distrib]

/-- Canonical parameters attached to the two actual singleton labels. -/
noncomputable def singletonParameterMap
    {N M L : ℕ} (i j : Fin (L + 1)) (d : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) :
    SingletonParameterTuple :=
  let X := startCompleteVertexLabel pair.1.1 L i
  let Y := startCompleteVertexLabel pair.1.2 L j
  (canonicalDPart X d,
    (canonicalCommonPart X d,
      (canonicalFirstRoot X, canonicalSecondRoot Y)))

/-- The fixed-offset labels are positive and lie below `M+L`. -/
theorem singletonLabels_pos_le_cutoff
    {N M L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (i j : Fin (L + 1)) :
    0 < startCompleteVertexLabel pair.1.1 L i ∧
      startCompleteVertexLabel pair.1.1 L i ≤
        boundedRatioCutoff M L ∧
      0 < startCompleteVertexLabel pair.1.2 L j ∧
      startCompleteVertexLabel pair.1.2 L j ≤
        boundedRatioCutoff M L := by
  have hcoords := pair_coordinates_two_le hN pair
  refine
    ⟨RationalChannelCode.startCompleteVertexLabel_pos
        hcoords.1 i,
      ?_,
      RationalChannelCode.startCompleteVertexLabel_pos
        hcoords.2 j,
      ?_⟩
  · simpa only [leftOccurrenceFactor] using
      leftOccurrenceFactor_le_cutoff hN pair (Sum.inl i)
  · simpa only [rightOccurrenceFactor] using
      rightOccurrenceFactor_le_cutoff hN pair (Sum.inr j)

/--
For singleton offset sets, membership in the square-class fibre supplies
the literal equation between the two selected labels.
-/
theorem singletonLabelProduct_eq_squareClass
    {N M A L K d : ℕ}
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {i j : Fin (L + 1)}
    (hshape : shape = ({i}, {j}))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ twoSingletonSquareClassFiber
        N M A L K shape d) :
    0 < d ∧ Squarefree d ∧
      ∃ z : ℕ, 0 < z ∧
        startCompleteVertexLabel pair.1.1 L i *
            startCompleteVertexLabel pair.1.2 L j =
          d * z ^ 2 := by
  rcases (mem_twoSingletonSquareClassFiber.mp hpair).2 with
    ⟨hd, hdsq, _hdsmooth, _hdBound,
      C, hC, _hcard, hleft, hright, z, hz, hwhole⟩
  refine ⟨hd, hdsq, z, hz, ?_⟩
  have hleftProduct :
      componentLeftProduct pair.1.1 pair.1.2 L C =
        startCompleteVertexLabel pair.1.1 L i := by
    rw [componentLeftProduct_eq_offsetProduct, hleft, hshape]
    simp
  have hrightProduct :
      componentRightProduct pair.1.1 pair.1.2 L C =
        startCompleteVertexLabel pair.1.2 L j := by
    rw [componentRightProduct_eq_offsetProduct, hright, hshape]
    simp
  rw [← hleftProduct, ← hrightProduct]
  exact hwhole

theorem singletonParameterMap_mem
    {N M A L K d : ℕ} (hN : 2 ≤ N)
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {i j : Fin (L + 1)}
    (hshape : shape = ({i}, {j}))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ twoSingletonSquareClassFiber
        N M A L K shape d) :
    singletonParameterMap i j d pair ∈
      singletonParameterTuples d (boundedRatioCutoff M L) := by
  let X := startCompleteVertexLabel pair.1.1 L i
  let Y := startCompleteVertexLabel pair.1.2 L j
  obtain ⟨hd, hdsq, z, hz, hequation⟩ :=
    singletonLabelProduct_eq_squareClass hshape hpair
  have hlabels := singletonLabels_pos_le_cutoff hN pair i j
  have hX : 0 < X := by simpa only [X] using hlabels.1
  have hXT : X ≤ boundedRatioCutoff M L := by
    simpa only [X] using hlabels.2.1
  have hY : 0 < Y := by simpa only [Y] using hlabels.2.2.1
  have hYT : Y ≤ boundedRatioCutoff M L := by
    simpa only [Y] using hlabels.2.2.2
  have hfactor :=
    canonical_factorizations hX hY hd hz hdsq
      (by simpa only [X, Y] using hequation)
  have hePos := canonicalDPart_pos (X := X) hd
  have hcPos := canonicalCommonPart_pos (X := X) hd
  have huPos :
      0 < canonicalFirstRoot X :=
    Nat.pos_of_ne_zero (canonicalSquarePart_ne_zero hX.ne')
  have hvPos :
      0 < canonicalSecondRoot Y :=
    Nat.pos_of_ne_zero (canonicalSquarePart_ne_zero hY.ne')
  have heLe := canonicalDPart_le (X := X) hd
  have hcLe : canonicalCommonPart X d ≤ boundedRatioCutoff M L :=
    (canonicalCommonPart_le_first hX).trans hXT
  have huLe : canonicalFirstRoot X ≤
      Nat.sqrt (boundedRatioCutoff M L) :=
    (canonicalFirstRoot_le_sqrt hX).trans
      (Nat.sqrt_le_sqrt hXT)
  have hvLe : canonicalSecondRoot Y ≤
      Nat.sqrt (boundedRatioCutoff M L) :=
    (canonicalSecondRoot_le_sqrt hY).trans
      (Nat.sqrt_le_sqrt hYT)
  change
    (canonicalDPart X d,
      (canonicalCommonPart X d,
        (canonicalFirstRoot X, canonicalSecondRoot Y))) ∈
      singletonParameterTuples d (boundedRatioCutoff M L)
  change
    (canonicalDPart X d,
      (canonicalCommonPart X d,
        (canonicalFirstRoot X, canonicalSecondRoot Y))) ∈
      (((Finset.Icc 1 d).product
        ((Finset.Icc 1 (boundedRatioCutoff M L)).product
          ((Finset.Icc 1 (Nat.sqrt (boundedRatioCutoff M L))).product
            (Finset.Icc 1 (Nat.sqrt (boundedRatioCutoff M L)))))).filter
        fun t : SingletonParameterTuple =>
          t.1 ∣ d ∧
          t.2.1.Coprime d ∧
          t.1 * t.2.1 * t.2.2.1 ^ 2 ≤ boundedRatioCutoff M L ∧
          (d / t.1) * t.2.1 * t.2.2.2 ^ 2 ≤
            boundedRatioCutoff M L)
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hePos, heLe⟩, ?_⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hcPos, hcLe⟩, ?_⟩
    apply Finset.mem_product.mpr
    exact
      ⟨Finset.mem_Icc.mpr ⟨huPos, huLe⟩,
        Finset.mem_Icc.mpr ⟨hvPos, hvLe⟩⟩
  · dsimp only [Prod.fst, Prod.snd]
    refine
      ⟨canonicalDPart_dvd_right X d,
        canonicalCommonPart_coprime hd,
        ?_, ?_⟩
    · calc
        canonicalDPart X d * canonicalCommonPart X d *
              canonicalFirstRoot X ^ 2 =
            X := hfactor.1.symm
        _ ≤ boundedRatioCutoff M L := hXT
    · calc
        d / canonicalDPart X d * canonicalCommonPart X d *
              canonicalSecondRoot Y ^ 2 =
            Y := hfactor.2.symm
        _ ≤ boundedRatioCutoff M L := hYT

/-- At one fixed offset, equality of positive complete labels fixes the start. -/
private theorem start_eq_of_singletonLabel_eq
    {L x y : ℕ} (i : Fin (L + 1))
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hlabel :
      startCompleteVertexLabel x L i =
        startCompleteVertexLabel y L i) :
    x = y := by
  simp only [startCompleteVertexLabel] at hlabel
  split at hlabel <;> omega

theorem singletonParameterMap_injective_on
    {N M A L K d : ℕ} (hN : 2 ≤ N)
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {i j : Fin (L + 1)}
    (hshape : shape = ({i}, {j})) :
    Set.InjOn (singletonParameterMap i j d)
      (twoSingletonSquareClassFiber
        N M A L K shape d : Set
          (SeparatedBoundedRatioPair N M L)) := by
  intro u hu v hv huv
  let Xu := startCompleteVertexLabel u.1.1 L i
  let Yu := startCompleteVertexLabel u.1.2 L j
  let Xv := startCompleteVertexLabel v.1.1 L i
  let Yv := startCompleteVertexLabel v.1.2 L j
  obtain ⟨hd, hdsq, zu, hzu, hequ⟩ :=
    singletonLabelProduct_eq_squareClass hshape hu
  obtain ⟨_hdv, _hdsqv, zv, hzv, heqv⟩ :=
    singletonLabelProduct_eq_squareClass hshape hv
  have huLabels := singletonLabels_pos_le_cutoff hN u i j
  have hvLabels := singletonLabels_pos_le_cutoff hN v i j
  have hXu : 0 < Xu := by simpa only [Xu] using huLabels.1
  have hYu : 0 < Yu := by simpa only [Yu] using huLabels.2.2.1
  have hXv : 0 < Xv := by simpa only [Xv] using hvLabels.1
  have hYv : 0 < Yv := by simpa only [Yv] using hvLabels.2.2.1
  have hfu :=
    canonical_factorizations hXu hYu hd hzu hdsq
      (by simpa only [Xu, Yu] using hequ)
  have hfv :=
    canonical_factorizations hXv hYv hd hzv hdsq
      (by simpa only [Xv, Yv] using heqv)
  have he :
      canonicalDPart Xu d = canonicalDPart Xv d := by
    simpa only [singletonParameterMap, Xu, Yu, Xv, Yv] using
      congrArg (fun t : SingletonParameterTuple => t.1) huv
  have hc :
      canonicalCommonPart Xu d = canonicalCommonPart Xv d := by
    simpa only [singletonParameterMap, Xu, Yu, Xv, Yv] using
      congrArg (fun t : SingletonParameterTuple => t.2.1) huv
  have huRoot :
      canonicalFirstRoot Xu = canonicalFirstRoot Xv := by
    simpa only [singletonParameterMap, Xu, Yu, Xv, Yv] using
      congrArg (fun t : SingletonParameterTuple => t.2.2.1) huv
  have hvRoot :
      canonicalSecondRoot Yu = canonicalSecondRoot Yv := by
    simpa only [singletonParameterMap, Xu, Yu, Xv, Yv] using
      congrArg (fun t : SingletonParameterTuple => t.2.2.2) huv
  have hXeq : Xu = Xv := by
    calc
      Xu =
          canonicalDPart Xu d * canonicalCommonPart Xu d *
            canonicalFirstRoot Xu ^ 2 := hfu.1
      _ =
          canonicalDPart Xv d * canonicalCommonPart Xv d *
            canonicalFirstRoot Xv ^ 2 := by
        rw [he, hc, huRoot]
      _ = Xv := hfv.1.symm
  have hYeq : Yu = Yv := by
    calc
      Yu =
          (d / canonicalDPart Xu d) *
            canonicalCommonPart Xu d *
              canonicalSecondRoot Yu ^ 2 := hfu.2
      _ =
          (d / canonicalDPart Xv d) *
            canonicalCommonPart Xv d *
              canonicalSecondRoot Yv ^ 2 := by
        rw [he, hc, hvRoot]
      _ = Yv := hfv.2.symm
  have hx :
      u.1.1 = v.1.1 :=
    start_eq_of_singletonLabel_eq i
      (show 1 ≤ u.1.1 by
        exact (pair_coordinates_two_le hN u).1.trans' (by omega))
      (show 1 ≤ v.1.1 by
        exact (pair_coordinates_two_le hN v).1.trans' (by omega))
      (by simpa only [Xu, Xv] using hXeq)
  have hy :
      u.1.2 = v.1.2 :=
    start_eq_of_singletonLabel_eq j
      (show 1 ≤ u.1.2 by
        exact (pair_coordinates_two_le hN u).2.trans' (by omega))
      (show 1 ≤ v.1.2 by
        exact (pair_coordinates_two_le hN v).2.trans' (by omega))
      (by simpa only [Yu, Yv] using hYeq)
  exact Subtype.ext (Prod.ext hx hy)

theorem card_twoSingletonSquareClassFiber_le_parameters
    {N M A L K d : ℕ} (hN : 2 ≤ N)
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {i j : Fin (L + 1)}
    (hshape : shape = ({i}, {j})) :
    (twoSingletonSquareClassFiber
        N M A L K shape d).card ≤
      (singletonParameterTuples
        d (boundedRatioCutoff M L)).card := by
  classical
  let f : SeparatedBoundedRatioPair N M L →
      SingletonParameterTuple :=
    singletonParameterMap i j d
  let source :=
    twoSingletonSquareClassFiber N M A L K shape d
  have himage :
      source.image f ⊆
        singletonParameterTuples d (boundedRatioCutoff M L) := by
    intro t ht
    obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp ht
    exact singletonParameterMap_mem hN hshape hpair
  calc
    source.card = (source.image f).card := by
      symm
      exact Finset.card_image_of_injOn
        (singletonParameterMap_injective_on hN hshape)
    _ ≤
        (singletonParameterTuples
          d (boundedRatioCutoff M L)).card :=
      Finset.card_le_card himage

/-! ## Summation over the smooth square class -/

/-- The completely explicit finite count left by the parametrization. -/
noncomputable def twoSingletonParameterCount
    (M L K : ℕ) : ℕ :=
  ∑ d ∈ squarefreeSmoothUpTo
      (L + 1) (boundedRatioCutoff M L ^ K),
    (singletonParameterTuples
      d (boundedRatioCutoff M L)).card

theorem card_twoSingletonShapeFiber_le_parameterCount
    {N M A L K : ℕ} (hN : 2 ≤ N)
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    (hshape : shape ∈ boundedOffsetShapes L K)
    (htotal : shape.1.card + shape.2.card = 2) :
    (boundedComponentHostsOfShape N M A L K shape).card ≤
      twoSingletonParameterCount M L K := by
  classical
  obtain ⟨hleft, hright⟩ :=
    shape_total_card_two_iff_singletons hshape htotal
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hleft
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hright
  have hshapeEq : shape = ({i}, {j}) := by
    apply Prod.ext
    · exact hi
    · exact hj
  unfold twoSingletonParameterCount
  calc
    (boundedComponentHostsOfShape N M A L K shape).card ≤
        ((squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K)).biUnion fun d =>
            twoSingletonSquareClassFiber
              N M A L K shape d).card :=
      Finset.card_le_card
        (boundedComponentHostsOfShape_subset_squareClassUnion
          hN shape)
    _ ≤
        ∑ d ∈ squarefreeSmoothUpTo
            (L + 1) (boundedRatioCutoff M L ^ K),
          (twoSingletonSquareClassFiber
            N M A L K shape d).card :=
      Finset.card_biUnion_le
    _ ≤
        ∑ d ∈ squarefreeSmoothUpTo
            (L + 1) (boundedRatioCutoff M L ^ K),
          (singletonParameterTuples
            d (boundedRatioCutoff M L)).card :=
      Finset.sum_le_sum fun d _hd =>
        card_twoSingletonSquareClassFiber_le_parameters
          hN hshapeEq

theorem twoSingletonShapeFiberMaximum_le_parameterCount
    {N M A L K : ℕ} (hN : 2 ≤ N) :
    twoSingletonShapeFiberMaximum N M A L K ≤
      twoSingletonParameterCount M L K := by
  unfold twoSingletonShapeFiberMaximum
  apply Finset.sup_le
  intro shape hshape
  by_cases htotal : shape.1.card + shape.2.card = 2
  · rw [if_pos htotal]
    exact card_twoSingletonShapeFiber_le_parameterCount
      hN hshape htotal
  · simp [htotal]

/--
For `K = 2`, nonemptiness of both sides forces every admissible shape to
be exactly a pair of singletons.  Thus the explicit parameter count already
controls the complete bounded-component host population.
-/
theorem card_boundedComponentHosts_two_le_parameterCount
    {N M A L : ℕ} (hN : 2 ≤ N) :
    (boundedComponentHosts N M A L 2).card ≤
      ((3 * (L + 1) ^ 2) ^ 2) *
        twoSingletonParameterCount M L 2 := by
  apply card_boundedComponentHosts_le_of_shapeFibers hN
  intro shape hshape
  have hdata := mem_boundedOffsetShapes.mp hshape
  have hleftPos : 0 < shape.1.card :=
    Finset.card_pos.mpr hdata.1
  have hrightPos : 0 < shape.2.card :=
    Finset.card_pos.mpr hdata.2.1
  have htotal : shape.1.card + shape.2.card = 2 := by
    omega
  exact
    card_twoSingletonShapeFiber_le_parameterCount
      hN hshape htotal

/-! ## The exact Euler product in the paper -/

/-- The Euler factor produced by summing the divisor split `e ∣ d`. -/
noncomputable def twoSingletonEulerProduct (B : ℕ) : ℝ :=
  ∏ p ∈ smallPrimesUpTo B,
    (1 + 2 * (Real.sqrt p)⁻¹)

/--
Powerset expansion of the exact Euler product.  A support contributes
`2^|S| / √(∏S)`, corresponding to the choices of the divisor `e ∣ d`.
-/
theorem sum_supportWeights_eq_twoSingletonEulerProduct (B : ℕ) :
    (∑ support ∈ (smallPrimesUpTo B).powerset,
        ∏ p ∈ support, (2 * (Real.sqrt p)⁻¹)) =
      twoSingletonEulerProduct B := by
  unfold twoSingletonEulerProduct
  exact
    (Finset.prod_one_add
      (s := smallPrimesUpTo B)
      (f := fun p : ℕ => 2 * (Real.sqrt p)⁻¹)).symm

/--
Summing the exact squarefree divisor weights over all smooth square
classes is bounded by the powerset Euler product.
-/
theorem sum_squarefreeSmooth_divisorWeights_le_eulerProduct
    (B X : ℕ) :
    (∑ d ∈ squarefreeSmoothUpTo B X,
        (d.divisors.card : ℝ) *
          (Real.sqrt d)⁻¹) ≤
      twoSingletonEulerProduct B := by
  classical
  let supports : Finset (Finset ℕ) :=
    (squarefreeSmoothUpTo B X).image
      (fun d : ℕ => d.primeFactors)
  have hsupports :
      supports ⊆ (smallPrimesUpTo B).powerset := by
    intro support hsupport
    obtain ⟨d, hd, rfl⟩ :=
      Finset.mem_image.mp hsupport
    exact Finset.mem_powerset.mpr
      (primeFactors_subset_smallPrimesUpTo hd)
  calc
    (∑ d ∈ squarefreeSmoothUpTo B X,
        (d.divisors.card : ℝ) *
          (Real.sqrt d)⁻¹) =
        ∑ d ∈ squarefreeSmoothUpTo B X,
          ∏ p ∈ d.primeFactors,
            (2 * (Real.sqrt p)⁻¹) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact squarefree_divisorWeight_eq_supportWeight
        (mem_squarefreeSmoothUpTo.mp hd).2.2.1
    _ =
        ∑ support ∈ supports,
          ∏ p ∈ support,
            (2 * (Real.sqrt p)⁻¹) := by
      symm
      dsimp only [supports]
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact
        primeFactors_injective_on_squarefreeSmoothUpTo B X
          ha hb hab
    _ ≤
        ∑ support ∈ (smallPrimesUpTo B).powerset,
          ∏ p ∈ support,
            (2 * (Real.sqrt p)⁻¹) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        hsupports
        (fun support _hsupport _hmissing => by positivity)
    _ = twoSingletonEulerProduct B :=
      sum_supportWeights_eq_twoSingletonEulerProduct B

/--
Finite harmonic/Euler bound for the complete two-singleton parameter
count.
-/
theorem twoSingletonParameterCount_cast_le_harmonicEuler
    (M L K : ℕ) :
    (twoSingletonParameterCount M L K : ℝ) ≤
      (boundedRatioCutoff M L : ℝ) *
        (harmonic (boundedRatioCutoff M L) : ℝ) *
          twoSingletonEulerProduct (L + 1) := by
  let T := boundedRatioCutoff M L
  let S :=
    squarefreeSmoothUpTo (L + 1) (T ^ K)
  calc
    (twoSingletonParameterCount M L K : ℝ) =
        ∑ d ∈ S,
          ((singletonParameterTuples d T).card : ℝ) := by
      simp only [twoSingletonParameterCount, T, S,
        Nat.cast_sum]
    _ ≤
        ∑ d ∈ S,
          (d.divisors.card : ℝ) *
            ((T : ℝ) * (harmonic T : ℝ) *
              (Real.sqrt d)⁻¹) := by
      exact Finset.sum_le_sum fun d hd =>
        card_singletonParameterTuples_cast_le_harmonic
          (mem_squarefreeSmoothUpTo.mp hd).1
    _ =
        ((T : ℝ) * (harmonic T : ℝ)) *
          (∑ d ∈ S,
            (d.divisors.card : ℝ) *
              (Real.sqrt d)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ ≤
        ((T : ℝ) * (harmonic T : ℝ)) *
          twoSingletonEulerProduct (L + 1) := by
      apply mul_le_mul_of_nonneg_left
        (sum_squarefreeSmooth_divisorWeights_le_eulerProduct
          (L + 1) (T ^ K))
      apply mul_nonneg (Nat.cast_nonneg _)
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum,
        Rat.cast_inv, Rat.cast_natCast]
      positivity
    _ =
        (boundedRatioCutoff M L : ℝ) *
          (harmonic (boundedRatioCutoff M L) : ℝ) *
            twoSingletonEulerProduct (L + 1) := by
      rfl

/-- Logarithmic form of the finite harmonic/Euler bound. -/
theorem twoSingletonParameterCount_cast_le_logEuler
    (M L K : ℕ) :
    (twoSingletonParameterCount M L K : ℝ) ≤
      (boundedRatioCutoff M L : ℝ) *
        (1 + Real.log (boundedRatioCutoff M L)) *
          twoSingletonEulerProduct (L + 1) := by
  refine
    (twoSingletonParameterCount_cast_le_harmonicEuler
      M L K).trans ?_
  have hH :
      (harmonic (boundedRatioCutoff M L) : ℝ) ≤
        1 + Real.log (boundedRatioCutoff M L) :=
    harmonic_le_one_add_log _
  have hT :
      0 ≤ (boundedRatioCutoff M L : ℝ) := by
    positivity
  have hEuler :
      0 ≤ twoSingletonEulerProduct (L + 1) := by
    unfold twoSingletonEulerProduct
    positivity
  apply mul_le_mul_of_nonneg_right _ hEuler
  exact mul_le_mul_of_nonneg_left hH hT

/-- The factor `1+2x` is bounded by `(1+x)²`, prime by prime. -/
theorem twoSingletonEulerProduct_le_square (B : ℕ) :
    twoSingletonEulerProduct B ≤
      (∏ p ∈ smallPrimesUpTo B,
        (1 + (Real.sqrt p)⁻¹)) ^ 2 := by
  unfold twoSingletonEulerProduct
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hx : 0 ≤ (Real.sqrt p)⁻¹ := by positivity
    nlinarith [sq_nonneg ((Real.sqrt p)⁻¹)]

/--
Prime-sensitive completion of the source Euler product.  Its exponent is
`O(√B/log B)` (with the already formalized explicit lower-order root term).
-/
theorem twoSingletonEulerProduct_le_primeSensitive
    {B : ℕ} (hB : 16 ≤ B) :
    twoSingletonEulerProduct B ≤
      Real.exp
        (2 *
          (2 * Real.sqrt (PrimeReciprocalSqrtSum.rootCutoff B) +
            56 * Real.sqrt (2 * B) /
              ((Nat.log 2 B / 2 : ℕ) : ℝ))) := by
  let P : ℝ :=
    ∏ p ∈ smallPrimesUpTo B,
      (1 + (Real.sqrt p)⁻¹)
  let E : ℝ :=
    2 * Real.sqrt (PrimeReciprocalSqrtSum.rootCutoff B) +
      56 * Real.sqrt (2 * B) /
        ((Nat.log 2 B / 2 : ℕ) : ℝ)
  have hP :
      P ≤ Real.exp E := by
    simpa only [P, E] using
      PrimeReciprocalSqrtSum.prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive_two_mul
        hB
  have hPnonneg : 0 ≤ P := by
    dsimp only [P]
    positivity
  calc
    twoSingletonEulerProduct B ≤ P ^ 2 :=
      twoSingletonEulerProduct_le_square B
    _ ≤ (Real.exp E) ^ 2 :=
      pow_le_pow_left₀ hPnonneg hP 2
    _ = Real.exp (2 * E) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ =
        Real.exp
          (2 *
            (2 * Real.sqrt (PrimeReciprocalSqrtSum.rootCutoff B) +
              56 * Real.sqrt (2 * B) /
                ((Nat.log 2 B / 2 : ℕ) : ℝ))) := by
      rfl

/--
Prime-sensitive explicit numerical form.  The exponent is the existing
`O(√B/log B)` bound with `B = L+1`.
-/
theorem twoSingletonParameterCount_cast_le_primeSensitive
    {M L K : ℕ} (hB : 16 ≤ L + 1) :
    (twoSingletonParameterCount M L K : ℝ) ≤
      (boundedRatioCutoff M L : ℝ) *
        (1 + Real.log (boundedRatioCutoff M L)) *
          Real.exp
            (2 *
              (2 * Real.sqrt
                    (PrimeReciprocalSqrtSum.rootCutoff (L + 1)) +
                56 *
                    Real.sqrt ((2 * (L + 1) : ℕ) : ℝ) /
                  ((Nat.log 2 (L + 1) / 2 : ℕ) : ℝ))) := by
  calc
    (twoSingletonParameterCount M L K : ℝ) ≤
        (boundedRatioCutoff M L : ℝ) *
          (1 + Real.log (boundedRatioCutoff M L)) *
            twoSingletonEulerProduct (L + 1) :=
      twoSingletonParameterCount_cast_le_logEuler M L K
    _ ≤
        (boundedRatioCutoff M L : ℝ) *
          (1 + Real.log (boundedRatioCutoff M L)) *
            Real.exp
              (2 *
                (2 * Real.sqrt
                      (PrimeReciprocalSqrtSum.rootCutoff (L + 1)) +
                  56 *
                    Real.sqrt ((2 * (L + 1) : ℕ) : ℝ) /
                    ((Nat.log 2 (L + 1) / 2 : ℕ) : ℝ))) := by
      have hEulerBound :
          twoSingletonEulerProduct (L + 1) ≤
            Real.exp
              (2 *
                (2 * Real.sqrt
                      (PrimeReciprocalSqrtSum.rootCutoff (L + 1)) +
                  56 *
                      Real.sqrt ((2 * (L + 1) : ℕ) : ℝ) /
                    ((Nat.log 2 (L + 1) / 2 : ℕ) : ℝ))) := by
        simpa only [Nat.cast_mul, Nat.cast_add,
          Nat.cast_ofNat, Nat.cast_one] using
          (twoSingletonEulerProduct_le_primeSensitive hB)
      apply mul_le_mul_of_nonneg_left
        hEulerBound
      have hHnonneg :
          0 ≤
            (harmonic (boundedRatioCutoff M L) : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum,
          Rat.cast_inv, Rat.cast_natCast]
        positivity
      have hlog :
          0 ≤ 1 + Real.log (boundedRatioCutoff M L) :=
        hHnonneg.trans (harmonic_le_one_add_log _)
      exact mul_nonneg (Nat.cast_nonneg _) hlog

/-- Prime-sensitive envelope for every fixed two-singleton shape. -/
theorem twoSingletonShapeFiberMaximum_cast_le_primeSensitive
    {N M A L K : ℕ} (hN : 2 ≤ N)
    (hB : 16 ≤ L + 1) :
    (twoSingletonShapeFiberMaximum N M A L K : ℝ) ≤
      (boundedRatioCutoff M L : ℝ) *
        (1 + Real.log (boundedRatioCutoff M L)) *
          Real.exp
            (2 *
              (2 * Real.sqrt
                    (PrimeReciprocalSqrtSum.rootCutoff (L + 1)) +
                56 *
                    Real.sqrt ((2 * (L + 1) : ℕ) : ℝ) /
                  ((Nat.log 2 (L + 1) / 2 : ℕ) : ℝ))) := by
  calc
    (twoSingletonShapeFiberMaximum N M A L K : ℝ) ≤
        (twoSingletonParameterCount M L K : ℝ) := by
      exact_mod_cast
        twoSingletonShapeFiberMaximum_le_parameterCount hN
    _ ≤ _ :=
      twoSingletonParameterCount_cast_le_primeSensitive hB

/--
Fully explicit prime-sensitive bound for all bounded component hosts in
degree two.
-/
theorem card_boundedComponentHosts_two_cast_le_primeSensitive
    {N M A L : ℕ} (hN : 2 ≤ N)
    (hB : 16 ≤ L + 1) :
    ((boundedComponentHosts N M A L 2).card : ℝ) ≤
      (((3 * (L + 1) ^ 2) ^ 2 : ℕ) : ℝ) *
        ((boundedRatioCutoff M L : ℝ) *
          (1 + Real.log (boundedRatioCutoff M L)) *
            Real.exp
              (2 *
                (2 * Real.sqrt
                      (PrimeReciprocalSqrtSum.rootCutoff (L + 1)) +
                  56 *
                      Real.sqrt ((2 * (L + 1) : ℕ) : ℝ) /
                    ((Nat.log 2 (L + 1) / 2 : ℕ) : ℝ)))) := by
  calc
    ((boundedComponentHosts N M A L 2).card : ℝ) ≤
        ((((3 * (L + 1) ^ 2) ^ 2) *
          twoSingletonParameterCount M L 2 : ℕ) : ℝ) := by
      exact_mod_cast
        card_boundedComponentHosts_two_le_parameterCount hN
    _ =
        (((3 * (L + 1) ^ 2) ^ 2 : ℕ) : ℝ) *
          (twoSingletonParameterCount M L 2 : ℝ) := by
      norm_cast
    _ ≤
        (((3 * (L + 1) ^ 2) ^ 2 : ℕ) : ℝ) *
          ((boundedRatioCutoff M L : ℝ) *
            (1 + Real.log (boundedRatioCutoff M L)) *
              Real.exp
                (2 *
                  (2 * Real.sqrt
                        (PrimeReciprocalSqrtSum.rootCutoff (L + 1)) +
                    56 *
                        Real.sqrt ((2 * (L + 1) : ℕ) : ℝ) /
                      ((Nat.log 2 (L + 1) / 2 : ℕ) : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left
        (twoSingletonParameterCount_cast_le_primeSensitive hB)
      positivity

end

end BoundedRatioTwoSingletonHosts
end PaperC
