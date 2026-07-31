import PaperC.Arithmetic.PrimeFactorsFactorialBound
import PaperC.Asymptotics.BoundedRatioManyDefectsFixedFibers
import PaperC.Asymptotics.BoundedRatioTerminalClosure
import PaperC.Asymptotics.ExpLogDivLogLog
import PaperC.Asymptotics.LogLogRunWindow
import PaperC.Arithmetic.ChebyshevPrimeCount
import PaperC.Arithmetic.PrimeCountBridge

set_option maxHeartbeats 3600000

/-!
# The Evertse--Silverman sum in the many-defects fixed fibres

For degree at least three, `BoundedRatioManyDefectsFixedFibers` reduces each
fixed square-class fibre to the explicit Evertse--Silverman factor

`2 * 7^(4 + 9 * (1 + ω(n)))`.

This file closes its uniform summation.  The only number-theoretic estimate
used for `ω` is the unconditional factorial inequality `ω(n)! ≤ n` from
`PrimeFactorsFactorialBound`.  Since a factorial eventually dominates every
fixed exponential, every fixed affine exponential in `ω(n)` is
reciprocal-power subpolynomial when `n` has polynomial height.

The finite sum over squarefree smooth coefficients is absorbed by the
already proved Chebyshev bound for their number.  No new bridge is
introduced.
-/

namespace PaperC
namespace BoundedRatioManyDefectsEvertseSum

open scoped BigOperators
open Affine
open BoundedRatioComponentHosts
open BoundedRatioDistinctKernelTwoDefects
open BoundedRatioManyDefectsFibers
open BoundedRatioManyDefectsFixedFibers
open ComponentNormalization
open DefectCounting
open EvertseSilvermanInput
open PrimeFactorsFactorialBound
open PropositionSixteenOne
open SquarefreeSmoothCount

noncomputable section

/--
Polynomial exponent controlling the bad integer
`2 * e * ∏_{r<s}(hᵣ-hₛ)` in a fixed degree-`degree` fibre.
-/
def evertseBadHeightExponent
    (K degree : ℕ) : ℕ :=
  1 + 2 * K + 2 * degree * degree

theorem evertseBadHeightExponent_pos
    (K degree : ℕ) :
    0 < evertseBadHeightExponent K degree := by
  unfold evertseBadHeightExponent
  omega

/--
Worst explicit Evertse--Silverman factor over all bad integers of height at
most `X^E`.
-/
noncomputable def evertsePolynomialHeightEnvelope
    (X E : ℕ) : ℕ :=
  (2 * 7 ^ 13) *
    7 ^ (9 * polynomialHeightOmega X E)

theorem one_le_evertsePolynomialHeightEnvelope
    (X E : ℕ) :
    1 ≤ evertsePolynomialHeightEnvelope X E := by
  unfold evertsePolynomialHeightEnvelope
  have hpos :
      0 < (2 * 7 ^ 13) *
        7 ^ (9 * polynomialHeightOmega X E) := by
    positivity
  omega

/--
The literal explicit Evertse--Silverman count is bounded by the universal
polynomial-height envelope.
-/
theorem explicitBound_le_evertsePolynomialHeightEnvelope
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ)
    {X E : ℕ}
    (hheight :
      2 * e.natAbs * pairDifferenceProduct shift ≤ X ^ E) :
    explicitBound shift e ≤
      evertsePolynomialHeightEnvelope X E := by
  let n :=
    2 * e.natAbs * pairDifferenceProduct shift
  have homega :
      n.primeFactors.card ≤ polynomialHeightOmega X E :=
    primeFactors_card_le_polynomialHeightOmega hheight
  have hexponent :
      4 + 9 * (1 + n.primeFactors.card) ≤
        13 + 9 * polynomialHeightOmega X E := by
    omega
  unfold explicitBound explicitAbscissaBound badPlaceCount
  change
    2 * 7 ^ (4 + 9 * (1 + n.primeFactors.card)) ≤
      (2 * 7 ^ 13) *
        7 ^ (9 * polynomialHeightOmega X E)
  calc
    2 * 7 ^ (4 + 9 * (1 + n.primeFactors.card)) ≤
        2 * 7 ^ (13 + 9 * polynomialHeightOmega X E) :=
      Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_right (by norm_num) hexponent)
    _ =
        (2 * 7 ^ 13) *
          7 ^ (9 * polynomialHeightOmega X E) := by
      rw [pow_add]
      ring

/--
Natural envelope for the complete ES fixed-fibre sum.  The first factor is
the exact powerset bound for squarefree `(L+1)`-smooth coefficients; the
second is one uniform summand.
-/
noncomputable def evertseFixedFiberResidual
    (B X K degree : ℕ) : ℕ :=
  2 ^ (smallPrimesUpTo B).card *
    (degree +
      evertsePolynomialHeightEnvelope X
        (evertseBadHeightExponent K degree))

theorem one_le_evertseFixedFiberResidual
    (B X K degree : ℕ) :
    1 ≤ evertseFixedFiberResidual B X K degree := by
  unfold evertseFixedFiberResidual
  have hfirst :
      1 ≤ 2 ^ (smallPrimesUpTo B).card :=
    Nat.one_le_pow _ _ (by norm_num)
  have hsecond :
      1 ≤ degree +
        evertsePolynomialHeightEnvelope X
          (evertseBadHeightExponent K degree) :=
    by
      have h :=
        one_le_evertsePolynomialHeightEnvelope
          X (evertseBadHeightExponent K degree)
      omega
  have hpos :
      0 <
        2 ^ (smallPrimesUpTo B).card *
          (degree +
            evertsePolynomialHeightEnvelope X
              (evertseBadHeightExponent K degree)) :=
    Nat.mul_pos (Nat.zero_lt_of_lt hfirst)
      (Nat.zero_lt_of_lt hsecond)
  exact hpos

/--
Shape-independent residual used for all mobile degrees between three and
ten.  Both the component budget and the degree are frozen at ten, and the
height is measured at the bounded-ratio terminal cutoff.
-/
noncomputable def evertseCommonFixedFiberResidual
    (κ₀ N L : ℕ) : ℕ :=
  evertseFixedFiberResidual
    (L + 1)
    (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N)
    10 10

/-- The common ES residual is pointwise at least one. -/
theorem one_le_evertseCommonFixedFiberResidual
    (κ₀ N L : ℕ) :
    1 ≤ evertseCommonFixedFiberResidual κ₀ N L := by
  exact
    one_le_evertseFixedFiberResidual
      (L + 1)
      (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N)
      10 10

/--
Real-cast form of the lower bound expected by later asymptotic products.
The threshold can be taken to be zero because the bound is pointwise.
-/
theorem evertseCommonFixedFiberResidual_eventually_one_le
    (κ₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      (1 : ℝ) ≤
        (evertseCommonFixedFiberResidual κ₀ N L : ℝ) := by
  refine ⟨0, ?_⟩
  intro N _hN L
  exact_mod_cast
    one_le_evertseCommonFixedFiberResidual κ₀ N L

/--
The literal powerset factor in the natural residual lies below the same
Chebyshev envelope used for squarefree smooth kernels.
-/
theorem two_pow_smallPrimesUpTo_cast_le_smoothKernelChebyshevEnvelope
    {B : ℕ} (hB : 4 ≤ B) :
    (((2 ^ (smallPrimesUpTo B).card : ℕ) : ℝ)) ≤
      smoothKernelChebyshevEnvelope B := by
  have hcountNat :=
    ChebyshevPrimeCount.count_le_seven_mul_div_log hB
  have hcountReal :
      ((smallPrimesUpTo B).card : ℝ) ≤
        (7 : ℝ) * (B : ℝ) /
          (Nat.log 2 B : ℝ) := by
    rw [← PrimeCountBridge.count_eq_card_smallPrimesUpTo]
    calc
      (PrimesUpTo.count B : ℝ) ≤
          (((7 * B) / Nat.log 2 B : ℕ) : ℝ) := by
        exact_mod_cast hcountNat
      _ ≤
          ((7 * B : ℕ) : ℝ) /
            (Nat.log 2 B : ℝ) :=
        Nat.cast_div_le
      _ =
          (7 : ℝ) * (B : ℝ) /
            (Nat.log 2 B : ℝ) := by
        norm_num
  have hlogTwoNonneg :
      0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos one_lt_two).le
  have hscaled :=
    mul_le_mul_of_nonneg_right hcountReal
      hlogTwoNonneg
  calc
    (((2 ^ (smallPrimesUpTo B).card : ℕ) : ℝ)) =
        (2 : ℝ) ^ (smallPrimesUpTo B).card := by
      norm_num
    _ =
        Real.exp
          (((smallPrimesUpTo B).card : ℝ) *
            Real.log 2) := by
      calc
        (2 : ℝ) ^ (smallPrimesUpTo B).card =
            (Real.exp (Real.log 2)) ^
              (smallPrimesUpTo B).card := by
          rw [Real.exp_log]
          norm_num
        _ =
            Real.exp
              (((smallPrimesUpTo B).card : ℝ) *
                Real.log 2) :=
          (Real.exp_nat_mul
            (Real.log 2)
            (smallPrimesUpTo B).card).symm
    _ ≤
        Real.exp
          ((7 * Real.log 2) *
            ((B : ℝ) /
              (Nat.log 2 B : ℝ))) := by
      apply Real.exp_le_exp.mpr
      calc
        ((smallPrimesUpTo B).card : ℝ) *
              Real.log 2 ≤
            ((7 : ℝ) * (B : ℝ) /
              (Nat.log 2 B : ℝ)) *
                Real.log 2 :=
          hscaled
        _ =
            (7 * Real.log 2) *
              ((B : ℝ) /
                (Nat.log 2 B : ℝ)) := by
          ring
    _ = smoothKernelChebyshevEnvelope B := rfl

/-! ## Polynomial height of the shifted discriminant support -/

private theorem offsetShift_natAbs_le
    {L : ℕ} (offsets : Finset (Fin (L + 1)))
    (i : Fin offsets.card) :
    (offsetShift offsets i).natAbs ≤ L + 1 := by
  have hbound :=
    AlignedRungeBridge.abs_channelVertexOffset_le
      ((offsetEnumeration offsets i).1)
  rw [Int.abs_eq_natAbs] at hbound
  exact_mod_cast hbound

private theorem offsetShift_difference_natAbs_le
    {L : ℕ} (offsets : Finset (Fin (L + 1)))
    (i j : Fin offsets.card) :
    (offsetShift offsets i -
      offsetShift offsets j).natAbs ≤
        2 * (L + 1) := by
  calc
    (offsetShift offsets i -
        offsetShift offsets j).natAbs ≤
        (offsetShift offsets i).natAbs +
          (offsetShift offsets j).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ 2 * (L + 1) := by
      have hi := offsetShift_natAbs_le offsets i
      have hj := offsetShift_natAbs_le offsets j
      omega

theorem pairDifferenceProduct_offsetShift_le
    {L : ℕ} (offsets : Finset (Fin (L + 1))) :
    pairDifferenceProduct (offsetShift offsets) ≤
      (2 * (L + 1)) ^
        (offsets.card * offsets.card) := by
  unfold pairDifferenceProduct
  calc
    (∏ r : Fin offsets.card, ∏ s : Fin offsets.card,
        if r < s then
          (offsetShift offsets r -
            offsetShift offsets s).natAbs
        else 1) ≤
        ∏ _r : Fin offsets.card,
          (2 * (L + 1)) ^ offsets.card := by
      apply Finset.prod_le_prod
      · intro r hr
        positivity
      · intro r hr
        calc
          (∏ s : Fin offsets.card,
              if r < s then
                (offsetShift offsets r -
                  offsetShift offsets s).natAbs
              else 1) ≤
              ∏ _s : Fin offsets.card,
                (2 * (L + 1)) := by
            apply Finset.prod_le_prod
            · intro s hs
              positivity
            · intro s hs
              split_ifs
              · exact
                  offsetShift_difference_natAbs_le
                    offsets r s
              · omega
          _ = (2 * (L + 1)) ^ offsets.card := by
            simp
    _ =
        ((2 * (L + 1)) ^ offsets.card) ^
          offsets.card := by
      simp
    _ =
        (2 * (L + 1)) ^
          (offsets.card * offsets.card) := by
      rw [pow_mul]

theorem pairDifferenceProduct_offsetShift_le_cutoffPow
    {L X : ℕ} (offsets : Finset (Fin (L + 1)))
    (hX : 2 ≤ X) (hLX : L + 1 ≤ X) :
    pairDifferenceProduct (offsetShift offsets) ≤
      X ^ (2 * offsets.card * offsets.card) := by
  have htwoX :
      2 * (L + 1) ≤ X ^ 2 := by
    calc
      2 * (L + 1) ≤ X * X :=
        Nat.mul_le_mul hX hLX
      _ = X ^ 2 := by ring
  calc
    pairDifferenceProduct (offsetShift offsets) ≤
        (2 * (L + 1)) ^
          (offsets.card * offsets.card) :=
      pairDifferenceProduct_offsetShift_le offsets
    _ ≤
        (X ^ 2) ^
          (offsets.card * offsets.card) :=
      Nat.pow_le_pow_left htwoX _
    _ =
        X ^ (2 * offsets.card * offsets.card) := by
      rw [← pow_mul]
      congr 1
      ring

/-! ## Polynomial height on actual fixed fibres -/

private theorem cutoff_bounds_of_pair
    {N M L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    2 ≤ boundedRatioCutoff M L ∧
      L + 1 ≤ boundedRatioCutoff M L := by
  have hpair :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hx :=
    BoundedRatioGeometry.mem_boundedRatioBlock.mp
      hpair.1
  unfold boundedRatioCutoff
  omega

private theorem left_base_succ_mem_block
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ leftBaseShapeFiber
        N M A L K base shape) :
    base + 1 ∈ boundedRatioBlock N M := by
  have hdata := mem_leftBaseShapeFiber.mp hpair
  have hsep :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hxTwo :=
    (pair_coordinates_two_le hN pair).1
  have heq : pair.1.1 = base + 1 := by
    omega
  simpa only [heq] using hsep.1

private theorem right_base_succ_mem_block
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ rightBaseShapeFiber
        N M A L K base shape) :
    base + 1 ∈ boundedRatioBlock N M := by
  have hdata := mem_rightBaseShapeFiber.mp hpair
  have hsep :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hyTwo :=
    (pair_coordinates_two_le hN pair).2
  have heq : pair.1.2 = base + 1 := by
    omega
  simpa only [heq] using hsep.2.1

private theorem shape_card_bounds_of_left_mem
    {N M A L K base : ℕ}
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ leftBaseShapeFiber
        N M A L K base shape) :
    shape.1.card ≤ K ∧ shape.2.card ≤ K := by
  have hdata := mem_leftBaseShapeFiber.mp hpair
  rcases
      (mem_boundedComponentHostsOfShape.mp hdata.1).2 with
    ⟨C, hC, hcard, hleft, hright⟩
  have htotal :
      shape.1.card + shape.2.card ≤ K := by
    rw [← hleft, ← hright,
      card_componentOffsets]
    exact hcard
  omega

private theorem shape_card_bounds_of_right_mem
    {N M A L K base : ℕ}
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ rightBaseShapeFiber
        N M A L K base shape) :
    shape.1.card ≤ K ∧ shape.2.card ≤ K := by
  have hdata := mem_rightBaseShapeFiber.mp hpair
  rcases
      (mem_boundedComponentHostsOfShape.mp hdata.1).2 with
    ⟨C, hC, hcard, hleft, hright⟩
  have htotal :
      shape.1.card + shape.2.card ≤ K := by
    rw [← hleft, ← hright,
      card_componentOffsets]
    exact hcard
  omega

private theorem shapeLeftProduct_le_cutoffPow_of_mem
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ leftBaseShapeFiber
        N M A L K base shape) :
    shapeLeftProduct shape (base + 1) ≤
      boundedRatioCutoff M L ^ K := by
  have hbase :=
    left_base_succ_mem_block hN shape hpair
  have hcard :=
    (shape_card_bounds_of_left_mem shape hpair).1
  have hcutoffOne :
      1 ≤ boundedRatioCutoff M L :=
    (cutoff_bounds_of_pair hN pair).1.trans'
      (by norm_num)
  unfold shapeLeftProduct
  calc
    (∏ i ∈ shape.1,
        startCompleteVertexLabel (base + 1) L i) ≤
        boundedRatioCutoff M L ^ shape.1.card := by
      apply Finset.prod_le_pow_card
      intro i hi
      exact
        BoundedRatioRelationalHosts.startCompleteVertexLabel_le_cutoff
          hbase i
    _ ≤ boundedRatioCutoff M L ^ K :=
      Nat.pow_le_pow_right hcutoffOne hcard

private theorem shapeRightProduct_le_cutoffPow_of_mem
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ rightBaseShapeFiber
        N M A L K base shape) :
    shapeRightProduct shape (base + 1) ≤
      boundedRatioCutoff M L ^ K := by
  have hbase :=
    right_base_succ_mem_block hN shape hpair
  have hcard :=
    (shape_card_bounds_of_right_mem shape hpair).2
  have hcutoffOne :
      1 ≤ boundedRatioCutoff M L :=
    (cutoff_bounds_of_pair hN pair).1.trans'
      (by norm_num)
  unfold shapeRightProduct
  calc
    (∏ i ∈ shape.2,
        startCompleteVertexLabel (base + 1) L i) ≤
        boundedRatioCutoff M L ^ shape.2.card := by
      apply Finset.prod_le_pow_card
      intro i hi
      exact
        BoundedRatioRelationalHosts.startCompleteVertexLabel_le_cutoff
          hbase i
    _ ≤ boundedRatioCutoff M L ^ K :=
      Nat.pow_le_pow_right hcutoffOne hcard

private theorem leftNormalizedCoefficient_le_cutoffPow
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ leftBaseShapeFiber
        N M A L K base shape)
    (hdPos : 0 < d)
    (hdBound :
      d ≤ boundedRatioCutoff M L ^ K) :
    leftNormalizedCoefficient shape base d ≤
      boundedRatioCutoff M L ^ (2 * K) := by
  have hproduct :=
    shapeLeftProduct_le_cutoffPow_of_mem
      hN shape hpair
  have hbase :=
    left_base_succ_mem_block hN shape hpair
  have hproductPos :
      0 < shapeLeftProduct shape (base + 1) := by
    unfold shapeLeftProduct
    apply Finset.prod_pos
    intro i hi
    exact
      RationalChannelCode.startCompleteVertexLabel_pos
        (by
          have hmem :=
            BoundedRatioGeometry.mem_boundedRatioBlock.mp hbase
          omega)
        i
  unfold leftNormalizedCoefficient
  calc
    squarefreeKernel
        (d * shapeLeftProduct shape (base + 1)) ≤
        d * shapeLeftProduct shape (base + 1) :=
      squarefreeKernel_le
        (Nat.mul_pos hdPos hproductPos)
    _ ≤
        boundedRatioCutoff M L ^ K *
          boundedRatioCutoff M L ^ K :=
      Nat.mul_le_mul hdBound hproduct
    _ = boundedRatioCutoff M L ^ (2 * K) := by
      rw [← pow_add]
      congr 1
      omega

private theorem rightNormalizedCoefficient_le_cutoffPow
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ rightBaseShapeFiber
        N M A L K base shape)
    (hdPos : 0 < d)
    (hdBound :
      d ≤ boundedRatioCutoff M L ^ K) :
    rightNormalizedCoefficient shape base d ≤
      boundedRatioCutoff M L ^ (2 * K) := by
  have hproduct :=
    shapeRightProduct_le_cutoffPow_of_mem
      hN shape hpair
  have hbase :=
    right_base_succ_mem_block hN shape hpair
  have hproductPos :
      0 < shapeRightProduct shape (base + 1) := by
    unfold shapeRightProduct
    apply Finset.prod_pos
    intro i hi
    exact
      RationalChannelCode.startCompleteVertexLabel_pos
        (by
          have hmem :=
            BoundedRatioGeometry.mem_boundedRatioBlock.mp hbase
          omega)
        i
  unfold rightNormalizedCoefficient
  calc
    squarefreeKernel
        (d * shapeRightProduct shape (base + 1)) ≤
        d * shapeRightProduct shape (base + 1) :=
      squarefreeKernel_le
        (Nat.mul_pos hdPos hproductPos)
    _ ≤
        boundedRatioCutoff M L ^ K *
          boundedRatioCutoff M L ^ K :=
      Nat.mul_le_mul hdBound hproduct
    _ = boundedRatioCutoff M L ^ (2 * K) := by
      rw [← pow_add]
      congr 1
      omega

theorem leftEvertseBadInteger_le_cutoffPow
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ leftBaseShapeFiber
        N M A L K base shape)
    (hd :
      d ∈ squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K)) :
    2 * leftNormalizedCoefficient shape base d *
        pairDifferenceProduct (offsetShift shape.2) ≤
      boundedRatioCutoff M L ^
        evertseBadHeightExponent K shape.2.card := by
  let X := boundedRatioCutoff M L
  have hX :=
    cutoff_bounds_of_pair hN pair
  have hdData :=
    mem_squarefreeSmoothUpTo.mp hd
  have he :
      leftNormalizedCoefficient shape base d ≤
        X ^ (2 * K) :=
    leftNormalizedCoefficient_le_cutoffPow
      hN shape hpair hdData.1 hdData.2.1
  have hdisc :
      pairDifferenceProduct (offsetShift shape.2) ≤
        X ^ (2 * shape.2.card * shape.2.card) :=
    pairDifferenceProduct_offsetShift_le_cutoffPow
      shape.2 hX.1 hX.2
  calc
    2 * leftNormalizedCoefficient shape base d *
        pairDifferenceProduct (offsetShift shape.2) ≤
        X * X ^ (2 * K) *
          X ^ (2 * shape.2.card * shape.2.card) :=
      Nat.mul_le_mul (Nat.mul_le_mul hX.1 he) hdisc
    _ =
        X ^ evertseBadHeightExponent K shape.2.card := by
      unfold evertseBadHeightExponent
      calc
        X * X ^ (2 * K) *
              X ^ (2 * shape.2.card * shape.2.card) =
            X ^ (1 + 2 * K) *
              X ^ (2 * shape.2.card * shape.2.card) := by
          rw [pow_add, pow_one]
        _ =
            X ^ ((1 + 2 * K) +
              2 * shape.2.card * shape.2.card) :=
          (pow_add _ _ _).symm
        _ =
            X ^ (1 + 2 * K +
              2 * shape.2.card * shape.2.card) := rfl

theorem rightEvertseBadInteger_le_cutoffPow
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ rightBaseShapeFiber
        N M A L K base shape)
    (hd :
      d ∈ squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K)) :
    2 * rightNormalizedCoefficient shape base d *
        pairDifferenceProduct (offsetShift shape.1) ≤
      boundedRatioCutoff M L ^
        evertseBadHeightExponent K shape.1.card := by
  let X := boundedRatioCutoff M L
  have hX :=
    cutoff_bounds_of_pair hN pair
  have hdData :=
    mem_squarefreeSmoothUpTo.mp hd
  have he :
      rightNormalizedCoefficient shape base d ≤
        X ^ (2 * K) :=
    rightNormalizedCoefficient_le_cutoffPow
      hN shape hpair hdData.1 hdData.2.1
  have hdisc :
      pairDifferenceProduct (offsetShift shape.1) ≤
        X ^ (2 * shape.1.card * shape.1.card) :=
    pairDifferenceProduct_offsetShift_le_cutoffPow
      shape.1 hX.1 hX.2
  calc
    2 * rightNormalizedCoefficient shape base d *
        pairDifferenceProduct (offsetShift shape.1) ≤
        X * X ^ (2 * K) *
          X ^ (2 * shape.1.card * shape.1.card) :=
      Nat.mul_le_mul (Nat.mul_le_mul hX.1 he) hdisc
    _ =
        X ^ evertseBadHeightExponent K shape.1.card := by
      unfold evertseBadHeightExponent
      calc
        X * X ^ (2 * K) *
              X ^ (2 * shape.1.card * shape.1.card) =
            X ^ (1 + 2 * K) *
              X ^ (2 * shape.1.card * shape.1.card) := by
          rw [pow_add, pow_one]
        _ =
            X ^ ((1 + 2 * K) +
              2 * shape.1.card * shape.1.card) :=
          (pow_add _ _ _).symm
        _ =
            X ^ (1 + 2 * K +
              2 * shape.1.card * shape.1.card) := rfl

/-! ## Domination of the complete fixed fibres -/

theorem card_leftBaseShapeFiber_degree_at_least_three_le_residual
    (hES : EvertseSilvermanAbscissaStatement)
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : 3 ≤ shape.2.card) :
    (leftBaseShapeFiber
        N M A L K base shape).card ≤
      evertseFixedFiberResidual
        (L + 1) (boundedRatioCutoff M L)
        K shape.2.card := by
  by_cases hempty :
      leftBaseShapeFiber N M A L K base shape = ∅
  · rw [hempty]
    simp
  · obtain ⟨pair, hpair⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hbase :
        2 ≤ base + 1 := by
      have hmem :=
        left_base_succ_mem_block hN shape hpair
      exact hN.trans
        (BoundedRatioGeometry.mem_boundedRatioBlock.mp hmem).1
    have hfinite :=
      card_leftBaseShapeFiber_degree_at_least_three
        hES (M := M) (A := A) (K := K)
          hN shape hdegree hbase
    let D :=
      squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K)
    let Q :=
      shape.2.card +
        evertsePolynomialHeightEnvelope
          (boundedRatioCutoff M L)
          (evertseBadHeightExponent K shape.2.card)
    have hsummand :
        ∀ d ∈ D,
          shape.2.card +
              explicitBound (offsetShift shape.2)
                (leftNormalizedCoefficient shape base d : ℤ) ≤
            Q := by
      intro d hd
      apply Nat.add_le_add_left
      apply explicitBound_le_evertsePolynomialHeightEnvelope
      have hheight :=
        leftEvertseBadInteger_le_cutoffPow
          hN shape hpair (by simpa only [D] using hd)
      simpa only [Int.natAbs_ofNat] using hheight
    calc
      (leftBaseShapeFiber
          N M A L K base shape).card ≤
          ∑ d ∈ D,
            (shape.2.card +
              explicitBound (offsetShift shape.2)
                (leftNormalizedCoefficient shape base d : ℤ)) := by
        simpa only [D] using hfinite
      _ ≤ ∑ _d ∈ D, Q :=
        Finset.sum_le_sum fun d hd ↦ hsummand d hd
      _ = D.card * Q := by simp
      _ ≤ 2 ^ (smallPrimesUpTo (L + 1)).card * Q :=
        Nat.mul_le_mul_right Q
          (card_squarefreeSmoothUpTo_le_two_pow
            (L + 1) (boundedRatioCutoff M L ^ K))
      _ =
          evertseFixedFiberResidual
            (L + 1) (boundedRatioCutoff M L)
            K shape.2.card := rfl

theorem card_rightBaseShapeFiber_degree_at_least_three_le_residual
    (hES : EvertseSilvermanAbscissaStatement)
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : 3 ≤ shape.1.card) :
    (rightBaseShapeFiber
        N M A L K base shape).card ≤
      evertseFixedFiberResidual
        (L + 1) (boundedRatioCutoff M L)
        K shape.1.card := by
  by_cases hempty :
      rightBaseShapeFiber N M A L K base shape = ∅
  · rw [hempty]
    simp
  · obtain ⟨pair, hpair⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hbase :
        2 ≤ base + 1 := by
      have hmem :=
        right_base_succ_mem_block hN shape hpair
      exact hN.trans
        (BoundedRatioGeometry.mem_boundedRatioBlock.mp hmem).1
    have hfinite :=
      card_rightBaseShapeFiber_degree_at_least_three
        hES (M := M) (A := A) (K := K)
          hN shape hdegree hbase
    let D :=
      squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K)
    let Q :=
      shape.1.card +
        evertsePolynomialHeightEnvelope
          (boundedRatioCutoff M L)
          (evertseBadHeightExponent K shape.1.card)
    have hsummand :
        ∀ d ∈ D,
          shape.1.card +
              explicitBound (offsetShift shape.1)
                (rightNormalizedCoefficient shape base d : ℤ) ≤
            Q := by
      intro d hd
      apply Nat.add_le_add_left
      apply explicitBound_le_evertsePolynomialHeightEnvelope
      have hheight :=
        rightEvertseBadInteger_le_cutoffPow
          hN shape hpair (by simpa only [D] using hd)
      simpa only [Int.natAbs_ofNat] using hheight
    calc
      (rightBaseShapeFiber
          N M A L K base shape).card ≤
          ∑ d ∈ D,
            (shape.1.card +
              explicitBound (offsetShift shape.1)
                (rightNormalizedCoefficient shape base d : ℤ)) := by
        simpa only [D] using hfinite
      _ ≤ ∑ _d ∈ D, Q :=
        Finset.sum_le_sum fun d hd ↦ hsummand d hd
      _ = D.card * Q := by simp
      _ ≤ 2 ^ (smallPrimesUpTo (L + 1)).card * Q :=
        Nat.mul_le_mul_right Q
          (card_squarefreeSmoothUpTo_le_two_pow
            (L + 1) (boundedRatioCutoff M L ^ K))
      _ =
          evertseFixedFiberResidual
            (L + 1) (boundedRatioCutoff M L)
            K shape.1.card := rfl

/-! ## Shape-independent domination at the terminal cutoff -/

private theorem boundedRatioCutoff_le_terminalLabelCutoff
    {κ₀ N M L : ℕ}
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) :
    boundedRatioCutoff M L ≤
      BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N := by
  unfold boundedRatioCutoff
    BoundedRatioTerminalClosure.terminalLabelCutoff
  calc
    M + L ≤ κ₀ * N + N :=
      Nat.add_le_add hMκ hL
    _ = (κ₀ + 1) * N := by
      rw [Nat.add_mul, one_mul]

/--
Every residual with degree at most ten and the actual bounded-ratio cutoff
is dominated by the common degree-ten terminal-cutoff residual.
-/
theorem evertseFixedFiberResidual_le_common
    {κ₀ N M L degree : ℕ}
    (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N)
    (hdegree : degree ≤ 10) :
    evertseFixedFiberResidual
        (L + 1) (boundedRatioCutoff M L)
        10 degree ≤
      evertseCommonFixedFiberResidual κ₀ N L := by
  let X := boundedRatioCutoff M L
  let Y :=
    BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N
  have hXY : X ≤ Y := by
    simpa only [X, Y] using
      boundedRatioCutoff_le_terminalLabelCutoff hMκ hL
  have hNY : N ≤ Y := by
    dsimp only [Y]
    unfold BoundedRatioTerminalClosure.terminalLabelCutoff
    exact Nat.le_mul_of_pos_left N (by omega)
  have hYone : 1 ≤ Y :=
    (by omega : 1 ≤ N).trans hNY
  have hheightExponent :
      evertseBadHeightExponent 10 degree ≤
        evertseBadHeightExponent 10 10 := by
    unfold evertseBadHeightExponent
    nlinarith
  have hbox :
      X ^ evertseBadHeightExponent 10 degree ≤
        Y ^ evertseBadHeightExponent 10 10 := by
    calc
      X ^ evertseBadHeightExponent 10 degree ≤
          Y ^ evertseBadHeightExponent 10 degree :=
        Nat.pow_le_pow_left hXY _
      _ ≤ Y ^ evertseBadHeightExponent 10 10 :=
        Nat.pow_le_pow_right hYone hheightExponent
  have homega :
      polynomialHeightOmega X
          (evertseBadHeightExponent 10 degree) ≤
        polynomialHeightOmega Y
          (evertseBadHeightExponent 10 10) :=
    polynomialHeightOmega_mono_of_pow_le hbox
  have henvelope :
      evertsePolynomialHeightEnvelope X
          (evertseBadHeightExponent 10 degree) ≤
        evertsePolynomialHeightEnvelope Y
          (evertseBadHeightExponent 10 10) := by
    unfold evertsePolynomialHeightEnvelope
    exact
      Nat.mul_le_mul_left (2 * 7 ^ 13)
        (Nat.pow_le_pow_right (by norm_num)
          (Nat.mul_le_mul_left 9 homega))
  unfold evertseCommonFixedFiberResidual
    evertseFixedFiberResidual
  dsimp only [X, Y] at henvelope
  exact
    Nat.mul_le_mul_left
      (2 ^ (smallPrimesUpTo (L + 1)).card)
      (Nat.add_le_add hdegree henvelope)

/--
Uniform terminal-cutoff domination of every left-oriented degree-at-least-
three shape in the size-ten component container.
-/
theorem card_leftBaseShapeFiber_degree_at_least_three_le_common
    (hES : EvertseSilvermanAbscissaStatement)
    {κ₀ N M A L base : ℕ}
    (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hshape : shape ∈ boundedOffsetShapes L 10)
    (hdegree : 3 ≤ shape.2.card) :
    (leftBaseShapeFiber
        N M A L 10 base shape).card ≤
      evertseCommonFixedFiberResidual κ₀ N L := by
  have hdegreeTen : shape.2.card ≤ 10 := by
    have hdata := mem_boundedOffsetShapes.mp hshape
    omega
  exact
    (card_leftBaseShapeFiber_degree_at_least_three_le_residual
      hES (M := M) (A := A) (K := 10)
        hN shape hdegree).trans
      (evertseFixedFiberResidual_le_common
        hN hMκ hL hdegreeTen)

/--
Uniform terminal-cutoff domination of every right-oriented degree-at-least-
three shape in the size-ten component container.
-/
theorem card_rightBaseShapeFiber_degree_at_least_three_le_common
    (hES : EvertseSilvermanAbscissaStatement)
    {κ₀ N M A L base : ℕ}
    (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hshape : shape ∈ boundedOffsetShapes L 10)
    (hdegree : 3 ≤ shape.1.card) :
    (rightBaseShapeFiber
        N M A L 10 base shape).card ≤
      evertseCommonFixedFiberResidual κ₀ N L := by
  have hdegreeTen : shape.1.card ≤ 10 := by
    have hdata := mem_boundedOffsetShapes.mp hshape
    omega
  exact
    (card_rightBaseShapeFiber_degree_at_least_three_le_residual
      hES (M := M) (A := A) (K := 10)
        hN shape hdegree).trans
      (evertseFixedFiberResidual_le_common
        hN hMκ hL hdegreeTen)

/-! ## Uniform reciprocal-power rate -/

/--
For every fixed polynomial exponent, the worst ES factor at the terminal
cutoff is uniformly subpolynomial in `N`.
-/
theorem
    evertsePolynomialHeightEnvelope_terminalLabelCutoff_uniformSubpolynomial
    {C : ℝ} (κ₀ E : ℕ) (hE : 0 < E) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N _L =>
        ((evertsePolynomialHeightEnvelope
          (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N)
          E : ℕ) : ℝ)) := by
  intro k hk
  have htwoE : 0 < 2 * E :=
    Nat.mul_pos (by omega) hE
  obtain ⟨Nomega, homega⟩ :=
    affinePow_polynomialHeightOmega_pow_le_eventually
      (2 * 7 ^ 13) 7 9 (2 * E) k
      (by norm_num) htwoE
  refine ⟨max Nomega (κ₀ + 1), ?_⟩
  intro N hN L _hrun
  have hNomega : Nomega ≤ N :=
    (le_max_left _ _).trans hN
  have hkappa : κ₀ + 1 ≤ N :=
    (le_max_right _ _).trans hN
  have hterminal :
      BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N ≤
        N ^ 2 := by
    unfold BoundedRatioTerminalClosure.terminalLabelCutoff
    calc
      (κ₀ + 1) * N ≤ N * N :=
        Nat.mul_le_mul_right N hkappa
      _ = N ^ 2 := by ring
  have hbox :
      BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N ^ E ≤
        N ^ (2 * E) := by
    calc
      BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N ^ E ≤
          (N ^ 2) ^ E :=
        Nat.pow_le_pow_left hterminal E
      _ = N ^ (2 * E) := by
        rw [← pow_mul]
  have hmaxOmega :
      polynomialHeightOmega
          (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N) E ≤
        polynomialHeightOmega N (2 * E) :=
    polynomialHeightOmega_mono_of_pow_le hbox
  have hbase :
      evertsePolynomialHeightEnvelope
          (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N) E ≤
        (2 * 7 ^ 13) *
          7 ^ (9 * polynomialHeightOmega N (2 * E)) := by
    unfold evertsePolynomialHeightEnvelope
    exact
      Nat.mul_le_mul_left (2 * 7 ^ 13)
        (Nat.pow_le_pow_right (by norm_num)
          (Nat.mul_le_mul_left 9 hmaxOmega))
  have hnat :
      (evertsePolynomialHeightEnvelope
          (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N) E) ^ k ≤
        N := by
    calc
      (evertsePolynomialHeightEnvelope
          (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N) E) ^ k ≤
          ((2 * 7 ^ 13) *
            7 ^ (9 * polynomialHeightOmega N (2 * E))) ^ k :=
        Nat.pow_le_pow_left hbase k
      _ ≤ N :=
        homega N hNomega
  have hcast :
      (((evertsePolynomialHeightEnvelope
          (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N) E) ^ k :
            ℕ) : ℝ) ≤
        (N : ℝ) := by
    exact_mod_cast hnat
  have hnonneg :
      0 ≤
        ((evertsePolynomialHeightEnvelope
          (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N) E :
            ℕ) : ℝ) := by
    positivity
  rw [abs_of_nonneg hnonneg]
  simpa only [Nat.cast_pow] using hcast

/-- The literal squarefree-smooth powerset factor is uniformly `N^o(1)`. -/
theorem two_pow_smallPrimesUpTo_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _N L =>
        (((2 ^ (smallPrimesUpTo (L + 1)).card : ℕ) : ℝ))) := by
  have hsmooth :=
    smoothKernelChebyshevEnvelope_uniformSubpolynomial hC
  apply UniformSubpolynomial.mono hsmooth
  obtain ⟨Nfour, hfour⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC 4
  refine ⟨Nfour, ?_⟩
  intro N hN L hrun
  have hbound :=
    two_pow_smallPrimesUpTo_cast_le_smoothKernelChebyshevEnvelope
      (hfour N hN L hrun)
  have hleft :
      0 ≤ (((2 ^ (smallPrimesUpTo (L + 1)).card : ℕ) : ℝ)) := by
    positivity
  have hright :
      0 ≤ smoothKernelChebyshevEnvelope (L + 1) := by
    unfold smoothKernelChebyshevEnvelope
    positivity
  simpa only [abs_of_nonneg hleft, abs_of_nonneg hright] using hbound

/--
The complete shape-independent ES fixed-fibre residual is uniformly
`N^o(1)` in every fixed critical run-length window.
-/
theorem evertseCommonFixedFiberResidual_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ((evertseCommonFixedFiberResidual κ₀ N L : ℕ) : ℝ)) := by
  have hfirst :=
    two_pow_smallPrimesUpTo_uniformSubpolynomial hC
  have henvelope :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N _L =>
          ((evertsePolynomialHeightEnvelope
            (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N)
            (evertseBadHeightExponent 10 10) : ℕ) : ℝ)) :=
    evertsePolynomialHeightEnvelope_terminalLabelCutoff_uniformSubpolynomial
      κ₀ (evertseBadHeightExponent 10 10)
        (evertseBadHeightExponent_pos 10 10)
  have hsummandModel :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      11 henvelope
  have hsummand :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N _L =>
          (((10 +
            evertsePolynomialHeightEnvelope
              (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N)
              (evertseBadHeightExponent 10 10) : ℕ) : ℝ))) := by
    apply UniformSubpolynomial.mono hsummandModel
    refine ⟨0, ?_⟩
    intro N _hN L _hrun
    let E :=
      evertsePolynomialHeightEnvelope
        (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N)
        (evertseBadHeightExponent 10 10)
    have hEone : 1 ≤ E := by
      dsimp only [E]
      exact one_le_evertsePolynomialHeightEnvelope _ _
    have hnat : 10 + E ≤ 11 * E := by
      omega
    have hleft : 0 ≤ (((10 + E : ℕ) : ℝ)) := by
      positivity
    have hright : 0 ≤ (11 : ℝ) * (E : ℝ) := by
      positivity
    rw [abs_of_nonneg hleft, abs_of_nonneg hright]
    exact_mod_cast hnat
  have hproduct :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      hfirst hsummand
  simpa only [
      evertseCommonFixedFiberResidual,
      evertseFixedFiberResidual,
      Nat.cast_mul] using hproduct

end

end BoundedRatioManyDefectsEvertseSum
end PaperC
