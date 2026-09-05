import PaperCV282.SizeTwoHostCounting
import PaperCV282.MacroscopicSmoothKernels
import PaperCV282.MacroscopicComponentNormalization

/-!
# Polynomial coefficient bounds and real counts for the actual component fibres

The shifted first start and the offset shape are the retained arithmetic
ones. The squarefree coefficient is bounded before applying a one-sided
split-product count; the finite maps count the genuine pair population.
-/

namespace PaperC.V282.MacroscopicComponentFibers

open Affine PropositionSixteenOne BoundedRatioComponentHosts BoundedRatioNonterminalHostCounts
open BoundedRatioManyDefectsFibers BoundedRatioManyDefectsFixedFibers
open ComponentNormalization SquarefreeSmoothCount
open scoped BigOperators

noncomputable section

/-- Products of an explicit offset set have the uniform cutoff bound. -/
theorem offset_product_pos_le_cutoff_pow
    {M L K base : ℕ} (offsets : Finset (Fin (L + 1)))
    (hbase : 0 < base) (hbaseM : base < M) (hcard : offsets.card ≤ K) :
    0 < (∏ i ∈ offsets, startCompleteVertexLabel (base + 1) L i) ∧
      (∏ i ∈ offsets, startCompleteVertexLabel (base + 1) L i) ≤ (M + L) ^ K := by
  have hlabels : ∀ i : Fin (L + 1), 0 < startCompleteVertexLabel (base + 1) L i ∧
      startCompleteVertexLabel (base + 1) L i ≤ M + L := by
    intro i
    unfold startCompleteVertexLabel
    split_ifs <;> have := i.isLt <;> omega
  refine ⟨Finset.prod_pos (fun i _ => (hlabels i).1), ?_⟩
  calc
    _ ≤ ∏ _i ∈ offsets, (M + L) := Finset.prod_le_prod
      (fun _ _ => Nat.zero_le _) (fun i _ => (hlabels i).2)
    _ = (M + L) ^ offsets.card := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hcard

/-- The exact shifted-base range is positive and below the upper endpoint. -/
theorem boundedStartBase_pos_lt {N M base : ℕ} (hN : 2 ≤ N)
    (hbase : base ∈ boundedStartBases N M) : 0 < base ∧ base < M := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hbase
  have hxi := Finset.mem_Ico.mp hx
  omega

/-- The normalized coefficient in the left fibre has polynomial height. -/
theorem leftNormalizedCoefficient_le_polynomial
    {N M L K base d : ℕ} (hN : 2 ≤ N) (hM : 2 ≤ M) (hL : L ≤ M)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hshape : shape ∈ boundedOffsetShapes L K) (hbase : base ∈ boundedStartBases N M)
    (hd : d ∈ squarefreeSmoothUpTo (L + 1) ((M + L) ^ K)) :
    leftNormalizedCoefficient shape base d ≤ M ^ (4 * K) := by
  have hb := boundedStartBase_pos_lt hN hbase
  have hs := mem_boundedOffsetShapes.mp hshape
  have hprod := offset_product_pos_le_cutoff_pow (K := K) shape.1 hb.1 hb.2 (by omega)
  have hddata := mem_squarefreeSmoothUpTo.mp hd
  have hcut : M + L ≤ M ^ 2 := by nlinarith
  unfold leftNormalizedCoefficient shapeLeftProduct
  calc
    _ ≤ d * (∏ i ∈ shape.1, startCompleteVertexLabel (base + 1) L i) :=
      squarefreeKernel_le (Nat.mul_pos (by omega) hprod.1)
    _ ≤ (M + L) ^ K * (M + L) ^ K := Nat.mul_le_mul hddata.2.1 hprod.2
    _ = (M + L) ^ (2 * K) := by rw [← pow_add]; congr 1; omega
    _ ≤ (M ^ 2) ^ (2 * K) := Nat.pow_le_pow_left hcut _
    _ = _ := by rw [← pow_mul]; congr 1; omega

/-- The normalized coefficient in the right fibre has the same polynomial height. -/
theorem rightNormalizedCoefficient_le_polynomial
    {N M L K base d : ℕ} (hN : 2 ≤ N) (hM : 2 ≤ M) (hL : L ≤ M)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hshape : shape ∈ boundedOffsetShapes L K) (hbase : base ∈ boundedStartBases N M)
    (hd : d ∈ squarefreeSmoothUpTo (L + 1) ((M + L) ^ K)) :
    rightNormalizedCoefficient shape base d ≤ M ^ (4 * K) := by
  have hb := boundedStartBase_pos_lt hN hbase
  have hs := mem_boundedOffsetShapes.mp hshape
  have hprod := offset_product_pos_le_cutoff_pow (K := K) shape.2 hb.1 hb.2 (by omega)
  have hddata := mem_squarefreeSmoothUpTo.mp hd
  have hcut : M + L ≤ M ^ 2 := by nlinarith
  unfold rightNormalizedCoefficient shapeRightProduct
  calc
    _ ≤ d * (∏ i ∈ shape.2, startCompleteVertexLabel (base + 1) L i) :=
      squarefreeKernel_le (Nat.mul_pos (by omega) hprod.1)
    _ ≤ (M + L) ^ K * (M + L) ^ K := Nat.mul_le_mul hddata.2.1 hprod.2
    _ = (M + L) ^ (2 * K) := by rw [← pow_add]; congr 1; omega
    _ ≤ (M ^ 2) ^ (2 * K) := Nat.pow_le_pow_left hcut _
    _ = _ := by rw [← pow_mul]; congr 1; omega

/-- Real solution counts transfer to the actual fixed square-class left fibre. -/
theorem card_leftFixedSquareClassFiber_cast_le
    {N M A L K base d : ℕ} {R : ℝ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hcount : PellInput.HasAtMostSolutionsReal
      (offsetProductNatFiber shape.2 (leftNormalizedCoefficient shape base d) M) R) :
    ((leftFixedSquareClassFiber N M A L K base shape d).card : ℝ) ≤ R := by
  classical
  let population := leftFixedSquareClassFiber N M A L K base shape d
  have hh := hcount (population.image (leftFixedSquareClassSolution shape)) (by
    intro solution hsolution
    obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp hsolution
    exact leftFixedSquareClassSolution_mem hN hpair)
  have hi : (population.image (leftFixedSquareClassSolution shape)).card = population.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv huv
    exact leftFixedSquareClassSolution_injective_on hN shape hu hv huv
  simpa only [hi] using hh

/-- Real solution counts transfer to the actual fixed square-class right fibre. -/
theorem card_rightFixedSquareClassFiber_cast_le
    {N M A L K base d : ℕ} {R : ℝ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hcount : PellInput.HasAtMostSolutionsReal
      (offsetProductNatFiber shape.1 (rightNormalizedCoefficient shape base d) M) R) :
    ((rightFixedSquareClassFiber N M A L K base shape d).card : ℝ) ≤ R := by
  classical
  let population := rightFixedSquareClassFiber N M A L K base shape d
  have hh := hcount (population.image (rightFixedSquareClassSolution shape)) (by
    intro solution hsolution
    obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp hsolution
    exact rightFixedSquareClassSolution_mem hN hpair)
  have hi : (population.image (rightFixedSquareClassSolution shape)).card = population.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv huv
    exact rightFixedSquareClassSolution_injective_on hN shape hu hv huv
  simpa only [hi] using hh

/-- Sum the real left-fibre estimate over the actual smooth square classes. -/
theorem card_leftBaseShapeFiber_cast_le_of_fixed_counts
    {N M A L K base : ℕ} {R : ℝ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hcount : ∀ d ∈ squarefreeSmoothUpTo (L + 1) ((M + L) ^ K),
      ((leftFixedSquareClassFiber N M A L K base shape d).card : ℝ) ≤ R) :
    ((leftBaseShapeFiber N M A L K base shape).card : ℝ) ≤
      ((squarefreeSmoothUpTo (L + 1) ((M + L) ^ K)).card : ℝ) * R := by
  classical
  have hc : ((leftBaseShapeFiber N M A L K base shape).card : ℝ) ≤
      (((squarefreeSmoothUpTo (L + 1) ((M + L) ^ K)).biUnion fun d =>
        leftFixedSquareClassFiber N M A L K base shape d).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (leftBaseShapeFiber_subset_squareClassUnion hN shape)
  calc
    _ ≤ _ := hc
    _ ≤ ∑ d ∈ squarefreeSmoothUpTo (L + 1) ((M + L) ^ K),
        ((leftFixedSquareClassFiber N M A L K base shape d).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ squarefreeSmoothUpTo (L + 1) ((M + L) ^ K), R := Finset.sum_le_sum hcount
    _ = _ := by simp

/-- Sum the real right-fibre estimate over the actual smooth square classes. -/
theorem card_rightBaseShapeFiber_cast_le_of_fixed_counts
    {N M A L K base : ℕ} {R : ℝ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hcount : ∀ d ∈ squarefreeSmoothUpTo (L + 1) ((M + L) ^ K),
      ((rightFixedSquareClassFiber N M A L K base shape d).card : ℝ) ≤ R) :
    ((rightBaseShapeFiber N M A L K base shape).card : ℝ) ≤
      ((squarefreeSmoothUpTo (L + 1) ((M + L) ^ K)).card : ℝ) * R := by
  classical
  have hc : ((rightBaseShapeFiber N M A L K base shape).card : ℝ) ≤
      (((squarefreeSmoothUpTo (L + 1) ((M + L) ^ K)).biUnion fun d =>
        rightFixedSquareClassFiber N M A L K base shape d).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (rightBaseShapeFiber_subset_squareClassUnion hN shape)
  calc
    _ ≤ _ := hc
    _ ≤ ∑ d ∈ squarefreeSmoothUpTo (L + 1) ((M + L) ^ K),
        ((rightFixedSquareClassFiber N M A L K base shape d).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ squarefreeSmoothUpTo (L + 1) ((M + L) ^ K), R := Finset.sum_le_sum hcount
    _ = _ := by simp

end
end PaperC.V282.MacroscopicComponentFibers
