import PaperC.Coding.DefectCodeRank
import PaperC.Coding.HammingDefectBound

/-!
# The two-parity column code from Section 8

For each of the `m` small residual components used in the proof of
Theorem 8.1, the paper forms a column

`((v_p(C))_{p ≤ B}, |C ∩ V_x| mod 2, |C ∩ V_y| mod 2)`.

This file isolates the finite linear-algebra and Hamming-theoretic content of
that construction.  The first `r` coordinates are left abstract: downstream
files instantiate them with the small-prime parities of component products.
The two final bits record the left and right vertex parities separately.
-/

namespace PaperC
namespace TwoParityColumnCode

open scoped BigOperators

/-- Append two distinguished bits to a binary column. -/
def appendTwo {r : ℕ} (v : Fin r → F₂) (left right : F₂) :
    Fin (r + 2) → F₂ :=
  Fin.lastCases right (Fin.lastCases left v)

@[simp]
theorem appendTwo_small {r : ℕ} (v : Fin r → F₂) (left right : F₂)
    (j : Fin r) :
    appendTwo v left right j.castSucc.castSucc = v j := by
  simp [appendTwo]

@[simp]
theorem appendTwo_left {r : ℕ} (v : Fin r → F₂) (left right : F₂) :
    appendTwo v left right (Fin.last r).castSucc = left := by
  simp [appendTwo]

@[simp]
theorem appendTwo_right {r : ℕ} (v : Fin r → F₂) (left right : F₂) :
    appendTwo v left right (Fin.last (r + 1)) = right := by
  simp [appendTwo]

/--
The Section 8 column map with `r` small-prime rows and two independent
cardinality-parity rows.
-/
noncomputable def twoAugmentedColumnMap {m r : ℕ}
    (columns : Fin m → (Fin r → F₂))
    (leftBit rightBit : Fin m → F₂) :
    (Fin m → F₂) →ₗ[F₂] (Fin (r + 2) → F₂) :=
  Fintype.linearCombination F₂
    (fun i ↦ appendTwo (columns i) (leftBit i) (rightBit i))

/-- Evaluation on one of the `r` small-prime coordinates. -/
theorem twoAugmentedColumnMap_apply_small {m r : ℕ}
    (columns : Fin m → (Fin r → F₂))
    (leftBit rightBit : Fin m → F₂)
    (x : Fin m → F₂) (j : Fin r) :
    twoAugmentedColumnMap columns leftBit rightBit x
        j.castSucc.castSucc =
      ∑ i : Fin m, x i * columns i j := by
  simp [twoAugmentedColumnMap, Fintype.linearCombination_apply, smul_eq_mul]

/-- Evaluation on the appended left-cardinality parity coordinate. -/
theorem twoAugmentedColumnMap_apply_left {m r : ℕ}
    (columns : Fin m → (Fin r → F₂))
    (leftBit rightBit : Fin m → F₂)
    (x : Fin m → F₂) :
    twoAugmentedColumnMap columns leftBit rightBit x
        (Fin.last r).castSucc =
      ∑ i : Fin m, x i * leftBit i := by
  simp [twoAugmentedColumnMap, Fintype.linearCombination_apply, smul_eq_mul]

/-- Evaluation on the appended right-cardinality parity coordinate. -/
theorem twoAugmentedColumnMap_apply_right {m r : ℕ}
    (columns : Fin m → (Fin r → F₂))
    (leftBit rightBit : Fin m → F₂)
    (x : Fin m → F₂) :
    twoAugmentedColumnMap columns leftBit rightBit x
        (Fin.last (r + 1)) =
      ∑ i : Fin m, x i * rightBit i := by
  simp [twoAugmentedColumnMap, Fintype.linearCombination_apply, smul_eq_mul]

/-- The two appended rows cost at most two extra dimensions of codimension. -/
theorem columns_sub_twoAugmentedRows_le_finrank_ker {m r : ℕ}
    (columns : Fin m → (Fin r → F₂))
    (leftBit rightBit : Fin m → F₂) :
    m - (r + 2) ≤ Module.finrank F₂
      (LinearMap.ker
        (twoAugmentedColumnMap columns leftBit rightBit)) :=
  DefectCodeRank.columns_sub_rows_le_finrank_ker
    (twoAugmentedColumnMap columns leftBit rightBit)

/-- A kernel word has zero weighted sum in the left parity row. -/
theorem kernel_left_weighted_sum_eq_zero {m r : ℕ}
    (columns : Fin m → (Fin r → F₂))
    (leftBit rightBit : Fin m → F₂)
    (x : Fin m → F₂)
    (hx : x ∈ LinearMap.ker
      (twoAugmentedColumnMap columns leftBit rightBit)) :
    ∑ i : Fin m, x i * leftBit i = 0 := by
  have hzero := congrFun (LinearMap.mem_ker.mp hx) (Fin.last r).castSucc
  simpa [twoAugmentedColumnMap_apply_left] using hzero

/-- A kernel word has zero weighted sum in the right parity row. -/
theorem kernel_right_weighted_sum_eq_zero {m r : ℕ}
    (columns : Fin m → (Fin r → F₂))
    (leftBit rightBit : Fin m → F₂)
    (x : Fin m → F₂)
    (hx : x ∈ LinearMap.ker
      (twoAugmentedColumnMap columns leftBit rightBit)) :
    ∑ i : Fin m, x i * rightBit i = 0 := by
  have hzero := congrFun (LinearMap.mem_ker.mp hx) (Fin.last (r + 1))
  simpa [twoAugmentedColumnMap_apply_right] using hzero

/--
The selected components have zero total left parity.  This is the first
separate even-cardinality equation required before the Runge step.
-/
theorem kernel_left_selected_sum_eq_zero {m r : ℕ}
    (columns : Fin m → (Fin r → F₂))
    (leftBit rightBit : Fin m → F₂)
    (x : Fin m → F₂)
    (hx : x ∈ LinearMap.ker
      (twoAugmentedColumnMap columns leftBit rightBit)) :
    ∑ i ∈ HammingBound.wordSupport x, leftBit i = 0 := by
  rw [DefectCodeRank.sum_wordSupport_eq_weighted_sum]
  exact kernel_left_weighted_sum_eq_zero columns leftBit rightBit x hx

/--
The selected components have zero total right parity.  This is the second
separate even-cardinality equation required before the Runge step.
-/
theorem kernel_right_selected_sum_eq_zero {m r : ℕ}
    (columns : Fin m → (Fin r → F₂))
    (leftBit rightBit : Fin m → F₂)
    (x : Fin m → F₂)
    (hx : x ∈ LinearMap.ker
      (twoAugmentedColumnMap columns leftBit rightBit)) :
    ∑ i ∈ HammingBound.wordSupport x, rightBit i = 0 := by
  rw [DefectCodeRank.sum_wordSupport_eq_weighted_sum]
  exact kernel_right_weighted_sum_eq_zero columns leftBit rightBit x hx

/--
Quantitative Hamming consequence used in Theorem 8.1.

If the component count `m` reaches the explicit threshold forced by the
integer Hamming estimate, the two-parity column map has a nonzero kernel word
supported on at most `2 * t` components.
-/
theorem exists_nonzero_kernel_word_hammingNorm_le {m r t : ℕ}
    (columns : Fin m → (Fin r → F₂))
    (leftBit rightBit : Fin m → F₂)
    (ht : 1 ≤ t)
    (hmt : 2 * t ≤ m)
    (hrm : r + 2 ≤ m)
    (hlarge : 2 * t * 2 ^ ((r + 2) / t + 1) ≤ m) :
    ∃ x : Fin m → F₂,
      x ≠ 0 ∧
      x ∈ LinearMap.ker
        (twoAugmentedColumnMap columns leftBit rightBit) ∧
      hammingNorm x ≤ 2 * t := by
  let C : Submodule F₂ (Fin m → F₂) :=
    LinearMap.ker (twoAugmentedColumnMap columns leftBit rightBit)
  by_contra hno
  push Not at hno
  have hweight : HammingBound.MinWeightAbove C (2 * t) := by
    intro c hc
    have hcval : (c : Fin m → F₂) ≠ 0 := by
      intro hczero
      apply hc
      exact Subtype.ext hczero
    exact hno (c : Fin m → F₂) hcval c.property
  have hfinrank :
      m - (r + 2) ≤ Module.finrank F₂ C := by
    exact columns_sub_twoAugmentedRows_le_finrank_ker
      columns leftBit rightBit
  have hvolume :
      (∑ j ∈ Finset.range (t + 1), m.choose j) ≤ 2 ^ (r + 2) :=
    HammingBound.sum_choose_le_pow_of_finrank_ge
      hweight hfinrank hrm
  have hshort :
      m < 2 * t * 2 ^ ((r + 2) / t + 1) :=
    HammingDefectBound.length_lt_of_sum_choose_le_two_pow
      ht hmt hvolume
  omega

end TwoParityColumnCode
end PaperC
