import PaperCV282.WindowValues
import PaperC.Analysis.CriticalWeightedDefect

/-!
# Finite defect mass for prescribed words

A word uses the values `x - 1 + i`, `i < B`. The historical arithmetic
mass instead counts defects in `[x, x + B]`. The exceptional value `x - 1`
is therefore counted explicitly, using the injectivity of the root map.
-/

namespace PaperC.V282.WordDefectCounting

open DefectivePredicate WindowValues
open scoped BigOperators

noncomputable section

/-- Classical decidability of the arithmetic defect predicate. -/
local instance instDecidableHDefective (H n : ℕ) : Decidable (HDefective H n) :=
  Classical.propDecidable _

/-- The natural weighted defect mass of the article's prescribed words. -/
def wordDefectMass (N B : ℕ) : ℕ :=
  ∑ x ∈ dyadicBlock N, (2 ^ (defectIndices B x B).card - 1)

/-- Positive bounded intrinsic defects belong to the finite arithmetic set. -/
theorem mem_positiveDefectValues_of_hDefective
    {H X n : ℕ} (hn : n ≠ 0) (hnX : n ≤ X)
    (hdef : HDefective H n) :
    n ∈ WeightedDefectCounting.positiveDefectValues
      (DefectCounting.smallPrimesUpTo H) X := by
  apply Finset.mem_erase.mpr
  exact ⟨hn, DefectCounting.mem_defectValues_of_HDefectRepresentation
    (representationOfHDefective hdef hn) hnX⟩

/-- All word vertices except its root lie in the historical forward interval. -/
theorem card_defectIndices_le_localCount_add_root
    {x B X : ℕ} (hx : 2 ≤ x) (hupper : x + B ≤ X) :
    (defectIndices B x B).card ≤
      IntervalDefectAggregation.localCount
          (WeightedDefectCounting.positiveDefectValues
            (DefectCounting.smallPrimesUpTo B) X) B x +
        (if HDefective B (x - 1) then 1 else 0) := by
  classical
  let defects := WeightedDefectCounting.positiveDefectValues
    (DefectCounting.smallPrimesUpTo B) X
  let localDefects := IntervalDefectAggregation.defectsInInterval defects B x
  let rootDefects : Finset ℕ :=
    if HDefective B (x - 1) then {x - 1} else ∅
  have hcard : (defectIndices B x B).card ≤
      (localDefects ∪ rootDefects).card := by
    apply Finset.card_le_card_of_injOn (vertex x B)
    · intro i hi
      have hdef : HDefective B (vertex x B i) := by
        simpa [defectIndices] using hi
      by_cases hi0 : i.val = 0
      · apply Finset.mem_union.mpr
        right
        have hroot : HDefective B (x - 1) := by
          simpa [vertex, hi0] using hdef
        simp [rootDefects, hroot, vertex, hi0]
      · apply Finset.mem_union.mpr
        left
        apply IntervalDefectAggregation.mem_defectsInInterval.mpr
        have hiB := i.isLt
        have hvpos : vertex x B i ≠ 0 := by unfold vertex; omega
        have hvupper : vertex x B i ≤ X := by unfold vertex; omega
        exact ⟨mem_positiveDefectValues_of_hDefective hvpos hvupper hdef,
          by unfold vertex; omega, by unfold vertex; omega⟩
    · intro i _ j _ hij
      apply Fin.ext
      unfold vertex at hij
      omega
  calc
    (defectIndices B x B).card ≤ (localDefects ∪ rootDefects).card := hcard
    _ ≤ localDefects.card + rootDefects.card := Finset.card_union_le _ _
    _ = IntervalDefectAggregation.localCount defects B x +
        (if HDefective B (x - 1) then 1 else 0) := by
      by_cases hroot : HDefective B (x - 1)
      · simp [rootDefects, hroot, localDefects, IntervalDefectAggregation.localCount]
      · simp [rootDefects, hroot, localDefects, IntervalDefectAggregation.localCount]

/-- Adding one possible root defect costs twice the interval weight and its indicator. -/
theorem two_pow_sub_one_le_twice_add_indicator
    {m a : ℕ} (P : Prop) [Decidable P]
    (hm : m ≤ a + if P then 1 else 0) :
    2 ^ m - 1 ≤ 2 * (2 ^ a - 1) + if P then 1 else 0 := by
  have hapos : 0 < 2 ^ a := pow_pos (by omega) _
  by_cases hP : P
  · simp only [if_pos hP] at hm ⊢
    have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) hm
    rw [pow_succ] at hpow
    omega
  · simp only [if_neg hP, Nat.add_zero] at hm ⊢
    have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) hm
    omega

/-- Distinct positive starts have distinct roots, so their defective roots cost one global count. -/
theorem sum_root_defect_indicator_le
    {N B : ℕ} (hN : 2 ≤ N) (s : Finset ℕ)
    (hs : s ⊆ dyadicBlock N) :
    ∑ x ∈ s, (if HDefective B (x - 1) then 1 else 0) ≤
      (WeightedDefectCounting.positiveDefectValues
        (DefectCounting.smallPrimesUpTo B) (3 * N)).card := by
  classical
  have hcard :
      (s.filter fun x => HDefective B (x - 1)).card ≤
        (WeightedDefectCounting.positiveDefectValues
          (DefectCounting.smallPrimesUpTo B) (3 * N)).card := by
    apply Finset.card_le_card_of_injOn (fun x => x - 1)
    · intro x hx
      obtain ⟨hxs, hdef⟩ := Finset.mem_filter.mp hx
      have hxblock := Finset.mem_Ico.mp (hs hxs)
      apply mem_positiveDefectValues_of_hDefective
      · change x - 1 ≠ 0
        omega
      · change x - 1 ≤ 3 * N
        omega
      · exact hdef
    · intro x hx y hy hxy
      have hxblock := Finset.mem_Ico.mp (hs (Finset.mem_filter.mp hx).1)
      have hyblock := Finset.mem_Ico.mp (hs (Finset.mem_filter.mp hy).1)
      change x - 1 = y - 1 at hxy
      omega
  simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hcard

/-- The full word defect mass over any dyadic mask is bounded by historical arithmetic mass. -/
theorem sum_wordDefectWeight_le
    {N B : ℕ} (hN : 2 ≤ N) (hB : B ≤ N)
    (s : Finset ℕ) (hs : s ⊆ dyadicBlock N) :
    ∑ x ∈ s, (2 ^ (defectIndices B x B).card - 1) ≤
      2 * CriticalWeightedDefect.dyadicDefectMass N B +
        (WeightedDefectCounting.positiveDefectValues
          (DefectCounting.smallPrimesUpTo B) (3 * N)).card := by
  classical
  let defects := WeightedDefectCounting.positiveDefectValues
    (DefectCounting.smallPrimesUpTo B) (3 * N)
  let a := fun x => IntervalDefectAggregation.localCount defects B x
  have hpoint (x : ℕ) (hx : x ∈ s) :
      2 ^ (defectIndices B x B).card - 1 ≤
        2 * (2 ^ a x - 1) + if HDefective B (x - 1) then 1 else 0 := by
    have hxblock := Finset.mem_Ico.mp (hs hx)
    apply two_pow_sub_one_le_twice_add_indicator
    exact card_defectIndices_le_localCount_add_root
      (by omega) (by omega : x + B ≤ 3 * N)
  have hmass : ∑ x ∈ s, (2 ^ a x - 1) ≤
      CriticalWeightedDefect.dyadicDefectMass N B := by
    exact Finset.sum_le_sum_of_subset hs
  calc
    ∑ x ∈ s, (2 ^ (defectIndices B x B).card - 1) ≤
        ∑ x ∈ s,
          (2 * (2 ^ a x - 1) + if HDefective B (x - 1) then 1 else 0) :=
      Finset.sum_le_sum hpoint
    _ = 2 * (∑ x ∈ s, (2 ^ a x - 1)) +
        ∑ x ∈ s, (if HDefective B (x - 1) then 1 else 0) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * CriticalWeightedDefect.dyadicDefectMass N B + defects.card :=
      Nat.add_le_add (Nat.mul_le_mul_left 2 hmass)
        (sum_root_defect_indicator_le hN s hs)

/-- Specialization to every start in the dyadic block. -/
theorem wordDefectMass_le
    {N B : ℕ} (hN : 2 ≤ N) (hB : B ≤ N) :
    wordDefectMass N B ≤
      2 * CriticalWeightedDefect.dyadicDefectMass N B +
        (WeightedDefectCounting.positiveDefectValues
          (DefectCounting.smallPrimesUpTo B) (3 * N)).card :=
  sum_wordDefectWeight_le hN hB (dyadicBlock N) (Finset.Subset.refl _)

end
end PaperC.V282.WordDefectCounting
