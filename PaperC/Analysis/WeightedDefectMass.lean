import PaperC.Analysis.DefectGlobalBound
import PaperC.Coding.IntervalDefectBound
import PaperC.Combinatorics.IntervalDefectAggregation

/-!
# Assembling the finite weighted defect mass

The pointwise Runge--Hamming estimate, the global Euler-product count, and the
sliding-interval double count are combined here.  The result is an explicit
finite inequality immediately preceding the uniform asymptotic notation in
equation (3.4).
-/

namespace PaperC
namespace WeightedDefectMass

open scoped BigOperators

/--
If `[U,U+H] ⊆ [1,X]`, filtering the global positive defect set by this
interval gives exactly the concrete interval set used by the coding theorem.
-/
theorem localCount_positiveDefectValues_eq
    {H U X : ℕ}
    (hU : 0 < U)
    (hUX : U + H ≤ X) :
    IntervalDefectAggregation.localCount
        (WeightedDefectCounting.positiveDefectValues
          (DefectCounting.smallPrimesUpTo H) X) H U =
      (IntervalDefectBound.defectsInInterval H U).card := by
  unfold IntervalDefectAggregation.localCount
  apply congrArg Finset.card
  ext n
  rw [IntervalDefectAggregation.mem_defectsInInterval,
    IntervalDefectBound.mem_defectsInInterval,
    WeightedDefectCounting.mem_positiveDefectValues_iff,
    DefectCounting.mem_defectValues_iff]
  constructor
  · rintro ⟨⟨hn0, _hnX, support, hs, a, ha, hvalue⟩,
      hUn, hnUpper⟩
    let rep :
        DefectCounting.DefectRepresentation
          (DefectCounting.smallPrimesUpTo H) n :=
      { support := support
        support_subset := hs
        squarePart := a
        value_eq := hvalue }
    have haLocal : a ≤ Nat.sqrt (U + H) := by
      apply DefectCounting.squarePart_le_sqrt
        (P := DefectCounting.smallPrimesUpTo H) (rep := rep)
      · intro p hp
        exact
          (DefectCounting.mem_smallPrimesUpTo.mp hp).1.one_lt.le
      · exact hnUpper
    exact
      ⟨⟨hnUpper, support, hs, a, haLocal, hvalue⟩, hUn, hnUpper⟩
  · rintro ⟨⟨_hnUpper, support, hs, a, ha, hvalue⟩,
      hUn, hnUpper⟩
    have hn0 : n ≠ 0 := by omega
    have haGlobal : a ≤ Nat.sqrt X :=
      ha.trans (Nat.sqrt_le_sqrt hUX)
    exact
      ⟨⟨hn0, hnUpper.trans hUX, support, hs, a, haGlobal, hvalue⟩,
        hUn, hnUpper⟩

/--
Fully assembled natural-number bound for the weighted local mass.

The hypothesis `PrimesUpTo.count H + 1 ≤ A*t` is the finite constant-ratio
condition supplied asymptotically by the Chebyshev estimate and the
logarithmic choice of `t`.
-/
theorem sum_two_pow_localCount_sub_one_le
    {H X t A : ℕ}
    (starts : Finset ℕ)
    (hH : 2 ≤ H)
    (hstartLower : ∀ u ∈ starts, 2 * H ≤ u)
    (hstartUpper : ∀ u ∈ starts, u + H ≤ X)
    (ht : 1 ≤ t)
    (hlog : ∀ u ∈ starts,
      (4 * t : ℝ) * Real.log (128 * (2 * t) * H) <
        Real.log u)
    (hratio : PrimesUpTo.count H + 1 ≤ A * t) :
    let defects :=
      WeightedDefectCounting.positiveDefectValues
        (DefectCounting.smallPrimesUpTo H) X
    ∑ u ∈ starts,
        (2 ^ IntervalDefectAggregation.localCount defects H u - 1) ≤
      (H + 1) * defects.card *
        2 ^ (2 * t * 2 ^ (A + 1)) := by
  dsimp only
  apply IntervalDefectAggregation.sum_two_pow_localCount_sub_one_le
  intro u hu
  rw [localCount_positiveDefectValues_eq
    (by have := hstartLower u hu; omega) (hstartUpper u hu)]
  exact Nat.le_of_lt
    (IntervalDefectBound.card_defectsInInterval_lt_of_log_of_count_ratio
      hH (hstartLower u hu) ht (hlog u hu) hratio)

/--
Real-valued form with the global arithmetic count replaced by its elementary
Euler-product estimate.
-/
theorem sum_two_pow_localCount_sub_one_cast_le
    {H X t A : ℕ}
    (starts : Finset ℕ)
    (hH : 2 ≤ H)
    (hstartLower : ∀ u ∈ starts, 2 * H ≤ u)
    (hstartUpper : ∀ u ∈ starts, u + H ≤ X)
    (ht : 1 ≤ t)
    (hlog : ∀ u ∈ starts,
      (4 * t : ℝ) * Real.log (128 * (2 * t) * H) <
        Real.log u)
    (hratio : PrimesUpTo.count H + 1 ≤ A * t) :
    let defects :=
      WeightedDefectCounting.positiveDefectValues
        (DefectCounting.smallPrimesUpTo H) X
    ((∑ u ∈ starts,
        (2 ^ IntervalDefectAggregation.localCount defects H u - 1) : ℕ) :
        ℝ) ≤
      (H + 1 : ℝ) * Real.sqrt X *
        Real.exp (2 * Real.sqrt H) *
        ((2 ^ (2 * t * 2 ^ (A + 1)) : ℕ) : ℝ) := by
  dsimp only
  let defects :=
    WeightedDefectCounting.positiveDefectValues
      (DefectCounting.smallPrimesUpTo H) X
  have hfinite :=
    sum_two_pow_localCount_sub_one_le
      starts hH hstartLower hstartUpper ht hlog hratio
  have hcast :
      (((∑ u ∈ starts,
          (2 ^ IntervalDefectAggregation.localCount defects H u - 1)) :
          ℕ) : ℝ) ≤
        (((H + 1) * defects.card *
          2 ^ (2 * t * 2 ^ (A + 1)) : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  calc
    (((∑ u ∈ starts,
        (2 ^ IntervalDefectAggregation.localCount defects H u - 1)) :
        ℕ) : ℝ)
        ≤ (((H + 1) * defects.card *
          2 ^ (2 * t * 2 ^ (A + 1)) : ℕ) : ℝ) :=
      hcast
    _ = (H + 1 : ℝ) * (defects.card : ℝ) *
          ((2 ^ (2 * t * 2 ^ (A + 1)) : ℕ) : ℝ) := by
      norm_num
    _ ≤ (H + 1 : ℝ) *
          (Real.sqrt X * Real.exp (2 * Real.sqrt H)) *
          ((2 ^ (2 * t * 2 ^ (A + 1)) : ℕ) : ℝ) := by
      gcongr
      exact card_positiveHDefectValues_cast_le_sqrt_mul_exp H X
    _ = (H + 1 : ℝ) * Real.sqrt X *
          Real.exp (2 * Real.sqrt H) *
          ((2 ^ (2 * t * 2 ^ (A + 1)) : ℕ) : ℝ) := by
      ring

/--
Chebyshev-specialized assembled mass bound.  Its hypotheses no longer mention
the cardinality of the prime-coordinate type.
-/
theorem sum_two_pow_localCount_sub_one_cast_le_of_chebyshev_budget
    {H X t A : ℕ}
    (starts : Finset ℕ)
    (hH : 4 ≤ H)
    (hstartLower : ∀ u ∈ starts, 2 * H ≤ u)
    (hstartUpper : ∀ u ∈ starts, u + H ≤ X)
    (ht : 1 ≤ t)
    (hlog : ∀ u ∈ starts,
      (4 * t : ℝ) * Real.log (128 * (2 * t) * H) <
        Real.log u)
    (hbudget :
      (7 * H) / Nat.log 2 H + 1 ≤ A * t) :
    let defects :=
      WeightedDefectCounting.positiveDefectValues
        (DefectCounting.smallPrimesUpTo H) X
    ((∑ u ∈ starts,
        (2 ^ IntervalDefectAggregation.localCount defects H u - 1) : ℕ) :
        ℝ) ≤
      (H + 1 : ℝ) * Real.sqrt X *
        Real.exp (2 * Real.sqrt H) *
        ((2 ^ (2 * t * 2 ^ (A + 1)) : ℕ) : ℝ) := by
  apply sum_two_pow_localCount_sub_one_cast_le
    starts (by omega) hstartLower hstartUpper ht hlog
  have hcount :=
    ChebyshevPrimeCount.count_le_seven_mul_div_log hH
  omega

/--
Uniform finite form for a family of translated intervals.  A single floored
radius chosen at the common lower endpoint `N` works for every start `u ≥ N`.
-/
theorem sum_two_pow_localCount_sub_one_cast_le_of_cappedRadius
    {N H X T A : ℕ}
    (starts : Finset ℕ)
    (hH : 4 ≤ H)
    (hN : 2 * H ≤ N)
    (hstartLower : ∀ u ∈ starts, N ≤ u)
    (hstartUpper : ∀ u ∈ starts, u + H ≤ X)
    (hT : 1 ≤ T)
    (hpositive :
      1 ≤ RungeLogarithmicGrowth.cappedRadius N H T)
    (hbelow :
      RungeLogarithmicGrowth.cappedRadius N H T ≤ T)
    (hbudget :
      (7 * H) / Nat.log 2 H + 1 ≤
        A * RungeLogarithmicGrowth.cappedRadius N H T) :
    let defects :=
      WeightedDefectCounting.positiveDefectValues
        (DefectCounting.smallPrimesUpTo H) X
    ((∑ u ∈ starts,
        (2 ^ IntervalDefectAggregation.localCount defects H u - 1) : ℕ) :
        ℝ) ≤
      (H + 1 : ℝ) * Real.sqrt X *
        Real.exp (2 * Real.sqrt H) *
        ((2 ^ (2 * RungeLogarithmicGrowth.cappedRadius N H T *
          2 ^ (A + 1)) : ℕ) : ℝ) := by
  apply
    sum_two_pow_localCount_sub_one_cast_le_of_chebyshev_budget
      starts hH
  · intro u hu
    exact hN.trans (hstartLower u hu)
  · exact hstartUpper
  · exact hpositive
  · intro u hu
    apply RungeLogarithmicGrowth.log_endpoint_mono
      (U := N) (V := u)
    · omega
    · exact hstartLower u hu
    · apply RungeLogarithmicGrowth.cappedRadius_log_endpoint
      · omega
      · omega
      · exact hT
      · exact hpositive
      · exact hbelow
  · exact hbudget

end WeightedDefectMass
end PaperC
