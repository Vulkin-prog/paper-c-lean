import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons

/-! # Integer power sums for Appendix G

Integral comparisons over all integers suffice; no prime distribution input
is used in these finite estimates.
-/
namespace PaperC.Prel8.RoughKernelPowerSums

open scoped BigOperators

/-- A decreasing power sum is bounded by its integral from the lower endpoint. -/
theorem sum_Ioc_le_integral (B X : ℕ) (hB : 1 ≤ B) (hBX : B ≤ X)
    {a : ℝ} (ha : a ≤ 0) :
    (∑ n ∈ Finset.Ioc B X, (n : ℝ) ^ a) ≤ ∫ x in (B : ℝ)..X, x ^ a := by
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ a) (Set.Icc (B : ℝ) X) := by
    refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos ha).mono ?_
    intro x hx
    exact (show (0 : ℝ) < B by exact_mod_cast (show 0 < B by omega)).trans_le hx.1
  have hsum := hanti.sum_le_integral_Ico hBX
  have hindex : (∑ i ∈ Finset.Ico B X, ((i + 1 : ℕ) : ℝ) ^ a) =
      ∑ n ∈ Finset.Ioc B X, (n : ℝ) ^ a := by
    refine Finset.sum_bij (fun i _ ↦ i + 1) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro i hi
      simp only [Finset.mem_Ico, Finset.mem_Ioc] at hi ⊢
      omega
    · intro i hi j hj hij
      change i + 1 = j + 1 at hij
      omega
    · intro n hn
      have hn' := Finset.mem_Ioc.mp hn
      refine ⟨n - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
  rwa [hindex] at hsum

/-- The truncated Rankin sum, including the endpoint 1 and the empty case. -/
theorem sum_Icc_rankin_le (T : ℕ) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    (∑ r ∈ Finset.Icc 1 T, (r : ℝ) ^ (-1 + σ)) ≤
      1 + (T : ℝ) ^ σ / σ := by
  by_cases hT : 1 ≤ T
  · have hsum := sum_Ioc_le_integral 1 T (by omega) hT (a := -1 + σ) (by linarith)
    have hint : (∫ x in (1 : ℝ)..T, x ^ (-1 + σ)) =
        ((T : ℝ) ^ σ - 1) / σ := by
      rw [integral_rpow (Or.inl (by linarith))]
      rw [show -1 + σ + 1 = σ by ring, Real.one_rpow]
    simp only [Nat.cast_one] at hsum
    rw [hint] at hsum
    have hsplit : Finset.Icc 1 T = insert 1 (Finset.Ioc 1 T) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [hsplit, Finset.sum_insert (by simp)]
    simp only [Nat.cast_one, Real.one_rpow]
    have : 0 ≤ 1 / σ := le_of_lt (one_div_pos.mpr hσ)
    calc
      1 + ∑ r ∈ Finset.Ioc 1 T, (r : ℝ) ^ (-1 + σ)
          ≤ 1 + ((T : ℝ) ^ σ - 1) / σ := add_le_add (le_refl 1) hsum
      _ ≤ 1 + (T : ℝ) ^ σ / σ := by rw [sub_div]; linarith
  · have : T = 0 := by omega
    subst T
    simp [Real.zero_rpow hσ.ne']

/-- A convergent power tail; the cutoff may exceed the upper endpoint. -/
theorem sum_Ioc_tail_le (Y X : ℕ) (hY : 1 ≤ Y) {s : ℝ} (hs : 0 < s) :
    (∑ r ∈ Finset.Ioc Y X, (r : ℝ) ^ (-1 - s)) ≤ (Y : ℝ) ^ (-s) / s := by
  by_cases hYX : Y ≤ X
  · have hsum := sum_Ioc_le_integral Y X hY hYX (a := -1 - s) (by linarith)
    have hint : (∫ x in (Y : ℝ)..X, x ^ (-1 - s)) =
        ((Y : ℝ) ^ (-s) - (X : ℝ) ^ (-s)) / s := by
      rw [integral_rpow]
      · rw [show -1 - s + 1 = -s by ring]
        ring
      · right
        refine ⟨by linarith, ?_⟩
        intro hz
        rw [Set.mem_uIcc] at hz
        have hy : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
        have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
        rcases hz with hz | hz <;> linarith
    rw [hint] at hsum
    exact hsum.trans (div_le_div_of_nonneg_right
      (sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg X) _)) hs.le)
  · have hempty : Finset.Ioc Y X = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have := Finset.mem_Ioc.mp hn
      omega
    rw [hempty, Finset.sum_empty]
    positivity

end PaperC.Prel8.RoughKernelPowerSums
