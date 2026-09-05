import PaperCV282.SplitProductLocalization
import PaperCV282.PositiveSquareclassPairs

/-!
# Unconditional split-product counting in polynomial height

Two distinct factors determine a positive-root Pell pair after their
canonical squareclasses are fixed. Localization pays for every possible
pair of squareclasses by the square of a single divisor count. This gives
the `M^epsilon` consequence needed for fixed-degree one-sided host counts,
with a threshold uniform over shifts and coefficients.
-/

namespace PaperC.V282.PolynomialSplitProducts

open ComponentNormalization DefectivePredicate PellInput
open SplitProductLocalization PositiveSquareclassPairs
open scoped BigOperators

noncomputable section

/-- Integer starts of a split-product square equation, with every factor positive. -/
def splitProductStart {d : ℕ} (h : Fin d → ℤ) (e H : ℕ) (X : ℤ) : Prop :=
  X.natAbs ≤ H ∧ (∀ i, 0 < X + h i) ∧
    ∃ Y : ℤ, ∏ i, (X + h i) = (e : ℤ) * Y ^ 2

/-- The positive canonical square root is no larger than its original integer. -/
theorem canonicalSquarePart_le {n : ℕ} (hn : 0 < n) : canonicalSquarePart n ≤ n := by
  obtain ⟨he, hesq, hv, heq⟩ := canonical_squarefree_decomposition hn
  calc
    canonicalSquarePart n ≤ canonicalSquarePart n ^ 2 := by nlinarith only [hv]
    _ ≤ squarefreeKernel n * canonicalSquarePart n ^ 2 := Nat.le_mul_of_pos_left _ he
    _ = n := heq.symm

/-- Height bookkeeping for a positive shifted factor. -/
theorem shifted_factor_le_polynomial {M K : ℕ} {X j : ℤ}
    (hM : 2 ≤ M) (hX : X.natAbs ≤ M ^ K) (hj : j.natAbs ≤ M ^ K) :
    (X + j).toNat ≤ M ^ (K + 1) := by
  calc
    (X + j).toNat ≤ (X + j).natAbs := by omega
    _ ≤ X.natAbs + j.natAbs := Int.natAbs_add_le _ _
    _ ≤ M ^ K + M ^ K := Nat.add_le_add hX hj
    _ ≤ M * M ^ K := by simpa only [two_mul] using Nat.mul_le_mul_right (M ^ K) hM
    _ = M ^ (K + 1) := (pow_succ' _ _).symm

/-- Fixing two squareclasses transfers the true start count injectively to positive Pell roots. -/
theorem card_fixed_squareclasses_le
    (s : Finset ℤ) {j k : ℤ} {A C H : ℕ} {R : ℝ}
    (hs : ∀ X ∈ s, 0 < X + j ∧ 0 < X + k ∧
      squarefreeKernel (X + j).toNat = A ∧ squarefreeKernel (X + k).toNat = C ∧
      (X + j).toNat ≤ H ∧ (X + k).toNat ≤ H)
    (hcount : HasAtMostSolutionsReal (positiveSquareclassBox A C H (j - k)) R) :
    (s.card : ℝ) ≤ R := by
  classical
  let f : ℤ → ℕ × ℕ := fun X =>
    (canonicalSquarePart (X + j).toNat, canonicalSquarePart (X + k).toNat)
  have hdecomp : ∀ X ∈ s,
      X + j = (A : ℤ) * ((f X).1 : ℤ) ^ 2 ∧
      X + k = (C : ℤ) * ((f X).2 : ℤ) ^ 2 := by
    intro X hX
    have hx := hs X hX
    have hjpos : 0 < (X + j).toNat := by omega
    have hkpos : 0 < (X + k).toNat := by omega
    have hjEq := (canonical_squarefree_decomposition hjpos).2.2.2
    have hkEq := (canonical_squarefree_decomposition hkpos).2.2.2
    rw [hx.2.2.1] at hjEq
    rw [hx.2.2.2.1] at hkEq
    constructor
    · have h := congrArg (fun n : ℕ => (n : ℤ)) hjEq
      simpa only [Nat.cast_mul, Nat.cast_pow, Int.toNat_of_nonneg hx.1.le, f] using h
    · have h := congrArg (fun n : ℕ => (n : ℤ)) hkEq
      simpa only [Nat.cast_mul, Nat.cast_pow, Int.toNat_of_nonneg hx.2.1.le, f] using h
  have hf : Set.InjOn f (s : Set ℤ) := by
    intro X hX Z hZ hXZ
    have hroot := congrArg Prod.fst hXZ
    have hfirst := (hdecomp X hX).1
    have hsecond := (hdecomp Z hZ).1
    rw [hroot] at hfirst
    linarith only [hfirst, hsecond]
  have himage : ∀ p ∈ s.image f, positiveSquareclassBox A C H (j - k) p := by
    intro p hp
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hp
    have hx := hs X hX
    have hjpos : 0 < (X + j).toNat := by omega
    have hkpos : 0 < (X + k).toNat := by omega
    refine ⟨(canonical_squarefree_decomposition hjpos).2.2.1,
      (canonical_squarefree_decomposition hkpos).2.2.1,
      (canonicalSquarePart_le hjpos).trans hx.2.2.2.2.1,
      (canonicalSquarePart_le hkpos).trans hx.2.2.2.2.2, ?_⟩
    have h := hdecomp X hX
    linarith only [h.1, h.2]
  have hcard := hcount (s.image f) himage
  rwa [Finset.card_image_iff.mpr hf] at hcard

/-- Fixed-degree split products have uniformly subpolynomially many integer starts.
The threshold precedes the complete shift tuple, coefficient and finite family. -/
theorem splitProductStart_atMost_rpow_eventually
    (K d : ℕ) (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ h : Fin d → ℤ, ∀ e : ℕ,
      Function.Injective h → 0 < e → e ≤ M ^ K →
      (∀ i, (h i).natAbs ≤ M ^ K) →
      HasAtMostSolutionsReal (splitProductStart h e (M ^ K)) ((M : ℝ) ^ epsilon) := by
  classical
  obtain ⟨Md, hdiv⟩ := card_squareclass_divisors_le_rpow_eventually K d (epsilon / 3) (by positivity)
  obtain ⟨Mp, hpell⟩ := positiveSquareclassBox_atMost_rpow_eventually (K + 1)
    (epsilon / 3) (by positivity)
  refine ⟨max Md (max Mp 2), ?_⟩
  intro M hM h e hh he heM hshift s hs
  have htail : max Mp 2 ≤ M := (le_max_right _ _).trans hM
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans htail
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by intro hij; have := congrArg Fin.val hij; dsimp [i, j] at this; omega
  have hdiff : h i - h j ≠ 0 := sub_ne_zero.mpr (fun hEq => hij (hh hEq))
  let S : Finset ℕ := (e * shiftDifferenceProduct h).divisors
  let color : ℤ → ℕ × ℕ := fun X =>
    (squarefreeKernel (X + h i).toNat, squarefreeKernel (X + h j).toNat)
  have htarget : e * shiftDifferenceProduct h ≠ 0 := (Nat.mul_pos he (shiftDifferenceProduct_pos hh)).ne'
  have hcolors : ∀ X ∈ s, color X ∈ S ×ˢ S := by
    intro X hX
    obtain ⟨hheight, hpositive, Y, heq⟩ := hs X hX
    exact Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨squarefreeKernel_shift_dvd hh he hpositive heq i, htarget⟩,
       Nat.mem_divisors.mpr ⟨squarefreeKernel_shift_dvd hh he hpositive heq j, htarget⟩⟩
  have hshiftDiff : (h i - h j).natAbs ≤ M ^ (K + 1) := by
    calc
      _ ≤ (h i).natAbs + (h j).natAbs := Int.natAbs_sub_le _ _
      _ ≤ M ^ K + M ^ K := Nat.add_le_add (hshift i) (hshift j)
      _ ≤ M * M ^ K := by simpa only [two_mul] using Nat.mul_le_mul_right (M ^ K) hMtwo
      _ = _ := (pow_succ' _ _).symm
  have hfibers : ∀ c ∈ S ×ˢ S,
      ((s.filter (fun X => color X = c)).card : ℝ) ≤ (M : ℝ) ^ (epsilon / 3) := by
    intro c hc
    let fiber := s.filter (fun X => color X = c)
    by_cases hempty : fiber = ∅
    · change (fiber.card : ℝ) ≤ _
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · obtain ⟨X, hX⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hXmem := Finset.mem_filter.mp hX
      have hXprop := hs X hXmem.1
      have hXcolor := hXmem.2
      have hiEq : squarefreeKernel (X + h i).toNat = c.1 := congrArg Prod.fst hXcolor
      have hjEq : squarefreeKernel (X + h j).toNat = c.2 := congrArg Prod.snd hXcolor
      have hiPos : 0 < (X + h i).toNat := by have := hXprop.2.1 i; omega
      have hjPos : 0 < (X + h j).toNat := by have := hXprop.2.1 j; omega
      have hA : 0 < c.1 := hiEq ▸ squarefreeKernel_pos _
      have hC : 0 < c.2 := hjEq ▸ squarefreeKernel_pos _
      have hAsq : Squarefree c.1 := hiEq ▸ squarefreeKernel_squarefree _
      have hCsq : Squarefree c.2 := hjEq ▸ squarefreeKernel_squarefree _
      have hAH : c.1 ≤ M ^ (K + 1) := by
        rw [← hiEq]
        exact (squarefreeKernel_le hiPos).trans (shifted_factor_le_polynomial hMtwo hXprop.1 (hshift i))
      have hCH : c.2 ≤ M ^ (K + 1) := by
        rw [← hjEq]
        exact (squarefreeKernel_le hjPos).trans (shifted_factor_le_polynomial hMtwo hXprop.1 (hshift j))
      apply card_fixed_squareclasses_le _ _
        (hpell M ((le_max_left _ _).trans htail) c.1 c.2 (M ^ (K + 1)) (h i - h j)
          hA hC hAsq hCsq hdiff hAH hCH le_rfl hshiftDiff)
      intro Z hZ
      have hz := Finset.mem_filter.mp hZ
      have hzprop := hs Z hz.1
      exact ⟨hzprop.2.1 i, hzprop.2.1 j, congrArg Prod.fst hz.2, congrArg Prod.snd hz.2,
        shifted_factor_le_polynomial hMtwo hzprop.1 (hshift i),
        shifted_factor_le_polynomial hMtwo hzprop.1 (hshift j)⟩
  have hsum : (s.card : ℝ) ≤ (S.card : ℝ) ^ 2 * (M : ℝ) ^ (epsilon / 3) := by
    rw [Finset.card_eq_sum_card_fiberwise hcolors, Nat.cast_sum]
    calc
      _ ≤ ∑ _c ∈ S ×ˢ S, (M : ℝ) ^ (epsilon / 3) := Finset.sum_le_sum hfibers
      _ = _ := by simp [pow_two]
  have hS : (S.card : ℝ) ≤ (M : ℝ) ^ (epsilon / 3) :=
    hdiv M ((le_max_left _ _).trans hM) e h heM hshift
  calc
    (s.card : ℝ) ≤ (S.card : ℝ) ^ 2 * (M : ℝ) ^ (epsilon / 3) := hsum
    _ ≤ ((M : ℝ) ^ (epsilon / 3)) ^ 2 * (M : ℝ) ^ (epsilon / 3) := by gcongr
    _ = (M : ℝ) ^ epsilon := by
      rw [pow_two, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
      congr 1
      ring

end
end PaperC.V282.PolynomialSplitProducts
