import PaperCV282.PolynomialSplitProducts

/-!
# Counting both coordinates of a split-product equation

The start count loses at most the two signs of the square root. This
records the full polynomial-height `M^epsilon` consequence for integral
solutions of the split-product equation, without imposing an additional
height restriction on the second coordinate.
-/

namespace PaperC.V282.PolynomialSplitSolutions

open PellInput PolynomialSplitProducts
open scoped BigOperators

noncomputable section

/-- The actual two-coordinate equation with positive shifted factors. -/
def splitProductSolution {d : ℕ} (h : Fin d → ℤ) (e H : ℕ) (p : ℤ × ℤ) : Prop :=
  p.1.natAbs ≤ H ∧ (∀ i, 0 < p.1 + h i) ∧
    ∏ i, (p.1 + h i) = (e : ℤ) * p.2 ^ 2

/-- Every solution projects to one of the already counted starts. -/
theorem splitProductSolution_to_start
    {d e H : ℕ} {h : Fin d → ℤ} {p : ℤ × ℤ}
    (hp : splitProductSolution h e H p) : splitProductStart h e H p.1 :=
  ⟨hp.1, hp.2.1, p.2, hp.2.2⟩

/-- Each fixed start has at most the two possible signs of its square root. -/
theorem card_splitProductSolution_fiber_le_two
    {d e H : ℕ} {h : Fin d → ℤ} (he : 0 < e)
    (s : Finset (ℤ × ℤ)) (hs : ∀ p ∈ s, splitProductSolution h e H p) (X : ℤ) :
    (s.filter (fun p => p.1 = X)).card ≤ 2 := by
  classical
  let fiber := s.filter (fun p => p.1 = X)
  by_cases hempty : fiber = ∅
  · change fiber.card ≤ 2
    rw [hempty]
    simp
  · obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hqmem := Finset.mem_filter.mp hq
    have hqeq := (hs q hqmem.1).2.2
    have hsubset : fiber ⊆ {(X, q.2), (X, -q.2)} := by
      intro p hp
      have hpmem := Finset.mem_filter.mp hp
      have hpeq := (hs p hpmem.1).2.2
      have hfirst : p.1 = q.1 := hpmem.2.trans hqmem.2.symm
      rw [hfirst] at hpeq
      have hsquare : p.2 ^ 2 = q.2 ^ 2 := mul_left_cancel₀
        (by exact_mod_cast he.ne' : (e : ℤ) ≠ 0) (hpeq.symm.trans hqeq)
      have hsign : p.2 = q.2 ∨ p.2 = -q.2 := sq_eq_sq_iff_eq_or_eq_neg.mp hsquare
      rcases hsign with hpos | hneg
      · have hpEq : p = (X, q.2) := Prod.ext hpmem.2 hpos
        simp only [hpEq, Finset.mem_insert, Finset.mem_singleton, true_or]
      · have hpEq : p = (X, -q.2) := Prod.ext hpmem.2 hneg
        simp only [hpEq, Finset.mem_insert, Finset.mem_singleton, or_true]
    change fiber.card ≤ 2
    exact (Finset.card_le_card hsubset).trans (Finset.card_insert_le _ _ |>.trans (by simp))

/-- The complete solution count is at most twice the start count. -/
theorem splitProductSolution_atMost_of_start
    {d e H : ℕ} {h : Fin d → ℤ} {R : ℝ} (he : 0 < e)
    (hcount : HasAtMostSolutionsReal (splitProductStart h e H) R) :
    HasAtMostSolutionsReal (splitProductSolution h e H) (2 * R) := by
  classical
  intro s hs
  have himage : ∀ X ∈ s.image Prod.fst, splitProductStart h e H X := by
    intro X hX
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hX
    exact splitProductSolution_to_start (hs p hp)
  have hstarts := hcount _ himage
  calc
    (s.card : ℝ) = ∑ X ∈ s.image Prod.fst, ((s.filter (fun p => p.1 = X)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_image Prod.fst s, Nat.cast_sum]
    _ ≤ ∑ _X ∈ s.image Prod.fst, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro X hX
      exact_mod_cast card_splitProductSolution_fiber_le_two he s hs X
    _ = 2 * ((s.image Prod.fst).card : ℝ) := by simp [mul_comm]
    _ ≤ 2 * R := mul_le_mul_of_nonneg_left hstarts (by norm_num)

/-- The full integral solution count has the same uniform positive-power bound. -/
theorem splitProductSolution_atMost_rpow_eventually
    (K d : ℕ) (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ h : Fin d → ℤ, ∀ e : ℕ,
      Function.Injective h → 0 < e → e ≤ M ^ K →
      (∀ i, (h i).natAbs ≤ M ^ K) →
      HasAtMostSolutionsReal (splitProductSolution h e (M ^ K)) ((M : ℝ) ^ epsilon) := by
  obtain ⟨Mstart, hstart⟩ := splitProductStart_atMost_rpow_eventually K d hd
    (epsilon / 2) (by positivity)
  refine ⟨max Mstart (max 1 ⌈(2 : ℝ) ^ (2 / epsilon)⌉₊), ?_⟩
  intro M hM h e hh he heM hshift
  have htail : max 1 ⌈(2 : ℝ) ^ (2 / epsilon)⌉₊ ≤ M := (le_max_right _ _).trans hM
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by have := (le_max_left _ _).trans htail; omega)
  have hbase : (2 : ℝ) ^ (2 / epsilon) ≤ M := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans htail)
  have htwo : (2 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    calc
      (2 : ℝ) = ((2 : ℝ) ^ (2 / epsilon)) ^ (epsilon / 2) := by
        rw [← Real.rpow_mul (by norm_num), div_mul_div_cancel₀ hepsilon.ne']
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hbase (by positivity)
  have hfinite := splitProductSolution_atMost_of_start he
    (hstart M ((le_max_left _ _).trans hM) h e hh he heM hshift)
  intro s hs
  calc
    (s.card : ℝ) ≤ 2 * (M : ℝ) ^ (epsilon / 2) := hfinite s hs
    _ ≤ (M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2) := by gcongr
    _ = (M : ℝ) ^ epsilon := by rw [← Real.rpow_add hMpos]; congr 1; ring

end
end PaperC.V282.PolynomialSplitSolutions
