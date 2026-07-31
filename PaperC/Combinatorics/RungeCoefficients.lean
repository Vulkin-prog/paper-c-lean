import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Coefficients in the Runge expansion

This file isolates the finite combinatorics used in equation (3.2) of
Paper C.  The analytic identity involving the product of square-root power
series is deliberately not part of this file.
-/

namespace PaperC
namespace RungeCoefficients

open Finset
open scoped BigOperators

noncomputable instance instBinomialRingRat : BinomialRing ℚ where
  multichoose r n :=
    (n.factorial : ℚ)⁻¹ * Polynomial.smeval (ascPochhammer ℕ n) r
  factorial_nsmul_multichoose r n := by
    simp only [nsmul_eq_mul]
    field_simp

/-- The generalized binomial coefficient `(1/2 choose j)`. -/
noncomputable def halfChoose (j : ℕ) : ℚ :=
  Ring.choose (1 / 2 : ℚ) j

/-- The standard one-step recurrence for generalized binomial coefficients
over `ℚ`. -/
theorem choose_succ_recursion (r : ℚ) (n : ℕ) :
    (n + 1 : ℚ) * Ring.choose r (n + 1) =
      (r - n) * Ring.choose r n := by
  apply (mul_left_cancel₀ (show (n.factorial : ℚ) ≠ 0 by positivity))
  calc
    (n.factorial : ℚ) * ((n + 1 : ℚ) * Ring.choose r (n + 1)) =
        ((n + 1).factorial : ℚ) * Ring.choose r (n + 1) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
    _ = (descPochhammer ℤ (n + 1)).smeval r := by
      simpa [nsmul_eq_mul] using
        (Ring.descPochhammer_eq_factorial_smul_choose r (n + 1)).symm
    _ = (descPochhammer ℤ n).smeval r * (r - n) := by
      rw [descPochhammer_succ_right, Polynomial.smeval_mul,
        Polynomial.smeval_sub, Polynomial.smeval_X,
        Polynomial.smeval_natCast]
      simp
    _ = (n.factorial : ℚ) * ((r - n) * Ring.choose r n) := by
      rw [Ring.descPochhammer_eq_factorial_smul_choose]
      simp only [nsmul_eq_mul]
      ring

/-- Quotient form of `choose_succ_recursion`. -/
theorem choose_succ_eq (r : ℚ) (n : ℕ) :
    Ring.choose r (n + 1) =
      Ring.choose r n * ((r - n) / (n + 1 : ℚ)) := by
  have h := choose_succ_recursion r n
  field_simp
  nlinarith

private theorem abs_half_step_le_one (n : ℕ) :
    |((1 / 2 : ℚ) - n) / (n + 1 : ℚ)| ≤ 1 := by
  have hden : 0 < (n + 1 : ℚ) := by positivity
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_le_iff₀ hden]
    linarith

/-- The elementary estimate `|(1/2 choose j)| ≤ 1` used in (3.2). -/
theorem abs_halfChoose_le_one (j : ℕ) : |halfChoose j| ≤ 1 := by
  induction j with
  | zero =>
      simp [halfChoose]
  | succ j ih =>
      rw [halfChoose, choose_succ_eq, abs_mul]
      calc
        |Ring.choose (1 / 2 : ℚ) j| *
              |((1 / 2 : ℚ) - j) / (j + 1 : ℚ)| ≤
            |Ring.choose (1 / 2 : ℚ) j| * 1 :=
          mul_le_mul_of_nonneg_left (abs_half_step_le_one j) (abs_nonneg _)
        _ ≤ 1 := by simpa [halfChoose] using ih

/-- The multiplicative Catalan recurrence, cast to `ℚ`. -/
private theorem catalan_succ_recursion (n : ℕ) :
    (n + 2 : ℚ) * (catalan (n + 1) : ℚ) =
      2 * (2 * n + 1 : ℚ) * (catalan n : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n + 1),
    ← succ_mul_catalan_eq_centralBinom n] at h
  have hq :
      (n + 1 : ℚ) * ((n + 2 : ℚ) * (catalan (n + 1) : ℚ)) =
        2 * (2 * n + 1 : ℚ) *
          ((n + 1 : ℚ) * (catalan n : ℚ)) := by
    exact_mod_cast h
  apply (mul_left_cancel₀ (show (n + 1 : ℚ) ≠ 0 by positivity))
  calc
    (n + 1 : ℚ) * ((n + 2 : ℚ) * (catalan (n + 1) : ℚ)) =
        2 * (2 * n + 1 : ℚ) *
          ((n + 1 : ℚ) * (catalan n : ℚ)) := hq
    _ = (n + 1 : ℚ) *
        (2 * (2 * n + 1 : ℚ) * (catalan n : ℚ)) := by ring

/-- The usual Catalan formula for the nonconstant coefficients of
`(1+z)^(1/2)`.  It also records the exact power-of-two denominator. -/
theorem halfChoose_succ_eq_catalan (n : ℕ) :
    halfChoose (n + 1) =
      (-1 : ℚ) ^ n * (catalan n : ℚ) / (2 : ℚ) ^ (2 * n + 1) := by
  induction n with
  | zero =>
      norm_num [halfChoose, Ring.choose_one_right, catalan_zero]
  | succ n ih =>
      change Ring.choose (1 / 2 : ℚ) ((n + 1) + 1) =
        (-1 : ℚ) ^ (n + 1) * (catalan (n + 1) : ℚ) /
          (2 : ℚ) ^ (2 * (n + 1) + 1)
      rw [choose_succ_eq]
      rw [show Ring.choose (1 / 2 : ℚ) (n + 1) = halfChoose (n + 1) by rfl]
      push_cast
      rw [ih]
      have hcat := catalan_succ_recursion n
      have hp :
          (2 : ℚ) ^ (2 * (n + 1) + 1) =
            4 * (2 : ℚ) ^ (2 * n + 1) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
        norm_num
        ring
      rw [hp, show (-1 : ℚ) ^ (n + 1) = (-1 : ℚ) ^ n * (-1) by rw [pow_succ]]
      field_simp
      ring_nf
      simp only [Nat.add_comm 1 n]
      linear_combination
        2 * hcat

/-- Multiplying `(1/2 choose j)` by `2^(2j)` gives an integer. -/
theorem two_pow_two_mul_halfChoose_isInt (j : ℕ) :
    ∃ z : ℤ, (2 : ℚ) ^ (2 * j) * halfChoose j = (z : ℚ) := by
  cases j with
  | zero =>
      exact ⟨1, by simp [halfChoose]⟩
  | succ n =>
      refine ⟨2 * (-1 : ℤ) ^ n * (catalan n : ℤ), ?_⟩
      rw [halfChoose_succ_eq_catalan]
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, pow_succ]
      push_cast
      field_simp

/-- Weak compositions of `m` into `d` labelled parts. -/
abbrev WeakComposition (d m : ℕ) :=
  {j : Fin d → ℕ // ∑ i, j i = m}

noncomputable instance instFintypeWeakComposition (d m : ℕ) :
    Fintype (WeakComposition d m) :=
  Fintype.ofEquiv (Sym (Fin d) m)
    (Sym.equivNatSumOfFintype (Fin d) m)

/-- Stars and bars, in the exact form needed for the Runge coefficient. -/
theorem card_weakComposition (d m : ℕ) :
    Fintype.card (WeakComposition d m) = (d + m - 1).choose m := by
  calc
    Fintype.card (WeakComposition d m) =
        Fintype.card (Sym (Fin d) m) :=
      Fintype.card_congr (Sym.equivNatSumOfFintype (Fin d) m).symm
    _ = (d + m - 1).choose m := by
      simpa using Sym.card_sym_eq_choose (α := Fin d) m

/-- The paper's symmetric stars-and-bars form
`(m+d-1 choose d-1)`, valid when there is at least one part. -/
theorem card_weakComposition_eq_choose_parts
    {d m : ℕ} (hd : 0 < d) :
    Fintype.card (WeakComposition d m) =
      (m + d - 1).choose (d - 1) := by
  rw [card_weakComposition, add_comm d m]
  exact Nat.choose_symm_of_eq_add (by omega)

/-- The loose but uniform estimate used in (3.2). -/
theorem card_weakComposition_le_two_pow
    {d m : ℕ} (hd : 0 < d) :
    Fintype.card (WeakComposition d m) ≤ 2 ^ (m + d) := by
  rw [card_weakComposition]
  by_cases hn0 : d + m - 1 = 0
  · have hm : m = 0 := by omega
    have hd1 : d = 1 := by omega
    subst m
    subst d
    norm_num
  exact (Nat.choose_le_two_pow (d + m - 1) m).trans
    (Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega))

/-- The finite multi-index sum which is the coefficient `c_m` in the
product of the `d` square-root series. -/
noncomputable def rungeCoefficient
    {d : ℕ} (γ : Fin d → ℤ) (m : ℕ) : ℚ :=
  ∑ j : WeakComposition d m,
    ∏ ν, halfChoose (j.1 ν) * (γ ν : ℚ) ^ (j.1 ν)

/-- A rational number represented by an integer. -/
def IsRatInteger (q : ℚ) : Prop :=
  ∃ z : ℤ, q = (z : ℚ)

private theorem IsRatInteger.mul {x y : ℚ}
    (hx : IsRatInteger x) (hy : IsRatInteger y) :
    IsRatInteger (x * y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a * b, by norm_cast⟩

private theorem IsRatInteger.add {x y : ℚ}
    (hx : IsRatInteger x) (hy : IsRatInteger y) :
    IsRatInteger (x + y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a + b, by norm_cast⟩

private theorem IsRatInteger.sum
    {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (hf : ∀ i ∈ s, IsRatInteger (f i)) :
    IsRatInteger (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (by simp)).add
        (ih fun i hi ↦ hf i (by simp [hi]))

private theorem IsRatInteger.prod
    {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (hf : ∀ i ∈ s, IsRatInteger (f i)) :
    IsRatInteger (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, by simp⟩
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hf a (by simp)).mul
        (ih fun i hi ↦ hf i (by simp [hi]))

private theorem scaled_rungeSummand_isRatInteger
    {d m : ℕ} (γ : Fin d → ℤ) (j : WeakComposition d m) :
    IsRatInteger
      ((2 : ℚ) ^ (2 * m) *
        ∏ ν, halfChoose (j.1 ν) * (γ ν : ℚ) ^ (j.1 ν)) := by
  have hlocal :
      ∀ ν : Fin d,
        IsRatInteger
          ((2 : ℚ) ^ (2 * j.1 ν) * halfChoose (j.1 ν) *
            (γ ν : ℚ) ^ (j.1 ν)) := by
    intro ν
    rcases two_pow_two_mul_halfChoose_isInt (j.1 ν) with ⟨z, hz⟩
    refine ⟨z * (γ ν) ^ (j.1 ν), ?_⟩
    rw [hz]
    norm_cast
  have hprod :
      IsRatInteger
        (∏ ν,
          ((2 : ℚ) ^ (2 * j.1 ν) * halfChoose (j.1 ν)) *
            (γ ν : ℚ) ^ (j.1 ν)) := by
    apply IsRatInteger.prod (s := (Finset.univ : Finset (Fin d)))
    · intro ν _
      exact hlocal ν
  have hexp : 2 * m = ∑ ν, 2 * j.1 ν := by
    calc
      2 * m = 2 * (∑ ν, j.1 ν) :=
        congrArg (fun x ↦ 2 * x) j.2.symm
      _ = ∑ ν, 2 * j.1 ν := Finset.mul_sum _ _ _
  rw [hexp, ← Finset.prod_pow_eq_pow_sum]
  rw [← Finset.prod_mul_distrib]
  simpa [mul_assoc] using hprod

/-- The first, sharper integrality statement behind (3.2):
`2^(2m) c_m` is integral. -/
theorem two_pow_two_mul_rungeCoefficient_isRatInteger
    {d : ℕ} (γ : Fin d → ℤ) (m : ℕ) :
    IsRatInteger ((2 : ℚ) ^ (2 * m) * rungeCoefficient γ m) := by
  unfold rungeCoefficient
  rw [Finset.mul_sum]
  apply IsRatInteger.sum
  intro j _
  exact scaled_rungeSummand_isRatInteger γ j

/-- The integrality assertion in (3.2): if `2m ≤ d`, then `2^d c_m`
is an integer. -/
theorem two_pow_mul_rungeCoefficient_isRatInteger
    {d m : ℕ} (γ : Fin d → ℤ) (hmd : 2 * m ≤ d) :
    IsRatInteger ((2 : ℚ) ^ d * rungeCoefficient γ m) := by
  rcases two_pow_two_mul_rungeCoefficient_isRatInteger γ m with ⟨z, hz⟩
  refine ⟨(2 : ℤ) ^ (d - 2 * m) * z, ?_⟩
  calc
    (2 : ℚ) ^ d * rungeCoefficient γ m =
        (2 : ℚ) ^ (d - 2 * m) *
          ((2 : ℚ) ^ (2 * m) * rungeCoefficient γ m) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmd]
    _ = (2 : ℚ) ^ (d - 2 * m) * (z : ℚ) := by rw [hz]
    _ = ((2 : ℤ) ^ (d - 2 * m) * z : ℤ) := by norm_cast

private theorem abs_rungeSummand_le
    {d m : ℕ} {γ : Fin d → ℤ} {R : ℚ}
    (hγ : ∀ ν, |(γ ν : ℚ)| ≤ R)
    (j : WeakComposition d m) :
    |∏ ν, halfChoose (j.1 ν) * (γ ν : ℚ) ^ (j.1 ν)| ≤ R ^ m := by
  rw [abs_prod]
  calc
    (∏ ν, |halfChoose (j.1 ν) * (γ ν : ℚ) ^ (j.1 ν)|) ≤
        ∏ ν, R ^ (j.1 ν) := by
      apply Finset.prod_le_prod
      · intro ν _
        exact abs_nonneg _
      · intro ν _
        rw [abs_mul, abs_pow]
        calc
          |halfChoose (j.1 ν)| * |(γ ν : ℚ)| ^ (j.1 ν) ≤
              1 * R ^ (j.1 ν) := by
            gcongr
            · exact abs_halfChoose_le_one _
            · exact hγ ν
          _ = R ^ (j.1 ν) := one_mul _
    _ = R ^ (∑ ν, j.1 ν) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = R ^ m := by rw [j.2]

/-- The precise finite-sum majorant behind the second inequality in (3.2). -/
theorem abs_rungeCoefficient_le_card_mul
    {d m : ℕ} {γ : Fin d → ℤ} {R : ℚ}
    (hγ : ∀ ν, |(γ ν : ℚ)| ≤ R) :
    |rungeCoefficient γ m| ≤
      (Fintype.card (WeakComposition d m) : ℚ) * R ^ m := by
  unfold rungeCoefficient
  calc
    |∑ j : WeakComposition d m,
        ∏ ν, halfChoose (j.1 ν) * (γ ν : ℚ) ^ (j.1 ν)| ≤
        ∑ j : WeakComposition d m,
          |∏ ν, halfChoose (j.1 ν) * (γ ν : ℚ) ^ (j.1 ν)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : WeakComposition d m, R ^ m :=
      Finset.sum_le_sum fun j _ ↦ abs_rungeSummand_le hγ j
    _ = (Fintype.card (WeakComposition d m) : ℚ) * R ^ m := by simp

/-- Equation (3.2)'s coefficient bound before the final simplification
`m ≤ d/2`, namely `|c_m| ≤ 2^(m+d) R^m`. -/
theorem abs_rungeCoefficient_le
    {d m : ℕ} {γ : Fin d → ℤ} {R : ℚ}
    (hd : 0 < d) (hR : 0 ≤ R)
    (hγ : ∀ ν, |(γ ν : ℚ)| ≤ R) :
    |rungeCoefficient γ m| ≤ (2 : ℚ) ^ (m + d) * R ^ m := by
  refine (abs_rungeCoefficient_le_card_mul hγ).trans ?_
  gcongr
  exact_mod_cast card_weakComposition_le_two_pow (d := d) (m := m) hd

/-- The final coarse form recorded in (3.2).  The paper has `m ≤ d / 2`;
the slightly weaker consequence `m ≤ d` is all that this estimate uses. -/
theorem abs_rungeCoefficient_le_eight_mul_pow
    {d m : ℕ} {γ : Fin d → ℤ} {R : ℚ}
    (hd : 0 < d) (hR : 1 ≤ R) (hmd : m ≤ d)
    (hγ : ∀ ν, |(γ ν : ℚ)| ≤ R) :
    |rungeCoefficient γ m| ≤ (8 * R) ^ d := by
  calc
    |rungeCoefficient γ m| ≤ (2 : ℚ) ^ (m + d) * R ^ m :=
      abs_rungeCoefficient_le hd (zero_le_one.trans hR) hγ
    _ ≤ (2 : ℚ) ^ (d + d) * R ^ d := by
      gcongr
      · norm_num
    _ = (4 * R) ^ d := by
      rw [pow_add, ← mul_pow]
      ring_nf
    _ ≤ (8 * R) ^ d := by
      gcongr
      nlinarith

end RungeCoefficients
end PaperC
