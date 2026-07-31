import Mathlib.Analysis.Normed.Group.Int
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# An elementary height bound for integral roots

This file isolates the last algebraic step in the proof of Paper C, Lemma 3.1.
For an integral polynomial `p`, its height is the largest absolute value of
one of its nonzero coefficients.  Cauchy's root bound, applied after mapping
`p` to `ℝ[X]`, gives the bound claimed in the paper.

In fact, integrality of the root and the strict form of Cauchy's bound give
the slightly stronger estimate `|u| ≤ height p`.  We also record verbatim the
weaker paper form `|u| ≤ 1 + height p`.
-/

namespace PaperC

open Finset NNReal Polynomial

/-- The (naive) height of an integral polynomial: the maximum of the absolute
values of its nonzero coefficients.  The height of the zero polynomial is
defined to be zero. -/
def integerPolynomialHeight (p : ℤ[X]) : ℕ :=
  p.support.sup fun n ↦ (p.coeff n).natAbs

@[simp]
theorem integerPolynomialHeight_zero :
    integerPolynomialHeight (0 : ℤ[X]) = 0 := by
  simp [integerPolynomialHeight]

/-- Every coefficient is bounded by the height, including coefficients outside
the support (which are zero). -/
theorem coeff_natAbs_le_integerPolynomialHeight (p : ℤ[X]) (n : ℕ) :
    (p.coeff n).natAbs ≤ integerPolynomialHeight p := by
  by_cases hn : n ∈ p.support
  · exact Finset.le_sup (f := fun m ↦ (p.coeff m).natAbs) hn
  · rw [Polynomial.notMem_support_iff.mp hn]
    simp [integerPolynomialHeight]

/-- The nonnegative norm of an integer viewed in `ℝ` is its natural absolute
value. -/
private theorem nnnorm_intCast_real (z : ℤ) :
    ‖(z : ℝ)‖₊ = (z.natAbs : ℝ≥0) := by
  apply NNReal.eq
  change |(z : ℝ)| = (z.natAbs : ℝ)
  rw [← Int.cast_abs]
  simpa only [Int.cast_natCast] using
    congrArg (fun w : ℤ ↦ (w : ℝ)) (Int.abs_eq_natAbs z)

/-- Cauchy's bound of the real polynomial obtained from `p` is no larger than
one plus the integral height of `p`. -/
theorem cauchyBound_map_intCast_le_height_add_one (p : ℤ[X]) :
    Polynomial.cauchyBound (p.map (Int.castRingHom ℝ)) ≤
      (integerPolynomialHeight p : ℝ≥0) + 1 := by
  by_cases hp : p = 0
  · subst p
    simp [integerPolynomialHeight]
  have hleading : p.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hp
  have hleading_one :
      (1 : ℝ≥0) ≤ ‖(p.map (Int.castRingHom ℝ)).leadingCoeff‖₊ := by
    rw [Polynomial.leadingCoeff_map_of_injective Int.cast_injective]
    change (1 : ℝ≥0) ≤ ‖(p.leadingCoeff : ℝ)‖₊
    rw [nnnorm_intCast_real]
    exact_mod_cast
      (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hleading))
  have hcoeff (n : ℕ) :
      ‖(p.map (Int.castRingHom ℝ)).coeff n‖₊ ≤
        (integerPolynomialHeight p : ℝ≥0) := by
    rw [Polynomial.coeff_map]
    change ‖(p.coeff n : ℝ)‖₊ ≤
      (integerPolynomialHeight p : ℝ≥0)
    rw [nnnorm_intCast_real]
    exact_mod_cast coeff_natAbs_le_integerPolynomialHeight p n
  rw [Polynomial.cauchyBound]
  apply add_le_add_left
  calc
    (Finset.range (p.map (Int.castRingHom ℝ)).natDegree).sup
          (fun n ↦ ‖(p.map (Int.castRingHom ℝ)).coeff n‖₊) /
        ‖(p.map (Int.castRingHom ℝ)).leadingCoeff‖₊
        ≤
      (Finset.range (p.map (Int.castRingHom ℝ)).natDegree).sup
          (fun n ↦ ‖(p.map (Int.castRingHom ℝ)).coeff n‖₊) / 1 := by
            gcongr
    _ =
      (Finset.range (p.map (Int.castRingHom ℝ)).natDegree).sup
        (fun n ↦ ‖(p.map (Int.castRingHom ℝ)).coeff n‖₊) := by
          simp
    _ ≤ (integerPolynomialHeight p : ℝ≥0) := by
      exact Finset.sup_le fun n _ ↦ hcoeff n

/-- Strong integral-root form.  It is one unit sharper than the real Cauchy
bound because both the root and the height are natural numbers. -/
theorem integerRoot_natAbs_le_height
    {p : ℤ[X]} (hp : p ≠ 0) {u : ℤ} (hu : p.IsRoot u) :
    u.natAbs ≤ integerPolynomialHeight p := by
  let pReal : ℝ[X] := p.map (Int.castRingHom ℝ)
  have hpReal : pReal ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff Int.cast_injective).2 hp
  have huReal : pReal.IsRoot (u : ℝ) := by
    exact hu.map (f := Int.castRingHom ℝ)
  have hroot :
      ‖(u : ℝ)‖₊ <
        (integerPolynomialHeight p : ℝ≥0) + 1 := by
    exact (huReal.norm_lt_cauchyBound hpReal).trans_le
      (cauchyBound_map_intCast_le_height_add_one p)
  have hrootNat :
      u.natAbs < integerPolynomialHeight p + 1 := by
    rw [nnnorm_intCast_real] at hroot
    exact_mod_cast hroot
  omega

/-- The exact formulation used in Paper C: an integral root of a nonzero
integral polynomial has absolute value at most one plus its height. -/
theorem integerRoot_natAbs_le_one_add_height
    {p : ℤ[X]} (hp : p ≠ 0) {u : ℤ} (hu : p.IsRoot u) :
    u.natAbs ≤ 1 + integerPolynomialHeight p := by
  have := integerRoot_natAbs_le_height hp hu
  omega

/-- Integer-valued version of `integerRoot_natAbs_le_one_add_height`, with
the usual absolute-value notation. -/
theorem integerRoot_abs_le_one_add_height
    {p : ℤ[X]} (hp : p ≠ 0) {u : ℤ} (hu : p.IsRoot u) :
    |u| ≤ ((1 + integerPolynomialHeight p : ℕ) : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast integerRoot_natAbs_le_one_add_height hp hu

end PaperC
