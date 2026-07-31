import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact uniqueness criterion for a reduced channel

This is the integer core of Paper C, Lemma 5.2.  Two reduced fractions with
bounded numerators and denominators cannot both give a sufficiently accurate
relation `b*y - a*x` once `x` is larger than the determinant error bound.
-/

namespace PaperC

/--
If two reduced positive pairs `(a,b)` and `(a',b')`, all bounded by `H`,
satisfy the channel inequalities with error scale `B`, and
`x > 4 H² B`, then the pairs coincide.
-/
theorem reducedChannel_unique
    (x y B H a b a' b' : ℕ)
    (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (hab : a.Coprime b) (hab' : a'.Coprime b')
    (haH : a ≤ H) (hbH : b ≤ H) (ha'H : a' ≤ H) (hb'H : b' ≤ H)
    (hx : 4 * H ^ 2 * B < x)
    (hclose :
      |(b : ℤ) * (y : ℤ) - (a : ℤ) * (x : ℤ)| <
        ((a + b) * B : ℕ))
    (hclose' :
      |(b' : ℤ) * (y : ℤ) - (a' : ℤ) * (x : ℤ)| <
        ((a' + b') * B : ℕ)) :
    a = a' ∧ b = b' := by
  let e : ℤ := (b : ℤ) * (y : ℤ) - (a : ℤ) * (x : ℤ)
  let e' : ℤ := (b' : ℤ) * (y : ℤ) - (a' : ℤ) * (x : ℤ)
  let det : ℤ := (a' : ℤ) * (b : ℤ) - (a : ℤ) * (b' : ℤ)
  have hidentity :
      det * (x : ℤ) = (b' : ℤ) * e - (b : ℤ) * e' := by
    dsimp [det, e, e']
    ring
  have hnonneg_b : (0 : ℤ) ≤ (b : ℤ) := by positivity
  have hnonneg_b' : (0 : ℤ) ≤ (b' : ℤ) := by positivity
  have herror :
      |det * (x : ℤ)| <
        (b' : ℤ) * (((a + b) * B : ℕ) : ℤ) +
          (b : ℤ) * (((a' + b') * B : ℕ) : ℤ) := by
    rw [hidentity]
    calc
      |(b' : ℤ) * e - (b : ℤ) * e'| ≤
          |(b' : ℤ) * e| + |(b : ℤ) * e'| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le ((b' : ℤ) * e) 0 ((b : ℤ) * e')
      _ = (b' : ℤ) * |e| + (b : ℤ) * |e'| := by
        simp [abs_mul, abs_of_nonneg, hnonneg_b, hnonneg_b']
      _ < (b' : ℤ) * (((a + b) * B : ℕ) : ℤ) +
          (b : ℤ) * (((a' + b') * B : ℕ) : ℤ) := by
        dsimp [e, e']
        exact add_lt_add
          (mul_lt_mul_of_pos_left hclose (by exact_mod_cast hb'))
          (mul_lt_mul_of_pos_left hclose' (by exact_mod_cast hb))
  have hbound :
      (b' : ℤ) * (((a + b) * B : ℕ) : ℤ) +
          (b : ℤ) * (((a' + b') * B : ℕ) : ℤ) ≤
        ((4 * H ^ 2 * B : ℕ) : ℤ) := by
    norm_cast
    calc
      b' * ((a + b) * B) + b * ((a' + b') * B) ≤
          H * ((H + H) * B) + H * ((H + H) * B) := by
            gcongr
      _ = 4 * H ^ 2 * B := by ring
  have hdetMul :
      |det * (x : ℤ)| < (x : ℤ) :=
    herror.trans_le hbound |>.trans (by exact_mod_cast hx)
  have hxpos : (0 : ℤ) < (x : ℤ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hx)
  have hdet : det = 0 := by
    by_contra hne
    have hone : (1 : ℤ) ≤ |det| := Int.one_le_abs hne
    rw [abs_mul, abs_of_pos hxpos] at hdetMul
    nlinarith
  have hcrossInt :
      (a' : ℤ) * (b : ℤ) = (a : ℤ) * (b' : ℤ) := by
    dsimp [det] at hdet
    linarith
  have hquot :
      ((a : ℤ) : ℚ) / (b : ℤ) =
        ((a' : ℤ) : ℚ) / (b' : ℤ) := by
    apply (div_eq_div_iff
      (by exact_mod_cast hb.ne')
      (by exact_mod_cast hb'.ne')).2
    exact_mod_cast hcrossInt.symm
  have hcopInt :
      Nat.Coprime (a : ℤ).natAbs (b : ℤ).natAbs := by
    simpa using hab
  have hcopInt' :
      Nat.Coprime (a' : ℤ).natAbs (b' : ℤ).natAbs := by
    simpa using hab'
  obtain ⟨haa', hbb'⟩ :=
    Rat.div_int_inj
      (by exact_mod_cast hb)
      (by exact_mod_cast hb')
      hcopInt hcopInt' hquot
  exact ⟨by exact_mod_cast haa', by exact_mod_cast hbb'⟩

end PaperC
