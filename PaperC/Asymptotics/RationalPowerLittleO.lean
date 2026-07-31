import PaperC.Asymptotics.RationalPowers
import Mathlib.Data.Real.Archimedean

/-!
# From rational-power bounds to uniform little-oh

The reciprocal-power convention

`|f|^(qk) ≤ N^(pk+1)`

contains a genuine power saving whenever `p/q < r`.  This module converts
that saving into the repository's literal uniform little-oh predicate
relative to `N^r`.

No sign assumption on `f` is needed: both asymptotic predicates are stated
using absolute values.
-/

namespace PaperC
namespace UniformRationalPower

/--
A uniform `N^(p/q+o(1))` bound is uniformly little-oh of `N^r` whenever
`p < r*q`.

The proof uses the reciprocal-power estimate with `k=2`.  The strict
exponent gap then leaves at least one power of `N`, which absorbs the
arbitrary positive little-oh constant.
-/
theorem littleO_natPower_of_lt
    {p q r : ℕ}
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hpqr : p < r * q)
    (hf :
      UniformRationalPowerSubpolynomialOn
        p q admissible f) :
    UniformLittleOOn admissible f
      (fun N _ => (N : ℝ) ^ r) := by
  have hq : 0 < q := by
    by_contra hqNot
    have hqZero : q = 0 :=
      Nat.eq_zero_of_not_pos hqNot
    simp only [hqZero, Nat.mul_zero, Nat.not_lt_zero] at hpqr
  have htwo : 0 < 2 := by omega
  have hqTwo : 0 < q * 2 :=
    Nat.mul_pos hq htwo
  obtain ⟨Nf, hNf⟩ := hf 2 htwo
  intro ε hε
  have hεPow : 0 < ε ^ (q * 2) :=
    pow_pos hε _
  obtain ⟨K : ℕ, hK⟩ :=
    exists_nat_gt (1 / ε ^ (q * 2))
  refine ⟨max Nf (max K 1), ?_⟩
  intro N hN L hNL
  have hNfN : Nf ≤ N :=
    (le_max_left Nf (max K 1)).trans hN
  have hNtail : max K 1 ≤ N :=
    (le_max_right Nf (max K 1)).trans hN
  have hKN : K ≤ N :=
    (le_max_left K 1).trans hNtail
  have hNoneNat : 1 ≤ N :=
    (le_max_right K 1).trans hNtail
  have hKNReal : (K : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hKN
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hNoneNat
  have hlarge :
      1 / ε ^ (q * 2) < (N : ℝ) :=
    hK.trans_le hKNReal
  have hunit :
      (1 : ℝ) ≤ ε ^ (q * 2) * (N : ℝ) := by
    have hstrict :
        (1 : ℝ) <
          (N : ℝ) * ε ^ (q * 2) :=
      (div_lt_iff₀ hεPow).mp hlarge
    calc
      (1 : ℝ) ≤ (N : ℝ) * ε ^ (q * 2) :=
        hstrict.le
      _ = ε ^ (q * 2) * (N : ℝ) := by
        rw [mul_comm]
  have hexponent :
      p * 2 + 1 + 1 ≤ r * (q * 2) := by
    have hpSucc : p + 1 ≤ r * q := by
      omega
    calc
      p * 2 + 1 + 1 = (p + 1) * 2 := by
        omega
      _ ≤ (r * q) * 2 :=
        Nat.mul_le_mul_right 2 hpSucc
      _ = r * (q * 2) :=
        Nat.mul_assoc r q 2
  have hpowerMono :
      (N : ℝ) ^ (p * 2 + 1 + 1) ≤
        (N : ℝ) ^ (r * (q * 2)) :=
    pow_le_pow_right₀ hNone hexponent
  have hscale :
      (N : ℝ) ^ (p * 2 + 1) ≤
        ε ^ (q * 2) *
          (N : ℝ) ^ (r * (q * 2)) := by
    calc
      (N : ℝ) ^ (p * 2 + 1) =
          1 * (N : ℝ) ^ (p * 2 + 1) := by
        rw [one_mul]
      _ ≤
          (ε ^ (q * 2) * (N : ℝ)) *
            (N : ℝ) ^ (p * 2 + 1) :=
        mul_le_mul_of_nonneg_right hunit (by positivity)
      _ =
          ε ^ (q * 2) *
            (N : ℝ) ^ (p * 2 + 1 + 1) := by
        calc
          (ε ^ (q * 2) * (N : ℝ)) *
                (N : ℝ) ^ (p * 2 + 1) =
              ε ^ (q * 2) *
                ((N : ℝ) * (N : ℝ) ^ (p * 2 + 1)) :=
            mul_assoc _ _ _
          _ =
              ε ^ (q * 2) *
                ((N : ℝ) ^ (p * 2 + 1) * (N : ℝ)) := by
            rw [mul_comm (N : ℝ)
              ((N : ℝ) ^ (p * 2 + 1))]
          _ =
              ε ^ (q * 2) *
                (N : ℝ) ^ (p * 2 + 1 + 1) :=
            congrArg
              (fun x : ℝ => ε ^ (q * 2) * x)
              (pow_succ (N : ℝ) (p * 2 + 1)).symm
      _ ≤
          ε ^ (q * 2) *
            (N : ℝ) ^ (r * (q * 2)) :=
        mul_le_mul_of_nonneg_left hpowerMono hεPow.le
  have hlargePower :
      |f N L| ^ (q * 2) ≤
        (ε * (N : ℝ) ^ r) ^ (q * 2) := by
    calc
      |f N L| ^ (q * 2) ≤
          (N : ℝ) ^ (p * 2 + 1) :=
        hNf N hNfN L hNL
      _ ≤
          ε ^ (q * 2) *
            (N : ℝ) ^ (r * (q * 2)) :=
        hscale
      _ =
          (ε * (N : ℝ) ^ r) ^ (q * 2) := by
        rw [mul_pow, ← pow_mul]
  have hroot :
      |f N L| ≤ ε * (N : ℝ) ^ r :=
    (pow_le_pow_iff_left₀
      (abs_nonneg (f N L))
      (mul_nonneg hε.le (by positivity))
      (Nat.ne_of_gt hqTwo)).mp hlargePower
  simpa only [abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) ^ r)]
    using hroot

/--
The exponent produced by Proposition 7.4 is strictly below the quadratic
scale:

`N^(19/12+o(1)) = o(N^2)`,

uniformly in the same admissible family.
-/
theorem nineteenTwelfths_littleO_quadratic
    {admissible : ℕ → ℕ → Prop}
    {R : ℕ → ℕ → ℝ}
    (hR :
      UniformRationalPowerSubpolynomialOn
        19 12 admissible R) :
    UniformLittleOOn admissible R
      (fun N _ => (N : ℝ) ^ 2) :=
  littleO_natPower_of_lt (by decide) hR

end UniformRationalPower
end PaperC
