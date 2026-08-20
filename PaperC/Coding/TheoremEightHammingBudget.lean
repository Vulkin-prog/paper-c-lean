import PaperC.Arithmetic.ChebyshevPrimeCount
import PaperC.Coding.TwoParityColumnCode
import PaperC.Probability.CriticalRunWindow
import Mathlib.Algebra.Order.Floor.Div

/-!
# An explicit Hamming budget for Theorem 8.1

This file supplies a fully integral choice of the radius in the component
code argument.  Write

`L = ⌊log₂ B⌋`, `ℓ = ⌊log₂ L⌋`, and

`t(B) = ⌈64 B / (L ℓ)⌉`.

The elementary Chebyshev estimate `L * π(B) ≤ 7B` then gives
`π(B) ≤ t(B) * ℓ`.  Consequently the exponential term in the Hamming
threshold is at most `4L`.  The two explicit large-`B` conditions below
absorb both the ceiling error and the remaining factor `1 / ℓ`.

The numerical constants are deliberately generous.  Their role is to make
all natural-number divisions and cancellations transparent, not to optimize
the threshold.
-/

namespace PaperC
namespace TheoremEightHammingBudget

/-- Integral radius used for the short component word in Theorem 8.1. -/
def componentHammingRadius (B : ℕ) : ℕ :=
  (64 * B) ⌈/⌉
    (Nat.log 2 B * Nat.log 2 (Nat.log 2 B))

private theorem sq_le_two_pow_of_four_le :
    ∀ n : ℕ, 4 ≤ n → n * n ≤ 2 ^ n := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      have hstep :
          (4 + (k + 1)) * (4 + (k + 1)) ≤
            2 * ((4 + k) * (4 + k)) := by
        nlinarith [Nat.zero_le k]
      calc
        (4 + (k + 1)) * (4 + (k + 1))
            ≤ 2 * ((4 + k) * (4 + k)) := hstep
        _ ≤ 2 * 2 ^ (4 + k) :=
          Nat.mul_le_mul_left 2 (ih (by omega))
        _ = 2 ^ (4 + (k + 1)) := by
          rw [show 4 + (k + 1) = (4 + k) + 1 by omega, pow_succ]
          ring

/--
The dyadic logarithmic denominator in `componentHammingRadius` is at most
`B`.  This is the elementary inequality
`L log₂ L ≤ L² ≤ 2^L ≤ B`.
-/
theorem radius_denominator_le
    {B : ℕ}
    (hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 B)) :
    Nat.log 2 B * Nat.log 2 (Nat.log 2 B) ≤ B := by
  let L := Nat.log 2 B
  let ell := Nat.log 2 L
  have hellpos : 0 < ell := by
    simpa only [ell, L] using
      (show 0 < Nat.log 2 (Nat.log 2 B) by omega)
  have helllarge : 16384 ≤ ell := by
    simpa only [ell, L] using hloglog
  have hLtwo : 2 ≤ L :=
    (Nat.log_pos_iff.mp hellpos).1
  have hLfour : 4 ≤ L := by
    have hpow :
        2 ^ 2 ≤ 2 ^ ell :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hLne : L ≠ 0 := by omega
    have hpell : 2 ^ ell ≤ L :=
      Nat.pow_log_le_self 2 hLne
    have : 4 ≤ 2 ^ ell := by
      simpa using hpow
    exact this.trans hpell
  have hBne : B ≠ 0 := by
    intro hB
    simp [L, ell, hB] at hloglog
  have hellL : ell ≤ L := by
    dsimp [ell]
    exact Nat.log_le_self 2 L
  calc
    Nat.log 2 B * Nat.log 2 (Nat.log 2 B) = L * ell := rfl
    _ ≤ L * L := Nat.mul_le_mul_left L hellL
    _ ≤ 2 ^ L := sq_le_two_pow_of_four_le L hLfour
    _ ≤ B := by
      dsimp [L]
      exact Nat.pow_log_le_self 2 hBne

/--
The single double-log threshold already implies the linear-log estimate used
to absorb the ceiling error.
-/
theorem log_linear_le_of_loglog
    {B : ℕ}
    (hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 B)) :
    256 * Nat.log 2 B ≤ B := by
  let L := Nat.log 2 B
  let ell := Nat.log 2 L
  have helllarge : 16384 ≤ ell := by
    simpa only [ell, L] using hloglog
  have hellpos : 0 < ell := by omega
  have hLne : L ≠ 0 := by
    have : 2 ≤ L := (Nat.log_pos_iff.mp hellpos).1
    omega
  have hL256 : 256 ≤ L := by
    calc
      256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ ell :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ L := Nat.pow_log_le_self 2 hLne
  have hLfour : 4 ≤ L := by omega
  have hBne : B ≠ 0 := by
    intro hB
    simp [L, ell, hB] at hloglog
  calc
    256 * Nat.log 2 B = 256 * L := rfl
    _ ≤ L * L := Nat.mul_le_mul_right L hL256
    _ ≤ 2 ^ L := sq_le_two_pow_of_four_le L hLfour
    _ ≤ B := by
      dsimp [L]
      exact Nat.pow_log_le_self 2 hBne

/--
Real-valued facade for the order of the chosen radius.  The logarithms here
are the exact integral dyadic logarithms used by the finite code.
-/
theorem componentHammingRadius_cast_le
    {B : ℕ}
    (hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 B)) :
    (componentHammingRadius B : ℝ) ≤
      65 * (B : ℝ) /
        ((Nat.log 2 B : ℝ) *
          (Nat.log 2 (Nat.log 2 B) : ℝ)) := by
  let L := Nat.log 2 B
  let ell := Nat.log 2 L
  let d := L * ell
  let q := (64 * B) / d
  let t := componentHammingRadius B
  have hellpos : 0 < ell := by
    simpa only [ell, L] using
      (show 0 < Nat.log 2 (Nat.log 2 B) by omega)
  have hLpos : 0 < L := by
    have : 2 ≤ L := (Nat.log_pos_iff.mp hellpos).1
    omega
  have hdpos : 0 < d := Nat.mul_pos hLpos hellpos
  have hdB : d ≤ B := by
    simpa only [d, L, ell] using radius_denominator_le hloglog
  have htupper : t ≤ q + 1 := by
    dsimp [t, q, componentHammingRadius]
    rw [ceilDiv_le_iff_le_mul hdpos]
    exact (Nat.lt_mul_div_succ (64 * B) hdpos).le
  have hqcast :
      (q : ℝ) ≤ (64 * (B : ℝ)) / (d : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hdpos : (0 : ℝ) < d)).2
    have hqmul : q * d ≤ 64 * B := by
      simpa only [q] using Nat.div_mul_le_self (64 * B) d
    exact_mod_cast hqmul
  have hone :
      (1 : ℝ) ≤ (B : ℝ) / (d : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hdpos : (0 : ℝ) < d)).2
    norm_num
    exact_mod_cast hdB
  calc
    (componentHammingRadius B : ℝ) = (t : ℝ) := rfl
    _ ≤ (q + 1 : ℕ) := by exact_mod_cast htupper
    _ = (q : ℝ) + 1 := by push_cast; ring
    _ ≤ (64 * (B : ℝ)) / (d : ℝ) + 1 :=
      add_le_add_left hqcast 1
    _ ≤ (64 * (B : ℝ)) / (d : ℝ) +
          (B : ℝ) / (d : ℝ) :=
      add_le_add_right hone _
    _ = 65 * (B : ℝ) / (d : ℝ) := by ring
    _ = 65 * (B : ℝ) /
        ((Nat.log 2 B : ℝ) *
          (Nat.log 2 (Nat.log 2 B) : ℝ)) := by
      norm_num [d, L, ell, Nat.cast_mul]

/-- The chosen ceiling radius is nonzero, in fact at least `64`. -/
theorem sixty_four_le_componentHammingRadius
    {B : ℕ}
    (hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 B)) :
    64 ≤ componentHammingRadius B := by
  let L := Nat.log 2 B
  let ell := Nat.log 2 L
  let d := L * ell
  let t := componentHammingRadius B
  have hellpos : 0 < ell := by
    simpa only [ell, L] using
      (show 0 < Nat.log 2 (Nat.log 2 B) by omega)
  have helllarge : 16384 ≤ ell := by
    simpa only [ell, L] using hloglog
  have hLpos : 0 < L := by
    have : 2 ≤ L := (Nat.log_pos_iff.mp hellpos).1
    omega
  have hdpos : 0 < d := Nat.mul_pos hLpos hellpos
  have hdB : d ≤ B := by
    simpa only [d, L, ell] using radius_denominator_le hloglog
  have hBpos : 0 < B := hLpos.trans_le (Nat.log_le_self 2 B)
  have hlower : 64 * B ≤ d * t := by
    simpa only [componentHammingRadius, d, t, L, ell] using
      ((ceilDiv_le_iff_le_mul hdpos).1
        (le_rfl :
          (64 * B) ⌈/⌉
              (Nat.log 2 B * Nat.log 2 (Nat.log 2 B)) ≤
            (64 * B) ⌈/⌉
              (Nat.log 2 B * Nat.log 2 (Nat.log 2 B))))
  have hBt : B * 64 ≤ B * t := by
    calc
      B * 64 = 64 * B := by ring
      _ ≤ d * t := hlower
      _ ≤ B * t := Nat.mul_le_mul_right t hdB
  exact Nat.le_of_mul_le_mul_left hBt hBpos

/--
Chebyshev plus the defining lower bound for the ceiling radius controls the
row-to-radius ratio by `log₂ log₂ B`.
-/
theorem primeRows_le_radius_mul_loglog
    {B : ℕ}
    (hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 B)) :
    PrimesUpTo.count B ≤
      componentHammingRadius B *
        Nat.log 2 (Nat.log 2 B) := by
  let L := Nat.log 2 B
  let ell := Nat.log 2 L
  let d := L * ell
  let t := componentHammingRadius B
  have hellpos : 0 < ell := by
    simpa only [ell, L] using
      (show 0 < Nat.log 2 (Nat.log 2 B) by omega)
  have helllarge : 16384 ≤ ell := by
    simpa only [ell, L] using hloglog
  have hLpos : 0 < L := by
    have : 2 ≤ L := (Nat.log_pos_iff.mp hellpos).1
    omega
  have hBfour : 4 ≤ B := by
    have hLfour : 4 ≤ L := by
      have hpow :
          2 ^ 2 ≤ 2 ^ ell :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hLne : L ≠ 0 := by omega
      have hpell : 2 ^ ell ≤ L :=
        Nat.pow_log_le_self 2 hLne
      have : 4 ≤ 2 ^ ell := by
        simpa using hpow
      exact this.trans hpell
    exact hLfour.trans (Nat.log_le_self 2 B)
  have hcheb :
      L * PrimesUpTo.count B ≤ 7 * B := by
    simpa only [L] using
      ChebyshevPrimeCount.log_mul_count_le_seven_mul hBfour
  have hdpos : 0 < d := Nat.mul_pos hLpos hellpos
  have hlower : 64 * B ≤ d * t := by
    simpa only [componentHammingRadius, d, t, L, ell] using
      ((ceilDiv_le_iff_le_mul hdpos).1
        (le_rfl :
          (64 * B) ⌈/⌉
              (Nat.log 2 B * Nat.log 2 (Nat.log 2 B)) ≤
            (64 * B) ⌈/⌉
              (Nat.log 2 B * Nat.log 2 (Nat.log 2 B))))
  have hmul :
      L * PrimesUpTo.count B ≤ L * (t * ell) := by
    calc
      L * PrimesUpTo.count B ≤ 7 * B := hcheb
      _ ≤ 64 * B := by omega
      _ ≤ d * t := hlower
      _ = L * (t * ell) := by
        dsimp [d]
        ring
  simpa only [t, ell, L] using
    Nat.le_of_mul_le_mul_left hmul hLpos

/--
The ceiling error in `t(B)` is harmless after multiplication by
`L = log₂ B`.
-/
theorem radius_mul_log_budget
    {B : ℕ}
    (hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 B))
    (hlogLinear : 256 * Nat.log 2 B ≤ B) :
    128 * (componentHammingRadius B * Nat.log 2 B) ≤ B := by
  let L := Nat.log 2 B
  let ell := Nat.log 2 L
  let d := L * ell
  let q := (64 * B) / d
  let t := componentHammingRadius B
  have hellpos : 0 < ell := by
    simpa only [ell, L] using
      (show 0 < Nat.log 2 (Nat.log 2 B) by omega)
  have hLpos : 0 < L := by
    have : 2 ≤ L := (Nat.log_pos_iff.mp hellpos).1
    omega
  have hdpos : 0 < d := Nat.mul_pos hLpos hellpos
  have htupper : t ≤ q + 1 := by
    dsimp [t, q, componentHammingRadius]
    rw [ceilDiv_le_iff_le_mul hdpos]
    exact (Nat.lt_mul_div_succ (64 * B) hdpos).le
  have hqmul : q * d ≤ 64 * B := by
    simpa only [q] using Nat.div_mul_le_self (64 * B) d
  have hqLmul :
      (q * L) * ell ≤ 64 * B := by
    calc
      (q * L) * ell = q * d := by
        dsimp [d]
        ring
      _ ≤ 64 * B := hqmul
  have hscaled :
      256 * (q * L) ≤ B := by
    have hfirst :
        (q * L) * 16384 ≤ 64 * B :=
      (Nat.mul_le_mul_left (q * L) hloglog).trans hqLmul
    have hcancel :
        64 * (256 * (q * L)) ≤ 64 * B := by
      convert hfirst using 1
      ring
    exact Nat.le_of_mul_le_mul_left hcancel (by omega)
  have htL :
      t * L ≤ q * L + L := by
    calc
      t * L ≤ (q + 1) * L := Nat.mul_le_mul_right L htupper
      _ = q * L + L := by ring
  have hdouble :
      256 * (t * L) ≤ 2 * B := by
    calc
      256 * (t * L) ≤ 256 * (q * L + L) :=
        Nat.mul_le_mul_left 256 htL
      _ = 256 * (q * L) + 256 * L := by ring
      _ ≤ B + B := Nat.add_le_add hscaled (by simpa [L] using hlogLinear)
      _ = 2 * B := by ring
  have hcancel :
      2 * (128 * (t * L)) ≤ 2 * B := by
    convert hdouble using 1
    ring
  simpa only [t, L] using
    Nat.le_of_mul_le_mul_left hcancel (by omega)

/--
All four hypotheses required by the finite two-parity Hamming theorem follow
from `m ≥ B/16` and two explicit large-`B` inequalities.
-/
theorem componentHammingRadius_conditions
    {B m : ℕ}
    (hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 B))
    (hlogLinear : 256 * Nat.log 2 B ≤ B)
    (hm : B / 16 ≤ m) :
    1 ≤ componentHammingRadius B ∧
      2 * componentHammingRadius B ≤ m ∧
      PrimesUpTo.count B + 2 ≤ m ∧
      2 * componentHammingRadius B *
          2 ^ ((PrimesUpTo.count B + 2) /
            componentHammingRadius B + 1) ≤
        m := by
  let L := Nat.log 2 B
  let ell := Nat.log 2 L
  let t := componentHammingRadius B
  let r := PrimesUpTo.count B
  have ht64 : 64 ≤ t := by
    simpa only [t] using
      sixty_four_le_componentHammingRadius hloglog
  have htpos : 0 < t := by omega
  have hr :
      r ≤ t * ell := by
    simpa only [r, t, ell, L] using
      primeRows_le_radius_mul_loglog hloglog
  have helllarge : 16384 ≤ ell := by
    simpa only [ell, L] using hloglog
  have hrplus :
      r + 2 ≤ t * (ell + 1) := by
    calc
      r + 2 ≤ t * ell + t :=
        Nat.add_le_add hr
          (show 2 ≤ t from (by omega))
      _ = t * (ell + 1) := by ring
  have hdiv :
      (r + 2) / t ≤ ell + 1 := by
    apply Nat.div_le_of_le_mul
    simpa [Nat.mul_comm] using hrplus
  have hexponent :
      (r + 2) / t + 1 ≤ ell + 2 :=
    Nat.add_le_add_right hdiv 1
  have hLne : L ≠ 0 := by
    have hellpos : 0 < ell := by
      simpa only [ell, L] using
        (show 0 < Nat.log 2 (Nat.log 2 B) by omega)
    have : 2 ≤ L := (Nat.log_pos_iff.mp hellpos).1
    omega
  have hpowlog : 2 ^ ell ≤ L :=
    Nat.pow_log_le_self 2 hLne
  have hpower :
      2 ^ ((r + 2) / t + 1) ≤ 4 * L := by
    calc
      2 ^ ((r + 2) / t + 1) ≤ 2 ^ (ell + 2) :=
        Nat.pow_le_pow_right (by omega) hexponent
      _ = 4 * 2 ^ ell := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ 4 * L := Nat.mul_le_mul_left 4 hpowlog
  have hradiusBudget :
      128 * (t * L) ≤ B := by
    simpa only [t, L] using
      radius_mul_log_budget hloglog hlogLinear
  have hthresholdB :
      2 * t * 2 ^ ((r + 2) / t + 1) ≤ B / 16 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).2
    calc
      (2 * t * 2 ^ ((r + 2) / t + 1)) * 16
          ≤ (2 * t * (4 * L)) * 16 :=
        Nat.mul_le_mul_right 16
          (Nat.mul_le_mul_left (2 * t) hpower)
      _ = 128 * (t * L) := by ring
      _ ≤ B := hradiusBudget
  have hlarge :
      2 * t * 2 ^ ((r + 2) / t + 1) ≤ m :=
    hthresholdB.trans hm
  have hmt : 2 * t ≤ m := by
    calc
      2 * t ≤ 2 * t * 2 ^ ((r + 2) / t + 1) := by
        exact Nat.le_mul_of_pos_right (2 * t)
          (pow_pos (by norm_num) _)
      _ ≤ m := hlarge
  have hL256 : 256 ≤ L := by
    calc
      256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ ell :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ L := hpowlog
  have hB64 : 64 ≤ B :=
    (by omega : 64 ≤ L).trans (Nat.log_le_self 2 B)
  have hBfour : 4 ≤ B := by omega
  have hcheb :
      L * r ≤ 7 * B := by
    simpa only [L, r] using
      ChebyshevPrimeCount.log_mul_count_le_seven_mul hBfour
  have hr32 :
      32 * r ≤ B := by
    have hfirst : 224 * r ≤ 7 * B :=
      (Nat.mul_le_mul_right r (by omega : 224 ≤ L)).trans hcheb
    have hcancel :
        7 * (32 * r) ≤ 7 * B := by
      convert hfirst using 1
      ring
    exact Nat.le_of_mul_le_mul_left hcancel (by omega)
  have hrowsB :
      r + 2 ≤ B / 16 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).2
    have hdouble :
        32 * (r + 2) ≤ 2 * B := by
      calc
        32 * (r + 2) = 32 * r + 64 := by ring
        _ ≤ B + B := Nat.add_le_add hr32 hB64
        _ = 2 * B := by ring
    have hcancel :
        2 * (16 * (r + 2)) ≤ 2 * B := by
      convert hdouble using 1
      ring
    have hcore :
        16 * (r + 2) ≤ B :=
      Nat.le_of_mul_le_mul_left hcancel (by omega)
    simpa [Nat.mul_comm] using hcore
  exact
    ⟨by omega, hmt, (hrowsB.trans hm), hlarge⟩

/--
One-threshold form of `componentHammingRadius_conditions`: the logarithmic
ceiling budget follows automatically from the double-log threshold.
-/
theorem componentHammingRadius_conditions_of_loglog
    {B m : ℕ}
    (hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 B))
    (hm : B / 16 ≤ m) :
    1 ≤ componentHammingRadius B ∧
      2 * componentHammingRadius B ≤ m ∧
      PrimesUpTo.count B + 2 ≤ m ∧
      2 * componentHammingRadius B *
          2 ^ ((PrimesUpTo.count B + 2) /
            componentHammingRadius B + 1) ≤
        m :=
  componentHammingRadius_conditions hloglog
    (log_linear_le_of_loglog hloglog) hm

-- Keep the threshold symbolic here: external kernels can otherwise try to
-- normalize the astronomically large closed double-exponential threshold.
private opaque
    componentHammingRadius_conditions_runLengthWindow_eventually_of_threshold
    (T : ℕ) (hT : 16384 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ m, (L + 1) / 16 ≤ m →
        1 ≤ componentHammingRadius (L + 1) ∧
          2 * componentHammingRadius (L + 1) ≤ m ∧
          PrimesUpTo.count (L + 1) + 2 ≤ m ∧
          2 * componentHammingRadius (L + 1) *
              2 ^ ((PrimesUpTo.count (L + 1) + 2) /
                componentHammingRadius (L + 1) + 1) ≤
            m := by
  let K : ℕ := 2 ^ (2 ^ T)
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hNadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nheight, hNheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := CriticalRunWindow.upperConstant)
      CriticalRunWindow.lowerConstant_pos K
  refine ⟨max Nwindow (max Nadm Nheight), ?_⟩
  intro N hN L hrun m hm
  have hNwindowN : Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail : max Nadm Nheight ≤ N :=
    (le_max_right _ _).trans hN
  have hNadmN : Nadm ≤ N :=
    (le_max_left _ _).trans hNtail
  have hNheightN : Nheight ≤ N :=
    (le_max_right _ _).trans hNtail
  have hfirst :=
    hNwindow N hNwindowN L hrun
  have hadmissible :
      CriticalWeightedDefect.Admissible
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1) :=
    hNadm N hNadmN (L + 1) hfirst.1
  have hheight : K ≤ L + 1 :=
    hNheight N hNheightN (L + 1) hadmissible
  have hfirstLog :
      2 ^ T ≤ Nat.log 2 (L + 1) := by
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    simpa only [K] using hheight
  have hthresholdLog :
      T ≤ Nat.log 2 (Nat.log 2 (L + 1)) := by
    exact Nat.le_log_of_pow_le Nat.one_lt_two hfirstLog
  exact
    componentHammingRadius_conditions_of_loglog
      (hT.trans hthresholdLog) hm

/--
Uniform eventual Hamming budget in the manuscript run-length window.

Here the prime cutoff is `B = L + 1`.  The threshold is independent of the
admissible run length `L` and of the component count `m`.
-/
theorem componentHammingRadius_conditions_runLengthWindow_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ m, (L + 1) / 16 ≤ m →
        1 ≤ componentHammingRadius (L + 1) ∧
          2 * componentHammingRadius (L + 1) ≤ m ∧
          PrimesUpTo.count (L + 1) + 2 ≤ m ∧
          2 * componentHammingRadius (L + 1) *
              2 ^ ((PrimesUpTo.count (L + 1) + 2) /
                componentHammingRadius (L + 1) + 1) ≤
            m :=
  componentHammingRadius_conditions_runLengthWindow_eventually_of_threshold
    16384 le_rfl hC

/--
Direct instantiation of the two-parity Hamming theorem with
`r = π(B)` and the explicit radius `t(B)`.
-/
theorem exists_nonzero_kernel_word_of_component_density
    {B m : ℕ}
    (columns : Fin m → (Fin (PrimesUpTo.count B) → F₂))
    (leftBit rightBit : Fin m → F₂)
    (hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 B))
    (hlogLinear : 256 * Nat.log 2 B ≤ B)
    (hm : B / 16 ≤ m) :
    ∃ x : Fin m → F₂,
      x ≠ 0 ∧
      x ∈ LinearMap.ker
        (TwoParityColumnCode.twoAugmentedColumnMap
          columns leftBit rightBit) ∧
      hammingNorm x ≤ 2 * componentHammingRadius B := by
  obtain ⟨ht, hmt, hrows, hlarge⟩ :=
    componentHammingRadius_conditions hloglog hlogLinear hm
  exact
    TwoParityColumnCode.exists_nonzero_kernel_word_hammingNorm_le
      columns leftBit rightBit ht hmt hrows hlarge

end TheoremEightHammingBudget
end PaperC
