import PaperC.Asymptotics.RationalPowers
import PaperC.Asymptotics.ThreeHalvesPower
import Mathlib.Data.Real.Sqrt

/-!
# Quadratic closure and square-root interpolation

This module records two generic closure properties used when the two
branches of Proposition 7.3 are recombined and then inserted into the
linear/quadratic residual interpolation.
-/

namespace PaperC
namespace UniformRationalPower

/--
The sum of two uniform `N^(2+o(1))` quantities is again uniformly
`N^(2+o(1))`.
-/
theorem add_quadratic
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hf :
      UniformRationalPowerSubpolynomialOn 2 1 admissible f)
    (hg :
      UniformRationalPowerSubpolynomialOn 2 1 admissible g) :
    UniformRationalPowerSubpolynomialOn 2 1 admissible
      (fun N L => f N L + g N L) := by
  intro k hk
  have htwok : 0 < 2 * k :=
    Nat.mul_pos (by omega) hk
  obtain ⟨Nf, hNf⟩ := hf (2 * k) htwok
  obtain ⟨Ng, hNg⟩ := hg (2 * k) htwok
  refine ⟨max (max Nf Ng) (4 ^ k), ?_⟩
  intro N hN L hNL
  have hNfN : Nf ≤ N :=
    (le_max_left Nf Ng).trans
      ((le_max_left (max Nf Ng) (4 ^ k)).trans hN)
  have hNgN : Ng ≤ N :=
    (le_max_right Nf Ng).trans
      ((le_max_left (max Nf Ng) (4 ^ k)).trans hN)
  have hfourN : 4 ^ k ≤ N :=
    (le_max_right (max Nf Ng) (4 ^ k)).trans hN
  have hfBound :
      |f N L| ^ (2 * k) ≤
        (N : ℝ) ^ (4 * k + 1) := by
    simpa only [one_mul,
      show 2 * (2 * k) = 4 * k by omega] using
      hNf N hNfN L hNL
  have hgBound :
      |g N L| ^ (2 * k) ≤
        (N : ℝ) ^ (4 * k + 1) := by
    simpa only [one_mul,
      show 2 * (2 * k) = 4 * k by omega] using
      hNg N hNgN L hNL
  let m : ℝ := max |f N L| |g N L|
  have hmNonneg : 0 ≤ m := by
    exact (abs_nonneg _).trans (le_max_left _ _)
  have hmBound :
      m ^ (2 * k) ≤ (N : ℝ) ^ (4 * k + 1) := by
    by_cases hfg : |f N L| ≤ |g N L|
    · simpa only [m, max_eq_right hfg] using hgBound
    · have hgf : |g N L| ≤ |f N L| := le_of_not_ge hfg
      simpa only [m, max_eq_left hgf] using hfBound
  have hadd :
      |f N L + g N L| ≤ 2 * m := by
    calc
      |f N L + g N L| ≤ |f N L| + |g N L| :=
        abs_add _ _
      _ ≤ m + m :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * m := by ring
  have hfourCast : (4 : ℝ) ^ k ≤ (N : ℝ) := by
    exact_mod_cast hfourN
  have htwoPow : (2 : ℝ) ^ (2 * k) = 4 ^ k := by
    rw [pow_mul]
    norm_num
  have hlargePow :
      |f N L + g N L| ^ (2 * k) ≤
        (N : ℝ) ^ (4 * k + 2) := by
    calc
      |f N L + g N L| ^ (2 * k) ≤
          (2 * m) ^ (2 * k) :=
        pow_le_pow_left₀ (abs_nonneg _) hadd _
      _ = (4 : ℝ) ^ k * m ^ (2 * k) := by
        rw [mul_pow, htwoPow]
      _ ≤ (N : ℝ) * (N : ℝ) ^ (4 * k + 1) :=
        mul_le_mul hfourCast hmBound
          (pow_nonneg hmNonneg _) (Nat.cast_nonneg N)
      _ = (N : ℝ) ^ (4 * k + 2) := by
        rw [show 4 * k + 2 = (4 * k + 1) + 1 by omega,
          pow_succ, mul_comm]
        ring
  have hsq :
      (|f N L + g N L| ^ k) ^ 2 ≤
        ((N : ℝ) ^ (2 * k + 1)) ^ 2 := by
    calc
      (|f N L + g N L| ^ k) ^ 2 =
          |f N L + g N L| ^ (2 * k) := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ (N : ℝ) ^ (4 * k + 2) :=
        hlargePow
      _ = ((N : ℝ) ^ (2 * k + 1)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
  simpa only [one_mul] using
    (sq_le_sq₀ (by positivity)
      (show 0 ≤ (N : ℝ) ^ (2 * k + 1) by positivity)).mp hsq

/--
Generic square-root interpolation closure.

If `H=N^(3/2+o(1))`, `Q=N^(2+o(1))`, and eventually all three
quantities are nonnegative with `R ≤ √H √Q`, then
`R=N^(7/4+o(1))`.
-/
theorem interpolate_threeHalves_quadratic
    {admissible : ℕ → ℕ → Prop}
    {H Q R : ℕ → ℕ → ℝ}
    (hH :
      UniformThreeHalvesSubpolynomialOn admissible H)
    (hQ :
      UniformRationalPowerSubpolynomialOn 2 1 admissible Q)
    (hvalid :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        0 ≤ H N L ∧ 0 ≤ Q N L ∧ 0 ≤ R N L ∧
          R N L ≤ Real.sqrt (H N L) * Real.sqrt (Q N L)) :
    UniformRationalPowerSubpolynomialOn 7 4 admissible R := by
  intro k hk
  have htwok : 0 < 2 * k :=
    Nat.mul_pos (by omega) hk
  have hfourk : 0 < 4 * k :=
    Nat.mul_pos (by omega) hk
  obtain ⟨NH, hNH⟩ := hH (2 * k) htwok
  obtain ⟨NQ, hNQ⟩ := hQ (4 * k) hfourk
  obtain ⟨Nv, hNv⟩ := hvalid
  refine ⟨max NH (max NQ Nv), ?_⟩
  intro N hN L hNL
  have hNHN : NH ≤ N :=
    (le_max_left NH (max NQ Nv)).trans hN
  have htail : max NQ Nv ≤ N :=
    (le_max_right NH (max NQ Nv)).trans hN
  have hNQN : NQ ≤ N :=
    (le_max_left NQ Nv).trans htail
  have hNvN : Nv ≤ N :=
    (le_max_right NQ Nv).trans htail
  obtain ⟨hHnonneg, hQnonneg, hRnonneg, hinterp⟩ :=
    hNv N hNvN L hNL
  have hHBound :
      (H N L) ^ (4 * k) ≤
        (N : ℝ) ^ (6 * k + 1) := by
    have h := hNH N hNHN L hNL
    rw [abs_of_nonneg hHnonneg] at h
    simpa only [
      show 2 * (2 * k) = 4 * k by omega,
      show 3 * (2 * k) = 6 * k by omega] using h
  have hQBound :
      (Q N L) ^ (4 * k) ≤
        (N : ℝ) ^ (8 * k + 1) := by
    have h := hNQ N hNQN L hNL
    rw [abs_of_nonneg hQnonneg] at h
    simpa only [one_mul,
      show 2 * (4 * k) = 8 * k by omega] using h
  have hsqrtH :
      (Real.sqrt (H N L)) ^ (8 * k) =
        (H N L) ^ (4 * k) := by
    rw [show 8 * k = 2 * (4 * k) by omega,
      pow_mul, Real.sq_sqrt hHnonneg]
  have hsqrtQ :
      (Real.sqrt (Q N L)) ^ (8 * k) =
        (Q N L) ^ (4 * k) := by
    rw [show 8 * k = 2 * (4 * k) by omega,
      pow_mul, Real.sq_sqrt hQnonneg]
  have hRlarge :
      |R N L| ^ (8 * k) ≤
        (N : ℝ) ^ (14 * k + 2) := by
    rw [abs_of_nonneg hRnonneg]
    calc
      (R N L) ^ (8 * k) ≤
          (Real.sqrt (H N L) * Real.sqrt (Q N L)) ^ (8 * k) :=
        pow_le_pow_left₀ hRnonneg hinterp _
      _ = (H N L) ^ (4 * k) * (Q N L) ^ (4 * k) := by
        rw [mul_pow, hsqrtH, hsqrtQ]
      _ ≤
          (N : ℝ) ^ (6 * k + 1) *
            (N : ℝ) ^ (8 * k + 1) :=
        mul_le_mul hHBound hQBound
          (pow_nonneg hQnonneg _)
          (pow_nonneg (Nat.cast_nonneg N) _)
      _ = (N : ℝ) ^ (14 * k + 2) := by
        rw [← pow_add]
        congr 1
        omega
  have hsq :
      (|R N L| ^ (4 * k)) ^ 2 ≤
        ((N : ℝ) ^ (7 * k + 1)) ^ 2 := by
    calc
      (|R N L| ^ (4 * k)) ^ 2 =
          |R N L| ^ (8 * k) := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ (N : ℝ) ^ (14 * k + 2) :=
        hRlarge
      _ = ((N : ℝ) ^ (7 * k + 1)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
  exact
    (sq_le_sq₀ (by positivity)
      (show 0 ≤ (N : ℝ) ^ (7 * k + 1) by positivity)).mp hsq

end UniformRationalPower
end PaperC
