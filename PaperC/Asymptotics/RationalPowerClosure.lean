import PaperC.Asymptotics.ExpSqrtLog
import PaperC.Asymptotics.RationalPowers
import PaperC.Asymptotics.ThreeHalvesPower
import Mathlib.Data.Real.Sqrt

/-!
# Closure properties for uniform rational-power bounds

This module records the three closure steps needed in Proposition 7.4:

* multiplication by a uniformly subpolynomial factor;
* addition of an `N^(5/3+o(1))` term and an
  `N^(3/2+o(1))` term;
* Cauchy--Schwarz interpolation from exponents `3/2` and `5/3`
  to `19/12`.

All statements use the reciprocal-power conventions of
`UniformRationalPowerSubpolynomialOn` and
`UniformThreeHalvesSubpolynomialOn`.
-/

namespace PaperC
namespace UniformRationalPower

/--
Multiplication by a uniformly subpolynomial factor preserves every
uniform rational-power bound with positive denominator.
-/
theorem mul_subpolynomial
    {p q : ℕ} (hq : 0 < q)
    {admissible : ℕ → ℕ → Prop}
    {f s : ℕ → ℕ → ℝ}
    (hf :
      UniformRationalPowerSubpolynomialOn p q admissible f)
    (hs : UniformSubpolynomialOn admissible s) :
    UniformRationalPowerSubpolynomialOn p q admissible
      (fun N L => s N L * f N L) := by
  intro k hk
  have htwok : 0 < 2 * k :=
    Nat.mul_pos (by omega) hk
  have htwoqk : 0 < 2 * (q * k) :=
    Nat.mul_pos (by omega) (Nat.mul_pos hq hk)
  obtain ⟨Nf, hNf⟩ := hf (2 * k) htwok
  obtain ⟨Ns, hNs⟩ := hs (2 * (q * k)) htwoqk
  refine ⟨max Nf Ns, ?_⟩
  intro N hN L hNL
  have hfBound :
      |f N L| ^ (2 * (q * k)) ≤
        (N : ℝ) ^ (2 * (p * k) + 1) := by
    have h := hNf N ((le_max_left _ _).trans hN) L hNL
    have hqExponent :
        q * (2 * k) = 2 * (q * k) := by
      ring
    have hpExponent :
        p * (2 * k) + 1 = 2 * (p * k) + 1 := by
      ring
    simpa only [hqExponent, hpExponent] using h
  have hsBound :
      |s N L| ^ (2 * (q * k)) ≤ (N : ℝ) := by
    simpa only using
      hNs N ((le_max_right _ _).trans hN) L hNL
  have hsq :
      (|s N L * f N L| ^ (q * k)) ^ 2 ≤
        ((N : ℝ) ^ (p * k + 1)) ^ 2 := by
    calc
      (|s N L * f N L| ^ (q * k)) ^ 2 =
          |s N L| ^ (2 * (q * k)) *
            |f N L| ^ (2 * (q * k)) := by
        rw [abs_mul, mul_pow, mul_pow]
        simp only [← pow_mul]
        congr 2 <;> omega
      _ ≤
          (N : ℝ) *
            (N : ℝ) ^ (2 * (p * k) + 1) :=
        mul_le_mul hsBound hfBound (by positivity) (by positivity)
      _ = ((N : ℝ) ^ (p * k + 1)) ^ 2 := by
        rw [← pow_mul]
        ring_nf
  exact
    (sq_le_sq₀ (by positivity)
      (show 0 ≤ (N : ℝ) ^ (p * k + 1) by positivity)).mp hsq

/--
The sum of an `N^(5/3+o(1))` term and an
`N^(3/2+o(1))` term is `N^(5/3+o(1))`.
-/
theorem add_fiveThird_threeHalves
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hf :
      UniformFiveThirdSubpolynomialOn admissible f)
    (hg :
      UniformThreeHalvesSubpolynomialOn admissible g) :
    UniformFiveThirdSubpolynomialOn admissible
      (fun N L => f N L + g N L) := by
  intro k hk
  have htwok : 0 < 2 * k :=
    Nat.mul_pos (by omega) hk
  have hthreek : 0 < 3 * k :=
    Nat.mul_pos (by omega) hk
  obtain ⟨Nf, hNf⟩ := hf (2 * k) htwok
  obtain ⟨Ng, hNg⟩ := hg (3 * k) hthreek
  refine ⟨max (max Nf Ng) (64 ^ k), ?_⟩
  intro N hN L hNL
  have hNfN : Nf ≤ N :=
    (le_max_left Nf Ng).trans
      ((le_max_left (max Nf Ng) (64 ^ k)).trans hN)
  have hNgN : Ng ≤ N :=
    (le_max_right Nf Ng).trans
      ((le_max_left (max Nf Ng) (64 ^ k)).trans hN)
  have hsixtyFourN : 64 ^ k ≤ N :=
    (le_max_right (max Nf Ng) (64 ^ k)).trans hN
  have hNoneNat : 1 ≤ N :=
    (Nat.one_le_pow k 64 (by omega)).trans hsixtyFourN
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hNoneNat
  have hfBound :
      |f N L| ^ (6 * k) ≤
        (N : ℝ) ^ (10 * k + 1) := by
    simpa only [
      show 3 * (2 * k) = 6 * k by omega,
      show 5 * (2 * k) = 10 * k by omega] using
      hNf N hNfN L hNL
  have hgRaw :
      |g N L| ^ (6 * k) ≤
        (N : ℝ) ^ (9 * k + 1) := by
    simpa only [
      show 2 * (3 * k) = 6 * k by omega,
      show 3 * (3 * k) = 9 * k by omega] using
      hNg N hNgN L hNL
  have hgBound :
      |g N L| ^ (6 * k) ≤
        (N : ℝ) ^ (10 * k + 1) :=
    hgRaw.trans
      (pow_le_pow_right₀ hNone (by omega))
  let m : ℝ := max |f N L| |g N L|
  have hmNonneg : 0 ≤ m :=
    (abs_nonneg _).trans (le_max_left _ _)
  have hmBound :
      m ^ (6 * k) ≤ (N : ℝ) ^ (10 * k + 1) := by
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
  have hsixtyFourCast : (64 : ℝ) ^ k ≤ (N : ℝ) := by
    exact_mod_cast hsixtyFourN
  have htwoPow : (2 : ℝ) ^ (6 * k) = 64 ^ k := by
    rw [pow_mul]
    norm_num
  have hlargePow :
      |f N L + g N L| ^ (6 * k) ≤
        (N : ℝ) ^ (10 * k + 2) := by
    calc
      |f N L + g N L| ^ (6 * k) ≤
          (2 * m) ^ (6 * k) :=
        pow_le_pow_left₀ (abs_nonneg _) hadd _
      _ = (64 : ℝ) ^ k * m ^ (6 * k) := by
        rw [mul_pow, htwoPow]
      _ ≤
          (N : ℝ) * (N : ℝ) ^ (10 * k + 1) :=
        mul_le_mul hsixtyFourCast hmBound
          (pow_nonneg hmNonneg _) (Nat.cast_nonneg N)
      _ = (N : ℝ) ^ (10 * k + 2) := by
        rw [show 10 * k + 2 = (10 * k + 1) + 1 by omega,
          pow_succ, mul_comm]
        ring
  have hsq :
      (|f N L + g N L| ^ (3 * k)) ^ 2 ≤
        ((N : ℝ) ^ (5 * k + 1)) ^ 2 := by
    calc
      (|f N L + g N L| ^ (3 * k)) ^ 2 =
          |f N L + g N L| ^ (6 * k) := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ (N : ℝ) ^ (10 * k + 2) :=
        hlargePow
      _ = ((N : ℝ) ^ (5 * k + 1)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
  exact
    (sq_le_sq₀ (by positivity)
      (show 0 ≤ (N : ℝ) ^ (5 * k + 1) by positivity)).mp hsq

/--
Symmetric form of `add_fiveThird_threeHalves`.
-/
theorem add_threeHalves_fiveThird
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hf :
      UniformThreeHalvesSubpolynomialOn admissible f)
    (hg :
      UniformFiveThirdSubpolynomialOn admissible g) :
    UniformFiveThirdSubpolynomialOn admissible
      (fun N L => f N L + g N L) := by
  have h :=
    add_fiveThird_threeHalves hg hf
  simpa only [add_comm] using h

/--
Cauchy--Schwarz interpolation between `N^(3/2+o(1))` and
`N^(5/3+o(1))`.

If eventually `R ≤ √H √Q` and all three quantities are nonnegative, then
`R=N^(19/12+o(1))`.
-/
theorem interpolate_threeHalves_fiveThird
    {admissible : ℕ → ℕ → Prop}
    {H Q R : ℕ → ℕ → ℝ}
    (hH :
      UniformThreeHalvesSubpolynomialOn admissible H)
    (hQ :
      UniformFiveThirdSubpolynomialOn admissible Q)
    (hvalid :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        0 ≤ H N L ∧ 0 ≤ Q N L ∧ 0 ≤ R N L ∧
          R N L ≤ Real.sqrt (H N L) * Real.sqrt (Q N L)) :
    UniformRationalPowerSubpolynomialOn 19 12 admissible R := by
  intro k hk
  have hsixk : 0 < 6 * k :=
    Nat.mul_pos (by omega) hk
  have hfourk : 0 < 4 * k :=
    Nat.mul_pos (by omega) hk
  obtain ⟨NH, hNH⟩ := hH (6 * k) hsixk
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
      (H N L) ^ (12 * k) ≤
        (N : ℝ) ^ (18 * k + 1) := by
    have h := hNH N hNHN L hNL
    rw [abs_of_nonneg hHnonneg] at h
    simpa only [
      show 2 * (6 * k) = 12 * k by omega,
      show 3 * (6 * k) = 18 * k by omega] using h
  have hQBound :
      (Q N L) ^ (12 * k) ≤
        (N : ℝ) ^ (20 * k + 1) := by
    have h := hNQ N hNQN L hNL
    rw [abs_of_nonneg hQnonneg] at h
    simpa only [
      show 3 * (4 * k) = 12 * k by omega,
      show 5 * (4 * k) = 20 * k by omega] using h
  have hsqrtH :
      (Real.sqrt (H N L)) ^ (24 * k) =
        (H N L) ^ (12 * k) := by
    rw [show 24 * k = 2 * (12 * k) by omega,
      pow_mul, Real.sq_sqrt hHnonneg]
  have hsqrtQ :
      (Real.sqrt (Q N L)) ^ (24 * k) =
        (Q N L) ^ (12 * k) := by
    rw [show 24 * k = 2 * (12 * k) by omega,
      pow_mul, Real.sq_sqrt hQnonneg]
  have hRlarge :
      |R N L| ^ (24 * k) ≤
        (N : ℝ) ^ (38 * k + 2) := by
    rw [abs_of_nonneg hRnonneg]
    calc
      (R N L) ^ (24 * k) ≤
          (Real.sqrt (H N L) * Real.sqrt (Q N L)) ^ (24 * k) :=
        pow_le_pow_left₀ hRnonneg hinterp _
      _ =
          (H N L) ^ (12 * k) *
            (Q N L) ^ (12 * k) := by
        rw [mul_pow, hsqrtH, hsqrtQ]
      _ ≤
          (N : ℝ) ^ (18 * k + 1) *
            (N : ℝ) ^ (20 * k + 1) :=
        mul_le_mul hHBound hQBound
          (pow_nonneg hQnonneg _)
          (pow_nonneg (Nat.cast_nonneg N) _)
      _ = (N : ℝ) ^ (38 * k + 2) := by
        rw [← pow_add]
        congr 1
        omega
  have hsq :
      (|R N L| ^ (12 * k)) ^ 2 ≤
        ((N : ℝ) ^ (19 * k + 1)) ^ 2 := by
    calc
      (|R N L| ^ (12 * k)) ^ 2 =
          |R N L| ^ (24 * k) := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ (N : ℝ) ^ (38 * k + 2) :=
        hRlarge
      _ = ((N : ℝ) ^ (19 * k + 1)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
  exact
    (sq_le_sq₀ (by positivity)
      (show 0 ≤ (N : ℝ) ^ (19 * k + 1) by positivity)).mp hsq

end UniformRationalPower
end PaperC
