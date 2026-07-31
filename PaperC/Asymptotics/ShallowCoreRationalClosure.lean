import PaperC.Asymptotics.RationalPowerClosure
import PaperC.Asymptotics.RationalPowerLittleO

/-!
# Rational-power closures for Proposition 7.5

This module isolates the exponent arithmetic used after the finite
shallow-core estimate:

* multiplying an `N^(p/q+o(1))` quantity by the exact factor `N^r`
  shifts the numerator from `p` to `p+r*q`;
* consequently `N²`, two subpolynomial factors, and an
  `N^(3/8+o(1))` density factor give `N^(19/8+o(1))`;
* Cauchy--Schwarz interpolation between `N^(3/2+o(1))` and
  `N^(19/8+o(1))` gives `N^(31/16+o(1))`;
* since `31/16 < 2`, the last rate is uniformly `o(N²)`.

All losses are handled inside the reciprocal-power predicates, so the
finite Proposition 7.5 module only needs to supply pointwise domination.
-/

namespace PaperC
namespace UniformRationalPower

/--
Multiplication by the exact natural power `N^r` shifts a rational exponent
from `p/q` to `(p+r*q)/q`.
-/
theorem natPower_mul
    {p q r : ℕ}
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hf :
      UniformRationalPowerSubpolynomialOn p q admissible f) :
    UniformRationalPowerSubpolynomialOn (p + r * q) q admissible
      (fun N L => (N : ℝ) ^ r * f N L) := by
  intro k hk
  obtain ⟨Nf, hNf⟩ := hf k hk
  refine ⟨Nf, ?_⟩
  intro N hN L hNL
  have hfBound :=
    hNf N hN L hNL
  calc
    |(N : ℝ) ^ r * f N L| ^ (q * k) =
        (N : ℝ) ^ (r * (q * k)) *
          |f N L| ^ (q * k) := by
      rw [abs_mul,
        abs_of_nonneg (show 0 ≤ (N : ℝ) ^ r by positivity),
        mul_pow, ← pow_mul]
    _ ≤
        (N : ℝ) ^ (r * (q * k)) *
          (N : ℝ) ^ (p * k + 1) :=
      mul_le_mul_of_nonneg_left hfBound (by positivity)
    _ = (N : ℝ) ^ ((p + r * q) * k + 1) := by
      rw [← pow_add]
      congr 1
      ring

/--
The exact combination needed for the shallow-core quadratic mass:

`N² * N^o(1) * N^(3/8+o(1)) = N^(19/8+o(1))`.
-/
theorem quadratic_mul_subpolynomial_threeEighths
    {admissible : ℕ → ℕ → Prop}
    {s density : ℕ → ℕ → ℝ}
    (hs : UniformSubpolynomialOn admissible s)
    (hdensity :
      UniformRationalPowerSubpolynomialOn
        3 8 admissible density) :
    UniformRationalPowerSubpolynomialOn 19 8 admissible
      (fun N L =>
        (N : ℝ) ^ 2 * s N L * density N L) := by
  have hproduct :
      UniformRationalPowerSubpolynomialOn 3 8 admissible
        (fun N L => s N L * density N L) :=
    mul_subpolynomial (by omega) hdensity hs
  have hshifted :=
    natPower_mul (r := 2) hproduct
  simpa only [show 3 + 2 * 8 = 19 by norm_num, mul_assoc]
    using hshifted

/--
Two independently established subpolynomial envelopes may be inserted in
the preceding closure without first changing their interfaces.
-/
theorem quadratic_mul_twoSubpolynomial_threeEighths
    {admissible : ℕ → ℕ → Prop}
    {s t density : ℕ → ℕ → ℝ}
    (hs : UniformSubpolynomialOn admissible s)
    (ht : UniformSubpolynomialOn admissible t)
    (hdensity :
      UniformRationalPowerSubpolynomialOn
        3 8 admissible density) :
    UniformRationalPowerSubpolynomialOn 19 8 admissible
      (fun N L =>
        (N : ℝ) ^ 2 * s N L * t N L * density N L) := by
  have hst :
      UniformSubpolynomialOn admissible
        (fun N L => s N L * t N L) :=
    ExpSqrtLog.uniformSubpolynomialOn_mul hs ht
  have hresult :=
    quadratic_mul_subpolynomial_threeEighths hst hdensity
  simpa only [mul_assoc] using hresult

/--
Cauchy--Schwarz interpolation between `N^(3/2+o(1))` and
`N^(19/8+o(1))`.

If eventually `R ≤ √H √Q` and all three quantities are nonnegative, then
`R=N^(31/16+o(1))`.
-/
theorem interpolate_threeHalves_nineteenEighths
    {admissible : ℕ → ℕ → Prop}
    {H Q R : ℕ → ℕ → ℝ}
    (hH :
      UniformThreeHalvesSubpolynomialOn admissible H)
    (hQ :
      UniformRationalPowerSubpolynomialOn 19 8 admissible Q)
    (hvalid :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        0 ≤ H N L ∧ 0 ≤ Q N L ∧ 0 ≤ R N L ∧
          R N L ≤ Real.sqrt (H N L) * Real.sqrt (Q N L)) :
    UniformRationalPowerSubpolynomialOn 31 16 admissible R := by
  intro k hk
  have heightk : 0 < 8 * k :=
    Nat.mul_pos (by omega) hk
  have htwok : 0 < 2 * k :=
    Nat.mul_pos (by omega) hk
  obtain ⟨NH, hNH⟩ := hH (8 * k) heightk
  obtain ⟨NQ, hNQ⟩ := hQ (2 * k) htwok
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
      (H N L) ^ (16 * k) ≤
        (N : ℝ) ^ (24 * k + 1) := by
    have h := hNH N hNHN L hNL
    rw [abs_of_nonneg hHnonneg] at h
    simpa only [
      show 2 * (8 * k) = 16 * k by omega,
      show 3 * (8 * k) = 24 * k by omega] using h
  have hQBound :
      (Q N L) ^ (16 * k) ≤
        (N : ℝ) ^ (38 * k + 1) := by
    have h := hNQ N hNQN L hNL
    rw [abs_of_nonneg hQnonneg] at h
    simpa only [
      show 8 * (2 * k) = 16 * k by omega,
      show 19 * (2 * k) = 38 * k by omega] using h
  have hsqrtH :
      (Real.sqrt (H N L)) ^ (32 * k) =
        (H N L) ^ (16 * k) := by
    rw [show 32 * k = 2 * (16 * k) by omega,
      pow_mul, Real.sq_sqrt hHnonneg]
  have hsqrtQ :
      (Real.sqrt (Q N L)) ^ (32 * k) =
        (Q N L) ^ (16 * k) := by
    rw [show 32 * k = 2 * (16 * k) by omega,
      pow_mul, Real.sq_sqrt hQnonneg]
  have hRlarge :
      |R N L| ^ (32 * k) ≤
        (N : ℝ) ^ (62 * k + 2) := by
    rw [abs_of_nonneg hRnonneg]
    calc
      (R N L) ^ (32 * k) ≤
          (Real.sqrt (H N L) * Real.sqrt (Q N L)) ^ (32 * k) :=
        pow_le_pow_left₀ hRnonneg hinterp _
      _ =
          (H N L) ^ (16 * k) *
            (Q N L) ^ (16 * k) := by
        rw [mul_pow, hsqrtH, hsqrtQ]
      _ ≤
          (N : ℝ) ^ (24 * k + 1) *
            (N : ℝ) ^ (38 * k + 1) :=
        mul_le_mul hHBound hQBound
          (pow_nonneg hQnonneg _)
          (pow_nonneg (Nat.cast_nonneg N) _)
      _ = (N : ℝ) ^ (62 * k + 2) := by
        rw [← pow_add]
        congr 1
        omega
  have hsq :
      (|R N L| ^ (16 * k)) ^ 2 ≤
        ((N : ℝ) ^ (31 * k + 1)) ^ 2 := by
    calc
      (|R N L| ^ (16 * k)) ^ 2 =
          |R N L| ^ (32 * k) := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ (N : ℝ) ^ (62 * k + 2) :=
        hRlarge
      _ = ((N : ℝ) ^ (31 * k + 1)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
  exact
    (sq_le_sq₀ (by positivity)
      (show 0 ≤ (N : ℝ) ^ (31 * k + 1) by positivity)).mp hsq

/--
The interpolated exponent of Proposition 7.5 is strictly below the
quadratic scale:

`N^(31/16+o(1)) = o(N²)`.
-/
theorem thirtyOneSixteenths_littleO_quadratic
    {admissible : ℕ → ℕ → Prop}
    {R : ℕ → ℕ → ℝ}
    (hR :
      UniformRationalPowerSubpolynomialOn
        31 16 admissible R) :
    UniformLittleOOn admissible R
      (fun N _ => (N : ℝ) ^ 2) :=
  littleO_natPower_of_lt (by decide) hR

end UniformRationalPower
end PaperC
