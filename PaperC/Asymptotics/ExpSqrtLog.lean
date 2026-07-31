import PaperC.Asymptotics.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Exponential square-root logarithms are subpolynomial

The finite estimates used around Proposition 3.2 contain factors of the form

`exp (C * sqrt (log N))`.

This file supplies the quantified bridge to the manuscript notation
`N^{o(1)}`.  In particular, the threshold is independent of every auxiliary
parameter occurring in an admissibility predicate.
-/

namespace PaperC
namespace ExpSqrtLog

/--
For a fixed nonnegative coefficient, `exp (C * sqrt (log N))` satisfies the
reciprocal-power formulation of `N^{o(1)}`.

The proof chooses an integer strictly above `exp ((k*C)^2)`.  Beyond that
threshold, `k*C < sqrt (log N)`, so the logarithm of the left-hand side is at
most `log N`.
-/
theorem pow_le_nat_eventually
    (C : ℝ) (hC : 0 ≤ C) (k : ℕ) (_hk : 0 < k) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (Real.exp (C * Real.sqrt (Real.log N))) ^ k ≤ (N : ℝ) := by
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (Real.exp ((((k : ℝ) * C) ^ 2)))
  refine ⟨N₀, ?_⟩
  intro N hNN₀
  have hthreshold :
      Real.exp ((((k : ℝ) * C) ^ 2)) < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hNN₀)
  have hNpos : 0 < (N : ℝ) :=
    (Real.exp_pos _).trans hthreshold
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by
    have hNnat : 0 < N := by exact_mod_cast hNpos
    exact_mod_cast (show 1 ≤ N by omega)
  have hlog_nonneg : 0 ≤ Real.log N :=
    Real.log_nonneg hNone
  have hsquare_lt_log :
      (((k : ℝ) * C) ^ 2) < Real.log N := by
    have hlogs := Real.log_lt_log (Real.exp_pos _) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hcoefficient_nonneg : 0 ≤ (k : ℝ) * C :=
    mul_nonneg (Nat.cast_nonneg k) hC
  have hcoefficient_le_sqrt :
      (k : ℝ) * C ≤ Real.sqrt (Real.log N) := by
    exact (Real.le_sqrt hcoefficient_nonneg hlog_nonneg).2
      hsquare_lt_log.le
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Real.log N) :=
    Real.sqrt_nonneg _
  have hexponent_le :
      (k : ℝ) * (C * Real.sqrt (Real.log N)) ≤
        Real.log N := by
    calc
      (k : ℝ) * (C * Real.sqrt (Real.log N)) =
          ((k : ℝ) * C) * Real.sqrt (Real.log N) := by ring
      _ ≤ Real.sqrt (Real.log N) * Real.sqrt (Real.log N) :=
        mul_le_mul_of_nonneg_right hcoefficient_le_sqrt hsqrt_nonneg
      _ = Real.log N := by
        rw [Real.mul_self_sqrt]
        exact hlog_nonneg
  calc
    (Real.exp (C * Real.sqrt (Real.log N))) ^ k =
        Real.exp ((k : ℝ) * (C * Real.sqrt (Real.log N))) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (Real.log N) :=
      Real.exp_le_exp.mpr hexponent_le
    _ = (N : ℝ) := Real.exp_log hNpos

/--
Uniform `N^{o(1)}` statement for a factor independent of the auxiliary
parameter.
-/
theorem uniformSubpolynomialOn
    (admissible : ℕ → ℕ → Prop) (C : ℝ) (hC : 0 ≤ C) :
    UniformSubpolynomialOn admissible
      (fun N _ => Real.exp (C * Real.sqrt (Real.log N))) := by
  intro k hk
  obtain ⟨N₀, hN₀⟩ := pow_le_nat_eventually C hC k hk
  refine ⟨N₀, ?_⟩
  intro N hNN₀ L _hNL
  simpa only [abs_of_pos (Real.exp_pos _)] using hN₀ N hNN₀

/--
The same estimate after replacing the logarithm by any nonnegative quantity
`H` bounded by `D * log N`.  This is the form needed for the Euler factor
`exp (2 * sqrt H)` when `H = O(log N)`.
-/
theorem exp_sqrt_of_le_log_pow_le_nat_eventually
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (k : ℕ) (hk : 0 < k) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H : ℕ,
      (H : ℝ) ≤ D * Real.log N →
      (Real.exp (C * Real.sqrt H)) ^ k ≤ (N : ℝ) := by
  obtain ⟨N₀, hN₀⟩ :=
    pow_le_nat_eventually (C * Real.sqrt D)
      (mul_nonneg hC (Real.sqrt_nonneg D)) k hk
  refine ⟨N₀, ?_⟩
  intro N hNN₀ H hH
  have hsqrt :
      Real.sqrt (H : ℝ) ≤
        Real.sqrt D * Real.sqrt (Real.log N) := by
    calc
      Real.sqrt (H : ℝ) ≤ Real.sqrt (D * Real.log N) :=
        Real.sqrt_le_sqrt hH
      _ = Real.sqrt D * Real.sqrt (Real.log N) :=
        Real.sqrt_mul hD _
  have hexp :
      Real.exp (C * Real.sqrt (H : ℝ)) ≤
        Real.exp ((C * Real.sqrt D) *
          Real.sqrt (Real.log N)) := by
    apply Real.exp_le_exp.mpr
    calc
      C * Real.sqrt (H : ℝ) ≤
          C * (Real.sqrt D * Real.sqrt (Real.log N)) :=
        mul_le_mul_of_nonneg_left hsqrt hC
      _ = (C * Real.sqrt D) * Real.sqrt (Real.log N) := by ring
  exact
    (pow_le_pow_left₀ (Real.exp_nonneg _) hexp k).trans
      (hN₀ N hNN₀)

/--
Uniform form of `exp_sqrt_of_le_log_pow_le_nat_eventually`.
-/
theorem uniformSubpolynomialOn_exp_sqrt_of_le_log
    (admissible : ℕ → ℕ → Prop)
    (H : ℕ → ℕ → ℕ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hH : ∀ N L, admissible N L →
      (H N L : ℝ) ≤ D * Real.log N) :
    UniformSubpolynomialOn admissible
      (fun N L => Real.exp (C * Real.sqrt (H N L))) := by
  intro k hk
  obtain ⟨N₀, hN₀⟩ :=
    exp_sqrt_of_le_log_pow_le_nat_eventually C D hC hD k hk
  refine ⟨N₀, ?_⟩
  intro N hNN₀ L hNL
  simpa only [abs_of_pos (Real.exp_pos _)] using
    hN₀ N hNN₀ (H N L) (hH N L hNL)

/--
Elementary envelope `x ≤ exp (2 * sqrt x)` for `x ≥ 0`.
-/
theorem le_exp_two_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ≤ Real.exp (2 * Real.sqrt x) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hsqrt_le_exp :
      Real.sqrt x ≤ Real.exp (Real.sqrt x) :=
    (le_add_of_nonneg_right zero_le_one).trans
      (Real.add_one_le_exp (Real.sqrt x))
  calc
    x = Real.sqrt x * Real.sqrt x :=
      (Real.mul_self_sqrt hx).symm
    _ ≤ Real.exp (Real.sqrt x) * Real.exp (Real.sqrt x) :=
      mul_le_mul hsqrt_le_exp hsqrt_le_exp
        hsqrt_nonneg (Real.exp_nonneg _)
    _ = Real.exp (2 * Real.sqrt x) := by
      rw [← Real.exp_add]
      congr 1
      ring

/--
If `H ≤ D * log N` and `log N ≥ 1`, then the elementary linear factor
`H + 1` is itself bounded by one exponential square-root logarithm.
-/
theorem linear_log_add_one_le_exp_sqrt_log
    {N H : ℕ} {D : ℝ}
    (hD : 0 ≤ D)
    (hlog : 1 ≤ Real.log N)
    (hH : (H : ℝ) ≤ D * Real.log N) :
    (H + 1 : ℝ) ≤
      Real.exp ((D + 2) * Real.sqrt (Real.log N)) := by
  let x : ℝ := Real.log N
  have hx : 0 ≤ x := zero_le_one.trans hlog
  have hsqrt_one : 1 ≤ Real.sqrt x := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hlog
  have hxexp : x ≤ Real.exp (2 * Real.sqrt x) :=
    le_exp_two_mul_sqrt hx
  have honeexp : 1 ≤ Real.exp (2 * Real.sqrt x) := by
    exact Real.one_le_exp (by positivity)
  have hlinear :
      (H + 1 : ℝ) ≤
        (D + 1) * Real.exp (2 * Real.sqrt x) := by
    calc
      (H + 1 : ℝ) = (H : ℝ) + 1 := by norm_num
      _ ≤ D * x + 1 := add_le_add hH le_rfl
      _ ≤ D * Real.exp (2 * Real.sqrt x) +
          Real.exp (2 * Real.sqrt x) :=
        add_le_add (mul_le_mul_of_nonneg_left hxexp hD) honeexp
      _ = (D + 1) * Real.exp (2 * Real.sqrt x) := by ring
  calc
    (H + 1 : ℝ) ≤
        (D + 1) * Real.exp (2 * Real.sqrt x) :=
      hlinear
    _ ≤ Real.exp (D * Real.sqrt x) *
        Real.exp (2 * Real.sqrt x) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      calc
        D + 1 ≤ Real.exp D := Real.add_one_le_exp D
        _ ≤ Real.exp (D * Real.sqrt x) := by
          apply Real.exp_le_exp.mpr
          nlinarith
    _ = Real.exp ((D + 2) * Real.sqrt x) := by
      rw [← Real.exp_add]
      congr 1
      ring

/--
The factor `H + 1` is subpolynomial uniformly for `H ≤ D * log N`.
-/
theorem linear_log_add_one_pow_le_nat_eventually
    (D : ℝ) (hD : 0 ≤ D) (k : ℕ) (hk : 0 < k) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H : ℕ,
      (H : ℝ) ≤ D * Real.log N →
      (H + 1 : ℝ) ^ k ≤ (N : ℝ) := by
  obtain ⟨Nexp, hNexp⟩ :=
    pow_le_nat_eventually (D + 2) (by linarith) k hk
  obtain ⟨Nlog, hNlog⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨max Nexp Nlog, ?_⟩
  intro N hN H hH
  have hNexp_le : Nexp ≤ N := (le_max_left _ _).trans hN
  have hNlog_le : Nlog ≤ N := (le_max_right _ _).trans hN
  have hexp_lt_N : Real.exp 1 < (N : ℝ) :=
    hNlog.trans_le (by exact_mod_cast hNlog_le)
  have hlog : 1 ≤ Real.log N := by
    have hlogs := Real.log_lt_log (Real.exp_pos 1) hexp_lt_N
    simpa only [Real.log_exp] using hlogs.le
  have hpoint :
      (H + 1 : ℝ) ≤
        Real.exp ((D + 2) * Real.sqrt (Real.log N)) :=
    linear_log_add_one_le_exp_sqrt_log hD hlog hH
  exact
    (pow_le_pow_left₀ (by positivity) hpoint k).trans
      (hNexp N hNexp_le)

/-- Uniform form of `linear_log_add_one_pow_le_nat_eventually`. -/
theorem uniformSubpolynomialOn_linear_log_add_one
    (admissible : ℕ → ℕ → Prop)
    (H : ℕ → ℕ → ℕ)
    (D : ℝ) (hD : 0 ≤ D)
    (hH : ∀ N L, admissible N L →
      (H N L : ℝ) ≤ D * Real.log N) :
    UniformSubpolynomialOn admissible
      (fun N L => (H N L + 1 : ℝ)) := by
  intro k hk
  obtain ⟨N₀, hN₀⟩ :=
    linear_log_add_one_pow_le_nat_eventually D hD k hk
  refine ⟨N₀, ?_⟩
  intro N hNN₀ L hNL
  have hnonneg : 0 ≤ (H N L + 1 : ℝ) := by positivity
  simpa only [abs_of_nonneg hnonneg] using
    hN₀ N hNN₀ (H N L) (hH N L hNL)

/--
Two reciprocal-power subpolynomial bounds can be combined by applying each
one at exponent `2*k`.
-/
theorem mul_pow_le_nat_of_twice
    {a b n : ℝ} {k : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 ≤ n)
    (ha2 : a ^ (2 * k) ≤ n)
    (hb2 : b ^ (2 * k) ≤ n) :
    (a * b) ^ k ≤ n := by
  have hasq : (a ^ k) ^ 2 ≤ n := by
    simpa only [← pow_mul, Nat.mul_comm] using ha2
  have hbsq : (b ^ k) ^ 2 ≤ n := by
    simpa only [← pow_mul, Nat.mul_comm] using hb2
  have hsq :
      ((a * b) ^ k) ^ 2 ≤ n ^ 2 := by
    calc
      ((a * b) ^ k) ^ 2 =
          (a ^ k) ^ 2 * (b ^ k) ^ 2 := by
        rw [mul_pow, mul_pow]
      _ ≤ n * n :=
        mul_le_mul hasq hbsq (sq_nonneg _) hn
      _ = n ^ 2 := by ring
  exact (sq_le_sq₀ (by positivity) hn).mp hsq

/--
`UniformSubpolynomialOn` is stable under pointwise multiplication.
-/
theorem uniformSubpolynomialOn_mul
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hf : UniformSubpolynomialOn admissible f)
    (hg : UniformSubpolynomialOn admissible g) :
    UniformSubpolynomialOn admissible
      (fun N L => f N L * g N L) := by
  intro k hk
  have htwok : 0 < 2 * k := Nat.mul_pos (by omega) hk
  obtain ⟨Nf, hNf⟩ := hf (2 * k) htwok
  obtain ⟨Ng, hNg⟩ := hg (2 * k) htwok
  refine ⟨max Nf Ng, ?_⟩
  intro N hN L hNL
  rw [abs_mul]
  apply mul_pow_le_nat_of_twice
      (abs_nonneg _) (abs_nonneg _) (Nat.cast_nonneg N)
  · exact hNf N ((le_max_left _ _).trans hN) L hNL
  · exact hNg N ((le_max_right _ _).trans hN) L hNL

/-- Every fixed real constant is uniformly subpolynomial. -/
theorem uniformSubpolynomialOn_const
    (admissible : ℕ → ℕ → Prop) (B : ℝ) :
    UniformSubpolynomialOn admissible (fun _ _ => B) := by
  intro k _hk
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (|B| ^ k)
  refine ⟨N₀, ?_⟩
  intro N hNN₀ L _hNL
  exact hN₀.le.trans (by exact_mod_cast hNN₀)

/-- Multiplication by a fixed real constant preserves uniform subpolynomiality. -/
theorem uniformSubpolynomialOn_const_mul
    {admissible : ℕ → ℕ → Prop}
    (B : ℝ) {f : ℕ → ℕ → ℝ}
    (hf : UniformSubpolynomialOn admissible f) :
    UniformSubpolynomialOn admissible
      (fun N L => B * f N L) :=
  uniformSubpolynomialOn_mul
    (uniformSubpolynomialOn_const admissible B) hf

/--
The coding factor `2^M` is subpolynomial whenever

`M ≤ D * log N / log (log N)`.

The threshold is chosen above
`exp (exp (k * D * log 2))`, making the exponent of `(2^M)^k` at most
`log N`.
-/
theorem two_pow_log_div_loglog_pow_le_nat_eventually
    (D : ℝ) (hD : 0 ≤ D) (k : ℕ) (_hk : 0 < k) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ,
      (M : ℝ) ≤
        D * Real.log N / Real.log (Real.log N) →
      (((2 ^ M : ℕ) : ℝ) ^ k) ≤ (N : ℝ) := by
  let A : ℝ := (k : ℝ) * D * Real.log 2
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (Real.exp (Real.exp A))
  refine ⟨N₀, ?_⟩
  intro N hNN₀ M hM
  have hthreshold :
      Real.exp (Real.exp A) < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hNN₀)
  have hlogN :
      Real.exp A < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos (Real.exp A)) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hloglogN :
      A < Real.log (Real.log N) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos A) hlogN
    simpa only [Real.log_exp] using hlogs
  have hlogNpos : 0 < Real.log N :=
    (Real.exp_pos A).trans hlogN
  have hloglogNpos : 0 < Real.log (Real.log N) :=
    hA.trans_lt hloglogN
  have hscaled :
      (k : ℝ) * (M : ℝ) * Real.log 2 ≤
        Real.log N := by
    calc
      (k : ℝ) * (M : ℝ) * Real.log 2 ≤
          (k : ℝ) *
              (D * Real.log N / Real.log (Real.log N)) *
              Real.log 2 := by
        apply mul_le_mul_of_nonneg_right _ hlogTwo.le
        exact mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg k)
      _ = Real.log N *
          (A / Real.log (Real.log N)) := by
        dsimp [A]
        ring
      _ ≤ Real.log N * 1 := by
        apply mul_le_mul_of_nonneg_left _ hlogNpos.le
        exact (div_le_one hloglogNpos).2 hloglogN.le
      _ = Real.log N := mul_one _
  have htwo :
      (((2 ^ M : ℕ) : ℝ)) =
        Real.exp ((M : ℝ) * Real.log 2) := by
    calc
      (((2 ^ M : ℕ) : ℝ)) = (2 : ℝ) ^ M := by
        norm_num
      _ = (Real.exp (Real.log 2)) ^ M := by
        rw [Real.exp_log]
        norm_num
      _ = Real.exp ((M : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul (Real.log 2) M).symm
  have hNpos : 0 < (N : ℝ) :=
    (Real.exp_pos _).trans hthreshold
  calc
    (((2 ^ M : ℕ) : ℝ) ^ k) =
        Real.exp ((k : ℝ) * ((M : ℝ) * Real.log 2)) := by
      rw [htwo, ← Real.exp_nat_mul]
    _ ≤ Real.exp (Real.log N) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hscaled]
    _ = (N : ℝ) := Real.exp_log hNpos

/-- Uniform form of the logarithm-over-logarithm estimate for `2^M`. -/
theorem uniformSubpolynomialOn_two_pow_log_div_loglog
    (admissible : ℕ → ℕ → Prop)
    (M : ℕ → ℕ → ℕ)
    (D : ℝ) (hD : 0 ≤ D)
    (hM : ∀ N L, admissible N L →
      (M N L : ℝ) ≤
        D * Real.log N / Real.log (Real.log N)) :
    UniformSubpolynomialOn admissible
      (fun N L => (((2 ^ M N L : ℕ) : ℝ))) := by
  intro k hk
  obtain ⟨N₀, hN₀⟩ :=
    two_pow_log_div_loglog_pow_le_nat_eventually D hD k hk
  refine ⟨N₀, ?_⟩
  intro N hNN₀ L hNL
  have hnonneg : 0 ≤ (((2 ^ M N L : ℕ) : ℝ)) := by positivity
  simpa only [abs_of_nonneg hnonneg] using
    hN₀ N hNN₀ (M N L) (hM N L hNL)

/--
The complete residual factor in the weighted defect estimate is uniformly
subpolynomial under the two natural logarithmic budgets.

This packages, with the same quantifier order as `UniformSubpolynomialOn`,

`(H+1) * exp (2*sqrt H) * 2^M = N^{o(1)}`.
-/
theorem uniformSubpolynomialOn_weighted_defect_factor
    (admissible : ℕ → ℕ → Prop)
    (H M : ℕ → ℕ → ℕ)
    (D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hH : ∀ N L, admissible N L →
      (H N L : ℝ) ≤ D * Real.log N)
    (hM : ∀ N L, admissible N L →
      (M N L : ℝ) ≤
        E * Real.log N / Real.log (Real.log N)) :
    UniformSubpolynomialOn admissible
      (fun N L =>
        (H N L + 1 : ℝ) *
          Real.exp (2 * Real.sqrt (H N L)) *
          (((2 ^ M N L : ℕ) : ℝ))) := by
  have hlinear :
      UniformSubpolynomialOn admissible
        (fun N L => (H N L + 1 : ℝ)) :=
    uniformSubpolynomialOn_linear_log_add_one
      admissible H D hD hH
  have hexponential :
      UniformSubpolynomialOn admissible
        (fun N L => Real.exp (2 * Real.sqrt (H N L))) :=
    uniformSubpolynomialOn_exp_sqrt_of_le_log
      admissible H 2 D (by norm_num) hD hH
  have hbinary :
      UniformSubpolynomialOn admissible
        (fun N L => (((2 ^ M N L : ℕ) : ℝ))) :=
    uniformSubpolynomialOn_two_pow_log_div_loglog
      admissible M E hE hM
  exact uniformSubpolynomialOn_mul
    (uniformSubpolynomialOn_mul hlinear hexponential) hbinary

end ExpSqrtLog
end PaperC
