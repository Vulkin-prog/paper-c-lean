import PaperC.Asymptotics.LogLogRunWindow
import PaperC.Asymptotics.PropositionElevenThree
import PaperC.Asymptotics.SectionThirteenCritical
import Mathlib.NumberTheory.Harmonic.Bounds

set_option maxHeartbeats 1800000

/-!
# Corollary 13.10: propagation of the quantitative arithmetic rate

This module first proves the analytic comparison which is essential for the
paper's quantitative conclusion:

`exp (-c sqrt(log N) / log log N) = O((log log N)⁻²)`.

It then transports Corollary 11.3 through the exact dyadic normalization
`2^(-2L)`, using the already proved critical-window balance
`N / 2^L = O_C(1)`.

The final part records a sharper, completely elementary finite estimate for
the dependency-edge prime sum.  It replaces the deliberately coarse
`3N/Y` estimate by the harmonic bound
`sum_{p ≤ 3N} 1/p ≤ 1 + log(3N)`.  No PNT, Mertens theorem, or new external
bridge is used.
-/

namespace PaperC
namespace SectionThirteenRate

open scoped BigOperators

open BadStartCount
open LargePrimeDependencyGraph
open PropositionElevenThree
open PropositionElevenTwo
open SectionThirteenCouplings
open SectionThirteenCritical
open SectionThirteenFiniteBound
open SteinChenCritical
open TerminalPrimeCutoff

noncomputable section

/-- The explicit rate displayed in Corollary 13.10. -/
noncomputable def inverseLogLogSquaredRate
    (N _L : ℕ) : ℝ :=
  1 / (Real.log (Real.log N)) ^ 2

/-- The corresponding quadratic numerator scale. -/
noncomputable def quadraticDivLogLogSquaredScale
    (N _L : ℕ) : ℝ :=
  (N : ℝ) ^ 2 / (Real.log (Real.log N)) ^ 2

/-- The same logarithmic scale with an arbitrary integral main power. -/
noncomputable def natPowerDivLogLogSquaredScale
    (r : ℕ) (N _L : ℕ) : ℝ :=
  (N : ℝ) ^ r / (Real.log (Real.log N)) ^ 2

/-! ## Elementary exponential-to-logarithmic comparison -/

/--
Pointwise analytic core of the passage from Corollary 11.3 to 13.10.

The explicit constant is intentionally generous.  The sixth Taylor term
for `exp(2 log log N)` bounds `(log log N)^6` by
`12 (log N)^2`; the fourth Taylor term
`(ct)^4/4! ≤ exp(ct)` then absorbs the displayed exponential.
-/
theorem loglog_sq_mul_exp_neg_sqrt_log_div_loglog_le
    {N : ℕ} {c : ℝ}
    (hc : 0 < c)
    (hlogN : 0 < Real.log N)
    (hloglogN : 0 < Real.log (Real.log N)) :
    (Real.log (Real.log N)) ^ 2 *
        Real.exp
          (-c * Real.sqrt (Real.log N) /
            Real.log (Real.log N)) ≤
      288 / c ^ 4 := by
  let a : ℝ := Real.log N
  let b : ℝ := Real.log (Real.log N)
  let t : ℝ := Real.sqrt a / b
  have ha : 0 < a := by simpa only [a] using hlogN
  have hb : 0 < b := by simpa only [b] using hloglogN
  have ht : 0 ≤ t := by
    dsimp only [t]
    positivity
  have hsqrtSq : (Real.sqrt a) ^ 2 = a :=
    Real.sq_sqrt ha.le
  have hTaylorB :=
    Real.pow_div_factorial_le_exp
      (2 * b) (by positivity) 6
  norm_num [Nat.factorial] at hTaylorB
  have hexpTwoB :
      Real.exp (2 * b) = a ^ 2 := by
    rw [show 2 * b = b + b by ring, Real.exp_add]
    dsimp only [b, a]
    rw [Real.exp_log hlogN]
    ring
  have htwoPow :
      (2 * b) ^ 6 = 64 * b ^ 6 := by ring
  rw [hexpTwoB, htwoPow] at hTaylorB
  have hbSixth :
      b ^ 6 ≤ 12 * a ^ 2 := by
    nlinarith [sq_nonneg a]
  have hsqrtFourth :
      (Real.sqrt a) ^ 4 = a ^ 2 := by
    calc
      (Real.sqrt a) ^ 4 =
          ((Real.sqrt a) ^ 2) ^ 2 := by ring
      _ = a ^ 2 := by rw [hsqrtSq]
  have htFourth :
      t ^ 4 = a ^ 2 / b ^ 4 := by
    dsimp only [t]
    rw [div_pow, hsqrtFourth]
  have hbSqLeT :
      b ^ 2 ≤ 12 * t ^ 4 := by
    rw [htFourth]
    rw [show 12 * (a ^ 2 / b ^ 4) =
      (12 * a ^ 2) / b ^ 4 by ring]
    apply (le_div_iff₀ (pow_pos hb 4)).2
    calc
      b ^ 2 * b ^ 4 = b ^ 6 := by ring
      _ ≤ 12 * a ^ 2 := hbSixth
  have hct : 0 ≤ c * t := mul_nonneg hc.le ht
  have hTaylor :=
    Real.pow_div_factorial_le_exp (c * t) hct 4
  norm_num at hTaylor
  have hpoly :
      c ^ 4 * t ^ 4 ≤
        24 * Real.exp (c * t) := by
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 24)).mp hTaylor
    nlinarith [show (c * t) ^ 4 = c ^ 4 * t ^ 4 by ring]
  have hcFourth : 0 < c ^ 4 := pow_pos hc 4
  have hexpPos : 0 < Real.exp (c * t) := Real.exp_pos _
  have htExp :
      t ^ 4 * Real.exp (-(c * t)) ≤
        24 / c ^ 4 := by
    rw [Real.exp_neg]
    apply (div_le_div_iff₀ hexpPos hcFourth).2
    nlinarith [hpoly]
  have hmain :
      b ^ 2 * Real.exp (-(c * t)) ≤
        288 / c ^ 4 := by
    calc
      b ^ 2 * Real.exp (-(c * t)) ≤
          (12 * t ^ 4) * Real.exp (-(c * t)) :=
        mul_le_mul_of_nonneg_right hbSqLeT (Real.exp_nonneg _)
      _ = 12 * (t ^ 4 * Real.exp (-(c * t))) := by ring
      _ ≤ 12 * (24 / c ^ 4) :=
        mul_le_mul_of_nonneg_left htExp (by norm_num)
      _ = 288 / c ^ 4 := by ring
  change b ^ 2 * Real.exp (-c * Real.sqrt a / b) ≤
    288 / c ^ 4
  convert hmain using 1
  dsimp only [t]
  ring_nf

/--
The Corollary 11.3 exponential scale is uniformly big-O of
`N²/(log log N)²`.
-/
theorem quantitativeHomogeneousScale_uniformBigO_loglogSquared
    {admissible : ℕ → ℕ → Prop}
    {c : ℝ} (hc : 0 < c) :
    UniformBigOOn admissible
      (quantitativeHomogeneousScale c)
      quadraticDivLogLogSquaredScale := by
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (Real.exp (Real.exp 1))
  let K : ℝ := 288 / c ^ 4
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, N₀, ?_⟩
  intro N hN L _hNL
  have hthreshold :
      Real.exp (Real.exp 1) < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hlogN :
      Real.exp 1 < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos (Real.exp 1)) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hloglogN :
      1 < Real.log (Real.log N) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos 1) hlogN
    simpa only [Real.log_exp] using hlogs
  have hpoint :=
    loglog_sq_mul_exp_neg_sqrt_log_div_loglog_le
      hc ((Real.exp_pos 1).trans hlogN)
      (zero_lt_one.trans hloglogN)
  have hloglogSq :
      0 < (Real.log (Real.log N)) ^ 2 :=
    pow_pos (zero_lt_one.trans hloglogN) 2
  have hNnonneg : 0 ≤ (N : ℝ) ^ 2 := by positivity
  have hscaleNonneg :
      0 ≤ quantitativeHomogeneousScale c N L := by
    unfold quantitativeHomogeneousScale
    positivity
  have htargetNonneg :
      0 ≤ quadraticDivLogLogSquaredScale N L := by
    unfold quadraticDivLogLogSquaredScale
    positivity
  rw [abs_of_nonneg hscaleNonneg,
    abs_of_nonneg htargetNonneg]
  unfold quantitativeHomogeneousScale
    quadraticDivLogLogSquaredScale
  rw [show
      K * ((N : ℝ) ^ 2 /
        (Real.log (Real.log N)) ^ 2) =
        (K * (N : ℝ) ^ 2) /
          (Real.log (Real.log N)) ^ 2 by ring]
  apply (le_div_iff₀ hloglogSq).2
  calc
    ((N : ℝ) ^ 2 *
          Real.exp
            (-c * Real.sqrt (Real.log N) /
              Real.log (Real.log N))) *
        (Real.log (Real.log N)) ^ 2 =
      (N : ℝ) ^ 2 *
        ((Real.log (Real.log N)) ^ 2 *
          Real.exp
            (-c * Real.sqrt (Real.log N) /
              Real.log (Real.log N))) := by ring
    _ ≤ (N : ℝ) ^ 2 * K :=
      mul_le_mul_of_nonneg_left hpoint hNnonneg
    _ = K * (N : ℝ) ^ 2 := by ring

/-- Transitivity of the repository's uniform big-O predicate. -/
theorem uniformBigOOn_trans
    {admissible : ℕ → ℕ → Prop}
    {f g h : ℕ → ℕ → ℝ}
    (hfg : UniformBigOOn admissible f g)
    (hgh : UniformBigOOn admissible g h) :
    UniformBigOOn admissible f h := by
  obtain ⟨K₁, hK₁, N₁, h₁⟩ := hfg
  obtain ⟨K₂, hK₂, N₂, h₂⟩ := hgh
  refine ⟨K₁ * K₂, mul_nonneg hK₁ hK₂, max N₁ N₂, ?_⟩
  intro N hN L hNL
  calc
    |f N L| ≤ K₁ * |g N L| :=
      h₁ N ((le_max_left _ _).trans hN) L hNL
    _ ≤ K₁ * (K₂ * |h N L|) :=
      mul_le_mul_of_nonneg_left
        (h₂ N ((le_max_right _ _).trans hN) L hNL) hK₁
    _ = (K₁ * K₂) * |h N L| := by ring

/-- Multiplication by a fixed real constant preserves uniform big-O. -/
theorem uniformBigOOn_const_mul
    {admissible : ℕ → ℕ → Prop}
    (B : ℝ) {f scale : ℕ → ℕ → ℝ}
    (hf : UniformBigOOn admissible f scale) :
    UniformBigOOn admissible
      (fun N L ↦ B * f N L) scale := by
  obtain ⟨K, hK, N₀, hN₀⟩ := hf
  refine ⟨|B| * K, mul_nonneg (abs_nonneg B) hK, N₀, ?_⟩
  intro N hN L hNL
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (hN₀ N hN L hNL) (abs_nonneg B)

/-- Eventual pointwise domination preserves uniform big-O. -/
theorem uniformBigOOn_mono
    {admissible : ℕ → ℕ → Prop}
    {f g scale : ℕ → ℕ → ℝ}
    (hg : UniformBigOOn admissible g scale)
    (hfg :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        |f N L| ≤ |g N L|) :
    UniformBigOOn admissible f scale := by
  obtain ⟨K, hK, Ng, hNg⟩ := hg
  obtain ⟨Nb, hNb⟩ := hfg
  refine ⟨K, hK, max Ng Nb, ?_⟩
  intro N hN L hNL
  exact
    (hNb N ((le_max_right _ _).trans hN) L hNL).trans
      (hNg N ((le_max_left _ _).trans hN) L hNL)

/-! ## Fixed power savings dominate the displayed logarithmic rate -/

/--
The square of `log log N` is uniformly subpolynomial, independently of the
admissible auxiliary parameter.
-/
theorem loglogSquared_uniformSubpolynomial
    (admissible : ℕ → ℕ → Prop) :
    UniformSubpolynomialOn admissible
      (fun N _ ↦ (Real.log (Real.log N)) ^ 2) := by
  have henvelope :
      UniformSubpolynomialOn admissible
        (fun N _ ↦
          4 * Real.exp (2 * Real.sqrt (Real.log N))) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul 4
      (ExpSqrtLog.uniformSubpolynomialOn admissible 2 (by norm_num))
  apply UniformSubpolynomial.mono henvelope
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp (Real.exp 1))
  refine ⟨N₀, ?_⟩
  intro N hN L _hNL
  have hthreshold :
      Real.exp (Real.exp 1) < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hlogN :
      Real.exp 1 < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos (Real.exp 1)) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hlogNpos : 0 < Real.log N :=
    (Real.exp_pos 1).trans hlogN
  have hloglogN :
      1 < Real.log (Real.log N) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos 1) hlogN
    simpa only [Real.log_exp] using hlogs
  have hloglogLe :=
    LogLogRunWindow.loglog_le_two_mul_sqrt_log hlogNpos
  have hsq :
      (Real.log (Real.log N)) ^ 2 ≤
        4 * Real.log N := by
    nlinarith [Real.sqrt_nonneg (Real.log N),
      Real.sq_sqrt hlogNpos.le]
  have hlogExp :
      Real.log N ≤
        Real.exp (2 * Real.sqrt (Real.log N)) :=
    ExpSqrtLog.le_exp_two_mul_sqrt hlogNpos.le
  rw [abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (by positivity :
      0 ≤ 4 * Real.exp (2 * Real.sqrt (Real.log N)))]
  exact hsq.trans
    (mul_le_mul_of_nonneg_left hlogExp (by norm_num))

/--
Any fixed rational power strictly below `r` enjoys the explicit
`N^r/(log log N)^2` big-O rate.

This is a purely analytic closure lemma.  Multiplication by
`(log log N)^2` preserves the reciprocal-power class, after which the
existing strict-power little-oh theorem is applied with coefficient one.
-/
theorem rationalPower_uniformBigO_natPowerDivLogLogSquared
    {p q r : ℕ} (hpqr : p < r * q)
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hf :
      UniformRationalPowerSubpolynomialOn
        p q admissible f) :
    UniformBigOOn admissible f
      (natPowerDivLogLogSquaredScale r) := by
  have hq : 0 < q := by
    by_contra hq0
    have hqZero : q = 0 := Nat.eq_zero_of_not_pos hq0
    simp only [hqZero, Nat.mul_zero, Nat.not_lt_zero] at hpqr
  have hscaled :
      UniformRationalPowerSubpolynomialOn p q admissible
        (fun N L ↦
          (Real.log (Real.log N)) ^ 2 * f N L) :=
    UniformRationalPower.mul_subpolynomial hq hf
      (loglogSquared_uniformSubpolynomial admissible)
  have hlittle :
      UniformLittleOOn admissible
        (fun N L ↦
          (Real.log (Real.log N)) ^ 2 * f N L)
        (fun N _ ↦ (N : ℝ) ^ r) :=
    UniformRationalPower.littleO_natPower_of_lt hpqr hscaled
  obtain ⟨Nf, hNf⟩ := hlittle 1 (by norm_num)
  obtain ⟨Nlog, hNlog⟩ :=
    exists_nat_gt (Real.exp (Real.exp 1))
  refine ⟨1, by norm_num, max Nf Nlog, ?_⟩
  intro N hN L hNL
  have hfBound :=
    hNf N ((le_max_left _ _).trans hN) L hNL
  have hthreshold :
      Real.exp (Real.exp 1) < (N : ℝ) :=
    hNlog.trans_le
      (by
        exact_mod_cast
          ((le_max_right Nf Nlog).trans hN))
  have hlogN :
      Real.exp 1 < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos (Real.exp 1)) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hloglogN :
      1 < Real.log (Real.log N) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos 1) hlogN
    simpa only [Real.log_exp] using hlogs
  have hloglogSq :
      0 < (Real.log (Real.log N)) ^ 2 :=
    pow_pos (zero_lt_one.trans hloglogN) 2
  have hpowNonneg : 0 ≤ (N : ℝ) ^ r := by positivity
  have hscaleNonneg :
      0 ≤ natPowerDivLogLogSquaredScale r N L := by
    unfold natPowerDivLogLogSquaredScale
    positivity
  have hloglogSqNonneg :
      0 ≤ (Real.log (Real.log N)) ^ 2 :=
    sq_nonneg _
  simp only [abs_mul, abs_of_nonneg hloglogSqNonneg,
    abs_of_nonneg hpowNonneg, one_mul] at hfBound
  rw [abs_of_nonneg hscaleNonneg, one_mul]
  unfold natPowerDivLogLogSquaredScale
  apply (le_div_iff₀ hloglogSq).2
  simpa only [mul_comm] using hfBound

/-- The real function `N` has the literal rational-power exponent `1`. -/
theorem natCast_uniformRationalPowerOne
    (admissible : ℕ → ℕ → Prop) :
    UniformRationalPowerSubpolynomialOn 1 1 admissible
      (fun N _ ↦ (N : ℝ)) := by
  intro k hk
  refine ⟨1, ?_⟩
  intro N hN L _hNL
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  rw [abs_of_nonneg (Nat.cast_nonneg N)]
  exact pow_le_pow_right₀ hNone (by omega)

/--
The elementary harmonic factor `1 + log(3N)` is uniformly
subpolynomial.
-/
theorem one_add_log_three_mul_uniformSubpolynomial
    (admissible : ℕ → ℕ → Prop) :
    UniformSubpolynomialOn admissible
      (fun N _ ↦ 1 + Real.log (3 * (N : ℝ))) := by
  let D : ℝ := 2 + Real.log 3
  have hD : 0 ≤ D := by
    dsimp only [D]
    have hlogThree : 0 ≤ Real.log (3 : ℝ) :=
      Real.log_nonneg (by norm_num)
    linarith
  have henvelope :
      UniformSubpolynomialOn admissible
        (fun N _ ↦
          D * Real.exp (2 * Real.sqrt (Real.log N))) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul D
      (ExpSqrtLog.uniformSubpolynomialOn admissible 2 (by norm_num))
  apply UniformSubpolynomial.mono henvelope
  refine ⟨2, ?_⟩
  intro N hN L _hNL
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hlogNnonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ N by omega))
  have hlogMul :
      Real.log (3 * (N : ℝ)) =
        Real.log 3 + Real.log N :=
    Real.log_mul (by norm_num) hNpos.ne'
  have hfactorNonneg :
      0 ≤ 1 + Real.log (3 * (N : ℝ)) := by
    rw [hlogMul]
    have hlogThree : 0 ≤ Real.log (3 : ℝ) :=
      Real.log_nonneg (by norm_num)
    linarith
  have hexpOne :
      1 ≤ Real.exp (2 * Real.sqrt (Real.log N)) :=
    Real.one_le_exp (by positivity)
  have hlogExp :
      Real.log N ≤
        Real.exp (2 * Real.sqrt (Real.log N)) :=
    ExpSqrtLog.le_exp_two_mul_sqrt hlogNnonneg
  rw [abs_of_nonneg hfactorNonneg,
    abs_of_nonneg (mul_nonneg hD (Real.exp_nonneg _))]
  rw [hlogMul]
  dsimp only [D]
  calc
    1 + (Real.log 3 + Real.log N) ≤
        1 + Real.log 3 +
          Real.exp (2 * Real.sqrt (Real.log N)) := by
      linarith
    _ ≤
        (2 + Real.log 3) *
          Real.exp (2 * Real.sqrt (Real.log N)) := by
      have hcoeff : 0 ≤ 1 + Real.log (3 : ℝ) := by
        have hlogThree : 0 ≤ Real.log (3 : ℝ) :=
          Real.log_nonneg (by norm_num)
        linarith
      calc
        1 + Real.log 3 +
              Real.exp (2 * Real.sqrt (Real.log N)) =
            Real.exp (2 * Real.sqrt (Real.log N)) +
              (1 + Real.log 3) := by ring
        _ ≤
            Real.exp (2 * Real.sqrt (Real.log N)) +
              (1 + Real.log 3) *
                Real.exp (2 * Real.sqrt (Real.log N)) :=
          add_le_add_left
            (by
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hexpOne hcoeff)
            _
        _ =
            (2 + Real.log 3) *
              Real.exp (2 * Real.sqrt (Real.log N)) := by ring

/--
An `N^(1/2+o(1))` quantity is
`O(N/(log log N)^2)`.
-/
theorem halfPower_uniformBigO_linearDivLogLogSquared
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hf : UniformHalfPowerSubpolynomialOn admissible f) :
    UniformBigOOn admissible f
      (natPowerDivLogLogSquaredScale 1) := by
  have hrat :
      UniformRationalPowerSubpolynomialOn 1 2 admissible f := by
    simpa only [UniformHalfPowerSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn, Nat.one_mul] using hf
  exact
    rationalPower_uniformBigO_natPowerDivLogLogSquared
      (p := 1) (q := 2) (r := 1) (by omega) hrat

/--
Corollary 11.3 immediately yields the quadratic
`N²/(log log N)²` numerator bound needed in Section 13.
-/
theorem homogeneousMass_uniformBigO_quadraticLogLogSquared
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (hhosts : PropositionNineNine.HostCountStatement C A)
    {c : ℝ} (hc : 0 < c)
    (hnonterminal :
      NonterminalSectorQuantitativeStatement
        C A c smallRowRank rankBudget)
    (hterminal :
      TerminalSectorMassStatement
        C A smallRowRank rankBudget) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (homogeneousMass A)
      quadraticDivLogLogSquaredScale :=
  uniformBigOOn_trans
    (PropositionElevenThree.corollary_eleven_three_uniformBigO
      hC A hA smallRowRank rankBudget hhosts hc
      hnonterminal hterminal)
    (quantitativeHomogeneousScale_uniformBigO_loglogSquared hc)

/-! ## Exact dyadic normalization -/

/--
A nonnegative numerator bounded by `N²/(log log N)²` becomes bounded by
`1/(log log N)²` after division by `2^(2L)` in the critical window.
-/
theorem normalizedQuadraticLogLog_uniformBigO
    {C : ℝ} (hC : 0 ≤ C)
    {f : ℕ → ℕ → ℝ}
    (hf :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        f quadraticDivLogLogSquaredScale)
    (hfNonneg : ∀ N L, 0 ≤ f N L) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦ f N L / (2 : ℝ) ^ (2 * L))
      inverseLogLogSquaredRate := by
  obtain ⟨K, hK, Nf, hf⟩ := hf
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let D : ℝ := K * CriticalRunWindow.balanceConstant C ^ 2
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, max Nf Nwindow, ?_⟩
  intro N hN L hrun
  have hfN :=
    hf N ((le_max_left _ _).trans hN) L hrun
  have hw :=
    hwindow N ((le_max_right _ _).trans hN) L hrun
  have hpowPos : 0 < (2 : ℝ) ^ (2 * L) := by positivity
  have hratioNonneg :
      0 ≤ (N : ℝ) / (2 : ℝ) ^ L := by positivity
  have hratioSq :
      ((N : ℝ) / (2 : ℝ) ^ L) ^ 2 ≤
        CriticalRunWindow.balanceConstant C ^ 2 :=
    pow_le_pow_left₀ hratioNonneg hw.2.2 2
  have htargetNonneg :
      0 ≤ quadraticDivLogLogSquaredScale N L := by
    unfold quadraticDivLogLogSquaredScale
    positivity
  have hrateNonneg :
      0 ≤ inverseLogLogSquaredRate N L := by
    unfold inverseLogLogSquaredRate
    positivity
  simp only [abs_div, abs_of_nonneg (hfNonneg N L),
    abs_of_pos hpowPos, abs_of_nonneg htargetNonneg,
    abs_of_nonneg hrateNonneg] at hfN ⊢
  unfold quadraticDivLogLogSquaredScale at hfN
  unfold inverseLogLogSquaredRate
  calc
    f N L / (2 : ℝ) ^ (2 * L) ≤
        (K * ((N : ℝ) ^ 2 /
          Real.log (Real.log N) ^ 2)) /
            (2 : ℝ) ^ (2 * L) :=
      div_le_div_of_nonneg_right hfN hpowPos.le
    _ =
        K * (((N : ℝ) / (2 : ℝ) ^ L) ^ 2) *
          (1 / Real.log (Real.log N) ^ 2) := by
      rw [show 2 * L = L * 2 by omega, pow_mul]
      ring
    _ ≤
        K * CriticalRunWindow.balanceConstant C ^ 2 *
          (1 / Real.log (Real.log N) ^ 2) := by
      gcongr
    _ = D * (1 / Real.log (Real.log N) ^ 2) := by
      dsimp only [D]

/--
A nonnegative numerator bounded by `N/(log log N)^2` has the displayed
Corollary 13.10 rate after division by `2^L`.
-/
theorem normalizedLinearLogLog_uniformBigO
    {C : ℝ} (hC : 0 ≤ C)
    {f : ℕ → ℕ → ℝ}
    (hf :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        f (natPowerDivLogLogSquaredScale 1))
    (hfNonneg : ∀ N L, 0 ≤ f N L) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦ f N L / (2 : ℝ) ^ L)
      inverseLogLogSquaredRate := by
  obtain ⟨K, hK, Nf, hf⟩ := hf
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let D : ℝ := K * CriticalRunWindow.balanceConstant C
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg hK (by
      unfold CriticalRunWindow.balanceConstant
      positivity)
  refine ⟨D, hD, max Nf Nwindow, ?_⟩
  intro N hN L hrun
  have hfN :=
    hf N ((le_max_left _ _).trans hN) L hrun
  have hw :=
    hwindow N ((le_max_right _ _).trans hN) L hrun
  have hpowPos : 0 < (2 : ℝ) ^ L := by positivity
  have htargetNonneg :
      0 ≤ natPowerDivLogLogSquaredScale 1 N L := by
    unfold natPowerDivLogLogSquaredScale
    positivity
  have hrateNonneg :
      0 ≤ inverseLogLogSquaredRate N L := by
    unfold inverseLogLogSquaredRate
    positivity
  simp only [abs_div, abs_of_nonneg (hfNonneg N L),
    abs_of_pos hpowPos, abs_of_nonneg htargetNonneg,
    abs_of_nonneg hrateNonneg] at hfN ⊢
  unfold natPowerDivLogLogSquaredScale at hfN
  unfold inverseLogLogSquaredRate
  simp only [pow_one] at hfN
  calc
    f N L / (2 : ℝ) ^ L ≤
        (K * ((N : ℝ) /
          Real.log (Real.log N) ^ 2)) /
            (2 : ℝ) ^ L :=
      div_le_div_of_nonneg_right hfN hpowPos.le
    _ =
        K * ((N : ℝ) / (2 : ℝ) ^ L) *
          (1 / Real.log (Real.log N) ^ 2) := by ring
    _ ≤
        K * CriticalRunWindow.balanceConstant C *
          (1 / Real.log (Real.log N) ^ 2) := by
      gcongr
      exact hw.2.2
    _ = D * (1 / Real.log (Real.log N) ^ 2) := by
      dsimp only [D]

/--
The terminal bad-start cardinality contribution has the explicit
Corollary 13.10 logarithmic rate.
-/
theorem normalized_terminalBadStarts_uniformBigO_explicitRate
    {C : ℝ} (hC : 0 ≤ C) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        ((terminalBadStarts N L
          (terminalPrimeCutoff (L + 1))).card : ℝ) /
            (2 : ℝ) ^ L)
      inverseLogLogSquaredRate := by
  apply normalizedLinearLogLog_uniformBigO hC
    (halfPower_uniformBigO_linearDivLogLogSquared
      (TerminalBadStartsCritical.terminalBadStarts_terminalCutoff_uniformHalfPower
        hC))
  intro N L
  positivity

/--
The weighted terminal-defect part of the bad-start coupling has the same
explicit rate.
-/
theorem normalizedTerminalDefectContribution_uniformBigO_explicitRate
    {C : ℝ} (hC : 0 ≤ C) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      BadStartMassCritical.normalizedTerminalDefectContribution
      inverseLogLogSquaredRate := by
  have hnormalized :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          BadStartMassCritical.terminalDefectWeightMassReal N L /
            (2 : ℝ) ^ L)
        inverseLogLogSquaredRate := by
    apply normalizedLinearLogLog_uniformBigO hC
      (halfPower_uniformBigO_linearDivLogLogSquared
        (BadStartMassCritical.terminalDefectWeightMass_uniformHalfPower hC))
    intro N L
    unfold BadStartMassCritical.terminalDefectWeightMassReal
    rw [BadStartMassCritical.terminalDefectWeightMass_eq_natCast]
    positivity
  have htwo := uniformBigOOn_const_mul 2 hnormalized
  convert htwo using 1
  funext N L
  unfold BadStartMassCritical.normalizedTerminalDefectContribution
  ring

/--
The complete terminal bad-start probability mass, obtained from the exact
two-cutoff inequality, has the displayed rate.
-/
theorem terminalBadStartProbabilityMass_uniformBigO_explicitRate
    {C : ℝ} (hC : 0 ≤ C) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      BadStartMassCritical.terminalBadStartProbabilityMass
      inverseLogLogSquaredRate := by
  let countContribution : ℕ → ℕ → ℝ :=
    fun N L ↦
      ((terminalBadStarts N L
        (terminalPrimeCutoff (L + 1))).card : ℝ) /
          (2 : ℝ) ^ L
  have hdefect :=
    normalizedTerminalDefectContribution_uniformBigO_explicitRate hC
  have hcount :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        countContribution inverseLogLogSquaredRate := by
    simpa only [countContribution] using
      normalized_terminalBadStarts_uniformBigO_explicitRate hC
  have hsum :=
    PropositionElevenThree.uniformBigOOn_add hdefect hcount
  apply uniformBigOOn_mono hsum
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  refine ⟨max Nwindow Nadm, ?_⟩
  intro N hN L hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hAdm :=
    hadm N ((le_max_right _ _).trans hN)
      (L + 1) hw.1
  have hfinite :=
    BadStartMassCritical.terminalBadStartProbabilityMass_le
      (N := N) (L := L) hAdm.2.1 hw.2.1
  have hprobNonneg :
      0 ≤ BadStartMassCritical.terminalBadStartProbabilityMass N L := by
    unfold BadStartMassCritical.terminalBadStartProbabilityMass
    apply Rat.cast_nonneg.mpr
    unfold BadStartMass.startProbabilityMass
    exact Finset.sum_nonneg fun x _ ↦
      BadStartMass.startProbability_nonneg N L x
  have hdefectNonneg :
      0 ≤
        BadStartMassCritical.normalizedTerminalDefectContribution N L := by
    unfold BadStartMassCritical.normalizedTerminalDefectContribution
      BadStartMassCritical.terminalDefectWeightMassReal
    rw [BadStartMassCritical.terminalDefectWeightMass_eq_natCast]
    positivity
  have hcountNonneg : 0 ≤ countContribution N L := by
    dsimp only [countContribution]
    positivity
  rw [abs_of_nonneg hprobNonneg,
    abs_of_nonneg (add_nonneg hdefectNonneg hcountNonneg)]
  exact hfinite

/-- The normalized arithmetic term `2^(-2L) R₂(N,L)` has exactly the
Corollary 13.10 logarithmic rate. -/
theorem normalizedHomogeneousMass_uniformBigO_explicitRate
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (hhosts : PropositionNineNine.HostCountStatement C A)
    {c : ℝ} (hc : 0 < c)
    (hnonterminal :
      NonterminalSectorQuantitativeStatement
        C A c smallRowRank rankBudget)
    (hterminal :
      TerminalSectorMassStatement
        C A smallRowRank rankBudget) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦ homogeneousMass A N L /
        (2 : ℝ) ^ (2 * L))
      inverseLogLogSquaredRate := by
  apply normalizedQuadraticLogLog_uniformBigO hC
    (homogeneousMass_uniformBigO_quadraticLogLogSquared
      hC A hA smallRowRank rankBudget hhosts hc
      hnonterminal hterminal)
  intro N L
  unfold homogeneousMass
  split_ifs
  · positivity
  · exact le_rfl

/-! ## A sharper finite edge estimate without Mertens -/

/-- The reciprocal-square contribution in the sharpened edge bound. -/
noncomputable def dependencyEdgeMainTerm
    (N L : ℕ) : ℝ :=
  (L + 1 : ℝ) ^ 2 *
    (28 * (N : ℝ) ^ 2 /
      ((terminalPrimeCutoff (L + 1) : ℝ) *
        (Nat.log 2 (terminalPrimeCutoff (L + 1)) : ℝ)))

/-- The harmonic reciprocal-prime contribution in the sharpened edge bound. -/
noncomputable def dependencyEdgeHarmonicTerm
    (N L : ℕ) : ℝ :=
  (L + 1 : ℝ) ^ 2 *
    (2 * (N : ℝ) * (1 + Real.log (3 * N)))

/-- The cardinal contribution in the sharpened edge bound. -/
noncomputable def dependencyEdgeLinearTerm
    (N L : ℕ) : ℝ :=
  (L + 1 : ℝ) ^ 2 * (3 * (N : ℝ))

/-- Every reciprocal prime in the dependency range is bounded by the
corresponding real harmonic sum. -/
theorem sum_inv_largePrimesInRange_le_harmonic
    (N Y : ℕ) :
    (∑ p ∈ largePrimesInRange Y (3 * N),
        1 / (p : ℝ)) ≤
      (harmonic (3 * N) : ℝ) := by
  have hsubset :
      largePrimesInRange Y (3 * N) ⊆
        Finset.Icc 1 (3 * N) := by
    intro p hp
    have hpData := mem_largePrimesInRange.mp hp
    exact Finset.mem_Icc.mpr
      ⟨hpData.1.two_le.trans' (by norm_num), hpData.2.2⟩
  calc
    (∑ p ∈ largePrimesInRange Y (3 * N),
        1 / (p : ℝ)) ≤
      ∑ p ∈ Finset.Icc 1 (3 * N),
        1 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p _hp _hpSmall ↦ by positivity)
    _ = (harmonic (3 * N) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum,
        Rat.cast_inv, Rat.cast_natCast, one_div]

/-- Harmonic logarithmic form of the preceding bound. -/
theorem sum_inv_largePrimesInRange_le_one_add_log
    (N Y : ℕ) :
    (∑ p ∈ largePrimesInRange Y (3 * N),
        1 / (p : ℝ)) ≤
      1 + Real.log (3 * N) :=
  (sum_inv_largePrimesInRange_le_harmonic N Y).trans
    (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        harmonic_le_one_add_log (3 * N))

/--
Sharpened finite dependency-edge estimate.  Compared with
`DependencyEdgeBound.card_orderedDependencyEdges_cast_le`, only the middle
reciprocal-prime sum is changed, from `3N/Y` to the elementary harmonic
majorant `1 + log(3N)`.
-/
theorem card_orderedDependencyEdges_cast_le_harmonic
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hLN : L ≤ N)
    (hLY : L ≤ Y) (hY : 4 ≤ Y) :
    ((orderedDependencyEdges N L Y).card : ℝ) ≤
      (L + 1 : ℝ) ^ 2 *
        (28 * (N : ℝ) ^ 2 /
            ((Y : ℝ) * (Nat.log 2 Y : ℝ)) +
          2 * (N : ℝ) * (1 + Real.log (3 * N)) +
          3 * (N : ℝ)) := by
  have hedgeQ :=
    card_orderedDependencyEdges_cast_le_prime_sum
      (N := N) (L := L) (Y := Y) hN hLN hLY
  have hedge := (Rat.cast_le (K := ℝ)).2 hedgeQ
  push_cast at hedge
  have hsquareQ :=
    DependencyEdgeBound.sum_inv_sq_largePrimesInRange_le
      (N := N) hY
  have hsquare := (Rat.cast_le (K := ℝ)).2 hsquareQ
  push_cast at hsquare
  have hinv :=
    sum_inv_largePrimesInRange_le_one_add_log N Y
  have hcard :
      ((largePrimesInRange Y (3 * N)).card : ℝ) ≤
        3 * (N : ℝ) := by
    exact_mod_cast
      DependencyEdgeBound.card_largePrimesInRange_le N Y
  have hexpand :
      (∑ p ∈ largePrimesInRange Y (3 * N),
          ((N : ℝ) / (p : ℝ) + 1) ^ 2) =
        (N : ℝ) ^ 2 *
            (∑ p ∈ largePrimesInRange Y (3 * N),
              1 / (p : ℝ) ^ 2) +
          2 * (N : ℝ) *
            (∑ p ∈ largePrimesInRange Y (3 * N),
              1 / (p : ℝ)) +
          (largePrimesInRange Y (3 * N)).card := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [Finset.card_eq_sum_ones]
    push_cast
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  rw [hexpand] at hedge
  calc
    ((orderedDependencyEdges N L Y).card : ℝ) ≤
        (L + 1 : ℝ) ^ 2 *
          ((N : ℝ) ^ 2 *
              (∑ p ∈ largePrimesInRange Y (3 * N),
                1 / (p : ℝ) ^ 2) +
            2 * (N : ℝ) *
              (∑ p ∈ largePrimesInRange Y (3 * N),
                1 / (p : ℝ)) +
            (largePrimesInRange Y (3 * N)).card) := hedge
    _ ≤
        (L + 1 : ℝ) ^ 2 *
          ((N : ℝ) ^ 2 *
              (28 / ((Y : ℝ) * (Nat.log 2 Y : ℝ))) +
            2 * (N : ℝ) * (1 + Real.log (3 * N)) +
            3 * (N : ℝ)) := by
      gcongr
    _ =
        (L + 1 : ℝ) ^ 2 *
          (28 * (N : ℝ) ^ 2 /
              ((Y : ℝ) * (Nat.log 2 Y : ℝ)) +
            2 * (N : ℝ) * (1 + Real.log (3 * N)) +
            3 * (N : ℝ)) := by ring

end

end SectionThirteenRate
end PaperC
