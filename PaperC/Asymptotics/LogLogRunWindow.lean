import PaperC.Asymptotics.ExpSqrtLog
import PaperC.Asymptotics.RationalPowerLittleO
import PaperC.Probability.CriticalRunWindow

/-!
# The logarithmically widening run-length window

Proposition 14.1 is uniform in the wider window

`|L - log₂ N| ≤ C⋆ log log N`.

The arithmetic input still applies because `L + 1` remains between two
fixed positive multiples of `log N`.  The only additional analytic feature
is that `N / 2^L` is no longer bounded by a constant.  It is nevertheless
uniformly subpolynomial: the window gives an exponential in `log log N`,
which is dominated here by an exponential in `sqrt (log N)`.

This file also records three general closure lemmas for the reciprocal-power
asymptotic predicates.  They are used below to retain the full
`N^(-1/2+o(1))` rate, rather than proving only convergence to zero.
-/

namespace PaperC

/-! ## General reciprocal-power closure lemmas -/

namespace UniformSubpolynomial

/-- Uniform subpolynomiality is stable under eventual pointwise domination. -/
theorem mono
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hg : UniformSubpolynomialOn admissible g)
    (hfg :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        |f N L| ≤ |g N L|) :
    UniformSubpolynomialOn admissible f := by
  intro k hk
  obtain ⟨Ng, hNg⟩ := hg k hk
  obtain ⟨Nb, hNb⟩ := hfg
  refine ⟨max Ng Nb, ?_⟩
  intro N hN L hNL
  exact
    (pow_le_pow_left₀ (abs_nonneg _)
      (hNb N ((le_max_right _ _).trans hN) L hNL) k).trans
      (hNg N ((le_max_left _ _).trans hN) L hNL)

end UniformSubpolynomial

namespace UniformHalfPower

/--
Multiplying an `N^(1/2+o(1))` quantity by an `N^o(1)` quantity preserves
the half-power rate.
-/
theorem mul_subpolynomial
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hf : UniformHalfPowerSubpolynomialOn admissible f)
    (hg : UniformSubpolynomialOn admissible g) :
    UniformHalfPowerSubpolynomialOn admissible
      (fun N L => f N L * g N L) := by
  intro k hk
  have htwok : 0 < 2 * k := Nat.mul_pos (by omega) hk
  have hfourk : 0 < 4 * k := Nat.mul_pos (by omega) hk
  obtain ⟨Nf, hNf⟩ := hf (2 * k) htwok
  obtain ⟨Ng, hNg⟩ := hg (4 * k) hfourk
  refine ⟨max Nf Ng, ?_⟩
  intro N hN L hNL
  have hfBound :
      |f N L| ^ (4 * k) ≤ (N : ℝ) ^ (2 * k + 1) := by
    have hexp : 2 * (2 * k) = 4 * k := by omega
    simpa only [hexp] using
      hNf N ((le_max_left _ _).trans hN) L hNL
  have hgBound :
      |g N L| ^ (4 * k) ≤ (N : ℝ) :=
    hNg N ((le_max_right _ _).trans hN) L hNL
  have hsq :
      (|f N L * g N L| ^ (2 * k)) ^ 2 ≤
        ((N : ℝ) ^ (k + 1)) ^ 2 := by
    calc
      (|f N L * g N L| ^ (2 * k)) ^ 2 =
          |f N L| ^ (4 * k) * |g N L| ^ (4 * k) := by
        rw [abs_mul, mul_pow, mul_pow]
        have hexp : (2 * k) * 2 = 4 * k := by omega
        simp only [← pow_mul, hexp]
      _ ≤ (N : ℝ) ^ (2 * k + 1) * (N : ℝ) :=
        mul_le_mul hfBound hgBound (by positivity)
          (by positivity)
      _ = ((N : ℝ) ^ (k + 1)) ^ 2 := by
        calc
          (N : ℝ) ^ (2 * k + 1) * (N : ℝ) =
              (N : ℝ) ^ (2 * k + 1 + 1) := by
            exact (pow_succ (N : ℝ) (2 * k + 1)).symm
          _ = (N : ℝ) ^ ((k + 1) * 2) := by
            congr 1
            omega
          _ = ((N : ℝ) ^ (k + 1)) ^ 2 := pow_mul _ _ _
  exact
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

end UniformHalfPower

namespace UniformNegativeHalfPower

/-- Every uniform `N^(-1/2+o(1))` quantity is uniformly `o(1)`. -/
theorem littleOOne
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hf : UniformNegativeHalfPowerSubpolynomialOn admissible f) :
    UniformLittleOOn admissible f (fun _ _ => 1) := by
  have hrat :
      UniformRationalPowerSubpolynomialOn 1 2 admissible
        (fun N L => (N : ℝ) * f N L) := by
    simpa [UniformNegativeHalfPowerSubpolynomialOn,
      UniformHalfPowerSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn] using hf
  have hscaled :
      UniformLittleOOn admissible
        (fun N L => (N : ℝ) * f N L)
        (fun N _ => (N : ℝ)) := by
    simpa only [pow_one] using
      (UniformRationalPower.littleO_natPower_of_lt
        (p := 1) (q := 2) (r := 1) (by omega) hrat)
  intro ε hε
  obtain ⟨Nf, hNf⟩ := hscaled ε hε
  refine ⟨max Nf 1, ?_⟩
  intro N hN L hNL
  have hNfN : Nf ≤ N := (le_max_left _ _).trans hN
  have hNone : 1 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hbound := hNf N hNfN L hNL
  simp only [abs_mul, abs_of_pos hNpos, abs_one, mul_one] at hbound ⊢
  apply (mul_le_mul_left hNpos).mp
  simpa only [mul_comm] using hbound

end UniformNegativeHalfPower

/-! ## The wider window and its analytic envelope -/

namespace LogLogRunWindow

/-- Literal window from Proposition 14.1. -/
def InRunLengthWindow (Cstar : ℝ) (N L : ℕ) : Prop :=
  |(L : ℝ) - Real.log N / Real.log 2| ≤
    Cstar * Real.log (Real.log N)

/--
A convenient subpolynomial envelope for `N / 2^L` in the wider window.
The factor `2` comes from the elementary inequality
`log log N ≤ 2 sqrt (log N)`.
-/
noncomputable def balanceEnvelope (Cstar : ℝ) (N : ℕ) : ℝ :=
  Real.exp
    ((2 * Cstar * Real.log 2) * Real.sqrt (Real.log N))

/-- Elementary logarithmic comparison used by both window conversions. -/
theorem loglog_le_two_mul_sqrt_log
    {N : ℕ} (hlogN : 0 < Real.log N) :
    Real.log (Real.log N) ≤
      2 * Real.sqrt (Real.log N) := by
  have hsqrtPos :
      0 < Real.sqrt (Real.log N) :=
    Real.sqrt_pos.2 hlogN
  have hlogSqrt :=
    Real.log_le_sub_one_of_pos hsqrtPos
  have hlogNonneg : 0 ≤ Real.log N := hlogN.le
  rw [Real.log_sqrt hlogNonneg] at hlogSqrt
  nlinarith [Real.sqrt_nonneg (Real.log N)]

/--
Eventually the widened run-length window still puts `L+1` in the fixed
logarithmic height window used by Proposition 3.2.  The same threshold also
records the elementary positivity conditions consumed later.
-/
theorem heightWindow_eventually
    {Cstar : ℝ} (hCstar : 0 ≤ Cstar) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      InRunLengthWindow Cstar N L →
        CriticalWindowParameters.InCriticalWindow
          CriticalRunWindow.lowerConstant
          CriticalRunWindow.upperConstant N (L + 1) ∧
        0 < L ∧
        2 ≤ N := by
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  let D : ℝ := 4 * Cstar * Real.log 2
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  let R : ℝ := max 1 (max (D ^ 2) (2 * Real.log 2))
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp R)
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  have hthreshold :
      Real.exp R < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hNpos : (0 : ℝ) < (N : ℝ) :=
    (Real.exp_pos R).trans hthreshold
  have hRlog : R < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos R) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hlogN : 0 < Real.log N :=
    (show (0 : ℝ) < 1 by norm_num).trans
      ((le_max_left 1 (max (D ^ 2) (2 * Real.log 2))).trans_lt hRlog)
  have hNtwo : 2 ≤ N := by
    have hNone : (1 : ℝ) < (N : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg N)).mp hlogN
    exact_mod_cast hNone
  have hloglog :
      Real.log (Real.log N) ≤
        2 * Real.sqrt (Real.log N) :=
    loglog_le_two_mul_sqrt_log hlogN
  have hDsquare :
      D ^ 2 < Real.log N :=
    (le_trans (le_max_left (D ^ 2) (2 * Real.log 2))
      (le_max_right 1 (max (D ^ 2) (2 * Real.log 2)))).trans_lt hRlog
  have hDsqrt :
      D ≤ Real.sqrt (Real.log N) := by
    exact
      (Real.le_sqrt hD hlogN.le).2 hDsquare.le
  have hsqrtNonneg :
      0 ≤ Real.sqrt (Real.log N) :=
    Real.sqrt_nonneg _
  have hsqrtSq :
      (Real.sqrt (Real.log N)) ^ 2 = Real.log N :=
    Real.sq_sqrt hlogN.le
  have herrorHalf :
      Cstar * Real.log (Real.log N) ≤
        (Real.log N / Real.log 2) / 2 := by
    have hfirst :
        Cstar * Real.log (Real.log N) ≤
          2 * Cstar * Real.sqrt (Real.log N) :=
      by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hloglog hCstar
    have hscaled :
        D * Real.sqrt (Real.log N) ≤ Real.log N := by
      calc
        D * Real.sqrt (Real.log N) ≤
            Real.sqrt (Real.log N) *
              Real.sqrt (Real.log N) :=
          mul_le_mul_of_nonneg_right hDsqrt hsqrtNonneg
        _ = Real.log N := by
          nlinarith [hsqrtSq]
    have hsecond :
        2 * Cstar * Real.sqrt (Real.log N) ≤
          (Real.log N / Real.log 2) / 2 := by
      rw [div_div]
      apply
        (le_div_iff₀
          (show 0 < Real.log 2 * (2 : ℝ) by positivity)).2
      dsimp only [D] at hscaled
      nlinarith
    exact hfirst.trans hsecond
  have hellTwo :
      (2 : ℝ) < Real.log N / Real.log 2 := by
    have htwoLog :
        2 * Real.log 2 < Real.log N :=
      (le_trans (le_max_right (D ^ 2) (2 * Real.log 2))
        (le_max_right 1 (max (D ^ 2) (2 * Real.log 2)))).trans_lt hRlog
    exact (lt_div_iff₀ hlogTwo).2 htwoLog
  let ell : ℝ := Real.log N / Real.log 2
  have hrun' :
      |(L : ℝ) - ell| ≤
        Cstar * Real.log (Real.log N) := by
    simpa only [InRunLengthWindow, ell] using hrun
  obtain ⟨hlower, hupper⟩ := abs_le.mp hrun'
  have herrorHalf' :
      Cstar * Real.log (Real.log N) ≤ ell / 2 := by
    simpa only [ell] using herrorHalf
  have hLlower : ell / 2 ≤ (L : ℝ) := by
    linarith
  have hLupper : (L : ℝ) + 1 ≤ 2 * ell := by
    have hone : (1 : ℝ) ≤ ell / 2 := by linarith
    linarith
  have hLpos : 0 < L := by
    have hLreal : (0 : ℝ) < (L : ℝ) := by
      have hellPos : (0 : ℝ) < ell := by linarith
      linarith
    exact_mod_cast hLreal
  have hcriticalLower :
      CriticalRunWindow.lowerConstant * Real.log N ≤
        ((L + 1 : ℕ) : ℝ) := by
    have hre :
        CriticalRunWindow.lowerConstant * Real.log N = ell / 2 := by
      dsimp [CriticalRunWindow.lowerConstant, ell]
      ring
    rw [hre]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hcriticalUpper :
      ((L + 1 : ℕ) : ℝ) ≤
        CriticalRunWindow.upperConstant * Real.log N := by
    have hre :
        CriticalRunWindow.upperConstant * Real.log N = 2 * ell := by
      dsimp [CriticalRunWindow.upperConstant, ell]
      ring
    rw [hre]
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact hLupper
  exact
    ⟨⟨CriticalRunWindow.lowerConstant_pos,
      CriticalRunWindow.lowerConstant_lt_upperConstant,
      hcriticalLower, hcriticalUpper⟩,
      hLpos, hNtwo⟩

/--
The balance ratio in the widened window is eventually bounded by the
explicit exponential-square-root envelope.
-/
theorem balanceRatio_le_envelope_eventually
    {Cstar : ℝ} (hCstar : 0 ≤ Cstar) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      InRunLengthWindow Cstar N L →
        (N : ℝ) / (2 : ℝ) ^ L ≤
          balanceEnvelope Cstar N := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  have hthreshold :
      Real.exp 1 < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hNpos : (0 : ℝ) < (N : ℝ) :=
    (Real.exp_pos 1).trans hthreshold
  have hlogN : 0 < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos 1) hthreshold
    have : (1 : ℝ) < Real.log N := by
      simpa only [Real.log_exp] using hlogs
    linarith
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hloglog :
      Real.log (Real.log N) ≤
        2 * Real.sqrt (Real.log N) :=
    loglog_le_two_mul_sqrt_log hlogN
  let ell : ℝ := Real.log N / Real.log 2
  have hrun' :
      |(L : ℝ) - ell| ≤
        Cstar * Real.log (Real.log N) := by
    simpa only [InRunLengthWindow, ell] using hrun
  have hlower :=
    (abs_le.mp hrun').1
  have hlogBound :
      Real.log N ≤
        (L : ℝ) * Real.log 2 +
          Cstar * Real.log (Real.log N) * Real.log 2 := by
    dsimp only [ell] at hlower
    have hmul :=
      mul_le_mul_of_nonneg_right hlower hlogTwo.le
    field_simp at hmul
    nlinarith
  have hpowExp :
      (2 : ℝ) ^ L =
        Real.exp ((L : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ L =
          (Real.exp (Real.log 2)) ^ L := by
        rw [Real.exp_log]
        norm_num
      _ = Real.exp ((L : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul (Real.log 2) L).symm
  have hraw :
      (N : ℝ) / (2 : ℝ) ^ L ≤
        Real.exp
          ((Cstar * Real.log 2) *
            Real.log (Real.log N)) := by
    apply (div_le_iff₀ (pow_pos (by norm_num) L)).2
    rw [hpowExp]
    calc
      (N : ℝ) = Real.exp (Real.log N) :=
        (Real.exp_log hNpos).symm
      _ ≤
          Real.exp
            ((L : ℝ) * Real.log 2 +
              (Cstar * Real.log 2) *
                Real.log (Real.log N)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hlogBound]
      _ =
          Real.exp
              ((Cstar * Real.log 2) *
                Real.log (Real.log N)) *
            Real.exp ((L : ℝ) * Real.log 2) := by
        rw [Real.exp_add]
        ring
  apply hraw.trans
  unfold balanceEnvelope
  apply Real.exp_le_exp.mpr
  have hcoefficient : 0 ≤ Cstar * Real.log 2 := by
    positivity
  have :=
    mul_le_mul_of_nonneg_left hloglog hcoefficient
  nlinarith

/-- The balance ratio `N / 2^L` is uniformly `N^o(1)` in the wider window. -/
theorem balanceRatio_uniformSubpolynomial
    {Cstar : ℝ} (hCstar : 0 ≤ Cstar) :
    UniformSubpolynomialOn (InRunLengthWindow Cstar)
      (fun N L => (N : ℝ) / (2 : ℝ) ^ L) := by
  have henvelope :
      UniformSubpolynomialOn (InRunLengthWindow Cstar)
        (fun N _ => balanceEnvelope Cstar N) := by
    simpa only [balanceEnvelope] using
      ExpSqrtLog.uniformSubpolynomialOn
        (InRunLengthWindow Cstar)
        (2 * Cstar * Real.log 2) (by positivity)
  apply UniformSubpolynomial.mono henvelope
  obtain ⟨N₀, hN₀⟩ :=
    balanceRatio_le_envelope_eventually hCstar
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  have henvelopePos : 0 < balanceEnvelope Cstar N := by
    unfold balanceEnvelope
    positivity
  rw [abs_of_nonneg (by positivity),
    abs_of_pos henvelopePos]
  exact hN₀ N hN L hrun

end LogLogRunWindow
end PaperC
