import PaperC.Analysis.CriticalWindowParameters

/-!
# Eventual Runge scale in the critical window

This file discharges the last real inequality left explicit in
`CriticalWindowParameters`: uniformly for

`c₁ * log N ≤ H ≤ c₂ * log N`,

the independently defined `requiredRadius` fits below the logarithmic Runge
quotient.  The proof never mentions `cappedRadius`.

The finite core uses two transparent comparisons:

* `log (256 * logarithmicCap N * H) ≤ 4 * log H`;
* `512 * log H ≤ log N`.

Both are proved below from one explicit lower bound on `log N`.
-/

namespace PaperC
namespace CriticalWindowScale

open CriticalWindowParameters

/-- Above `8`, the integral binary logarithm dominates the natural logarithm. -/
theorem real_log_le_nat_log_two {H : ℕ} (hH : 8 ≤ H) :
    Real.log H ≤ (Nat.log 2 H : ℝ) := by
  have hHpos : 0 < H := by omega
  have hLthree : 3 ≤ Nat.log 2 H := by
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num
    exact hH
  have hpow :
      H < 2 ^ (Nat.log 2 H + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) H
  have hlog :
      Real.log (H : ℝ) <
        Real.log (((2 ^ (Nat.log 2 H + 1) : ℕ) : ℝ)) := by
    apply Real.log_lt_log
    · exact_mod_cast hHpos
    · exact_mod_cast hpow
  have hlogTwo : Real.log (2 : ℝ) < 3 / 4 := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hupper :
      ((Nat.log 2 H + 1 : ℕ) : ℝ) * Real.log 2 ≤
        (Nat.log 2 H : ℝ) := by
    have hcast : (3 : ℝ) ≤ (Nat.log 2 H : ℝ) := by
      exact_mod_cast hLthree
    have hnonneg :
        0 ≤ ((Nat.log 2 H + 1 : ℕ) : ℝ) := by positivity
    calc
      ((Nat.log 2 H + 1 : ℕ) : ℝ) * Real.log 2
          ≤ ((Nat.log 2 H + 1 : ℕ) : ℝ) * (3 / 4) :=
        mul_le_mul_of_nonneg_left hlogTwo.le hnonneg
      _ ≤ (Nat.log 2 H : ℝ) := by
        push_cast
        linarith
  have hrewrite :
      Real.log (((2 ^ (Nat.log 2 H + 1) : ℕ) : ℝ)) =
        ((Nat.log 2 H + 1 : ℕ) : ℝ) * Real.log 2 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hrewrite] at hlog
  exact hlog.le.trans hupper

/-- Real upper bound for natural-number division. -/
private theorem cast_nat_div_le_div
    {a b : ℕ} (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)).2
  exact_mod_cast Nat.div_mul_le_self a b

/-- A ceiling quotient is at most the ordinary quotient plus one. -/
private theorem cast_ceilDiv_le_div_add_one
    {a b : ℕ} (hb : 0 < b) :
    ((a ⌈/⌉ b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) + 1 := by
  have hnat : a ⌈/⌉ b ≤ a / b + 1 := by
    rw [ceilDiv_le_iff_le_mul hb]
    exact (Nat.lt_mul_div_succ a hb).le
  calc
    ((a ⌈/⌉ b : ℕ) : ℝ) ≤ ((a / b + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = ((a / b : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (a : ℝ) / (b : ℝ) + 1 :=
      add_le_add (cast_nat_div_le_div hb) le_rfl

/--
The generous definition of `codingConstant` contains the exact factor needed
to absorb the upper endpoint of the critical window.
-/
theorem two_fifty_six_mul_c₂_le_codingConstant
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    256 * c₂ ≤ (codingConstant c₁ c₂ : ℝ) := by
  have hc₂ : 0 < c₂ := hc₁.trans hc₁c₂
  have hinv : 0 < 1 / c₁ := one_div_pos.mpr hc₁
  have hbase :
      256 * c₂ ≤ 256 * (1 + c₂) * (1 + 1 / c₁) := by
    nlinarith [mul_nonneg
      (show 0 ≤ 256 * (1 + c₂) by positivity)
      (show 0 ≤ 1 / c₁ by positivity)]
  exact hbase.trans (Nat.le_ceil _)

/--
Uniform upper bound for the independently chosen radius.

This is the key arithmetic estimate: no `cappedRadius` occurs in either its
hypotheses or its conclusion.
-/
theorem requiredRadius_cast_le
    {c₁ c₂ : ℝ} {N H : ℕ}
    (hwindow : InCriticalWindow c₁ c₂ N H)
    (hH : 8 ≤ H) :
    (requiredRadius H (codingConstant c₁ c₂) : ℝ) ≤
      7 * Real.log N / (256 * Real.log H) + 2 := by
  let A := codingConstant c₁ c₂
  let L := Nat.log 2 H
  have hc₁ : 0 < c₁ := hwindow.1
  have hc₁c₂ : c₁ < c₂ := hwindow.2.1
  have hc₂ : 0 < c₂ := hc₁.trans hc₁c₂
  have hA : 1 ≤ A :=
    one_le_codingConstant hc₁ hc₁c₂
  have hApos : 0 < A := by omega
  have hLthree : 3 ≤ L := by
    dsimp [L]
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num
    exact hH
  have hLpos : 0 < L := by omega
  have hlogHpos : 0 < Real.log (H : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < H by omega)
  have hlogHL : Real.log (H : ℝ) ≤ (L : ℝ) := by
    simpa only [L] using real_log_le_nat_log_two hH
  have hdivDemand :
      (((7 * H) / L : ℕ) : ℝ) ≤
        (7 : ℝ) * H / Real.log H := by
    calc
      (((7 * H) / L : ℕ) : ℝ) ≤
          ((7 * H : ℕ) : ℝ) / (L : ℝ) :=
        cast_nat_div_le_div hLpos
      _ = (7 : ℝ) * H / (L : ℝ) := by
        norm_num [Nat.cast_mul]
      _ ≤ (7 : ℝ) * H / Real.log H := by
        exact div_le_div_of_nonneg_left (by positivity)
          hlogHpos hlogHL
  have hdemand :
      (chebyshevDemand H : ℝ) ≤
        (7 : ℝ) * H / Real.log H + 1 := by
    dsimp [chebyshevDemand, L] at hdivDemand ⊢
    push_cast
    linarith
  have hceil :
      (requiredRadius H A : ℝ) ≤
        (chebyshevDemand H : ℝ) / (A : ℝ) + 1 := by
    exact cast_ceilDiv_le_div_add_one hApos
  have hlogNnonneg : 0 ≤ Real.log (N : ℝ) := by
    exact Real.log_natCast_nonneg N
  have hAabsorb :
      (H : ℝ) / (A : ℝ) ≤ Real.log N / 256 := by
    apply (div_le_iff₀ (by exact_mod_cast hApos : (0 : ℝ) < A)).2
    have hAc₂ :
        256 * c₂ ≤ (A : ℝ) := by
      simpa only [A] using
        two_fifty_six_mul_c₂_le_codingConstant hc₁ hc₁c₂
    calc
      (H : ℝ) ≤ c₂ * Real.log N := hwindow.2.2.2
      _ ≤ (A : ℝ) * (Real.log N / 256) := by
        have := mul_le_mul_of_nonneg_right hAc₂ hlogNnonneg
        nlinarith [show
          (A : ℝ) * (Real.log N / 256) =
            Real.log N / 256 * (A : ℝ) by ring]
      _ = (Real.log N / 256) * (A : ℝ) := by ring
  have hmain :
      ((7 : ℝ) * H / Real.log H) / (A : ℝ) ≤
        7 * Real.log N / (256 * Real.log H) := by
    have hseven :
        (7 : ℝ) * ((H : ℝ) / (A : ℝ)) ≤
          7 * (Real.log N / 256) :=
      mul_le_mul_of_nonneg_left hAabsorb (by norm_num)
    calc
      ((7 : ℝ) * H / Real.log H) / (A : ℝ) =
          ((7 : ℝ) * ((H : ℝ) / (A : ℝ))) / Real.log H := by
        field_simp
      _ ≤ (7 * (Real.log N / 256)) / Real.log H :=
        div_le_div_of_nonneg_right hseven hlogHpos.le
      _ = 7 * Real.log N / (256 * Real.log H) := by ring
  have hAone : (1 : ℝ) / (A : ℝ) ≤ 1 := by
    exact (div_le_one (by exact_mod_cast hApos : (0 : ℝ) < A)).2
      (by exact_mod_cast hA)
  calc
    (requiredRadius H (codingConstant c₁ c₂) : ℝ) =
        (requiredRadius H A : ℝ) := rfl
    _ ≤ (chebyshevDemand H : ℝ) / (A : ℝ) + 1 := hceil
    _ ≤ (((7 : ℝ) * H / Real.log H + 1) / (A : ℝ)) + 1 := by
      gcongr
    _ = (((7 : ℝ) * H / Real.log H) / (A : ℝ)) +
        (1 / (A : ℝ)) + 1 := by ring
    _ ≤ 7 * Real.log N / (256 * Real.log H) + 2 := by
      linarith

/--
Finite closure of the scaled-log inequality from two elementary logarithmic
comparisons.
-/
theorem scaled_log_le_of_log_comparisons
    {c₁ c₂ : ℝ} {N H : ℕ}
    (hwindow : InCriticalWindow c₁ c₂ N H)
    (hH : 8 ≤ H)
    (henvelope :
      Real.log (256 * logarithmicCap N * H) ≤
        4 * Real.log H)
    (hsmall : 512 * Real.log H ≤ Real.log N) :
    (requiredRadius H (codingConstant c₁ c₂) : ℝ) *
          (8 * Real.log (256 * logarithmicCap N * H)) ≤
        Real.log N := by
  have hlogHpos : 0 < Real.log (H : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < H by omega)
  have hradius := requiredRadius_cast_le hwindow hH
  have hradiusNonneg :
      0 ≤ (requiredRadius H (codingConstant c₁ c₂) : ℝ) := by positivity
  have henvNonneg :
      0 ≤ Real.log (256 * logarithmicCap N * H : ℝ) := by
    have hc₂ : 0 < c₂ := hwindow.1.trans hwindow.2.1
    have hlogNpos : 0 < Real.log (N : ℝ) := by
      by_contra h
      have hlogNnonpos : Real.log (N : ℝ) ≤ 0 := le_of_not_gt h
      have hupperNonpos : c₂ * Real.log (N : ℝ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc₂.le hlogNnonpos
      have hHpos : 0 < (H : ℝ) := by positivity
      exact (not_le_of_gt (hHpos.trans_le hwindow.2.2.2)) hupperNonpos
    have hNreal : (1 : ℝ) < (N : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg N)).mp hlogNpos
    have hN : 2 ≤ N := by exact_mod_cast hNreal
    have hT : 1 ≤ logarithmicCap N :=
      one_le_logarithmicCap hN
    have hbase : 1 ≤ 256 * logarithmicCap N * H := by
      have hHone : 1 ≤ H := by omega
      calc
        1 ≤ 256 := by norm_num
        _ = 256 * 1 * 1 := by norm_num
        _ ≤ 256 * logarithmicCap N * H :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 256 hT) hHone
    exact Real.log_nonneg (by exact_mod_cast hbase)
  calc
    (requiredRadius H (codingConstant c₁ c₂) : ℝ) *
          (8 * Real.log (256 * logarithmicCap N * H))
        ≤ (7 * Real.log N / (256 * Real.log H) + 2) *
            (8 * Real.log (256 * logarithmicCap N * H)) :=
      mul_le_mul_of_nonneg_right hradius (by positivity)
    _ ≤ (7 * Real.log N / (256 * Real.log H) + 2) *
            (8 * (4 * Real.log H)) := by
      apply mul_le_mul_of_nonneg_left
      · nlinarith
      · positivity
    _ ≤ Real.log N := by
      have hexpand :
          (7 * Real.log N / (256 * Real.log H) + 2) *
              (8 * (4 * Real.log H)) =
            (7 / 8) * Real.log N + 64 * Real.log H := by
        field_simp
        ring
      rw [hexpand]
      nlinarith

/--
A fixed explicit lower bound ensuring all logarithmic comparisons used in the
critical window.  It depends only on `c₁,c₂`.
-/
noncomputable def criticalLogThreshold (c₁ c₂ : ℝ) : ℝ :=
  max 1
    (max (8 / c₁)
      (max (512 / (c₁ * c₁))
        (max (1024 * Real.log (max 1 c₂))
          (2048 * Real.log 2048))))

/--
Elementary scaled logarithm estimate used for the second iterated logarithm.
-/
theorem one_zero_two_four_mul_log_le_self
    {x : ℝ} (hx : 0 < x)
    (hlarge : 2048 * Real.log 2048 ≤ x) :
    1024 * Real.log x ≤ x := by
  let y : ℝ := x / 2048
  have hy : 0 ≤ y := by
    dsimp [y]
    positivity
  have hypos : 0 < y := by
    dsimp [y]
    positivity
  have hlogy : Real.log y ≤ y :=
    Real.log_le_self hy
  have hsplit :
      Real.log x = Real.log y + Real.log 2048 := by
    have hmul : y * 2048 = x := by
      dsimp [y]
      field_simp
    rw [← hmul, Real.log_mul hypos.ne' (by norm_num)]
  rw [hsplit]
  calc
    1024 * (Real.log y + Real.log 2048)
        ≤ 1024 * (y + Real.log 2048) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hlogy _) (by norm_num)
    _ = x / 2 + 1024 * Real.log 2048 := by
      dsimp [y]
      ring
    _ ≤ x := by nlinarith

/--
The explicit threshold implies the two finite logarithmic comparisons,
uniformly over the whole critical window.
-/
theorem log_comparisons_of_criticalLogThreshold
    {c₁ c₂ : ℝ} {N H : ℕ}
    (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂)
    (hwindow : InCriticalWindow c₁ c₂ N H)
    (hthreshold :
      criticalLogThreshold c₁ c₂ ≤ Real.log N) :
    8 ≤ H ∧
      Real.log (256 * logarithmicCap N * H) ≤
        4 * Real.log H ∧
      512 * Real.log H ≤ Real.log N := by
  let x : ℝ := Real.log N
  let D : ℝ := max 1 c₂
  have hxthreshold :
      max 1
        (max (8 / c₁)
          (max (512 / (c₁ * c₁))
            (max (1024 * Real.log D)
              (2048 * Real.log 2048)))) ≤ x := by
    simpa only [criticalLogThreshold, x, D] using hthreshold
  obtain ⟨hxone, hrest⟩ := max_le_iff.mp hxthreshold
  obtain ⟨hx8, hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hxcoeff, hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hxD, hxlog⟩ := max_le_iff.mp hrest
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hc₂ : 0 < c₂ := hc₁.trans hc₁c₂
  have hDone : 1 ≤ D := by
    exact le_max_left _ _
  have hDpos : 0 < D := zero_lt_one.trans_le hDone
  have hc₂D : c₂ ≤ D := le_max_right _ _
  have hH8real : (8 : ℝ) ≤ H := by
    calc
      (8 : ℝ) = c₁ * (8 / c₁) := by field_simp
      _ ≤ c₁ * x := mul_le_mul_of_nonneg_left hx8 hc₁.le
      _ ≤ (H : ℝ) := hwindow.2.2.1
  have hH8 : 8 ≤ H := by exact_mod_cast hH8real
  have hHpos : 0 < (H : ℝ) := by positivity
  have hlogHpos : 0 < Real.log (H : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hlogx :
      1024 * Real.log x ≤ x :=
    one_zero_two_four_mul_log_le_self hxpos hxlog
  have hHupper : (H : ℝ) ≤ D * x := by
    calc
      (H : ℝ) ≤ c₂ * x := hwindow.2.2.2
      _ ≤ D * x := mul_le_mul_of_nonneg_right hc₂D hxpos.le
  have hlogHupper :
      Real.log (H : ℝ) ≤ Real.log D + Real.log x := by
    calc
      Real.log (H : ℝ) ≤ Real.log (D * x) := by
        apply Real.log_le_log hHpos
        exact hHupper
      _ = Real.log D + Real.log x :=
        Real.log_mul hDpos.ne' hxpos.ne'
  have hsmall :
      512 * Real.log (H : ℝ) ≤ x := by
    calc
      512 * Real.log (H : ℝ) ≤
          512 * (Real.log D + Real.log x) :=
        mul_le_mul_of_nonneg_left hlogHupper (by norm_num)
      _ ≤ x := by nlinarith
  have hcoeff :
      512 / c₁ ≤ (H : ℝ) := by
    calc
      512 / c₁ = c₁ * (512 / (c₁ * c₁)) := by
        field_simp
      _ ≤ c₁ * x :=
        mul_le_mul_of_nonneg_left hxcoeff hc₁.le
      _ ≤ (H : ℝ) := hwindow.2.2.1
  have hT :
      (logarithmicCap N : ℝ) ≤ 2 * x := by
    dsimp only [logarithmicCap, x]
    exact (Nat.ceil_lt_add_one hxpos.le).le.trans (by linarith)
  have hxH :
      x ≤ (H : ℝ) / c₁ := by
    apply (le_div_iff₀ hc₁).2
    simpa only [x, mul_comm] using hwindow.2.2.1
  have hbase :
      ((256 * logarithmicCap N * H : ℕ) : ℝ) ≤
        (H : ℝ) ^ 3 := by
    calc
      ((256 * logarithmicCap N * H : ℕ) : ℝ) =
          256 * (logarithmicCap N : ℝ) * (H : ℝ) := by
        push_cast
        ring
      _ ≤ 256 * (2 * x) * (H : ℝ) := by
        gcongr
      _ ≤ 256 * (2 * ((H : ℝ) / c₁)) * (H : ℝ) := by
        gcongr
      _ = (512 / c₁) * (H : ℝ) ^ 2 := by ring
      _ ≤ (H : ℝ) * (H : ℝ) ^ 2 := by
        gcongr
      _ = (H : ℝ) ^ 3 := by ring
  have henvelope :
      Real.log (256 * logarithmicCap N * H) ≤
        4 * Real.log H := by
    have hbasePos :
        0 < ((256 * logarithmicCap N * H : ℕ) : ℝ) := by
      have hNreal : (1 : ℝ) < (N : ℝ) :=
        (Real.log_pos_iff (Nat.cast_nonneg N)).mp hxpos
      have hN : 2 ≤ N := by exact_mod_cast hNreal
      have hTpos : 1 ≤ logarithmicCap N :=
        one_le_logarithmicCap hN
      positivity
    calc
      Real.log (256 * logarithmicCap N * H) ≤
          Real.log ((H : ℝ) ^ 3) :=
        Real.log_le_log
          (by
            simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbasePos)
          (by
            simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbase)
      _ = 3 * Real.log H := by
        rw [Real.log_pow]
        norm_num
      _ ≤ 4 * Real.log H := by nlinarith
  exact ⟨hH8, henvelope, hsmall⟩

/--
The scaled-log hypothesis of `CriticalWindowParameters` follows from the
single explicit threshold `criticalLogThreshold`.
-/
theorem scaled_log_le_of_criticalLogThreshold
    {c₁ c₂ : ℝ} {N H : ℕ}
    (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂)
    (hwindow : InCriticalWindow c₁ c₂ N H)
    (hthreshold :
      criticalLogThreshold c₁ c₂ ≤ Real.log N) :
    (requiredRadius H (codingConstant c₁ c₂) : ℝ) *
          (8 * Real.log (256 * logarithmicCap N * H)) ≤
        Real.log N := by
  obtain ⟨hH, henvelope, hsmall⟩ :=
    log_comparisons_of_criticalLogThreshold
      hc₁ hc₁c₂ hwindow hthreshold
  exact
    scaled_log_le_of_log_comparisons
      hwindow hH henvelope hsmall

/--
Uniform eventual closure of the critical-window Runge scale.

The threshold `N₀` depends only on `c₁,c₂`; the quantifiers over `N,H` have
the order needed by Proposition 3.2.
-/
theorem scaled_log_le_eventually
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H : ℕ,
      InCriticalWindow c₁ c₂ N H →
      (requiredRadius H (codingConstant c₁ c₂) : ℝ) *
            (8 * Real.log (256 * logarithmicCap N * H)) ≤
          Real.log N := by
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (Real.exp (criticalLogThreshold c₁ c₂))
  refine ⟨N₀, ?_⟩
  intro N hNN₀ H hwindow
  have hexp :
      Real.exp (criticalLogThreshold c₁ c₂) < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hNN₀)
  have hlogs :=
    Real.log_lt_log
      (Real.exp_pos (criticalLogThreshold c₁ c₂)) hexp
  have hthreshold :
      criticalLogThreshold c₁ c₂ ≤ Real.log N := by
    simpa only [Real.log_exp] using hlogs.le
  exact
    scaled_log_le_of_criticalLogThreshold
      hc₁ hc₁c₂ hwindow hthreshold

end CriticalWindowScale
end PaperC
