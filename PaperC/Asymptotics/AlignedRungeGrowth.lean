import PaperC.Analysis.RungeLogarithmicGrowth
import PaperC.Asymptotics.ExpSqrtLog
import PaperC.Probability.CriticalRunWindow

set_option maxHeartbeats 1800000

/-!
# Uniform Runge growth on an aligned channel

This file closes the numerical Runge comparison used in Theorem 8.1.  Put
`B = L + 1`, let the channel height satisfy `H ≤ B^A`, and suppose that the
component-code radius has the paper scale

`t ≤ D B / (log B log log B)`.

Uniformly in `x ∈ [N,2N)`, in the positive channel coefficient `a`, and in
every `1 ≤ k ≤ 43t`, the quantitative Runge scale

`(128 * (2k) * (3HB))^(4k)`

is eventually strictly smaller than `a*x`.  The proof is deliberately split
into a finite logarithmic lemma and the eventual critical-window wrapper.
-/

namespace PaperC
namespace AlignedRungeGrowth

/--
Finite logarithmic comparison.  The assumptions expose exactly the
inequalities used in the eventual argument:

* the Runge base is polynomial in `B`;
* the radius has size `B / (log B log log B)`;
* `B` is at most a fixed multiple of `log N`;
* `log log B` eventually absorbs the fixed coefficient.
-/
theorem rungeScale_lt_of_log_budget
    {N B H t k a x A : ℕ} {D c₂ : ℝ}
    (hD : 0 ≤ D)
    (hN : 2 ≤ N)
    (hx : N ≤ x) (ha : 1 ≤ a)
    (hB : 768 ≤ B)
    (hH : 1 ≤ H) (hHupper : H ≤ B ^ A)
    (hk : 1 ≤ k) (hkt : k ≤ 43 * t)
    (hlogB : 1 ≤ Real.log B)
    (hloglogB : 1 ≤ Real.log (Real.log B))
    (hDleB : D ≤ (B : ℝ))
    (hBupper : (B : ℝ) ≤ c₂ * Real.log N)
    (ht :
      (t : ℝ) ≤
        D * B /
          (Real.log B * Real.log (Real.log B)))
    (hcoefficient :
      172 * (A + 6 : ℕ) * D * c₂ <
        Real.log (Real.log B)) :
    (128 * (2 * k) * (3 * H * B)) ^ (4 * k) < a * x := by
  have hBposNat : 0 < B := by omega
  have hBpos : 0 < (B : ℝ) := by positivity
  have hlogBpos : 0 < Real.log (B : ℝ) := by linarith
  have hloglogBpos :
      0 < Real.log (Real.log (B : ℝ)) := by linarith
  have hdenOne :
      (1 : ℝ) ≤
        Real.log B * Real.log (Real.log B) := by
    nlinarith
  have htBsqReal :
      (t : ℝ) ≤ (B : ℝ) ^ 2 := by
    calc
      (t : ℝ) ≤
          D * B /
            (Real.log B * Real.log (Real.log B)) := ht
      _ ≤ D * B :=
        div_le_self (mul_nonneg hD (Nat.cast_nonneg B)) hdenOne
      _ ≤ (B : ℝ) * B :=
        mul_le_mul_of_nonneg_right hDleB (Nat.cast_nonneg B)
      _ = (B : ℝ) ^ 2 := by ring
  have htBsq : t ≤ B ^ 2 := by
    exact_mod_cast htBsqReal
  have hfortythree : 43 ≤ B ^ 2 := by
    nlinarith
  have hkBfour : k ≤ B ^ 4 := by
    calc
      k ≤ 43 * t := hkt
      _ ≤ 43 * B ^ 2 :=
        Nat.mul_le_mul_left 43 htBsq
      _ ≤ B ^ 2 * B ^ 2 :=
        Nat.mul_le_mul_right (B ^ 2) hfortythree
      _ = B ^ 4 := by ring
  have hpow :
      B ^ (A + 5) = B ^ 4 * B ^ A * B := by
    rw [show A + 5 = 4 + A + 1 by omega, pow_succ, pow_add]
  have hbase :
      128 * (2 * k) * (3 * H * B) ≤ B ^ (A + 6) := by
    calc
      128 * (2 * k) * (3 * H * B) ≤
          128 * (2 * B ^ 4) * (3 * B ^ A * B) := by
        gcongr
      _ = 768 * B ^ (A + 5) := by
        rw [hpow]
        ring
      _ ≤ B * B ^ (A + 5) :=
        Nat.mul_le_mul_right (B ^ (A + 5)) hB
      _ = B ^ ((A + 5) + 1) :=
        (pow_succ' B (A + 5)).symm
      _ = B ^ (A + 6) := by
        congr 1
  have hbasePos :
      0 < 128 * (2 * k) * (3 * H * B) := by
    positivity
  have hlogBase :
      Real.log (128 * (2 * k) * (3 * H * B)) ≤
        (A + 6 : ℕ) * Real.log B := by
    calc
      Real.log (128 * (2 * k) * (3 * H * B)) ≤
          Real.log (B ^ (A + 6) : ℕ) := by
        apply Real.log_le_log
        · exact_mod_cast hbasePos
        · exact_mod_cast hbase
      _ = (A + 6 : ℕ) * Real.log B := by
        rw [Nat.cast_pow, Real.log_pow]
  have hkReal : (k : ℝ) ≤ 43 * (t : ℝ) := by
    exact_mod_cast hkt
  have hAlogNonneg :
      0 ≤ (A + 6 : ℕ) * Real.log B := by
    positivity
  have htScaled :
      (172 : ℝ) * t ≤
        172 *
          (D * B /
            (Real.log B * Real.log (Real.log B))) := by
    exact mul_le_mul_of_nonneg_left ht (by norm_num)
  have hscaled :
      (4 * k : ℝ) *
          Real.log (128 * (2 * k) * (3 * H * B)) ≤
        (172 * (A + 6 : ℕ) * D) *
          ((B : ℝ) / Real.log (Real.log B)) := by
    calc
      (4 * k : ℝ) *
            Real.log (128 * (2 * k) * (3 * H * B)) ≤
          (4 * k : ℝ) *
            ((A + 6 : ℕ) * Real.log B) :=
        mul_le_mul_of_nonneg_left hlogBase (by positivity)
      _ ≤ (4 * (43 * t) : ℝ) *
            ((A + 6 : ℕ) * Real.log B) := by
        apply mul_le_mul_of_nonneg_right _ hAlogNonneg
        nlinarith
      _ = (172 : ℝ) * t *
            ((A + 6 : ℕ) * Real.log B) := by ring
      _ ≤
          (172 *
              (D * B /
                (Real.log B * Real.log (Real.log B)))) *
            ((A + 6 : ℕ) * Real.log B) :=
        mul_le_mul_of_nonneg_right htScaled hAlogNonneg
      _ = (172 * (A + 6 : ℕ) * D) *
            ((B : ℝ) / Real.log (Real.log B)) := by
        field_simp [hlogBpos.ne', hloglogBpos.ne']
        ring
  have hcoefficientNonneg :
      0 ≤ (172 * (A + 6 : ℕ) * D : ℝ) := by
    positivity
  have hlogNpos : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hnum :
      (172 * (A + 6 : ℕ) * D : ℝ) * B ≤
        (172 * (A + 6 : ℕ) * D : ℝ) *
          (c₂ * Real.log N) :=
    mul_le_mul_of_nonneg_left hBupper hcoefficientNonneg
  have hratio :
      (172 * (A + 6 : ℕ) * D * c₂) /
          Real.log (Real.log B) < 1 :=
    (div_lt_one hloglogBpos).2 hcoefficient
  have hstrict :
      (172 * (A + 6 : ℕ) * D) *
          ((B : ℝ) / Real.log (Real.log B)) <
        Real.log N := by
    calc
      (172 * (A + 6 : ℕ) * D) *
            ((B : ℝ) / Real.log (Real.log B)) =
          ((172 * (A + 6 : ℕ) * D) * B) /
            Real.log (Real.log B) := by ring
      _ ≤
          ((172 * (A + 6 : ℕ) * D) *
              (c₂ * Real.log N)) /
            Real.log (Real.log B) :=
        div_le_div_of_nonneg_right hnum hloglogBpos.le
      _ =
          Real.log N *
            ((172 * (A + 6 : ℕ) * D * c₂) /
              Real.log (Real.log B)) := by ring
      _ < Real.log N * 1 :=
        mul_lt_mul_of_pos_left hratio hlogNpos
      _ = Real.log N := mul_one _
  have hNU : N ≤ a * x := by
    calc
      N ≤ x := hx
      _ = 1 * x := by omega
      _ ≤ a * x := Nat.mul_le_mul_right x ha
  have hlogNU :
      Real.log N ≤ Real.log (a * x : ℕ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hNU
  apply
    RungeLogarithmicGrowth.endpoint_growth_of_log
      hk
      (show 1 ≤ 3 * H * B by
        have : 0 < 3 * H * B := by positivity
        omega)
      (show 2 ≤ a * x by omega)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (hscaled.trans_lt hstrict |>.trans_le hlogNU)

/--
Uniform eventual form in the literal run-length window.  The constant `D`
may depend on the fixed density parameter (for example on `α`), but the
threshold is uniform in `L,H,t,k,a,x`.
-/
theorem rungeScale_lt_eventually
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ H, 1 ≤ H → H ≤ (L + 1) ^ A →
      ∀ t : ℕ,
        (t : ℝ) ≤
          D * (L + 1 : ℕ) /
            (Real.log (L + 1 : ℕ) *
              Real.log (Real.log (L + 1 : ℕ))) →
      ∀ k : ℕ, 1 ≤ k → k ≤ 43 * t →
      ∀ a : ℕ, 1 ≤ a → ∀ x : ℕ, x ∈ dyadicBlock N →
        (128 * (2 * k) * (3 * H * (L + 1))) ^ (4 * k) <
          a * x := by
  let c₁ : ℝ := CriticalRunWindow.lowerConstant
  let c₂ : ℝ := CriticalRunWindow.upperConstant
  let coefficient : ℝ := 172 * (A + 6 : ℕ) * D * c₂
  let S : ℝ := 769 + D + coefficient
  let threshold : ℝ :=
    Real.exp (Real.exp (Real.exp S) / c₁)
  have hc₁ : 0 < c₁ := by
    simpa only [c₁] using CriticalRunWindow.lowerConstant_pos
  have hc₂ : 0 < c₂ := by
    exact
      (CriticalRunWindow.lowerConstant_pos.trans
        CriticalRunWindow.lowerConstant_lt_upperConstant)
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  have hSnonneg : 0 ≤ S := by
    dsimp only [S]
    positivity
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nthreshold, hNthreshold⟩ :=
    exists_nat_gt threshold
  refine ⟨max Nwindow (max Nthreshold 2), ?_⟩
  intro N hN L hrun H hH hHupper t ht k hk hkt a ha x hx
  have hNwindowN : Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail : max Nthreshold 2 ≤ N :=
    (le_max_right _ _).trans hN
  have hNthresholdN : Nthreshold ≤ N :=
    (le_max_left _ _).trans hNtail
  have hNtwo : 2 ≤ N :=
    (le_max_right _ _).trans hNtail
  have hthresholdN : threshold < (N : ℝ) :=
    hNthreshold.trans_le (by exact_mod_cast hNthresholdN)
  have hlogThreshold :
      Real.exp (Real.exp S) / c₁ < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos _) hthresholdN
    simpa only [threshold, Real.log_exp] using hlogs
  have hexpexp_le_log :
      Real.exp (Real.exp S) <
        c₁ * Real.log N := by
    have :=
      (div_lt_iff₀ hc₁).mp hlogThreshold
    nlinarith
  have hcritical :=
    (hNwindow N hNwindowN L hrun).1
  have hexpexp_lt_B :
      Real.exp (Real.exp S) < (L + 1 : ℕ) := by
    exact hexpexp_le_log.trans_le hcritical.2.2.1
  have hexpS_lt_logB :
      Real.exp S < Real.log (L + 1 : ℕ) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos _) hexpexp_lt_B
    simpa only [Real.log_exp] using hlogs
  have hS_lt_loglogB :
      S < Real.log (Real.log (L + 1 : ℕ)) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos _) hexpS_lt_logB
    simpa only [Real.log_exp] using hlogs
  have hS_lt_expexpS :
      S < Real.exp (Real.exp S) := by
    have h₁ := Real.add_one_le_exp S
    have h₂ := Real.add_one_le_exp (Real.exp S)
    linarith
  have hB : 768 ≤ L + 1 := by
    have h768S : (768 : ℝ) < S := by
      dsimp only [S]
      linarith
    have h768B : (768 : ℝ) < (L + 1 : ℕ) :=
      h768S.trans hS_lt_expexpS |>.trans hexpexp_lt_B
    exact_mod_cast h768B.le
  have hDleB : D ≤ (L + 1 : ℕ) := by
    have hDS : D < S := by
      dsimp only [S]
      linarith
    exact
      (hDS.trans hS_lt_expexpS |>.trans hexpexp_lt_B).le
  have hlogB :
      1 ≤ Real.log (L + 1 : ℕ) := by
    have honeExpS : (1 : ℝ) ≤ Real.exp S :=
      Real.one_le_exp hSnonneg
    exact honeExpS.trans hexpS_lt_logB.le
  have hloglogB :
      1 ≤ Real.log (Real.log (L + 1 : ℕ)) := by
    have honeS : (1 : ℝ) ≤ S := by
      dsimp only [S]
      linarith
    exact honeS.trans hS_lt_loglogB.le
  have hcoefficientAbsorbed :
      172 * (A + 6 : ℕ) * D * c₂ <
        Real.log (Real.log (L + 1 : ℕ)) := by
    have hcoefficientS : coefficient < S := by
      dsimp only [S]
      linarith
    simpa only [coefficient] using
      hcoefficientS.trans hS_lt_loglogB
  have hxLower : N ≤ x :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).1
  exact
    rungeScale_lt_of_log_budget
      (N := N) (B := L + 1) (H := H) (t := t) (k := k)
      (a := a) (x := x) (A := A) (D := D) (c₂ := c₂)
      hD hNtwo hxLower ha hB hH hHupper hk hkt
      hlogB hloglogB hDleB hcritical.2.2.2 ht
      hcoefficientAbsorbed

/-! ## The translation-range condition -/

/--
Two extra powers of `B+1` absorb the numerical factor `6`.  This is the
finite polynomial estimate behind the Runge translation condition.
-/
theorem six_mul_pow_lt_succ_pow_add_two
    (B e : ℕ) (hB : 2 ≤ B) (he : 0 < e) :
    6 * B ^ e < (B + 1) ^ (e + 2) := by
  have hpow : B ^ e < (B + 1) ^ e :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self B) he.ne'
  have hsix : 6 ≤ (B + 1) ^ 2 := by
    nlinarith
  calc
    6 * B ^ e < 6 * (B + 1) ^ e :=
      (Nat.mul_lt_mul_left (by omega : 0 < 6)).2 hpow
    _ ≤ (B + 1) ^ 2 * (B + 1) ^ e :=
      Nat.mul_le_mul_right ((B + 1) ^ e) hsix
    _ = (B + 1) ^ (2 + e) :=
      (pow_add (B + 1) 2 e).symm
    _ = (B + 1) ^ (e + 2) := by
      congr 1
      omega

/--
Uniformly in the same run-length window, the polynomial radius
`R = 3 H (L+1)` satisfies `2R ≤ a*x` once `H ≤ (L+1)^A`,
`a ≥ 1`, and `x ∈ [N,2N)`.
-/
theorem translationRange_eventually
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ H, 1 ≤ H → H ≤ (L + 1) ^ A →
      ∀ a : ℕ, 1 ≤ a → ∀ x : ℕ, x ∈ dyadicBlock N →
        2 * (3 * H * (L + 1)) ≤ a * x := by
  have hupperNonneg :
      0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Npower, hNpower⟩ :=
    ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually
      CriticalRunWindow.upperConstant hupperNonneg
      (A + 3) (by omega)
  refine ⟨max Nwindow Npower, ?_⟩
  intro N hN L hrun H _hH hHupper a ha x hx
  have hNwindowN : Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have hNpowerN : Npower ≤ N :=
    (le_max_right _ _).trans hN
  have hfirst := hNwindow N hNwindowN L hrun
  have hBupper :
      (((L + 1 : ℕ) : ℝ) ≤
        CriticalRunWindow.upperConstant * Real.log N) :=
    hfirst.1.2.2.2
  have hpowerReal :=
    hNpower N hNpowerN (L + 1) hBupper
  have hpowerNat :
      ((L + 1) + 1) ^ (A + 3) ≤ N := by
    exact_mod_cast hpowerReal
  have hBtwo : 2 ≤ L + 1 := by
    have hLpos := hfirst.2.1
    omega
  have hpoly :
      2 * (3 * H * (L + 1)) <
        ((L + 1) + 1) ^ (A + 3) := by
    calc
      2 * (3 * H * (L + 1)) =
          6 * H * (L + 1) := by ring
      _ ≤ 6 * (L + 1) ^ A * (L + 1) :=
        Nat.mul_le_mul_right (L + 1)
          (Nat.mul_le_mul_left 6 hHupper)
      _ = 6 * (L + 1) ^ (A + 1) := by
        rw [pow_succ]
        ring
      _ < ((L + 1) + 1) ^ ((A + 1) + 2) :=
        six_mul_pow_lt_succ_pow_add_two
          (L + 1) (A + 1) hBtwo (by omega)
      _ = ((L + 1) + 1) ^ (A + 3) := by
        congr 1
  have hxLower : N ≤ x :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).1
  have hNU : N ≤ a * x := by
    calc
      N ≤ x := hxLower
      _ = 1 * x := by omega
      _ ≤ a * x := Nat.mul_le_mul_right x ha
  exact (hpoly.trans_le hpowerNat).le.trans hNU

/--
Joint eventual package for the two numerical hypotheses consumed by the
aligned quantitative Runge bridge.
-/
theorem rungeNumerics_eventually
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ H, 1 ≤ H → H ≤ (L + 1) ^ A →
      ∀ t : ℕ,
        (t : ℝ) ≤
          D * (L + 1 : ℕ) /
            (Real.log (L + 1 : ℕ) *
              Real.log (Real.log (L + 1 : ℕ))) →
      ∀ a : ℕ, 1 ≤ a → ∀ x : ℕ, x ∈ dyadicBlock N →
        (∀ k : ℕ, 1 ≤ k → k ≤ 43 * t →
          (128 * (2 * k) * (3 * H * (L + 1))) ^ (4 * k) <
            a * x) ∧
          2 * (3 * H * (L + 1)) ≤ a * x := by
  obtain ⟨Ngrowth, hgrowth⟩ :=
    rungeScale_lt_eventually hC hD A
  obtain ⟨Ntranslation, htranslation⟩ :=
    translationRange_eventually hC A
  refine ⟨max Ngrowth Ntranslation, ?_⟩
  intro N hN L hrun H hH hHupper t ht a ha x hx
  have hNgrowth : Ngrowth ≤ N :=
    (le_max_left _ _).trans hN
  have hNtranslation : Ntranslation ≤ N :=
    (le_max_right _ _).trans hN
  constructor
  · intro k hk hkt
    exact
      hgrowth N hNgrowth L hrun H hH hHupper t ht
        k hk hkt a ha x hx
  · exact
      htranslation N hNtranslation L hrun
        H hH hHupper a ha x hx

end AlignedRungeGrowth
end PaperC
