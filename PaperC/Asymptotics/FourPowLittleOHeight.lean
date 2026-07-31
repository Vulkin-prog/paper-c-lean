import PaperC.Asymptotics.ExpSqrtLog

/-!
# Exponentiating a little-oh height loss

Proposition 7.4 produces a natural-valued exponent `m(N,L)` which is
uniformly `o(H)` while the critical height `H` is `O(log N)`.  This file
packages the elementary implication

`m = o(H)` and `H ≤ D log N`  `⇒`  `4^m = N^o(1)`

with the quantifier order used throughout Paper C.
-/

namespace PaperC
namespace FourPowLittleOHeight

/--
If a natural-valued exponent is uniformly little-oh of a nonnegative height,
and that height is eventually bounded by a fixed multiple of `log N`, then
`4` to that exponent is uniformly subpolynomial.
-/
theorem uniformSubpolynomialOn_four_pow_of_uniformLittleO_height
    {admissible : ℕ → ℕ → Prop}
    (m : ℕ → ℕ → ℕ)
    (H : ℕ → ℕ → ℝ)
    (D : ℝ) (hD : 0 ≤ D)
    (hm :
      UniformLittleOOn admissible
        (fun N L => (m N L : ℝ)) H)
    (hHnonneg :
      ∀ N L, admissible N L → 0 ≤ H N L)
    (hHlog :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        H N L ≤ D * Real.log N) :
    UniformSubpolynomialOn admissible
      (fun N L => (((4 ^ m N L : ℕ) : ℝ))) := by
  intro k hk
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hDplus : 0 < D + 1 := by linarith
  have hlogFour : 0 < Real.log (4 : ℝ) :=
    Real.log_pos (by norm_num)
  let ε : ℝ :=
    1 / ((k : ℝ) * (D + 1) * Real.log 4)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨Nlittle, hNlittle⟩ := hm ε hε
  obtain ⟨Nheight, hNheight⟩ := hHlog
  refine ⟨max 2 (max Nlittle Nheight), ?_⟩
  intro N hN L hNL
  have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
  have hNtail : max Nlittle Nheight ≤ N :=
    (le_max_right _ _).trans hN
  have hmBound :=
    hNlittle N ((le_max_left _ _).trans hNtail) L hNL
  have hheight :=
    hNheight N ((le_max_right _ _).trans hNtail) L hNL
  have hHnonneg' : 0 ≤ H N L := hHnonneg N L hNL
  have hmNonneg : 0 ≤ (m N L : ℝ) := by positivity
  have hmLe :
      (m N L : ℝ) ≤ ε * H N L := by
    simpa only [abs_of_nonneg hmNonneg, abs_of_nonneg hHnonneg'] using
      hmBound
  have hlogN : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast hNtwo)
  have hscaled :
      (k : ℝ) * (m N L : ℝ) * Real.log 4 ≤
        Real.log N := by
    calc
      (k : ℝ) * (m N L : ℝ) * Real.log 4 ≤
          (k : ℝ) * (ε * H N L) * Real.log 4 := by
        apply mul_le_mul_of_nonneg_right _ hlogFour.le
        exact mul_le_mul_of_nonneg_left hmLe hkReal.le
      _ ≤
          (k : ℝ) * (ε * (D * Real.log N)) *
            Real.log 4 := by
        apply mul_le_mul_of_nonneg_right _ hlogFour.le
        apply mul_le_mul_of_nonneg_left _ hkReal.le
        exact mul_le_mul_of_nonneg_left hheight hε.le
      _ = (D / (D + 1)) * Real.log N := by
        dsimp [ε]
        field_simp
      _ ≤ 1 * Real.log N := by
        apply mul_le_mul_of_nonneg_right _ hlogN.le
        exact (div_le_one hDplus).2 (by linarith)
      _ = Real.log N := one_mul _
  have hfour :
      (((4 ^ m N L : ℕ) : ℝ)) =
        Real.exp ((m N L : ℝ) * Real.log 4) := by
    calc
      (((4 ^ m N L : ℕ) : ℝ)) =
          (4 : ℝ) ^ m N L := by norm_num
      _ = (Real.exp (Real.log 4)) ^ m N L := by
        rw [Real.exp_log]
        norm_num
      _ = Real.exp ((m N L : ℝ) * Real.log 4) :=
        (Real.exp_nat_mul (Real.log 4) (m N L)).symm
  have hNpos : 0 < (N : ℝ) := by positivity
  have hbaseNonneg :
      0 ≤ (((4 ^ m N L : ℕ) : ℝ)) := by positivity
  rw [abs_of_nonneg hbaseNonneg, hfour, ← Real.exp_nat_mul]
  calc
    Real.exp ((k : ℝ) *
        ((m N L : ℝ) * Real.log 4))
        ≤ Real.exp (Real.log N) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hscaled]
    _ = (N : ℝ) := Real.exp_log hNpos

end FourPowLittleOHeight
end PaperC
