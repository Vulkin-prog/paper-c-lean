import PaperC.Asymptotics.SectionThirteenRate

set_option maxHeartbeats 1800000

/-!
# Asymptotic scale comparison tools

This module records the generic transitivity lemmas used to pass from a
quantitative big-O estimate to a qualitative little-o estimate.  In
particular, both `N²/(log log N)²` and the positive Corollary 11.3
exponential scale are uniformly little-o of `N²`.  These are derived
analytic comparisons and introduce no bridge proposition.
-/

namespace PaperC
namespace NonterminalSectorSaving

open PropositionElevenThree
open PropositionElevenTwo
open SectionThirteenRate

noncomputable section

/-! ## Asymptotic calculus -/

/--
A uniform big-O estimate followed by a uniform little-o estimate is a
uniform little-o estimate.  All thresholds remain uniform in the auxiliary
parameter.
-/
theorem uniformBigOOn_trans_uniformLittleOOn
    {admissible : ℕ → ℕ → Prop}
    {f g h : ℕ → ℕ → ℝ}
    (hfg : UniformBigOOn admissible f g)
    (hgh : UniformLittleOOn admissible g h) :
    UniformLittleOOn admissible f h := by
  obtain ⟨K, hK, Nf, hf⟩ := hfg
  intro ε hε
  let δ : ℝ := ε / (K + 1)
  have hKone : 0 < K + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact div_pos hε hKone
  obtain ⟨Ng, hg⟩ := hgh δ hδ
  refine ⟨max Nf Ng, ?_⟩
  intro N hN L hNL
  have hNf : Nf ≤ N := (le_max_left Nf Ng).trans hN
  have hNg : Ng ≤ N := (le_max_right Nf Ng).trans hN
  have hKdiv : K / (K + 1) ≤ 1 :=
    (div_le_one hKone).2 (by linarith)
  have hKδ : K * δ ≤ ε := by
    dsimp only [δ]
    calc
      K * (ε / (K + 1)) =
          (K / (K + 1)) * ε := by ring
      _ ≤ 1 * ε :=
        mul_le_mul_of_nonneg_right hKdiv hε.le
      _ = ε := one_mul ε
  calc
    |f N L| ≤ K * |g N L| := hf N hNf L hNL
    _ ≤ K * (δ * |h N L|) :=
      mul_le_mul_of_nonneg_left (hg N hNg L hNL) hK
    _ = (K * δ) * |h N L| := by ring
    _ ≤ ε * |h N L| :=
      mul_le_mul_of_nonneg_right hKδ (abs_nonneg (h N L))

/--
The intermediate scale `N²/(log log N)²` is uniformly little-o of `N²`.
The admissibility predicate is arbitrary because the comparison is
pointwise once `N` is beyond the threshold.
-/
theorem quadraticDivLogLogSquaredScale_uniformLittleO_quadratic
    (admissible : ℕ → ℕ → Prop) :
    UniformLittleOOn admissible
      quadraticDivLogLogSquaredScale
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt
      (Real.exp (Real.exp (1 / ε + 1)))
  refine ⟨N₀, ?_⟩
  intro N hN L _hNL
  let b : ℝ := Real.log (Real.log N)
  have hthreshold :
      Real.exp (Real.exp (1 / ε + 1)) < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hexponent : 0 < 1 / ε + 1 := by
    positivity
  have hlogN :
      Real.exp (1 / ε + 1) < Real.log N := by
    have hlogs :=
      Real.log_lt_log
        (Real.exp_pos (Real.exp (1 / ε + 1)))
        hthreshold
    simpa only [Real.log_exp] using hlogs
  have hbLower : 1 / ε + 1 < b := by
    have hlogs :=
      Real.log_lt_log
        (Real.exp_pos (1 / ε + 1))
        hlogN
    simpa only [b, Real.log_exp] using hlogs
  have hbPos : 0 < b := by
    linarith
  have hbOne : 1 ≤ b := by
    have : 0 < 1 / ε := one_div_pos.mpr hε
    linarith
  have hInvLt : 1 / ε < b := by
    linarith
  have hbLeSq : b ≤ b ^ 2 := by
    nlinarith [sq_nonneg (b - 1)]
  have hInvSq : 1 / ε < b ^ 2 :=
    hInvLt.trans_le hbLeSq
  have hcoeff : 1 ≤ ε * b ^ 2 := by
    have hstrict : 1 < b ^ 2 * ε :=
      (div_lt_iff₀ hε).mp hInvSq
    nlinarith
  have hbSqPos : 0 < b ^ 2 := pow_pos hbPos 2
  have hNnonneg : 0 ≤ (N : ℝ) ^ 2 := by positivity
  have hscaleNonneg :
      0 ≤ quadraticDivLogLogSquaredScale N L := by
    unfold quadraticDivLogLogSquaredScale
    positivity
  rw [abs_of_nonneg hscaleNonneg, abs_of_nonneg hNnonneg]
  change (N : ℝ) ^ 2 / b ^ 2 ≤ ε * (N : ℝ) ^ 2
  apply (div_le_iff₀ hbSqPos).2
  calc
    (N : ℝ) ^ 2 =
        (N : ℝ) ^ 2 * 1 := by ring
    _ ≤ (N : ℝ) ^ 2 * (ε * b ^ 2) :=
      mul_le_mul_of_nonneg_left hcoeff hNnonneg
    _ = (ε * (N : ℝ) ^ 2) * b ^ 2 := by ring

/--
For every positive `c`, the explicit exponential scale is uniformly
little-o of the quadratic scale.
-/
theorem quantitativeHomogeneousScale_uniformLittleO_quadratic
    {admissible : ℕ → ℕ → Prop}
    {c : ℝ} (hc : 0 < c) :
    UniformLittleOOn admissible
      (quantitativeHomogeneousScale c)
      (fun N _ ↦ (N : ℝ) ^ 2) :=
  uniformBigOOn_trans_uniformLittleOOn
    (quantitativeHomogeneousScale_uniformBigO_loglogSquared hc)
    (quadraticDivLogLogSquaredScale_uniformLittleO_quadratic
      admissible)

/--
Any estimate at the positive quantitative homogeneous scale implies the
corresponding qualitative quadratic little-o estimate.
-/
theorem uniformBigO_quantitativeHomogeneousScale_implies_littleO_quadratic
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    {c : ℝ} (hc : 0 < c)
    (hf :
      UniformBigOOn admissible f
        (quantitativeHomogeneousScale c)) :
    UniformLittleOOn admissible f
      (fun N _ ↦ (N : ℝ) ^ 2) :=
  uniformBigOOn_trans_uniformLittleOOn hf
    (quantitativeHomogeneousScale_uniformLittleO_quadratic hc)

end

end NonterminalSectorSaving
end PaperC
