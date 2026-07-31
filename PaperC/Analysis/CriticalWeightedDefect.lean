import PaperC.Analysis.CriticalWindowParameters
import PaperC.Analysis.CriticalWindowScale
import PaperC.Analysis.DefectPointwiseRate
import PaperC.Asymptotics.CappedRadiusDyadic
import PaperC.Asymptotics.ExpSqrtLog
import PaperC.Asymptotics.HalfPower

/-!
# Uniform form of the weighted defect estimate

This module packages the canonical sum over `N ≤ u < 2N`, then converts its
finite bound into the fully quantified meaning of `N^(1/2+o(1))`.
-/

namespace PaperC
namespace CriticalWeightedDefect

open scoped BigOperators

/-- The exact weighted sum appearing on the left of equation (3.4). -/
noncomputable def dyadicDefectMass (N H : ℕ) : ℕ :=
  let defects :=
    WeightedDefectCounting.positiveDefectValues
      (DefectCounting.smallPrimesUpTo H) (3 * N)
  ∑ u ∈ Finset.Ico N (2 * N),
    (2 ^ IntervalDefectAggregation.localCount defects H u - 1)

/--
The critical window together with the three explicit finite thresholds
isolated by `CriticalWindowParameters`.
-/
def Admissible (c₁ c₂ : ℝ) (N H : ℕ) : Prop :=
  CriticalWindowParameters.InCriticalWindow c₁ c₂ N H ∧
    2 ≤ N ∧
    (4 : ℝ) ≤ c₁ * Real.log N ∧
    2 * c₂ * Real.log N ≤ (N : ℝ) ∧
    (CriticalWindowParameters.requiredRadius H
          (CriticalWindowParameters.codingConstant c₁ c₂) : ℝ) *
        (8 * Real.log
          (256 * CriticalWindowParameters.logarithmicCap N * H)) ≤
      Real.log N

/-- The complete factor left after extracting `sqrt N` from the finite bound. -/
noncomputable def residualFactor
    (c₁ c₂ : ℝ) (N H : ℕ) : ℝ :=
  let A := CriticalWindowParameters.codingConstant c₁ c₂
  let T := CriticalWindowParameters.logarithmicCap N
  let t := RungeLogarithmicGrowth.cappedRadius N H T
  (H + 1 : ℝ) * Real.sqrt 3 *
    Real.exp (2 * Real.sqrt H) *
    ((2 ^ (2 * t * 2 ^ (A + 1)) : ℕ) : ℝ)

/-- Canonical finite specialization of the weighted defect-mass theorem. -/
theorem dyadicDefectMass_cast_le
    {c₁ c₂ : ℝ} {N H : ℕ}
    (h : Admissible c₁ c₂ N H) :
    (dyadicDefectMass N H : ℝ) ≤
      (H + 1 : ℝ) * Real.sqrt ((3 * N : ℕ) : ℝ) *
        Real.exp (2 * Real.sqrt H) *
        ((2 ^ (2 *
          RungeLogarithmicGrowth.cappedRadius N H
            (CriticalWindowParameters.logarithmicCap N) *
          2 ^ (CriticalWindowParameters.codingConstant c₁ c₂ + 1)) :
            ℕ) : ℝ) := by
  rcases h with ⟨hwindow, hN, hfour, htranslation, hscale⟩
  have hfinite :=
    CriticalWindowParameters.sum_two_pow_localCount_sub_one_cast_le_of_criticalWindow
        (c₁ := c₁) (c₂ := c₂) (N := N) (H := H) (X := 3 * N)
        (Finset.Ico N (2 * N)) hwindow hN hfour htranslation
        (by
          intro u hu
          exact (Finset.mem_Ico.mp hu).1)
        (by
          intro u hu
          have huUpper : u < 2 * N := (Finset.mem_Ico.mp hu).2
          have htwoH : 2 * H ≤ N :=
            CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
              hwindow htranslation
          omega)
        hscale
  simpa only [dyadicDefectMass] using hfinite

/-- The residual factor is nonnegative. -/
theorem residualFactor_nonneg
    (c₁ c₂ : ℝ) (N H : ℕ) :
    0 ≤ residualFactor c₁ c₂ N H := by
  unfold residualFactor
  positivity

/--
In every fixed critical window, admissible heights tend uniformly to
infinity.  This is the exact hypothesis consumed by the capped-radius
dyadic-loss theorem.
-/
theorem height_tends_to_infinity
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) :
    ∀ M : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H,
      Admissible c₁ c₂ N H → M ≤ H := by
  intro M
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (Real.exp ((M : ℝ) / c₁))
  refine ⟨N₀, ?_⟩
  intro N hN H hAdm
  have hthreshold :
      Real.exp ((M : ℝ) / c₁) < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hlog :
      (M : ℝ) / c₁ < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos _) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hM :
      (M : ℝ) < c₁ * Real.log N := by
    calc
      (M : ℝ) < Real.log N * c₁ := (div_lt_iff₀ hc₁).mp hlog
      _ = c₁ * Real.log N := by ring
  exact_mod_cast hM.le.trans hAdm.1.2.2.1

/-- The full residual factor is uniformly `N^{o(1)}`. -/
theorem residualFactor_uniformSubpolynomial
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    UniformSubpolynomialOn (Admissible c₁ c₂)
      (residualFactor c₁ c₂) := by
  let A := CriticalWindowParameters.codingConstant c₁ c₂
  let T : ℕ → ℕ → ℕ :=
    fun N _ => CriticalWindowParameters.logarithmicCap N
  let D : ℕ := 2 * 2 ^ (A + 1)
  have hc₂ : 0 ≤ c₂ := (hc₁.trans hc₁c₂).le
  have hheight :
      ∀ N H, Admissible c₁ c₂ N H →
        (H : ℝ) ≤ c₂ * Real.log N := by
    intro N H h
    exact h.1.2.2.2
  have hlinear :
      UniformSubpolynomialOn (Admissible c₁ c₂)
        (fun _ H => (H + 1 : ℝ)) :=
    ExpSqrtLog.uniformSubpolynomialOn_linear_log_add_one
      (Admissible c₁ c₂) (fun _ H => H) c₂ hc₂ hheight
  have hexponential :
      UniformSubpolynomialOn (Admissible c₁ c₂)
        (fun _ H => Real.exp (2 * Real.sqrt H)) :=
    ExpSqrtLog.uniformSubpolynomialOn_exp_sqrt_of_le_log
      (Admissible c₁ c₂) (fun _ H => H) 2 c₂
      (by norm_num) hc₂ hheight
  have hT :
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H,
        Admissible c₁ c₂ N H → 1 ≤ T N H := by
    refine ⟨0, ?_⟩
    intro N _ H h
    exact CriticalWindowParameters.one_le_logarithmicCap h.2.1
  have hbinaryD :
      UniformSubpolynomialOn (Admissible c₁ c₂)
        (fun N H =>
          ((2 ^ (D *
            RungeLogarithmicGrowth.cappedRadius N H (T N H)) : ℕ) :
              ℝ)) :=
    CappedRadiusDyadic.uniformSubpolynomialOn_two_cappedRadius
      (Admissible c₁ c₂) T D hT (height_tends_to_infinity hc₁)
  have hbinary :
      UniformSubpolynomialOn (Admissible c₁ c₂)
        (fun N H =>
          ((2 ^ (2 *
            RungeLogarithmicGrowth.cappedRadius N H
              (CriticalWindowParameters.logarithmicCap N) *
            2 ^ (CriticalWindowParameters.codingConstant c₁ c₂ + 1)) :
              ℕ) : ℝ)) := by
    simpa [A, T, D, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      hbinaryD
  have hconst :
      UniformSubpolynomialOn (Admissible c₁ c₂)
        (fun _ _ => Real.sqrt 3) :=
    ExpSqrtLog.uniformSubpolynomialOn_const
      (Admissible c₁ c₂) (Real.sqrt 3)
  have hproduct :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      (ExpSqrtLog.uniformSubpolynomialOn_mul
        (ExpSqrtLog.uniformSubpolynomialOn_mul hlinear hconst)
        hexponential)
      hbinary
  simpa only [residualFactor] using hproduct

/--
Fully quantified form of equation (3.4):
the canonical weighted defect mass is `N^(1/2+o(1))`, uniformly over all
heights satisfying the explicit critical-window thresholds.
-/
theorem dyadicDefectMass_uniformHalfPower
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    UniformHalfPowerSubpolynomialOn (Admissible c₁ c₂)
      (fun N H => (dyadicDefectMass N H : ℝ)) := by
  apply UniformHalfPower.of_sqrt_mul_subpolynomial
    (residualFactor_uniformSubpolynomial hc₁ hc₁c₂)
  refine ⟨0, ?_⟩
  intro N _ H h
  rw [abs_of_nonneg (by positivity),
    abs_of_nonneg (residualFactor_nonneg c₁ c₂ N H)]
  have hfinite := dyadicDefectMass_cast_le h
  calc
    (dyadicDefectMass N H : ℝ) ≤
        (H + 1 : ℝ) * Real.sqrt ((3 * N : ℕ) : ℝ) *
          Real.exp (2 * Real.sqrt H) *
          ((2 ^ (2 *
            RungeLogarithmicGrowth.cappedRadius N H
              (CriticalWindowParameters.logarithmicCap N) *
            2 ^ (CriticalWindowParameters.codingConstant c₁ c₂ + 1)) :
              ℕ) : ℝ) := hfinite
    _ = Real.sqrt N * residualFactor c₁ c₂ N H := by
      unfold residualFactor
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      ring

/--
Eventually, the lower edge `c₁ log N ≤ H` of the critical window implies
`log log N ≤ 8 log H`.  The generous factor `8` avoids any hidden
asymptotic equivalence.
-/
theorem eventually_loglog_le_eight_log_height
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H,
      Admissible c₁ c₂ N H →
        0 < Real.log (Real.log N) ∧
        Real.log (Real.log N) ≤ 8 * Real.log H := by
  let R : ℝ := max 1 ((1 / c₁) ^ 2)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp R)
  refine ⟨N₀, ?_⟩
  intro N hN H hAdm
  have hthreshold : Real.exp R < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hRlog : R < Real.log N := by
    have hlogs := Real.log_lt_log (Real.exp_pos R) hthreshold
    simpa only [Real.log_exp] using hlogs
  have honeLog : (1 : ℝ) < Real.log N :=
    (le_max_left 1 ((1 / c₁) ^ 2)).trans_lt hRlog
  have hloglog : 0 < Real.log (Real.log N) :=
    Real.log_pos honeLog
  have hrecipSq :
      (1 / c₁) ^ 2 < Real.log N :=
    (le_max_right 1 ((1 / c₁) ^ 2)).trans_lt hRlog
  have hrecipPos : 0 < 1 / c₁ := one_div_pos.mpr hc₁
  have hrecipSqrt :
      1 / c₁ < Real.sqrt (Real.log N) := by
    have hsqrt :=
      Real.sqrt_lt_sqrt (sq_nonneg (1 / c₁)) hrecipSq
    simpa only [Real.sqrt_sq hrecipPos.le] using hsqrt
  have hsqrtNonneg : 0 ≤ Real.sqrt (Real.log N) :=
    Real.sqrt_nonneg _
  have hlogNonneg : 0 ≤ Real.log N := by linarith
  have hsqrtSq :
      (Real.sqrt (Real.log N)) ^ 2 = Real.log N :=
    Real.sq_sqrt hlogNonneg
  have hsqrtLe :
      Real.sqrt (Real.log N) ≤ c₁ * Real.log N := by
    have hone :
        1 < c₁ * Real.sqrt (Real.log N) := by
      calc
        (1 : ℝ) = (1 / c₁) * c₁ := by field_simp
        _ < Real.sqrt (Real.log N) * c₁ :=
          mul_lt_mul_of_pos_right hrecipSqrt hc₁
        _ = c₁ * Real.sqrt (Real.log N) := by ring
    nlinarith
  have hsqrtH :
      Real.sqrt (Real.log N) ≤ (H : ℝ) :=
    hsqrtLe.trans hAdm.1.2.2.1
  have hsqrtPos : 0 < Real.sqrt (Real.log N) := by positivity
  have hlogMono :
      Real.log (Real.sqrt (Real.log N)) ≤ Real.log H :=
    Real.log_le_log hsqrtPos hsqrtH
  have hhalf :
      Real.log (Real.log N) / 2 ≤ Real.log H := by
    simpa only [Real.log_sqrt hlogNonneg] using hlogMono
  exact ⟨hloglog, by nlinarith⟩

/--
Pointwise part of Proposition 3.2 at the canonical interval `[N,N+H]`,
in the explicit uniform-big-O predicate:

`m_H(N) = O_{c₁,c₂}(log N / log log N)`.
-/
theorem pointwise_uniformBigO
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (_hc₁c₂ : c₁ < c₂) :
    UniformBigOOn (Admissible c₁ c₂)
      (fun N H =>
        ((IntervalDefectBound.defectsInInterval H N).card : ℝ))
      (fun N _ => Real.log N / Real.log (Real.log N)) := by
  let C : ℝ :=
    ((2 * 2 ^
      (CriticalWindowParameters.codingConstant c₁ c₂ + 1) : ℕ) : ℝ)
  obtain ⟨Nlog, hNlog⟩ :=
    eventually_loglog_le_eight_log_height (c₂ := c₂) hc₁
  refine ⟨C, by dsimp [C]; positivity, Nlog, ?_⟩
  intro N hN H hAdm
  obtain ⟨hloglog, hcompare⟩ := hNlog N hN H hAdm
  rcases hAdm with
    ⟨hwindow, hNtwo, hfour, htranslation, hscale⟩
  obtain ⟨hHfour, hT, ht, htT, hbudget⟩ :=
    CriticalWindowParameters.cappedRadius_conditions_of_criticalWindow
      hwindow hNtwo hfour hscale
  have hcard :=
    DefectPointwiseRate.card_defectsInInterval_cast_lt_log_div
      hHfour
      (CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
        hwindow htranslation)
      hT ht htT hbudget
  have hlogNpos : 0 < Real.log N := by
    by_contra h
    have hnonpos : Real.log N ≤ 0 := le_of_not_gt h
    nlinarith [hc₁]
  have hlogHpos : 0 < Real.log H := by
    apply Real.log_pos
    exact_mod_cast (show 1 < H by omega)
  have hquot :
      Real.log N / (8 * Real.log H) ≤
        Real.log N / Real.log (Real.log N) := by
    apply (div_le_div_iff₀ (by positivity) hloglog).2
    exact mul_le_mul_of_nonneg_left hcompare hlogNpos.le
  rw [abs_of_nonneg (by positivity), abs_of_pos
    (div_pos hlogNpos hloglog)]
  exact hcard.le.trans
    (mul_le_mul_of_nonneg_left hquot (by positivity))

/--
All three explicit finite thresholds are automatic eventually in the
critical window.  This is the bridge which removes the technical predicate
`Admissible` from the final statement of Proposition 3.2.
-/
theorem admissible_eventually
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H,
      CriticalWindowParameters.InCriticalWindow c₁ c₂ N H →
        Admissible c₁ c₂ N H := by
  obtain ⟨Nscale, hscale⟩ :=
    CriticalWindowScale.scaled_log_le_eventually hc₁ hc₁c₂
  let R : ℝ := max 1 (max (4 / c₁) (8 * c₂))
  obtain ⟨Nbasic, hNbasic0⟩ := exists_nat_gt (Real.exp R)
  refine ⟨max Nscale Nbasic, ?_⟩
  intro N hN H hwindow
  have hNscale : Nscale ≤ N := (le_max_left _ _).trans hN
  have hNbasicN : Nbasic ≤ N := (le_max_right _ _).trans hN
  have hthreshold : Real.exp R < (N : ℝ) :=
    hNbasic0.trans_le (by exact_mod_cast hNbasicN)
  have hRlog : R < Real.log N := by
    have hlogs := Real.log_lt_log (Real.exp_pos R) hthreshold
    simpa only [Real.log_exp] using hlogs
  have honeLog : (1 : ℝ) < Real.log N :=
    (le_max_left 1 (max (4 / c₁) (8 * c₂))).trans_lt hRlog
  have hNtwo : 2 ≤ N := by
    have hNoneReal : (1 : ℝ) < (N : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg N)).mp
        (zero_lt_one.trans honeLog)
    exact_mod_cast hNoneReal
  have hfour :
      (4 : ℝ) ≤ c₁ * Real.log N := by
    have hfourLog :
        4 / c₁ < Real.log N :=
      (le_trans (le_max_left (4 / c₁) (8 * c₂))
        (le_max_right 1 (max (4 / c₁) (8 * c₂)))).trans_lt hRlog
    have := (div_lt_iff₀ hc₁).mp hfourLog
    nlinarith
  have hc₂ : 0 < c₂ := hc₁.trans hc₁c₂
  have heightexp :
      8 * c₂ < Real.log N :=
    (le_trans (le_max_right (4 / c₁) (8 * c₂))
      (le_max_right 1 (max (4 / c₁) (8 * c₂)))).trans_lt hRlog
  have hlogNpos : 0 < Real.log N := zero_lt_one.trans honeLog
  have hadd :
      1 + Real.log N / 2 ≤ Real.exp (Real.log N / 2) :=
    by simpa [add_comm] using
      Real.add_one_le_exp (Real.log N / 2)
  have hsquare :
      (1 + Real.log N / 2) ^ 2 ≤
        (Real.exp (Real.log N / 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hadd 2
  have hquad :
      (Real.log N) ^ 2 / 4 ≤ Real.exp (Real.log N) := by
    calc
      (Real.log N) ^ 2 / 4 ≤ (1 + Real.log N / 2) ^ 2 := by
        nlinarith
      _ ≤ (Real.exp (Real.log N / 2)) ^ 2 := hsquare
      _ = Real.exp (Real.log N) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have htranslation :
      2 * c₂ * Real.log N ≤ (N : ℝ) := by
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast
      (show 0 < N by omega)
    calc
      2 * c₂ * Real.log N ≤ (Real.log N) ^ 2 / 4 := by
        nlinarith
      _ ≤ Real.exp (Real.log N) := hquad
      _ = (N : ℝ) := Real.exp_log hNpos
  exact
    ⟨hwindow, hNtwo, hfour, htranslation,
      hscale N hNscale H hwindow⟩

/--
Equation (3.4) with exactly the manuscript's critical-window predicate:
the additional finite thresholds have been eliminated uniformly.
-/
theorem dyadicDefectMass_uniformHalfPower_on_window
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    UniformHalfPowerSubpolynomialOn
      (CriticalWindowParameters.InCriticalWindow c₁ c₂)
      (fun N H => (dyadicDefectMass N H : ℝ)) := by
  have hmass := dyadicDefectMass_uniformHalfPower hc₁ hc₁c₂
  obtain ⟨Nadm, hNadm⟩ := admissible_eventually hc₁ hc₁c₂
  intro k hk
  obtain ⟨Nmass, hNmass⟩ := hmass k hk
  refine ⟨max Nadm Nmass, ?_⟩
  intro N hN H hwindow
  exact
    hNmass N ((le_max_right _ _).trans hN) H
      (hNadm N ((le_max_left _ _).trans hN) H hwindow)

/--
The pointwise `O(log N / log log N)` estimate with exactly the manuscript's
critical-window predicate.
-/
theorem pointwise_uniformBigO_on_window
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    UniformBigOOn
      (CriticalWindowParameters.InCriticalWindow c₁ c₂)
      (fun N H =>
        ((IntervalDefectBound.defectsInInterval H N).card : ℝ))
      (fun N _ => Real.log N / Real.log (Real.log N)) := by
  obtain ⟨K, hK, Npoint, hpoint⟩ :=
    pointwise_uniformBigO hc₁ hc₁c₂
  obtain ⟨Nadm, hNadm⟩ := admissible_eventually hc₁ hc₁c₂
  refine ⟨K, hK, max Nadm Npoint, ?_⟩
  intro N hN H hwindow
  exact
    hpoint N ((le_max_right _ _).trans hN) H
      (hNadm N ((le_max_left _ _).trans hN) H hwindow)

end CriticalWeightedDefect
end PaperC
