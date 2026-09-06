import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert

/-!
# The upper exponential saddle branch

The function exp(u)/u is inverted on [1,infinity). The lower branch is never
used. The definition below has value 1 below exp(1); all mathematical endpoints
state the relevant domain explicitly.
-/

namespace PaperC.V282.SaddleBranch

open Set Filter Topology

noncomputable section

def saddleRatio (u : ℝ) : ℝ := Real.exp u / u

theorem hasDerivAt_saddleRatio {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt saddleRatio (Real.exp u * (u - 1) / u ^ 2) u := by
  change HasDerivAt (fun t : ℝ => Real.exp t / t) _ u
  exact ((Real.hasDerivAt_exp u).div (hasDerivAt_id u) hu).congr_deriv (by simp only [id_eq]; ring)

theorem continuousOn_saddleRatio :
    ContinuousOn saddleRatio (Ici 1) := by
  intro u hu
  exact (hasDerivAt_saddleRatio (by linarith [show 1 ≤ u from hu])).continuousAt.continuousWithinAt

theorem strictMonoOn_saddleRatio :
    StrictMonoOn saddleRatio (Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) continuousOn_saddleRatio
  intro u hu
  have huone : 1 < u := by simpa only [interior_Ici, mem_Ioi] using hu
  rw [(hasDerivAt_saddleRatio (by linarith)).deriv]
  exact div_pos (mul_pos (Real.exp_pos _) (by linarith)) (sq_pos_of_pos (by linarith))

theorem tendsto_saddleRatio_atTop :
    Tendsto saddleRatio atTop atTop := by
  change Tendsto (fun u : ℝ => Real.exp u / u) atTop atTop
  simpa only [pow_one] using Real.tendsto_exp_div_pow_atTop 1

theorem existsUnique_saddleRatio {nu : ℝ} (hnu : Real.exp 1 ≤ nu) :
    ∃! u : ℝ, 1 ≤ u ∧ saddleRatio u = nu := by
  obtain ⟨u, hu, heq⟩ := intermediate_value_Ici continuousOn_saddleRatio
    tendsto_saddleRatio_atTop (show nu ∈ Ici (saddleRatio 1) by simpa [saddleRatio] using hnu)
  refine ⟨u, ⟨hu, heq⟩, ?_⟩
  intro v hv
  exact strictMonoOn_saddleRatio.injOn hv.1 hu (hv.2.trans heq.symm)

def upperSaddleBranch (nu : ℝ) : ℝ :=
  if hnu : Real.exp 1 ≤ nu then Classical.choose (existsUnique_saddleRatio hnu) else 1

theorem upperSaddleBranch_spec {nu : ℝ} (hnu : Real.exp 1 ≤ nu) :
    1 ≤ upperSaddleBranch nu ∧ saddleRatio (upperSaddleBranch nu) = nu := by
  rw [upperSaddleBranch, dif_pos hnu]
  exact (Classical.choose_spec (existsUnique_saddleRatio hnu)).1

theorem upperSaddleBranch_eq_of_spec {nu u : ℝ} (hu : 1 ≤ u)
    (heq : saddleRatio u = nu) :
    upperSaddleBranch nu = u := by
  have hnu : Real.exp 1 ≤ nu := by
    have hh := strictMonoOn_saddleRatio.monotoneOn
      (show (1 : ℝ) ∈ Ici 1 by simp) hu hu
    rw [heq] at hh
    simpa only [saddleRatio, div_one] using hh
  exact strictMonoOn_saddleRatio.injOn (upperSaddleBranch_spec hnu).1 hu
    ((upperSaddleBranch_spec hnu).2.trans heq.symm)

theorem upperSaddleBranch_saddleRatio {u : ℝ} (hu : 1 ≤ u) :
    upperSaddleBranch (saddleRatio u) = u :=
  upperSaddleBranch_eq_of_spec hu rfl

theorem upperSaddleBranch_exp_one : upperSaddleBranch (Real.exp 1) = 1 := by
  exact upperSaddleBranch_eq_of_spec (by norm_num) (by simp [saddleRatio])

theorem upperSaddleBranch_pos {nu : ℝ} (hnu : Real.exp 1 ≤ nu) :
    0 < upperSaddleBranch nu := by
  linarith [(upperSaddleBranch_spec hnu).1]

theorem saddleRatio_le_iff {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    saddleRatio u ≤ saddleRatio v ↔ u ≤ v :=
  strictMonoOn_saddleRatio.le_iff_le hu hv

theorem le_upperSaddleBranch_iff {nu u : ℝ} (hnu : Real.exp 1 ≤ nu) (hu : 1 ≤ u) :
    u ≤ upperSaddleBranch nu ↔ saddleRatio u ≤ nu := by
  simpa only [(upperSaddleBranch_spec hnu).2] using
    (saddleRatio_le_iff hu (upperSaddleBranch_spec hnu).1).symm

theorem strictMonoOn_upperSaddleBranch :
    StrictMonoOn upperSaddleBranch (Ici (Real.exp 1)) := by
  intro nu hnu mu hmu hlt
  apply (strictMonoOn_saddleRatio.lt_iff_lt
    (upperSaddleBranch_spec hnu).1 (upperSaddleBranch_spec hmu).1).1
  simpa [(upperSaddleBranch_spec hnu).2, (upperSaddleBranch_spec hmu).2] using hlt

theorem tendsto_upperSaddleBranch_atTop :
    Tendsto upperSaddleBranch atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (max (Real.exp 1) (saddleRatio (max 1 b)))] with nu hnu
  have hdomain : Real.exp 1 ≤ nu := (le_max_left _ _).trans hnu
  exact (le_max_right 1 b).trans
    ((le_upperSaddleBranch_iff hdomain (le_max_left 1 b)).2 ((le_max_right _ _).trans hnu))

theorem exp_upperSaddleBranch {nu : ℝ} (hnu : Real.exp 1 ≤ nu) :
    Real.exp (upperSaddleBranch nu) = nu * upperSaddleBranch nu := by
  exact (div_eq_iff (ne_of_gt (upperSaddleBranch_pos hnu))).1
    (upperSaddleBranch_spec hnu).2

theorem log_saddleRatio {u : ℝ} (hu : 0 < u) :
    Real.log (saddleRatio u) = u - Real.log u := by
  rw [saddleRatio, Real.log_div (Real.exp_ne_zero _) (ne_of_gt hu), Real.log_exp]

theorem log_upperSaddleBranch_identity {nu : ℝ} (hnu : Real.exp 1 ≤ nu) :
    Real.log nu = upperSaddleBranch nu - Real.log (upperSaddleBranch nu) := by
  calc
    Real.log nu = Real.log (saddleRatio (upperSaddleBranch nu)) :=
      congrArg Real.log (upperSaddleBranch_spec hnu).2.symm
    _ = _ := log_saddleRatio (upperSaddleBranch_pos hnu)

end

end PaperC.V282.SaddleBranch
