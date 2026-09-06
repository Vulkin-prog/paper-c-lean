import PaperCV282.SaddleBranch
import PaperCV282.ExponentialIntegral

/-!
# Existence and uniqueness of the two implicit cutoff scales

A positive scalar a treats both equations V=a D(H/V). The paper uses a=1
and a=2. The threshold is explicit in the fixed scalar and precedes H.
No prime-counting estimate or asymptotic expansion is assumed.
-/

namespace PaperC.V282.SaddleParameters

open Set Filter Topology SaddleBranch ExponentialIntegral

noncomputable section

def saddleCost (nu : ℝ) : ℝ :=
  nu * upperSaddleBranch nu - exponentialIntegral (upperSaddleBranch nu)

theorem saddleCost_eq_param {nu : ℝ} (hnu : Real.exp 1 ≤ nu) :
    saddleCost nu = saddleCostParam (upperSaddleBranch nu) := by
  unfold saddleCost saddleCostParam
  rw [exp_upperSaddleBranch hnu]

theorem saddleCost_saddleRatio {u : ℝ} (hu : 1 ≤ u) :
    saddleCost (saddleRatio u) = saddleCostParam u := by
  unfold saddleCost saddleCostParam
  rw [upperSaddleBranch_saddleRatio hu]
  rw [saddleRatio]
  field_simp [show u ≠ 0 by linarith]

theorem strictMonoOn_saddleCost :
    StrictMonoOn saddleCost (Ici (Real.exp 1)) := by
  intro nu hnu mu hmu hlt
  rw [saddleCost_eq_param hnu, saddleCost_eq_param hmu]
  exact strictMonoOn_saddleCostParam (upperSaddleBranch_spec hnu).1
    (upperSaddleBranch_spec hmu).1 (strictMonoOn_upperSaddleBranch hnu hmu hlt)

theorem tendsto_saddleCost_atTop : Tendsto saddleCost atTop atTop := by
  apply (tendsto_saddleCostParam_atTop.comp tendsto_upperSaddleBranch_atTop).congr'
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with nu hnu
  exact (saddleCost_eq_param hnu).symm

def saddleParameterBase : ℝ := max 2 (3 - saddleCostParam 2)

theorem saddleParameterBase_ge_two : 2 ≤ saddleParameterBase := le_max_left _ _

theorem saddleCostParam_base_ge_one : 1 ≤ saddleCostParam saddleParameterBase := by
  have h := saddleCostParam_linear_lower saddleParameterBase_ge_two
  have hb : 3 - saddleCostParam 2 ≤ saddleParameterBase := le_max_right _ _
  linarith

def saddleHeight (a u : ℝ) : ℝ := a * saddleRatio u * saddleCostParam u

def saddleThreshold (a : ℝ) : ℝ := saddleHeight a saddleParameterBase

theorem saddleHeight_strict {a u v : ℝ} (ha : 0 < a)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hcost : 0 ≤ saddleCostParam u) (huv : u < v) :
    saddleHeight a u < saddleHeight a v := by
  have hf : 0 < saddleRatio u := div_pos (Real.exp_pos _) (by linarith)
  have hg := strictMonoOn_saddleCostParam hu hv huv
  have hgv : 0 ≤ saddleCostParam v := hcost.trans hg.le
  unfold saddleHeight
  calc
    a * saddleRatio u * saddleCostParam u < a * saddleRatio u * saddleCostParam v :=
      mul_lt_mul_of_pos_left hg (mul_pos ha hf)
    _ ≤ a * saddleRatio v * saddleCostParam v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (strictMonoOn_saddleRatio hu hv huv).le ha.le) hgv

theorem strictMonoOn_saddleHeight {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (saddleHeight a) (Ici saddleParameterBase) := by
  intro u hu v hv huv
  have hb : 1 ≤ saddleParameterBase := by linarith [saddleParameterBase_ge_two]
  have hcost := strictMonoOn_saddleCostParam.monotoneOn hb (hb.trans hu) hu
  exact saddleHeight_strict ha (hb.trans hu) (hb.trans hv)
    ((by linarith [saddleCostParam_base_ge_one] : 0 ≤ saddleCostParam saddleParameterBase).trans hcost) huv

theorem continuousOn_saddleHeight (a : ℝ) :
    ContinuousOn (saddleHeight a) (Ici saddleParameterBase) := by
  have hsub : Ici saddleParameterBase ⊆ Ici (1 : ℝ) := by
    intro u hu
    change 1 ≤ u
    linarith [show saddleParameterBase ≤ u from hu, saddleParameterBase_ge_two]
  exact (continuousOn_const.mul (continuousOn_saddleRatio.mono hsub)).mul
    (continuousOn_saddleCostParam.mono hsub)

theorem tendsto_saddleHeight_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (saddleHeight a) atTop atTop := by
  exact (tendsto_saddleRatio_atTop.const_mul_atTop ha).atTop_mul_atTop₀
    tendsto_saddleCostParam_atTop

theorem saddleThreshold_pos {a : ℝ} (ha : 0 < a) : 0 < saddleThreshold a := by
  unfold saddleThreshold saddleHeight
  have hb : 0 < saddleParameterBase := by linarith [saddleParameterBase_ge_two]
  exact mul_pos (mul_pos ha (div_pos (Real.exp_pos _) hb))
    (by linarith [saddleCostParam_base_ge_one])

theorem existsUnique_saddleHeight {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    ∃! u : ℝ, saddleParameterBase ≤ u ∧ saddleHeight a u = H := by
  obtain ⟨u, hu, heq⟩ := intermediate_value_Ici (continuousOn_saddleHeight a)
    (tendsto_saddleHeight_atTop ha) hH
  refine ⟨u, ⟨hu, heq⟩, ?_⟩
  intro v hv
  exact (strictMonoOn_saddleHeight ha).injOn hv.1 hu (hv.2.trans heq.symm)

def saddleParameter (a H : ℝ) : ℝ :=
  if h : 0 < a ∧ saddleThreshold a ≤ H then
    Classical.choose (existsUnique_saddleHeight h.1 h.2)
  else saddleParameterBase

theorem saddleParameter_spec {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    saddleParameterBase ≤ saddleParameter a H ∧ saddleHeight a (saddleParameter a H) = H := by
  rw [saddleParameter, dif_pos ⟨ha, hH⟩]
  exact (Classical.choose_spec (existsUnique_saddleHeight ha hH)).1

def saddleCutoff (a H : ℝ) : ℝ := a * saddleCostParam (saddleParameter a H)

theorem saddleCutoff_pos {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    0 < saddleCutoff a H := by
  have hu := (saddleParameter_spec ha hH).1
  have hb : 1 ≤ saddleParameterBase := by linarith [saddleParameterBase_ge_two]
  have hcost := strictMonoOn_saddleCostParam.monotoneOn hb (hb.trans hu) hu
  exact mul_pos ha (by linarith [saddleCostParam_base_ge_one])

theorem div_saddleCutoff_eq_ratio {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    H / saddleCutoff a H = saddleRatio (saddleParameter a H) := by
  apply (div_eq_iff (ne_of_gt (saddleCutoff_pos ha hH))).2
  calc
    H = saddleHeight a (saddleParameter a H) := (saddleParameter_spec ha hH).2.symm
    _ = _ := by unfold saddleHeight saddleCutoff; ring

theorem saddleCutoff_domain {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    Real.exp 1 ≤ H / saddleCutoff a H := by
  rw [div_saddleCutoff_eq_ratio ha hH]
  have hu : 1 ≤ saddleParameter a H :=
    (by linarith [saddleParameterBase_ge_two] : 1 ≤ saddleParameterBase).trans
      (saddleParameter_spec ha hH).1
  simpa only [saddleRatio, div_one] using strictMonoOn_saddleRatio.monotoneOn
    (show (1 : ℝ) ∈ Ici 1 by simp) hu hu

theorem upperSaddleBranch_div_saddleCutoff {a H : ℝ} (ha : 0 < a)
    (hH : saddleThreshold a ≤ H) :
    upperSaddleBranch (H / saddleCutoff a H) = saddleParameter a H := by
  rw [div_saddleCutoff_eq_ratio ha hH]
  exact upperSaddleBranch_saddleRatio
    ((by linarith [saddleParameterBase_ge_two] : 1 ≤ saddleParameterBase).trans
      (saddleParameter_spec ha hH).1)

theorem saddleCutoff_equation {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    saddleCutoff a H = a * saddleCost (H / saddleCutoff a H) := by
  rw [saddleCost_eq_param (saddleCutoff_domain ha hH),
    upperSaddleBranch_div_saddleCutoff ha hH]
  rfl

theorem saddleCutoff_unique {a H V : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H)
    (hV : 0 < V) (hnu : Real.exp 1 ≤ H / V) (heq : V = a * saddleCost (H / V)) :
    V = saddleCutoff a H := by
  have hself := saddleCutoff_equation ha hH
  have hselfpos := saddleCutoff_pos ha hH
  have hselfnu := saddleCutoff_domain ha hH
  have hHpos : 0 < H := (saddleThreshold_pos ha).trans_le hH
  rcases lt_trichotomy V (saddleCutoff a H) with hlt | hequal | hgt
  · have hdiv : H / saddleCutoff a H < H / V := div_lt_div_of_pos_left hHpos hV hlt
    have hcost := strictMonoOn_saddleCost hselfnu hnu hdiv
    have hprod := mul_lt_mul_of_pos_left hcost ha
    linarith
  · exact hequal
  · have hdiv : H / V < H / saddleCutoff a H :=
      div_lt_div_of_pos_left hHpos hselfpos hgt
    have hcost := strictMonoOn_saddleCost hnu hselfnu hdiv
    have hprod := mul_lt_mul_of_pos_left hcost ha
    linarith

theorem existsUnique_saddleCutoff {a H : ℝ} (ha : 0 < a)
    (hH : saddleThreshold a ≤ H) :
    ∃! V : ℝ, 0 < V ∧ Real.exp 1 ≤ H / V ∧ V = a * saddleCost (H / V) := by
  exact ⟨saddleCutoff a H,
    ⟨saddleCutoff_pos ha hH, saddleCutoff_domain ha hH, saddleCutoff_equation ha hH⟩,
    fun V hV => saddleCutoff_unique ha hH hV.1 hV.2.1 hV.2.2⟩

theorem hard_and_soft_saddles_exist :
    ∃ Hzero : ℝ, ∀ H ≥ Hzero,
      (∃! V : ℝ, 0 < V ∧ Real.exp 1 ≤ H / V ∧ V = saddleCost (H / V)) ∧
      (∃! V : ℝ, 0 < V ∧ Real.exp 1 ≤ H / V ∧ V = 2 * saddleCost (H / V)) := by
  refine ⟨max (saddleThreshold 1) (saddleThreshold 2), ?_⟩
  intro H hH
  constructor
  · simpa only [one_mul] using existsUnique_saddleCutoff (by norm_num : (0 : ℝ) < 1)
      ((le_max_left _ _).trans hH)
  · exact existsUnique_saddleCutoff (by norm_num : (0 : ℝ) < 2)
      ((le_max_right _ _).trans hH)

end

end PaperC.V282.SaddleParameters
