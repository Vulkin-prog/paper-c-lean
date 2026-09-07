import PaperCV282.MacroTransportInformation
import PaperCV282.MovableMarkedBudget

/-! # Absorbing the restored low sites under the movable labelled information margin -/
namespace PaperC.V282.MacroTransportMovableInformation

open Filter Topology SaddleParameters SaddleScales SaddlePoissonScales SaddleCutoffAdmissibility
open MovableMarkedBudget MacroTransportInformation

noncomputable section

theorem movable_restored_budget_eventually (c d : ℝ) (hc : 0<c) (hd : 0<d) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ I rate : ℝ, 0≤I → 1≤rate →
      movableLogCost I rate≤saddleCutoff 2 (Real.log M)/2-c*saddleNu 2 (Real.log M) →
      Real.exp I*(37*(rate*Real.exp (-saddleCutoff 2 (Real.log M)/2+(c/2)*saddleNu 2 (Real.log M))+
        rate^2*Real.exp (-saddleCutoff 2 (Real.log M)+(c/2)*saddleNu 2 (Real.log M))+
        rate*(1+rate)*(M : ℝ)^(-(1/(6 : ℝ))))+
        2*Real.exp (-d*(Real.log M/Real.log (Real.log M))))≤
      2*(64*Real.exp (-(c/2)*saddleNu 2 (Real.log M))+64*(M : ℝ)^(-(1/(12 : ℝ)))+
        3*Real.exp (-saddleCutoff 2 (Real.log M)))+
        2*Real.exp (-(d/2)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Nb,hb⟩ := movable_budget_bound_eventually c hc
  obtain ⟨Nd,hdp⟩ := information_weighted_deep_eventually 2 1 d (by norm_num) hd
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns,hs⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop (saddleThreshold 2)))
  refine ⟨max Nb (max Nd (max Ns 2)),?_⟩
  intro M hM I rate hI hr hbudget
  have hn : (1 : ℝ)≤M := by exact_mod_cast (show 1≤M by omega)
  have hV := saddleCutoff_pos (a := 2) (by norm_num) (hs M (by omega))
  have hnu : 0≤saddleNu 2 (Real.log M) := by
    unfold saddleNu
    exact div_nonneg (Real.log_nonneg hn) hV.le
  have hiV : I≤1*saddleCutoff 2 (Real.log M) := by
    have hl := Real.log_nonneg hr
    unfold movableLogCost at hbudget
    nlinarith [mul_nonneg hc.le hnu]
  have hdeep := hdp M (by omega) I hiV
  have hraw := hb M (by omega) I rate hI hr hbudget
  have ht : 0≤Real.exp I*((rate/(2 : ℝ)^(movableMarkCutoff M+1))*(2+(M : ℝ)^(-(1/(3 : ℝ))))) := by positivity
  have hcore : 0≤Real.exp I*(rate*Real.exp (-saddleCutoff 2 (Real.log M)/2+(c/2)*saddleNu 2 (Real.log M))+
        rate^2*Real.exp (-saddleCutoff 2 (Real.log M)+(c/2)*saddleNu 2 (Real.log M))+
        rate*(1+rate)*(M : ℝ)^(-(1/(6 : ℝ)))) := by positivity
  nlinarith only [hraw,ht,hcore,hdeep]

theorem movable_restored_error_tendsto_zero (c d : ℝ) (hc : 0<c) (hd : 0<d) :
    Tendsto (fun M : ℕ =>
      2*(64*Real.exp (-(c/2)*saddleNu 2 (Real.log M))+64*(M : ℝ)^(-(1/(12 : ℝ)))+
        3*Real.exp (-saddleCutoff 2 (Real.log M)))+
        2*Real.exp (-(d/2)*(Real.log M/Real.log (Real.log M)))) atTop (𝓝 0) := by
  have hmain := movable_budget_error_tendsto_zero c hc
  have hdeep := PrefixScalarConvergence.deep_remainder_tendsto_zero (d/2) (by positivity)
  simpa only [mul_zero,add_zero] using (hmain.const_mul 2).add (hdeep.const_mul 2)

end
end PaperC.V282.MacroTransportMovableInformation
