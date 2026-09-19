import PaperCPrel8.MicroscopicActualGeometry
import PaperCPrel8.DirectedFootprintAsymptotics

/-! # Uniform numerical rates for the retained-field comparison

The sparse graph term keeps two factors of intensity but gains two saddle
exponents. The local cost is polynomially small after information and support
inflation. These are proved estimates, not assumed convergence premises.
-/
namespace PaperC.Prel8.MicroscopicRetainedRates
open PaperC.Prel8.MicroscopicProfileBudget PaperC.Prel8.DirectedFootprintAsymptotics
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.SaddlePoissonScales
open PaperC.V282.AggregateCutoffRemainder
open Filter Topology
noncomputable section

/-- The two-intensity graph contribution retains twice the information margin. -/
theorem graph_budget_absorption {I lambda V nu c eta : ℝ}
    (hI : 0 ≤ I) (hlambda : 0 < lambda)
    (hb : I+Real.log lambda ≤ V-c*nu) :
    Real.exp I*lambda^2*Real.exp (-2*V+eta*nu) ≤ Real.exp (-(2*c-eta)*nu) := by
  have hp : Real.exp I*lambda ≤ Real.exp (V-c*nu) := by
    simpa only [Real.exp_add,Real.exp_log hlambda] using Real.exp_le_exp.mpr hb
  have hl : lambda ≤ Real.exp (V-c*nu) := by nlinarith [Real.one_le_exp hI]
  have hq := mul_le_mul hp hl hlambda.le (Real.exp_pos _).le
  calc
    _ ≤ (Real.exp (V-c*nu)*Real.exp (V-c*nu))*Real.exp (-2*V+eta*nu) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith only [hq]
    _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring

/-- A logarithmic support square is eventually smaller than exp(V). -/
theorem support_square_le_saddle (beta : ℝ) (hbeta : 0 < beta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ Q : ℕ, (Q:ℝ) ≤ beta*Real.log M →
      (Q+1:ℝ)^2 ≤ Real.exp (saddleCutoff 1 (Real.log M)) := by
  obtain ⟨Mp,hp⟩ := logarithmic_support_absorption beta 1 hbeta (by norm_num)
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hn := (tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).comp hlog
  have hr := (tendsto_saddleCutoff_div_nu (by norm_num : (0:ℝ)<1)).comp hlog
  obtain ⟨Mn,hnu⟩ := eventually_atTop.mp (hn.eventually (eventually_gt_atTop (0:ℝ)))
  obtain ⟨Mr,hquot⟩ := eventually_atTop.mp (hr.eventually (eventually_ge_atTop (1:ℝ)))
  refine ⟨max Mp (max Mn Mr), ?_⟩
  intro M hM Q hQ
  have hn0 : 0 < saddleNu 1 (Real.log M) := hnu M (by omega)
  have hnv : saddleNu 1 (Real.log M) ≤ saddleCutoff 1 (Real.log M) := by
    have h := (le_div_iff₀ hn0).mp (hquot M (by omega))
    simpa only [one_mul] using h
  have h := hp M (by omega) Q hQ
  simp only [one_mul] at h
  exact (by nlinarith [sq_nonneg (Q+1:ℝ)] : (Q+1:ℝ)^2 ≤ Real.exp (saddleNu 1 (Real.log M))).trans
    (Real.exp_le_exp.mpr hnv)

/-- Every fixed multiple of the conditional local cost has a uniform power saving. -/
theorem local_budget_rate (beta K epsilon : ℝ) (hbeta : 0 < beta)
    (hK : 0 < K) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ Q : ℕ, (Q:ℝ) ≤ beta*Real.log M →
      ∀ I lambda : ℝ, 0 ≤ I → 1 ≤ lambda →
      I+Real.log lambda ≤ saddleCutoff 1 (Real.log M) →
      K*Real.exp I*lambda^2*(Q+1:ℝ)^2/(M:ℝ) ≤ (M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  obtain ⟨Ms,hs⟩ := support_square_le_saddle beta hbeta
  obtain ⟨Me,he⟩ := eventually_atTop.mp
    (constant_exp_saddle_le_power_eventually (3*K) 3 (2/3+epsilon) (by positivity) (by linarith))
  refine ⟨max 1 (max Ms Me), ?_⟩
  intro M hM Q hQ I lambda hI hl hb
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0<M by omega)
  have hr := conditional_rate_factor_le hI hl hb
  have hs' := hs M (by omega) Q hQ
  have he' := he M (by omega)
  have hrate : Real.exp I*lambda^2 ≤ 3*Real.exp (2*saddleCutoff 1 (Real.log M)) := by
    nlinarith [Real.exp_pos I]
  calc
    _ ≤ K*(3*Real.exp (2*saddleCutoff 1 (Real.log M)))*Real.exp (saddleCutoff 1 (Real.log M))/(M:ℝ) := by
      apply div_le_div_of_nonneg_right _ hm.le
      calc
        _ = K*(Real.exp I*lambda^2)*(Q+1:ℝ)^2 := by ring
        _ ≤ _ := by gcongr
    _ = (3*K)*Real.exp (3*saddleCutoff 1 (Real.log M))/(M:ℝ) := by
      rw [show 3*saddleCutoff 1 (Real.log M)=2*saddleCutoff 1 (Real.log M)+saddleCutoff 1 (Real.log M) by ring,Real.exp_add]
      ring
    _ ≤ (M:ℝ)^(2/3+epsilon)/(M:ℝ) := div_le_div_of_nonneg_right he' hm.le
    _ = _ := by
      have hx := Real.rpow_sub hm (2/3+epsilon) 1
      rw [Real.rpow_one] at hx
      rw [← hx]
      congr 1
      ring

/-- Finite ledger algebra: local, sparse graph and relation errors suffice. -/
theorem retained_ledger_bound {p m n g b r I V nu c : ℝ} {Q : ℕ}
    (_hp : 0 ≤ p) (hn : 0 ≤ n) (hnm : n ≤ m) (_hg : 0 ≤ g) (hgm : g ≤ m)
    (hI : 0 ≤ I) (hbase : b ≤ n^2*Real.exp (-2*V+c*nu)+n*(Q+1:ℝ)^2)
    (hlocal : 11*Real.exp I*(m*p)^2*(Q+1:ℝ)^2/m ≤ r)
    (hm : 0 < m)
    (hgraph : Real.exp I*(m*p)^2*Real.exp (-2*V+c*nu) ≤ Real.exp (-c*nu)) :
    p^2*(g+b+4*g*(2*(Q:ℝ)+1)+Real.exp I*b) ≤ 2*Real.exp (-c*nu)+r := by
  have hi := Real.one_le_exp hI
  have hq : 0 ≤ (Q:ℝ) := Nat.cast_nonneg Q
  have hnear : g+4*g*(2*(Q:ℝ)+1) ≤ 9*m*(Q+1:ℝ)^2 := by
    have hh : 1+4*(2*(Q:ℝ)+1) ≤ 9*(Q+1:ℝ)^2 := by nlinarith
    have hx := mul_le_mul hgm hh (by positivity) hm.le
    nlinarith only [hx]
  have hb : b ≤ m^2*Real.exp (-2*V+c*nu)+m*(Q+1:ℝ)^2 := by
    apply hbase.trans
    gcongr
  have hsum : b+Real.exp I*b ≤ 2*Real.exp I*(m^2*Real.exp (-2*V+c*nu)+m*(Q+1:ℝ)^2) := by
    have hx := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1+Real.exp I by positivity)
    have hz : 0 ≤ m^2*Real.exp (-2*V+c*nu)+m*(Q+1:ℝ)^2 := by positivity
    nlinarith [mul_nonneg (show 0≤Real.exp I-1 by linarith) hz]
  have hl : 11*Real.exp I*p^2*m*(Q+1:ℝ)^2 ≤ r := by
    convert hlocal using 1
    field_simp
  have hnine : 9*p^2*m*(Q+1:ℝ)^2 ≤ 9*Real.exp I*p^2*m*(Q+1:ℝ)^2 := by
    convert mul_le_mul_of_nonneg_right hi (show 0 ≤ 9*p^2*m*(Q+1:ℝ)^2 by positivity) using 1 <;> ring
  have ht := mul_le_mul_of_nonneg_left (add_le_add hnear hsum) (sq_nonneg p)
  nlinarith only [ht,hl,hnine,hgraph]

end
end PaperC.Prel8.MicroscopicRetainedRates
