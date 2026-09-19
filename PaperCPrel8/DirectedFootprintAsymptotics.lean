import PaperCPrel8.ReciprocalPivotAsymptotics

/-! # Full directed footprint estimate at logarithmic support size

The polynomial support factor is absorbed at the second scale, uniformly
before the support, good set, prime cylinder and actual pivot family are chosen.
-/
namespace PaperC.Prel8.DirectedFootprintAsymptotics
open PaperC.Prel8.ReciprocalPivotAsymptotics PaperC.Prel8.OddPrimePivot
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.PrimeEulerPNT
open Set Filter Topology
noncomputable section

/-- Any fixed quadratic logarithmic support factor is absorbed at scale nu. -/
theorem logarithmic_support_absorption (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ Q : ℕ, (Q : ℝ)≤beta*Real.log M →
      2*(Q+1 : ℝ)^2 ≤ Real.exp (delta*saddleNu 1 (Real.log M)) := by
  let C : ℝ := 2*(beta+1)^2
  have hC : 0<C := by dsimp [C]; positivity
  have hlim : Tendsto (fun H => (Real.log C+2*Real.log H)/saddleNu 1 H) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := Real.log C)).div_atTop
      (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ)<1))).add
      ((tendsto_log_div_saddleNu (by norm_num : (0 : ℝ)<1)).const_mul 2)
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using h
  have hnatlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hall : ∀ᶠ M : ℕ in atTop, ∀ Q : ℕ, (Q : ℝ)≤beta*Real.log M →
      2*(Q+1 : ℝ)^2 ≤ Real.exp (delta*saddleNu 1 (Real.log M)) := by
    filter_upwards [hnatlog.eventually (hlim.eventually (gt_mem_nhds hdelta)),
      hnatlog.eventually (eventually_ge_atTop (1 : ℝ)),
      hnatlog.eventually ((tendsto_saddleNu_atTop (by norm_num : (0 : ℝ)<1)).eventually
        (eventually_gt_atTop (0 : ℝ)))] with M herr hH hnu
    intro Q hQ
    have hprefactor := (div_le_iff₀ hnu).mp herr.le
    have hQ' : (Q+1 : ℝ)≤(beta+1)*Real.log M := by linarith
    have hsq := sq_le_sq₀ (by positivity : (0 : ℝ)≤Q+1) (by positivity : 0≤(beta+1)*Real.log M) |>.mpr hQ'
    calc
      _ ≤ C*(Real.log M)^2 := by dsimp [C]; nlinarith
      _ = Real.exp (Real.log C+2*Real.log (Real.log M)) := by
        rw [two_mul]
        simp only [Real.exp_add, Real.exp_log hC, Real.exp_log (by linarith : 0<Real.log M), pow_two]
      _ ≤ _ := Real.exp_le_exp.mpr hprefactor
  exact eventually_atTop.mp hall

/-- Full finite-and-asymptotic F.6 bound for any actual good set of logarithmic support. -/
theorem directed_footprint_final_bound (hPNT : PrimeNumberTheoremRemainder)
    (beta epsilon : ℝ) (hbeta : 0<beta) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ C n Q : ℕ, M≤2*(n+Q) → Q≤n →
      (Q : ℝ)≤beta*Real.log M →
      ∀ (G : Finset ℕ) (q : ℕ → Fin (Q+1) → PrimeUpTo C),
      G ⊆ Finset.Icc 1 n →
      (∀ j ∈ G, ∀ a : Fin (Q+1), (q j a).val.val=largestOddPrime (j+a.val)) →
      (∀ j ∈ G, ∀ a : Fin (Q+1), ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊<largestOddPrime (j+a.val)) →
      (∑ j ∈ G, ((PrimeForcing.directedFootprint G Q (q j)).card : ℝ)) ≤
        (n : ℝ)^2*Real.exp (-2*saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) +
          (n : ℝ)*(Q+1 : ℝ)^2 := by
  obtain ⟨Mraw,hraw⟩ := directed_footprint_hard_bound hPNT (epsilon/2) (by positivity)
  obtain ⟨Mpoly,hpoly⟩ := logarithmic_support_absorption beta (epsilon/2) hbeta (by positivity)
  refine ⟨max Mraw Mpoly, ?_⟩
  intro M hM C n Q hpop hQn hQ G q hG hq hgood
  have hr := hraw M (by omega) C n Q hpop G q hG hq hgood
  have hp := hpoly M (by omega) Q hQ
  let V := saddleCutoff 1 (Real.log M)
  let nu := saddleNu 1 (Real.log M)
  have hsize : ((n+Q : ℕ) : ℝ)≤2*n := by exact_mod_cast (show n+Q≤2*n by omega)
  have hexp : Real.exp ((epsilon/2)*nu)*Real.exp (-2*V+(epsilon/2)*nu) =
      Real.exp (-2*V+epsilon*nu) := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (n : ℝ)*(Q+1 : ℝ)^2 + n*(n+Q : ℕ)*(Q+1 : ℝ)^2*Real.exp (-2*V+(epsilon/2)*nu) := by
      convert hr using 1
      ring
    _ ≤ (n : ℝ)*(Q+1 : ℝ)^2 + n*(2*n)*(Q+1 : ℝ)^2*Real.exp (-2*V+(epsilon/2)*nu) := by
      gcongr
    _ = (n : ℝ)*(Q+1 : ℝ)^2 + n^2*(2*(Q+1 : ℝ)^2)*Real.exp (-2*V+(epsilon/2)*nu) := by ring
    _ ≤ (n : ℝ)*(Q+1 : ℝ)^2 + n^2*Real.exp ((epsilon/2)*nu)*Real.exp (-2*V+(epsilon/2)*nu) := by
      gcongr
    _ = (n : ℝ)*(Q+1 : ℝ)^2 + n^2*(Real.exp ((epsilon/2)*nu)*Real.exp (-2*V+(epsilon/2)*nu)) := by ring
    _ = _ := by rw [hexp]; ring

end
end PaperC.Prel8.DirectedFootprintAsymptotics
