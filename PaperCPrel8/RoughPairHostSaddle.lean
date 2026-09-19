import PaperCPrel8.RoughPairReciprocalSaddle
import PaperCPrel8.RoughPairHosts
import PaperCPrel8.RoughKernelStrongCount

/-! # Uniform hard-saddle count for the actual single-target rough hosts -/
namespace PaperC.Prel8.RoughPairHostSaddle
open Filter Topology RoughPairReciprocalSaddle RoughPairHosts RoughKernelStrongCount
open V282.SaddleParameters V282.SaddleScales V282.PrimeEulerPNT LargeOddKernel
noncomputable section

/-- The full -2V exponent, uniformly before the support length and population are chosen. -/
theorem hosted_pairs_saddle (hPNT : PrimeNumberTheoremRemainder)
    (beta : ℝ) (hbeta : 0<beta) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ n Q X : ℕ,
      n+Q≤X → M≤X → X≤2*M → (Q:ℝ)≤beta*Real.log M →
      ((hostedPairs n Q ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊).card:ℝ)≤
        (M:ℝ)^2*Real.exp (-2*saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mr,hr⟩ := hard_reciprocal hPNT (beta+1) (by linarith) (epsilon:=epsilon/2) (by positivity)
  obtain ⟨Mp,hp⟩ := polynomial_absorption beta (epsilon/2) hbeta (by positivity)
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Mh,hh⟩ := eventually_atTop.mp (hl.eventually (eventually_ge_atTop (5:ℝ)))
  refine ⟨max 1 (max Mr (max Mp Mh)),?_⟩
  intro M hM n Q X hn hMX hXM hQ
  let V := saddleCutoff 1 (Real.log M)
  let nu := saddleNu 1 (Real.log M)
  let Y := ⌊Real.exp V⌋₊
  let S := ∑ m∈(Finset.Icc 1 X).filter (fun m ↦ 1<largeOddKernel Y m),
    (Q+1:ℝ)^ArithmeticFunction.cardDistinctFactors (largeOddKernel Y m)/(largeOddKernel Y m:ℝ)
  have hH := hh M (by omega)
  have hz : (Q+1:ℝ)≤(beta+1)*Real.log M := by linarith
  have hX : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hs : S≤3*Real.exp (-2*V+(epsilon/2)*nu)*X :=
    (div_le_iff₀ hX).mp (hr M (by omega) X hMX (Q+1) (by positivity) hz)
  have hc := hosted_pairs_count n Q Y X hn
  change _ ≤ 2*(Q+1)*(X:ℝ)*S at hc
  have hx : (X:ℝ)^2≤4*(M:ℝ)^2 := by
    have hh : (X:ℝ)≤2*M := by exact_mod_cast hXM
    nlinarith [show (0:ℝ)≤X by positivity,show (0:ℝ)≤M by positivity]
  have hpoly : 24*(Q+1:ℝ)≤Real.exp ((epsilon/2)*nu) := by
    apply le_trans _ (hp M (by omega) Q hQ)
    have hq : (0:ℝ)≤Q+1 := by positivity
    nlinarith
  calc
    _ ≤ 2*(Q+1)*(X:ℝ)*(3*Real.exp (-2*V+(epsilon/2)*nu)*X) :=
      hc.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = 6*(Q+1)*(X:ℝ)^2*Real.exp (-2*V+(epsilon/2)*nu) := by ring
    _ ≤ 6*(Q+1)*(4*(M:ℝ)^2)*Real.exp (-2*V+(epsilon/2)*nu) := by gcongr
    _ = (M:ℝ)^2*(24*(Q+1))*Real.exp (-2*V+(epsilon/2)*nu) := by ring
    _ ≤ (M:ℝ)^2*Real.exp ((epsilon/2)*nu)*Real.exp (-2*V+(epsilon/2)*nu) := by gcongr
    _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; dsimp [V,nu]; ring

end
end PaperC.Prel8.RoughPairHostSaddle
