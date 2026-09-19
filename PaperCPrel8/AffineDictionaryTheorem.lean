import PaperCPrel8.AffineDictionaryRates
import PaperCPrel8.TypicalDictionaryTheorem
import PaperCV282.SaddlePoissonScales

/-! # A uniform mean distance and exceptional fraction for typical dictionaries

The dictionary is held fixed inside every distance. The rate and threshold
are independent of its cardinality, within the actual intensity window.
-/
namespace PaperC.Prel8.AffineDictionaryTheorem
open Filter Topology
open PaperC.SectionTwelveMoments
open PaperC.V282.RandomDictionary PaperC.V282.DictionaryFieldInfinite
open PaperC.V282.PrimeEulerPNT PaperC.V282.ProcessAGGInput
open PaperC.V282.HardPoissonRates PaperC.V282.LogarithmicWordPowers
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.SaddlePoissonScales
open PaperC.Prel8.AffineDictionaryRates PaperC.Prel8.TypicalDictionaryTransfer
open PaperC.Prel8.DictionaryAverage
open PaperC.Prel8.TypicalDictionaryTheorem PaperC.Prel8.AffineDictionaryInclusion
noncomputable section

/-- Uniform mean comparison, allowing dictionaries much larger than sqrt(N). -/
theorem mean_rate_eventually (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K epsilon eta : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hK : 0 ≤ K) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L m r : ℕ,
      betaMin*Real.log N ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log N →
      1 ≤ m → m ≤ 2^(L+1) → r ≤ L+1 → m=2^(L+1-r) → (N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)) ≤ K →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
      affineAverage (L+1) r (maskedDistance N L (hardCutoff N) mask) ≤ rate K epsilon eta N := by
  obtain ⟨Nr,hr⟩ := typical_rate_eventually hAGG hPNT betaMin betaMax epsilon eta hbetaMin hbeta hepsilon heta
  obtain ⟨Nl,hl⟩ := polynomial_factor_le_rpow_eventually betaMax (hbetaMin.trans hbeta).le 1 1
    (2/3+epsilon) (by linarith)
  refine ⟨max Nr (max Nl 1),?_⟩
  intro N hN L m r hlo hhi hm hmb hrank heq hKbound mask hmask
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have ha : 0 ≤ (N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)) := by positivity
  have hs : ((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))^2 ≤ K^2 := by nlinarith
  have hL : (L+1:ℝ) ≤ (N:ℝ)^(2/3+epsilon) := by
    simpa only [one_mul,pow_one,abs_of_nonneg (by positivity : (0:ℝ)≤L+1)] using
      hl N (by omega) L (by simpa only [Nat.cast_add,Nat.cast_one] using hhi)
  have hexp : (N:ℝ)^(2/3+epsilon)=(N:ℝ)*(N:ℝ)^(-(1/(3:ℝ))+epsilon) := by
    conv_rhs => lhs; rw [← Real.rpow_one (N:ℝ)]
    rw [← Real.rpow_add hn]
    congr 1
    ring
  rw [hexp] at hL
  have hd := mul_le_mul_of_nonneg_left hL
    (show 0 ≤ ((m:ℝ)/(2:ℝ)^(L+1))^2*(N:ℝ) by positivity)
  have hsP := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hn.le (-(1/(3:ℝ))+epsilon))
  have hex := Real.exp_nonneg (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))
  have hcoef : 2*((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))+6*((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))^2 ≤ 2*K+6*K^2 := by nlinarith
  have hcE := mul_le_mul_of_nonneg_right hcoef hex
  have hdiv : ((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))^2/m ≤ K^2 :=
    (div_le_self (sq_nonneg _) hmR).trans hs
  have hcP := mul_le_mul_of_nonneg_left (add_le_add hdiv hKbound)
    (Real.rpow_nonneg hn.le (-(1/(3:ℝ))+epsilon))
  have h := hr N (by omega) L m r hlo hhi hm hmb hrank heq mask hmask
  unfold rate
  nlinarith

end
end PaperC.Prel8.AffineDictionaryTheorem
