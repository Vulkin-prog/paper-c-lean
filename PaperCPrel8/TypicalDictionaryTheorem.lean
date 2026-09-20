import PaperCPrel8.TypicalDictionaryRates
import PaperCV282.SaddlePoissonScales

/-! # A uniform mean distance and exceptional fraction for typical dictionaries

The dictionary is held fixed inside every distance. The rate and threshold
are independent of its cardinality, within the actual intensity window.
-/
namespace PaperC.Prel8.TypicalDictionaryTheorem
open Filter Topology
open PaperC.SectionTwelveMoments
open PaperC.V282.RandomDictionary PaperC.V282.DictionaryFieldInfinite
open PaperC.V282.PrimeEulerPNT PaperC.V282.ProcessAGGInput
open PaperC.V282.HardPoissonRates PaperC.V282.LogarithmicWordPowers
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.SaddlePoissonScales
open PaperC.Prel8.TypicalDictionaryRates PaperC.Prel8.TypicalDictionaryTransfer
open PaperC.Prel8.DictionaryAverage
noncomputable section

/-- Explicit deterministic rate, for any fixed positive saddle and polynomial slack. -/
def rate (K epsilon eta : ℝ) (N : ℕ) : ℝ :=
  (2*K+6*K^2)*Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
  (10*K^2+2*K)*(N:ℝ)^(-(1/(3:ℝ))+epsilon)

theorem rate_nonneg {K : ℝ} (hK : 0 ≤ K) (epsilon eta : ℝ) (N : ℕ) :
    0 ≤ rate K epsilon eta N := by unfold rate; positivity

/-- The finite-cylinder masked law at the full mask is exactly the recorded conditional law. -/
theorem full_mask_distance_eq (N L Y : ℕ) (W : Finset (Fin (L+1) → PaperC.F₂)) :
    maskedDistance N L Y (dyadicBlock N) W=dictionaryConditionalDistance N L Y W := by
  simp only [maskedDistance,dictionaryConditionalDistance,conditionalDictionaryLaw_at_dyadic]

/-- Uniform mean comparison, allowing dictionaries much larger than sqrt(N). -/
theorem mean_rate_eventually (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K epsilon eta : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hK : 0 ≤ K) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L m : ℕ,
      betaMin*Real.log N ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log N →
      1 ≤ m → m ≤ 2^(L+1) → (N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)) ≤ K →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
      dictionaryAverage (L+1) m (maskedDistance N L (hardCutoff N) mask) ≤ rate K epsilon eta N := by
  obtain ⟨Nr,hr⟩ := typical_rate_eventually hAGG hPNT betaMin betaMax epsilon eta hbetaMin hbeta hepsilon heta
  obtain ⟨Nl,hl⟩ := polynomial_factor_le_rpow_eventually betaMax (hbetaMin.trans hbeta).le 1 1
    (2/3+epsilon) (by linarith)
  refine ⟨max Nr (max Nl 1),?_⟩
  intro N hN L m hlo hhi hm hmb hKbound mask hmask
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
  have h := hr N (by omega) L m hlo hhi hm hmb mask hmask
  unfold rate
  nlinarith

/-- The genuine infinite source law has the same dictionary-averaged bound. -/
theorem mean_unconditional_le {N L Y m : ℕ} {r : ℝ}
    (hr : dictionaryAverage (L+1) m (dictionaryConditionalDistance N L Y) ≤ r) :
    dictionaryAverage (L+1) m (dictionaryDistance N L) ≤ r :=
  (average_mono (fun W _ => dictionaryDistance_le_conditionalDistance N L Y W)).trans hr

/-- The exceptional proportion controls each fixed dictionary's mean conditional distance. -/
theorem exceptional_fraction_le {N L Y m : ℕ} (hm : m ≤ 2^(L+1)) {r t : ℝ} (ht : 0 < t)
    (hr : dictionaryAverage (L+1) m (dictionaryConditionalDistance N L Y) ≤ r) :
    dictionaryFraction (L+1) m (fun W => t < dictionaryConditionalDistance N L Y W) ≤ min 1 (r/t) :=
  fraction_gt_le hm _ (fun W _ => dictionaryConditionalDistance_nonneg N L Y W) ht hr

/-- Every fixed-slack deterministic rate tends to zero for epsilon<1/3. -/
theorem rate_tendsto_zero (K epsilon eta : ℝ) (hepsilon : epsilon < 1/3) :
    Tendsto (rate K epsilon eta) atTop (𝓝 0) := by
  have hE := saddle_exponential_nat_tendsto_zero 1 1 eta (by norm_num) (by norm_num)
  have hP : Tendsto (fun N : ℕ => (N:ℝ)^(-(1/(3:ℝ))+epsilon)) atTop (𝓝 0) := by
    have he : -(1/(3:ℝ)-epsilon)= -(1/(3:ℝ))+epsilon := by ring
    simpa only [Function.comp_def,he] using
      (tendsto_rpow_neg_atTop (by linarith : (0:ℝ) < 1/3-epsilon)).comp tendsto_natCast_atTop_atTop
  change Tendsto (fun N => rate K epsilon eta N) _ _
  simpa only [rate,neg_mul,one_mul,mul_zero,add_zero] using
    (hE.const_mul (2*K+6*K^2)).add (hP.const_mul (10*K^2+2*K))

end
end PaperC.Prel8.TypicalDictionaryTheorem
