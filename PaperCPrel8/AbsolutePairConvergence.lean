import PaperCPrel8.AbsolutePairTheorem
import PaperCV282.SaddleRateConvergence

/-! # G.7's uniform vanishing conclusion for actual varying conditional fields -/
namespace PaperC.Prel8.AbsolutePairConvergence
open Filter Topology AbsolutePairTheorem AbsolutePairLedger ActualSignedPalm
open MicroscopicActualGeometry MicroscopicPaperBudget MicroscopicProfileBudget MicroscopicGoodField
open ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
open V282.PrimeEulerPNT V282.SaddleScales V282.SaddleParameters V282.SaddleRateConvergence
noncomputable section

theorem activity_nonneg {C : ℕ} (mu : FinitePMF (SampleSpace C)) (L E : ℕ) (G : Finset ℕ) :
    0≤activity mu L E G := by
  unfold activity
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · exact le_refl 0
  · exact Finset.sum_nonneg (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ abs_nonneg _))

/-- No assumed decay input: the source regime and the arithmetic bounds imply o(1). -/
theorem pair_tendsto_zero (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0<betaMin) (hband : betaMin<betaMax) (hc : 0<c)
    (M L C : ℕ → ℕ) (I : ℕ → ℝ) (G : ℕ → Finset ℕ)
    (hM : Tendsto M atTop atTop)
    (A : ∀ k, SmallSample (C k) (primeCutoff (M k)) → Prop)
    (hA : ∀ k, 0<eventProbability (FinitePMF.uniform (SampleSpace (C k)))
      (fun w ↦ A k (restrictSmall (C k) (primeCutoff (M k)) w)))
    (hregime : ∀ᶠ k : ℕ in atTop,
      betaMin*Real.log (M k)≤(L k+1:ℝ) ∧ (L k+1:ℝ)≤betaMax*Real.log (M k) ∧
      0≤I k ∧ 1≤siteRate (M k) (L k) ∧
      I k+Real.log (siteRate (M k) (L k))≤saddleCutoff 1 (Real.log (M k))-c*saddleNu 1 (Real.log (M k)) ∧
      M k+(L k+paperExcess (M k) (L k) (I k)+1)≤C k ∧
      G k⊆goodSites (M k) (M k-L k) (L k) (paperExcess (M k) (L k) (I k)) (primeCutoff (M k)) ∧
      I k = -Real.log (eventProbability (FinitePMF.uniform (SampleSpace (C k)))
        (fun w ↦ A k (restrictSmall (C k) (primeCutoff (M k)) w)))) :
    Tendsto (fun k ↦ activity (sourceLaw (A k) (hA k)) (L k) (paperExcess (M k) (L k) (I k)) (G k))
      atTop (𝓝 0) := by
  obtain ⟨M0,hmain⟩ := pair_margin_eventually hPNT betaMin betaMax c c (1/6)
    hbetaMin hband hc (by linarith) (by norm_num)
  have he := (margin_exponential_nat_tendsto_zero 1 (2*c) 0 (by norm_num) (by linarith)).const_mul 4
  have hp := (polynomial_error_nat_tendsto_zero (1/6) (by norm_num)).const_mul 2
  have hh : Tendsto (fun k ↦ 4*Real.exp (-c*saddleNu 1 (Real.log (M k)))+
      2*(M k:ℝ)^(-(1/(3:ℝ))+(1/6))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (he.add hp).comp hM
  apply squeeze_zero' (Eventually.of_forall fun k ↦ activity_nonneg _ _ _ _) _ hh
  filter_upwards [hregime,hM.eventually (eventually_ge_atTop M0)] with k hk hMk
  obtain ⟨hlo,hhi,hI,hr,hb,hC,hG,hi⟩ := hk
  have hb' := hmain (M k) hMk (L k) (I k) hlo hhi hI hr hb (C k) hC (G k) hG (A k) (hA k) hi
  have hexp : Real.exp (-I k-c*saddleNu 1 (Real.log (M k)))≤Real.exp (-c*saddleNu 1 (Real.log (M k))) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

end
end PaperC.Prel8.AbsolutePairConvergence
