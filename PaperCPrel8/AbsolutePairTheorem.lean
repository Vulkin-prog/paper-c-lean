import PaperCPrel8.AbsolutePairGeometry
import PaperCPrel8.AbsolutePairRates
import PaperCPrel8.ArithmeticLowMarginals

/-! # The full conditional pair activity, uniformly on deterministic good subsets

Both cutoffs are the paper's actual cutoffs. The source cylinder can be minimal.
No pair-decay premise or Stein solution assumption is needed.
-/
namespace PaperC.Prel8.AbsolutePairTheorem
open AbsolutePairGeometry AbsolutePairRates AbsolutePairLedger RoughPairHostSaddle
open MicroscopicActualGeometry MicroscopicPaperBudget MicroscopicProfileBudget MicroscopicRetainedRates
open MicroscopicGoodField MicroscopicRelationExcess ActualSignedPalm ArithmeticLowMarginals
open ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
open V282.AllStartSoftPoisson V282.SaddleParameters V282.PrimeEulerPNT
open scoped NNReal
noncomputable section

/-- Uniform arithmetic bound with arbitrarily small loss on the second saddle scale. -/
theorem pair_bound_eventually (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c eta epsilon : ℝ) (hbetaMin : 0<betaMin) (hband : betaMin<betaMax)
    (hc : 0<c) (heta : 0<eta) (hepsilon : 0<epsilon) :
    ∃ M0 : ℕ, ∀ M≥M0, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M≤(L+1:ℝ) → (L+1:ℝ)≤betaMax*Real.log M →
      0≤I → 1≤siteRate M L →
      I+Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*V282.SaddleScales.saddleNu 1 (Real.log M) →
      ∀ C : ℕ, M+(L+paperExcess M L I+1)≤C →
      ∀ G : Finset ℕ, G⊆goodSites M (M-L) L (paperExcess M L I) (primeCutoff M) →
      ∀ A : SmallSample C (primeCutoff M) → Prop,
      ∀ hA : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C (primeCutoff M) w)),
      I = -Real.log (eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C (primeCutoff M) w))) →
      activity (sourceLaw A hA) L (paperExcess M L I) G≤
        4*(Real.exp I*(fullRate M L:ℝ)^2*
          Real.exp (-2*saddleCutoff 1 (Real.log M)+eta*V282.SaddleScales.saddleNu 1 (Real.log M)))+
            2*(M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  have hbeta : 0<betaMax := hbetaMin.trans hband
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hbetaMin hband hc
  obtain ⟨Mh,hh⟩ := hosted_pairs_saddle hPNT (betaMax+1) (by linarith) heta
  obtain ⟨Ml,hl⟩ := local_budget_rate (betaMax+1) 8 epsilon (by linarith) (by norm_num) hepsilon
  obtain ⟨Mr,hr⟩ := conditional_actual_profile_bound betaMin betaMax epsilon hbetaMin hband hepsilon
  refine ⟨max 1 (max Mg (max Mh (max Ml Mr))),?_⟩
  intro M hM L I hlo hhi hI hrate hbudget C hC G hG A hA hinfo
  have g := hg M (by omega) L I hlo hhi hI hrate hbudget
  let Q := L+paperExcess M L I+1
  have hQ : (Q:ℝ)≤(betaMax+1)*Real.log M := by
    have := g.shifted_upper
    dsimp only [Q]
    push_cast
    linarith
  have geom0 : GoodGeometry C (primeCutoff M) L (paperExcess M L I)
      (goodSites M (M-L) L (paperExcess M L I) (primeCutoff M)) :=
    goodSites_geometry g.length_pos (by have := g.strong_prime; omega)
      (by have := g.strong_prime; omega) (by omega)
  have geom := geometry_subset geom0 hG
  have hGn := hG.trans (goodSites_subset M (M-L) L (paperExcess M L I) (primeCutoff M))
  have hgm : (G.card:ℝ)≤M := by
    have hn := Finset.card_le_card hGn
    simp only [Nat.card_Icc,Nat.add_sub_cancel] at hn
    exact_mod_cast hn.trans (Nat.sub_le M L)
  have hb := hh M (by omega) (M-L) Q (M+Q) (by omega) (by omega)
    (by have := g.support_short; dsimp [Q]; omega) hQ
  have hlocal := hl M (by omega) Q hQ I (fullRate M L) hI g.ambient_rate g.ambient_budget
  have hrel := hr M (by omega) (M-L) L (primeCutoff M) C I
    hlo hhi hI g.ambient_rate g.ambient_budget g.interior_end hC
  have hsub := mul_le_mul_of_nonneg_left (separatedExcess_mono (C:=C) (L:=L) (E:=paperExcess M L I) hG)
    (show 0≤Real.exp I*(1/(2:ℝ)^L)^2 by positivity)
  have hrel' : Real.exp I*(1/(2:ℝ)^L)^2*separatedExcess C L (paperExcess M L I) G≤
      (M:ℝ)^(-(1/(3:ℝ))+epsilon) := by nlinarith only [hsub,hrel]
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  rw [fullRate_coe] at hlocal ⊢
  have hn := ledger_bound (p:=1/(2:ℝ)^L) (m:=M) (g:=G.card)
    (b:=(RoughPairHosts.hostedPairs (M-L) Q (primeCutoff M)).card)
    (R:=separatedExcess C L (paperExcess M L I) G) (I:=I) (Q:=Q)
    hm hgm hb (by convert hlocal using 1; ring) hrel'
  have hi : Real.exp I=(eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun w ↦ A (restrictSmall C (primeCutoff M) w)))⁻¹ := by
    rw [hinfo,Real.exp_neg,Real.exp_log hA]
  apply (activity_le_counts geom g.strong_prime hGn A hA).trans
  convert hn using 1
  · rw [hi]
    dsimp only [Q]
    push_cast
    ring
  · ring

/-- The paper budget gives any decay exponent strictly below twice its margin. -/
theorem pair_margin_eventually (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c d epsilon : ℝ) (hbetaMin : 0<betaMin) (hband : betaMin<betaMax)
    (hd : 0<d) (hdc : d<2*c) (hepsilon : 0<epsilon) :
    ∃ M0 : ℕ, ∀ M≥M0, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M≤(L+1:ℝ) → (L+1:ℝ)≤betaMax*Real.log M →
      0≤I → 1≤siteRate M L →
      I+Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*V282.SaddleScales.saddleNu 1 (Real.log M) →
      ∀ C : ℕ, M+(L+paperExcess M L I+1)≤C →
      ∀ G : Finset ℕ, G⊆goodSites M (M-L) L (paperExcess M L I) (primeCutoff M) →
      ∀ A : SmallSample C (primeCutoff M) → Prop,
      ∀ hA : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C (primeCutoff M) w)),
      I = -Real.log (eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C (primeCutoff M) w))) →
      activity (sourceLaw A hA) L (paperExcess M L I) G≤
        4*Real.exp (-I-d*V282.SaddleScales.saddleNu 1 (Real.log M))+
          2*(M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  let a := (c+d/2)/2
  let eta := 2*a-d
  have ha : a<c := by dsimp [a]; linarith
  have heta : 0<eta := by dsimp [eta,a]; linarith
  obtain ⟨Mp,hp⟩ := pair_bound_eventually hPNT betaMin betaMax c eta epsilon
    hbetaMin hband (by linarith) heta hepsilon
  obtain ⟨Mb,hb⟩ := paper_to_ambient_budget_eventually betaMax c a (hbetaMin.trans hband) ha
  refine ⟨max Mp Mb,?_⟩
  intro M hM L I hlo hhi hI hr hbudget C hC G hG A hA hinfo
  have hp' := hp M (by omega) L I hlo hhi hI hr hbudget C hC G hG A hA hinfo
  obtain ⟨hlambda,hambient⟩ := hb M (by omega) L I hhi hr hbudget
  have hx := information_gain (show 0<(fullRate M L:ℝ) by linarith) hambient (eta:=eta)
  have he : 2*a-eta=d := by dsimp [eta]; ring
  rw [he] at hx
  linarith

end
end PaperC.Prel8.AbsolutePairTheorem
