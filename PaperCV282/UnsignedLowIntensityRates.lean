import PaperCV282.SignedAggregateRates

/-! # Whole-band arithmetic for the signed aggregate, with the enlarged-window loss explicit -/
namespace PaperC.V282.UnsignedLowIntensityRates

open ExactMarkedArithmeticRates DictionaryArithmeticRates FullBandArithmetic DyadicFullValueProfile
open SignedAggregateRates SignedAggregateArithmetic SignedDirectionalFactors MaskedArithmeticGeometry MaskedPairGeometry
open RelationProfileRestriction TwoWindowParity SectionTwelveMoments AllStartSoftPoisson
open HardPoissonRates SaddleParameters SaddleScales PrimeEulerPNT

noncomputable section

/-- A numerical assembly using the directional bound only where it improves the saddle term. -/
theorem ledger_numeric_all_intensities_le {lambda ell F H P m d a g r s : ℝ}
    (hlambda : 0 ≤ lambda) (hell : 1 ≤ ell) (hF : 1 ≤ F) (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hsd : s*lambda ≤ 12*ell)
    (hm : m ≤ lambda*P) (hd : d ≤ lambda*H) (ha : a ≤ lambda^2*P)
    (hg : g ≤ lambda^2*H) (hr : r ≤ F*P*(lambda^2+2*lambda)) :
    m+2*d+s*(10*a+2*g+r) ≤ 32*(lambda*ell*H+F*(lambda^2+lambda)*P) := by
  have hl0 : 0 ≤ lambda := by linarith
  have he0 : 0 ≤ ell := by linarith
  have hf0 : 0 ≤ F := by linarith
  have hsa : s*a ≤ lambda^2*P :=
    (mul_le_mul_of_nonneg_left ha hs0).trans (by nlinarith [mul_nonneg (sq_nonneg lambda) hP])
  have hsr : s*r ≤ F*P*(lambda^2+2*lambda) :=
    (mul_le_mul_of_nonneg_left hr hs0).trans (by
      have hp : 0 ≤ F*P*(lambda^2+2*lambda) := by positivity
      nlinarith)
  have hsg : s*g ≤ 12*ell*lambda*H := by
    have hh := mul_le_mul_of_nonneg_right hsd (mul_nonneg hl0 hH)
    have hg' := mul_le_mul_of_nonneg_left hg hs0
    nlinarith only [hh,hg']
  have hFP : lambda^2*P ≤ F*lambda^2*P := by nlinarith [mul_nonneg (sq_nonneg lambda) hP]
  have hm' : lambda*P ≤ F*lambda*P := by nlinarith [mul_nonneg hl0 hP]
  have hH' : lambda*H ≤ lambda*ell*H := by
    have hh := mul_le_mul_of_nonneg_left hell (mul_nonneg hl0 hH)
    nlinarith only [hh]
  have hp0 : 0 ≤ F*lambda^2*P := by positivity
  have hpl : 0 ≤ F*lambda*P := by positivity
  have hh0 : 0 ≤ lambda*ell*H := by positivity
  nlinarith only [hm,hd,hsa,hsr,hsg,hFP,hm',hH',hp0,hpl,hh0]

/-- A whole-band estimate before L and E, retaining the exact factor 2^(2E+2). -/
theorem signed_aggregate_ledger_all_intensities_eventually
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin*Real.log N ≤ (L+1 : ℝ) → (L+E+2 : ℝ) ≤ betaMax*Real.log N →
      signedAggregateLedger N L E (hardCutoff N) (dyadicBlock N) ≤
        32*((fullRate N L : ℝ)*(1+max 0 (Real.log (2*(fullRate N L : ℝ))))*
          Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
          (2 : ℝ)^(2*E+2)*((fullRate N L : ℝ)^2+(fullRate N L : ℝ))*(N : ℝ)^(-(1/(3 : ℝ))+epsilon)) := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨Nm,hm⟩ := dictionary_defect_cost_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Nc,hc⟩ := dictionary_cutoff_costs_le_eventually hPNT betaMax eta hbetaMax heta
  obtain ⟨Na,ha⟩ := marked_diagonal_cost_le_eventually betaMax epsilon hbetaMax.le hepsilon
  obtain ⟨Nr,hr⟩ := enlarged_valueWeightMass_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max 1 (max Nm (max Nc (max Na Nr))),?_⟩
  intro N hN L E hlo hhi
  have hlam : 0 < (fullRate N L : ℝ) := by
    rw [fullRate_coe]
    have : 0 < N := by omega
    positivity
  have hlhi : (L+1 : ℝ) ≤ betaMax*Real.log N := by
    have hE : (0 : ℝ) ≤ E := by positivity
    linarith
  have hqhi : ((L+E+1 : ℕ)+1 : ℝ) ≤ betaMax*Real.log N := by push_cast; linarith
  have hqlo : betaMin*Real.log N ≤ (L+E+2 : ℝ) := by
    have hE : (0 : ℝ) ≤ E := by positivity
    linarith
  have hdef := hm N (by omega) L hlo hlhi (dyadicBlock N) (Finset.Subset.refl _) (1/(2 : ℝ)^L) (by positivity)
  obtain ⟨hbad,hedges⟩ := hc N (by omega) (L+E+1) hqhi (dyadicBlock N) (Finset.Subset.refl _)
    (1/(2 : ℝ)^L) (by positivity)
  have hdiag := ha N (by omega) L (L+E+1) hqhi
  have hrelation := hr N (by omega) L E hqlo hhi (dyadicBlock N) (Finset.Subset.refl _)
  have heq : (N : ℝ)*(1/(2 : ℝ)^L)=(fullRate N L : ℝ) := by simp only [fullRate_coe]; ring
  rw [heq] at hdef hbad hedges
  have hsd : signedDirectionalFactor (fullRate N L)*(fullRate N L : ℝ) ≤
      12*(1+max 0 (Real.log (2*(fullRate N L : ℝ)))) := by
    have h := min_le_right (1 : ℝ) (12*((1+max 0 (Real.log (2*(fullRate N L : ℝ))))/(fullRate N L : ℝ)))
    have hlpos : (0 : ℝ)<fullRate N L := by linarith
    have hh := mul_le_mul_of_nonneg_right h hlpos.le
    dsimp only [signedDirectionalFactor]
    exact hh.trans_eq (by field_simp)
  have hf : (1 : ℝ) ≤ (2 : ℝ)^(2*E+2) := one_le_pow₀ (by norm_num)
  have hn := ledger_numeric_all_intensities_le
    (lambda := (fullRate N L : ℝ)) (ell := 1+max 0 (Real.log (2*(fullRate N L : ℝ))))
    (F := (2 : ℝ)^(2*E+2))
    (H := Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)))
    (P := (N : ℝ)^(-(1/(3 : ℝ))+epsilon))
    (m := (1/(2 : ℝ)^L)*(fullDefectMass L (dyadicBlock N) : ℝ))
    (a := (1/(2 : ℝ)^L)^2*((N : ℝ)*(L+E+2)))
    hlam.le (by have h := le_max_left 0 (Real.log (2*(fullRate N L : ℝ))); linarith)
    hf (Real.exp_nonneg _) (Real.rpow_nonneg (by positivity) _)
    (signedDirectionalFactor_nonneg (fullRate N L).coe_nonneg) (signedDirectionalFactor_le_one _) hsd
    (by simpa only [mul_comm] using hdef) hbad
    (by convert hdiag using 1 <;> push_cast <;> ring) hedges
    hrelation
  unfold signedAggregateLedger
  convert hn using 1; ring

end
end PaperC.V282.UnsignedLowIntensityRates
