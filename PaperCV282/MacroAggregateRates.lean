import PaperCV282.MacroAggregateArithmetic
import PaperCV282.MacroAggregateValueProfile
import PaperCV282.MacroscopicMarkedLedger

/-! # Actual one-intensity aggregate arithmetic on macroscopic retained populations -/
namespace PaperC.V282.MacroAggregateRates

open ExactMarkedArithmeticRates MacroAggregateArithmetic SignedDirectionalFactors
open MacroscopicMaskGeometry MaskedArithmeticGeometry MaskedPairGeometry TwoWindowParity
open RelationProfileRestriction AllStartSoftPoisson HardPoissonRates SaddleParameters SaddleScales
open PrimeEulerPNT FiniteStartMaskAverages

noncomputable section

/-- A numerical assembly using the directional bound only where it improves the saddle term. -/
theorem signed_ledger_numeric_le {lambda ell F H P m d a g r s : ℝ}
    (hlambda : 1 ≤ lambda) (hell : 1 ≤ ell) (hF : 1 ≤ F) (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hsd : s*lambda ≤ 24*ell)
    (hm : m ≤ lambda*P) (hd : d ≤ lambda*H) (ha : a ≤ lambda^2*P)
    (hg : g ≤ lambda^2*H) (hr : r ≤ F*P*(lambda^2+2*lambda)) :
    m+2*d+s*(10*a+2*g+r) ≤ 64*(lambda*ell*H+F*lambda^2*P) := by
  have hl0 : 0 ≤ lambda := by linarith
  have he0 : 0 ≤ ell := by linarith
  have hf0 : 0 ≤ F := by linarith
  have hsa : s*a ≤ lambda^2*P :=
    (mul_le_mul_of_nonneg_left ha hs0).trans (by nlinarith [mul_nonneg (sq_nonneg lambda) hP])
  have hsr : s*r ≤ F*P*(lambda^2+2*lambda) :=
    (mul_le_mul_of_nonneg_left hr hs0).trans (by
      have hp : 0 ≤ F*P*(lambda^2+2*lambda) := by positivity
      nlinarith)
  have hsg : s*g ≤ 24*ell*lambda*H := by
    have hh := mul_le_mul_of_nonneg_right hsd (mul_nonneg hl0 hH)
    have hg' := mul_le_mul_of_nonneg_left hg hs0
    nlinarith only [hh,hg']
  have hl2 : lambda ≤ lambda^2 := by nlinarith
  have hFP : lambda^2*P ≤ F*lambda^2*P := by nlinarith [mul_nonneg (sq_nonneg lambda) hP]
  have hm' : lambda*P ≤ F*lambda^2*P :=
    (mul_le_mul_of_nonneg_right hl2 hP).trans hFP
  have hr' : F*P*(lambda^2+2*lambda) ≤ 3*F*lambda^2*P := by
    have hh := mul_le_mul_of_nonneg_left hl2 (mul_nonneg hf0 hP)
    nlinarith only [hh]
  have hH' : lambda*H ≤ lambda*ell*H := by
    have hh := mul_le_mul_of_nonneg_left hell (mul_nonneg hl0 hH)
    nlinarith only [hh]
  have hp0 : 0 ≤ F*lambda^2*P := by positivity
  have hh0 : 0 ≤ lambda*ell*H := by positivity
  nlinarith only [hm,hd,hsa,hsr,hsg,hFP,hm',hr',hH',hp0,hh0]

/-- A whole-band estimate before L and E, retaining the exact factor 2^(2E+2). -/
theorem signed_aggregate_ledger_rate_eventually
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0<delta) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin*Real.log N ≤ (L+1 : ℝ) → (L+E+2 : ℝ) ≤ betaMax*Real.log N →
      1 ≤ (fullRate N L : ℝ) →
      ∀ C : ℕ, N+(L+E+1)≤C → ∀ mask : Finset ℕ,
      mask ⊆ Finset.Icc ⌈(N : ℝ)^delta⌉₊ N → (N : ℝ)/2≤mask.card →
      aggregateLedger C L E (hardCutoff N) mask ≤
        64*((fullRate N L : ℝ)*(1+max 0 (Real.log (2*(fullRate N L : ℝ))))*
          Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
          (2 : ℝ)^(2*E+2)*(fullRate N L : ℝ)^2*(N : ℝ)^(-(1/(3 : ℝ))+epsilon)) := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨Nm,hm⟩ := MacroscopicMarkedLedger.defect_cost_le_eventually betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  obtain ⟨Nc,hc⟩ := MacroscopicMarkedLedger.cutoff_costs_le_eventually hPNT betaMax eta hbetaMax heta
  obtain ⟨Na,ha⟩ := marked_diagonal_cost_le_eventually betaMax epsilon hbetaMax.le hepsilon
  obtain ⟨Nr,hr⟩ := MacroAggregateValueProfile.enlarged_valueWeightMass_le_eventually betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max 2 (max Nm (max Nc (max Na Nr))),?_⟩
  intro N hN L E hlo hhi hlam C hC mask hmask hcard
  have hbounded : mask ⊆ Finset.Icc 2 N := fun x hx =>
    MacroscopicArithmeticBounds.closed_macroscopic_subset_Icc (by omega) hdelta (hmask hx)
  have hcardle : (mask.card : ℝ)≤N := by
    have hc := Finset.card_le_card hbounded
    have hi : (Finset.Icc 2 N).card≤N := by simp only [Nat.card_Icc]; omega
    exact_mod_cast hc.trans hi
  have hmuHalf : (fullRate N L : ℝ)/2≤(maskRate L mask : ℝ) := by
    change (N : ℝ)/(2 : ℝ)^L/2≤(mask.card : ℝ)/(2 : ℝ)^L
    have hh := div_le_div_of_nonneg_right hcard (by positivity : (0 : ℝ)≤2^L)
    simpa only [div_div,mul_comm] using hh
  have hmuUpper : (maskRate L mask : ℝ)≤(fullRate N L : ℝ) := by
    exact div_le_div_of_nonneg_right hcardle (by positivity)
  have hlhi : (L+1 : ℝ) ≤ betaMax*Real.log N := by
    have hE : (0 : ℝ) ≤ E := by positivity
    linarith
  have hqhi : ((L+E+1 : ℕ)+1 : ℝ) ≤ betaMax*Real.log N := by push_cast; linarith
  have hqlo : betaMin*Real.log N ≤ (L+E+2 : ℝ) := by
    have hE : (0 : ℝ) ≤ E := by positivity
    linarith
  have hdef := hm N (by omega) L hlo hlhi mask hmask (1/(2 : ℝ)^L) (by positivity)
  obtain ⟨hbad,hedges⟩ := hc N (by omega) (L+E+1) hqhi mask hbounded
    (1/(2 : ℝ)^L) (by positivity)
  have hdiag := ha N (by omega) L (L+E+1) hqhi
  have hrelation := hr N (by omega) L E hqlo hhi C hC mask hmask
  have heq : (N : ℝ)*(1/(2 : ℝ)^L)=(fullRate N L : ℝ) := by simp only [fullRate_coe]; ring
  rw [heq] at hdef hbad hedges
  have hsd : signedDirectionalFactor (maskRate L mask)*(fullRate N L : ℝ) ≤
      24*(1+max 0 (Real.log (2*(fullRate N L : ℝ)))) := by
    have hpos : (0 : ℝ)<fullRate N L := by linarith
    exact (le_div_iff₀ hpos).mp (directional_factor_le_ambient hpos hmuHalf hmuUpper)
  have hdiag' : (1/(2 : ℝ)^L)^2*((mask.card : ℝ)*(L+E+2))≤
      (fullRate N L : ℝ)^2*(N : ℝ)^(-(1/(3 : ℝ))+epsilon) := by
    have hdiag0 : (1/(2 : ℝ)^L)^2*((N : ℝ)*(L+E+2))≤
        (fullRate N L : ℝ)^2*(N : ℝ)^(-(1/(3 : ℝ))+epsilon) := by
      convert hdiag using 1 <;> push_cast <;> ring
    apply le_trans _ hdiag0
    have hh : (mask.card : ℝ)*(L+E+2)≤(N : ℝ)*(L+E+2) := by gcongr
    exact mul_le_mul_of_nonneg_left hh (sq_nonneg (1/(2 : ℝ)^L))
  have hf : (1 : ℝ) ≤ (2 : ℝ)^(2*E+2) := one_le_pow₀ (by norm_num)
  have hn := signed_ledger_numeric_le
    (lambda := (fullRate N L : ℝ)) (ell := 1+max 0 (Real.log (2*(fullRate N L : ℝ))))
    (F := (2 : ℝ)^(2*E+2))
    (H := Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)))
    (P := (N : ℝ)^(-(1/(3 : ℝ))+epsilon))
    (m := (1/(2 : ℝ)^L)*(fullDefectMass L mask : ℝ))
    (a := (1/(2 : ℝ)^L)^2*((mask.card : ℝ)*(L+E+2)))
    hlam (by have h := le_max_left 0 (Real.log (2*(fullRate N L : ℝ))); linarith)
    hf (Real.exp_nonneg _) (Real.rpow_nonneg (by positivity) _)
    (signedDirectionalFactor_nonneg (maskRate L mask).coe_nonneg) (signedDirectionalFactor_le_one _) hsd
    (by simpa only [mul_comm] using hdef) hbad
    hdiag' hedges
    hrelation
  unfold aggregateLedger
  convert hn using 1; ring

end
end PaperC.V282.MacroAggregateRates
