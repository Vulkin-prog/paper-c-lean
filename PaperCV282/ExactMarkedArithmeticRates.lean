import PaperCV282.ExactMarkedLedger
import PaperCV282.DictionaryArithmeticRates

/-!
# The marked arithmetic ledger at its two actual lengths

The base length controls the defect and relation masses. The maximal
length controls deletion, graph edges, and local neighbours. The threshold
is uniform before the base length and the excess truncation.
-/
namespace PaperC.V282.ExactMarkedArithmeticRates

open ExactMarkedLedger DictionaryArithmeticRates FullBandArithmetic
open MaskedArithmeticGeometry MaskedPairGeometry SectionTwelveMoments TwoWindowParity
open HardPoissonRates SaddleParameters SaddleScales PrimeEulerPNT AllStartSoftPoisson
open LogarithmicWordPowers

noncomputable section

/-- The maximal local radius is absorbed without changing the base intensity. -/
theorem marked_diagonal_cost_le_eventually (betaMax epsilon : ℝ)
    (hbeta : 0 ≤ betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L Q : ℕ,
      (Q+1 : ℝ) ≤ betaMax*Real.log N →
      (1/(2 : ℝ)^L)^2*(N : ℝ)*(Q+1) ≤
        (N : ℝ)^(-(1/(3 : ℝ))+epsilon)*(fullRate N L : ℝ)^2 := by
  obtain ⟨Nzero,hzero⟩ := polynomial_factor_le_rpow_eventually betaMax hbeta 1 1 epsilon hepsilon
  refine ⟨max Nzero 1,?_⟩
  intro N hN L Q hQ
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hone : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hlength : (Q+1 : ℝ)≤(N : ℝ)^epsilon := by
    simpa only [one_mul,pow_one,abs_of_nonneg (by positivity : (0 : ℝ)≤Q+1)] using
      hzero N (by omega) Q (by simpa using hQ)
  have hscale : (Q+1 : ℝ)/(N : ℝ)≤(N : ℝ)^(-(1/(3 : ℝ))+epsilon) := by
    calc
      _ ≤ (N : ℝ)^epsilon/(N : ℝ) := div_le_div_of_nonneg_right hlength hn.le
      _ = (N : ℝ)^(epsilon-1) := by rw [Real.rpow_sub hn,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hone (by linarith)
  calc
    _ = (fullRate N L : ℝ)^2*((Q+1 : ℝ)/(N : ℝ)) := by
      simp only [fullRate_coe]
      field_simp
    _ ≤ (fullRate N L : ℝ)^2*(N : ℝ)^(-(1/(3 : ℝ))+epsilon) :=
      mul_le_mul_of_nonneg_left hscale (sq_nonneg _)
    _ = _ := by ring

/-- A universal constant combines the five separately proved arithmetic costs. -/
theorem ledger_numeric_bound {p lambda H R M D A G T : ℝ}
    (hlambda : 0 ≤ lambda) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hm : p*M ≤ lambda*R) (hd : p*D ≤ lambda*H)
    (ha : p^2*A ≤ lambda^2*R) (hg : p^2*G ≤ lambda^2*H)
    (ht : p^2*T ≤ R*(lambda^2+2*lambda)) :
    p*(M+2*D)+p^2*(20*A+4*G+2*T) ≤
      32*lambda*(1+lambda)*(H+R) := by
  have hsum := add_le_add (add_le_add hm (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ)≤2)))
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ)≤20))
      (mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ)≤4)))
      (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ)≤2)))
  have hpad : 0 ≤ (30*lambda+28*lambda^2)*H+(27*lambda+10*lambda^2)*R := by positivity
  nlinarith only [hsum,hpad]

/-- The full marked ledger, with the literal base and maximal supports, throughout the whole band. -/
theorem exact_marked_arithmetic_rate_eventually
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin*Real.log N ≤ (L+1 : ℝ) → (L+E+2 : ℝ) ≤ betaMax*Real.log N →
      exactMarkedLedger N L E (hardCutoff N) (dyadicBlock N) ≤
        32*(fullRate N L : ℝ)*(1+(fullRate N L : ℝ))*
          (Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
            (N : ℝ)^(-(1/(3 : ℝ))+epsilon)) := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨Nm,hm⟩ := dictionary_defect_cost_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Nc,hc⟩ := dictionary_cutoff_costs_le_eventually hPNT betaMax eta hbetaMax heta
  obtain ⟨Na,ha⟩ := marked_diagonal_cost_le_eventually betaMax epsilon hbetaMax.le hepsilon
  obtain ⟨Nr,hr⟩ := normalized_relation_mass_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max 1 (max Nm (max Nc (max Na Nr))),?_⟩
  intro N hN L E hlo hhi
  have hlhi : (L+1 : ℝ)≤betaMax*Real.log N := by
    have hE : (0 : ℝ)≤E := by positivity
    linarith
  have hqhi : ((L+E+1 : ℕ)+1 : ℝ)≤betaMax*Real.log N := by
    push_cast
    linarith
  have hdef := hm N (by omega) L hlo hlhi (dyadicBlock N) (Finset.Subset.refl _)
    (1/(2 : ℝ)^L) (by positivity)
  obtain ⟨hbad,hedges⟩ := hc N (by omega) (L+E+1) hqhi (dyadicBlock N) (Finset.Subset.refl _)
    (1/(2 : ℝ)^L) (by positivity)
  have hdiag := ha N (by omega) L (L+E+1) hqhi
  have hrelation := hr N (by omega) L hlo hlhi
  have hlam : (N : ℝ)*(1/(2 : ℝ)^L)=(fullRate N L : ℝ) := by simp only [fullRate_coe];ring
  rw [hlam] at hdef hbad hedges
  have hm' : (1/(2 : ℝ)^L)*(fullDefectMass L (dyadicBlock N) : ℝ) ≤
      (fullRate N L : ℝ)*(N : ℝ)^(-(1/(3 : ℝ))+epsilon) := by simpa only [mul_comm] using hdef
  have ha' : (1/(2 : ℝ)^L)^2*((N : ℝ)*(L+E+2)) ≤
      (fullRate N L : ℝ)^2*(N : ℝ)^(-(1/(3 : ℝ))+epsilon) := by
    convert hdiag using 1 <;> push_cast <;> ring
  have ht' : (1/(2 : ℝ)^L)^2*(jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ) ≤
      (N : ℝ)^(-(1/(3 : ℝ))+epsilon)*((fullRate N L : ℝ)^2+2*(fullRate N L : ℝ)) := by
    convert hrelation using 1
    rw [Nat.mul_comm 2 L,pow_mul]
    ring
  unfold exactMarkedLedger
  convert ledger_numeric_bound (by positivity : (0 : ℝ)≤(fullRate N L : ℝ))
    (Real.exp_nonneg _) (Real.rpow_nonneg (by positivity) _) hm' hbad ha' hedges ht' using 1
  ring

end
end PaperC.V282.ExactMarkedArithmeticRates
