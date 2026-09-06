import PaperCV282.DictionaryArithmeticRates

/-!
# Uniform assembly of the actual dictionary arithmetic ledger

The positive multiplicative constants are explicit. The first-moment,
edge and capped-pair quantities are the actual populations already proved
in the preceding modules. No probability comparison is assumed here.
-/

namespace PaperC.V282.DictionaryErrorLedger

open DictionaryProfileNormalization DictionaryArithmeticRates
open PrimeEulerPNT HardPoissonRates SaddleParameters SaddleScales
open MaskedArithmeticGeometry MaskedPairGeometry CappedRelationMass TwoWindowParity
open SectionTwelveMoments

noncomputable section

/-- The right-hand side of the dictionary rate, with a quantified exponential remainder. -/
def dictionaryError (N : ℕ) (lambda m omega epsilon eta : ℝ) : ℝ :=
  lambda * omega + lambda * (1 + lambda) *
      Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) +
    (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) * dictionaryPolynomialProfile lambda m

/-- The finite arithmetic error from deletion and the labelled process comparison. -/
def dictionaryArithmeticLedger (N L Y : ℕ) (a omega : ℝ) : ℝ :=
  a * ((fullDefectMass L (dyadicBlock N) : ℝ) + 2 * ((fullBadStarts N L Y).card : ℝ)) +
    4 * a ^ 2 * ((N : ℝ) * (L + 1 : ℝ) +
      ((maskedSupportEdges L Y (dyadicBlock N)).card : ℝ) +
      cappedValueMass (dyadicCutoff N L) L (1 / a) (separatedPairs (dyadicBlock N) L)) +
    4 * ((N : ℝ) * a) * omega

theorem dictionaryError_nonneg (N : ℕ) {lambda m omega epsilon eta : ℝ}
    (hlambda : 0 ≤ lambda) (hm : 0 ≤ m) (homega : 0 ≤ omega) :
    0 ≤ dictionaryError N lambda m omega epsilon eta := by
  unfold dictionaryError
  have hp := dictionaryPolynomialProfile_nonneg hlambda hm
  positivity

/-- Numerical addition keeps a single absolute constant for all three error scales. -/
theorem ledger_assembly {a N M D E R B omega P e m : ℝ}
    (ha : 0 ≤ a) (hN : 0 ≤ N) (homega : 0 ≤ omega) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hm : 0 ≤ m)
    (hM : a * M ≤ P * (N * a))
    (hD : a * D ≤ (N * a) * e)
    (hE : a ^ 2 * E ≤ (N * a) ^ 2 * e)
    (hB : a ^ 2 * N * B ≤ P * ((N * a) ^ (4 / (3 : ℝ)) * m ^ (2 / (3 : ℝ))))
    (hR : a ^ 2 * R ≤ P * dictionaryPolynomialProfile (N * a) m) :
    a * (M + 2 * D) + 4 * a ^ 2 * (N * B + E + R) + 4 * (N * a) * omega ≤
      8 * ((N * a) * omega + (N * a) * (1 + N * a) * e +
        P * dictionaryPolynomialProfile (N * a) m) := by
  have hfirst : 0 ≤ (N * a) ^ (11 / (6 : ℝ)) * m ^ (1 / (6 : ℝ)) := by positivity
  have hthird : 0 ≤ (N * a) ^ (4 / (3 : ℝ)) * m ^ (2 / (3 : ℝ)) := by positivity
  have hmean : 0 ≤ N * a := mul_nonneg hN ha
  have hpfirst := mul_nonneg hP hfirst
  have hpthird := mul_nonneg hP hthird
  have hpmean := mul_nonneg hP hmean
  have hemean := mul_nonneg he hmean
  have hesquare := mul_nonneg he (sq_nonneg (N * a))
  have hoverlap := mul_nonneg hmean homega
  unfold dictionaryPolynomialProfile at *
  nlinarith

/-- The literal finite ledger has the printed full-band rate, uniformly before m and Omega. -/
theorem dictionary_ledger_hard_rate_eventually
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ m omega : ℝ, 0 < m → 0 ≤ omega →
      dictionaryArithmeticLedger N L (hardCutoff N) (m / (2 : ℝ) ^ (L + 1)) omega ≤
        8 * dictionaryError N ((N : ℝ) * (m / (2 : ℝ) ^ (L + 1))) m omega epsilon eta := by
  obtain ⟨Nr,hr⟩ := dictionary_capped_mass_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Nm,hm⟩ := dictionary_defect_cost_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Nb,hb⟩ := dictionary_diagonal_length_le_eventually betaMax epsilon (hbetaMin.trans hbeta).le hepsilon
  obtain ⟨Nc,hc⟩ := dictionary_cutoff_costs_le_eventually hPNT betaMax eta (hbetaMin.trans hbeta) heta
  refine ⟨max Nr (max Nm (max Nb (max Nc 1))), ?_⟩
  intro N hN L hlo hhi m omega hmpos homega
  let a : ℝ := m / (2 : ℝ) ^ (L + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ham : a ≤ m := div_le_self hmpos.le (one_le_pow₀ (by norm_num))
  have hn : (0 : ℝ) ≤ N := by positivity
  have hcap := hr N (by omega) L hlo hhi _ (Finset.Subset.refl _) m hmpos
  have hdef := hm N (by omega) L hlo hhi _ (Finset.Subset.refl _) a ha.le
  have hdiag := hb N (by omega) L hhi a m ha ham
  obtain ⟨hbad,hedge⟩ := hc N (by omega) L hhi _ (Finset.Subset.refl _) a ha.le
  have hmask : fullBadMask N L (hardCutoff N) (dyadicBlock N) = fullBadStarts N L (hardCutoff N) :=
    Finset.inter_eq_right.mpr (fullBadStarts_subset_block N L _)
  rw [hmask] at hbad
  exact ledger_assembly ha.le hn homega (Real.rpow_nonneg hn _) (Real.exp_nonneg _)
    hmpos.le hdef hbad hedge hdiag hcap

end
end PaperC.V282.DictionaryErrorLedger
