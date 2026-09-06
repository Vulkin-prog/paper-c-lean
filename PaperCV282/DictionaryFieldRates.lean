import PaperCV282.DictionaryFieldBounds
import PaperCV282.DictionaryFieldInfinite
import PaperCV282.DictionaryRateConvergence
import PaperCV282.SaddleCutoffAdmissibility

/-!
# Theorem 5.1 on the full logarithmic band

The finite process comparison and all arithmetic inputs are instantiated
on the actual labelled field. The threshold precedes the dictionary as
well as its length and cardinality. The exponential remainder is quantified
by every positive eta, uniformly in the dictionary.
-/

namespace PaperC.V282.DictionaryFieldRates

open MeasureTheory Set DictionaryFieldInfinite DictionaryFieldBounds DictionaryFieldModel
open DictionaryFieldTransfer DictionaryErrorLedger DictionaryRateConvergence WordOverlapSum
open HardPoissonRates SaddleCutoffAdmissibility PrimeEulerPNT ProcessAGGInput
open ConditionalStartProbability ConditionalAGGAverage InfiniteConditionalWords
open InfiniteCylinderTransfer SectionTwelveMoments FiniteFieldPoissonCoupling FiniteFieldTotalVariation

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- The exact three-term dictionary error evaluated at its real cardinality and intensity. -/
def dictionaryFieldRate (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) (epsilon eta : ℝ) : ℝ :=
  dictionaryError N ((N : ℝ)*(dictionaryRate L W : ℝ)) W.card (overlapWeight W) epsilon eta

/-- Every coordinate of the target field has the prescribed B-bit intensity. -/
theorem allWordRates_full_eq (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    allWordRates N L W (dyadicBlock N) = fun _ => wordRate L := by
  funext i
  simp [allWordRates,i.1.property]

/-- Equation (5.7) already compares the true conditional cylinder law. -/
theorem dictionaryConditionalDistance_le_ledger (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (W : Finset (Fin (L+1) → F₂)) (hW : W.Nonempty)
    (hN : 2 ≤ N) (hY : 2*(L+1) ≤ Y) :
    dictionaryConditionalDistance N L Y W ≤
      dictionaryArithmeticLedger N L Y (dictionaryRate L W : ℝ) (overlapWeight W) := by
  unfold dictionaryConditionalDistance
  simp_rw [conditionalDictionaryLaw_at_dyadic]
  exact equation_five_seven hAGG W hW hN hY

/-- A single threshold supplies the full-band field rate and the full prime cylinder. -/
theorem dictionary_conditional_rate_eventually (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ betaMax * Real.log N →
      hardCutoff N ≤ dyadicCutoff N L ∧
      ∀ W : Finset (Fin (L+1) → F₂), W.Nonempty →
        dictionaryConditionalDistance N L (hardCutoff N) W ≤ 8 * dictionaryFieldRate N L W epsilon eta := by
  have hbpos : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨Nr,hr⟩ := dictionary_ledger_hard_rate_eventually hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  obtain ⟨Na,ha⟩ := saddleCutoff_nat_admissible_eventually 1 (2*betaMax) (by norm_num) (by positivity)
  obtain ⟨Nu,hu⟩ := saddleCutoff_nat_admissible_eventually 1 betaMax (by norm_num) hbpos
  refine ⟨max Nr (max Na (max Nu 2)), ?_⟩
  intro N hN L hlo hhi
  have hhi' : (L+1+1 : ℝ) ≤ (2*betaMax)*Real.log N := by nlinarith
  have hlarge := (ha N (by omega) (L+1) (by exact_mod_cast hhi')).2.2.1
  have hupper := (hu N (by omega) L hhi).2.2.2
  refine ⟨hupper, ?_⟩
  intro W hW
  have hm : (0 : ℝ) < W.card := by exact_mod_cast Finset.card_pos.mpr hW
  have hfinite := dictionaryConditionalDistance_le_ledger hAGG (N := N) W hW (by omega) hlarge
  have harith := hr N (by omega) L hlo hhi W.card (overlapWeight W) hm (overlapWeight_nonneg W)
  rw [← dictionaryRate_coe] at harith
  exact hfinite.trans harith

/-- Equation (5.2), for both the true full-F_Y conditional average and the unconditional field. -/
theorem theorem_five_one_full_band (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ betaMax * Real.log N →
      smallPrimeSigmaAlgebra (dyadicCutoff N L) (hardCutoff N) =
        MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance ∧
      ∀ W : Finset (Fin (L+1) → F₂), W.Nonempty →
        dictionaryConditionalDistance N L (hardCutoff N) W ≤ 8 * dictionaryFieldRate N L W epsilon eta ∧
        dictionaryDistance N L W ≤ 8 * dictionaryFieldRate N L W epsilon eta := by
  obtain ⟨Nzero,hzero⟩ := dictionary_conditional_rate_eventually hAGG hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  refine ⟨Nzero, ?_⟩
  intro N hN L hlo hhi
  obtain ⟨hcut,hbound⟩ := hzero N hN L hlo hhi
  refine ⟨smallPrimeSigmaAlgebra_eq_primeCylinder hcut, ?_⟩
  intro W hW
  exact ⟨hbound W hW,(dictionaryDistance_le_conditionalDistance N L (hardCutoff N) W).trans (hbound W hW)⟩

end
end PaperC.V282.DictionaryFieldRates
