import PaperCV282.IidWordPoisson
import PaperCV282.DictionaryFieldCritical
import PaperCV282.DictionaryCountTargets

/-!
# Corollary 5.2: replacement by independent signs

Both actual infinite fields are compared with the identical labelled product
Poisson law. All thresholds precede the varying dictionaries. The final vector
of word counts uses the proved independent Poisson column-sum target.
-/
namespace PaperC.V282.IidWordComparison

open Filter Topology IidWordField IidWordInfinite IidWordPoisson
open DictionaryFieldModel DictionaryFieldTransfer DictionaryFieldInfinite DictionaryFieldCritical
open DictionaryCriticalWindow DictionaryCountTargets WordOverlapSum CriticalRunWindow
open PrimeEulerPNT ProcessAGGInput FiniteFieldTotalVariation FiniteFieldPoissonCoupling
open InfiniteRademacher SectionTwelveMoments

noncomputable section

/-- A concrete vanishing iid error throughout the growing-dictionary critical window. -/
theorem iid_critical_bound_eventually (hAGG : ProcessAGGStatement)
    (C delta : ℝ) (hdelta : 0 < delta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      ∀ W : Finset (Fin (L+1) → F₂), W.Nonempty →
      (W.card : ℝ) ≤ (N : ℝ) ^ (1/2-delta) →
      |(L+1 : ℝ) - Real.log ((N : ℝ)*W.card) / Real.log 2| ≤ C →
      iidPoissonDistance N L W ≤
        4 * (Real.exp (C*Real.log 2) * overlapWeight W +
          (Real.exp (C*Real.log 2))^2 * upperConstant * (Real.log N / N)) := by
  obtain ⟨Nb,hb⟩ := dictionary_critical_log_band_eventually C
  refine ⟨max Nb 2, ?_⟩
  intro N hN L W hW hcard hwindow
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hm : (1 : ℝ) ≤ W.card := by exact_mod_cast Finset.card_pos.mpr hW
  have hmpos : (0 : ℝ) < W.card := by linarith
  have hmhalf : (W.card : ℝ) ≤ (N : ℝ) ^ (1/(2 : ℝ)) :=
    hcard.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hw : |((L+1 : ℕ) : ℝ) - Real.log ((N : ℝ)*W.card) / Real.log 2| ≤ C := by
    simpa only [Nat.cast_add,Nat.cast_one] using hwindow
  have hB := (hb N (by omega) W.card hm hmhalf (L+1) hw).2
  have hLambda : (N : ℝ) * (dictionaryRate L W : ℝ) ≤ Real.exp (C*Real.log 2) := by
    simpa only [dictionaryRate_coe,mul_div_assoc] using (dictionary_intensity_bounds hn hmpos hw).2
  have ho := overlapWeight_nonneg W
  have hnon : 0 ≤ (N : ℝ) * (dictionaryRate L W : ℝ) := by positivity
  calc
    iidPoissonDistance N L W ≤ 4 * (((N : ℝ) * (dictionaryRate L W : ℝ)) * overlapWeight W +
        ((N : ℝ) * (dictionaryRate L W : ℝ))^2 * (L+1 : ℝ) / N) :=
      iidPoissonDistance_le_normalized hAGG W hW (by omega)
    _ ≤ 4 * (Real.exp (C*Real.log 2) * overlapWeight W +
        (Real.exp (C*Real.log 2))^2 * (upperConstant * Real.log N) / N) := by
      gcongr
      exact_mod_cast hB
    _ = _ := by ring

/-- The actual iid field converges to the same product Poisson target under (5.3). -/
theorem iid_field_critical_convergence (hAGG : ProcessAGGStatement) (C delta : ℝ) (hdelta : 0 < delta)
    (L : ℕ → ℕ) (W : ∀ N : ℕ, Finset (Fin (L N+1) → F₂))
    (hcritical : ∀ᶠ N : ℕ in atTop, (W N).Nonempty ∧
      ((W N).card : ℝ) ≤ (N : ℝ) ^ (1/2-delta) ∧
      |(L N+1 : ℝ) - Real.log ((N : ℝ)*(W N).card) / Real.log 2| ≤ C)
    (hoverlap : Tendsto (fun N => overlapWeight (W N)) atTop (𝓝 0)) :
    Tendsto (fun N => iidPoissonDistance N (L N) (W N)) atTop (𝓝 0) := by
  obtain ⟨Nzero,hzero⟩ := iid_critical_bound_eventually hAGG C delta hdelta
  have hlog : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ =>
      4 * (Real.exp (C*Real.log 2) * overlapWeight (W N) +
        (Real.exp (C*Real.log 2))^2 * upperConstant * (Real.log N / N))) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      ((hoverlap.const_mul (Real.exp (C*Real.log 2))).add
        (hlog.const_mul ((Real.exp (C*Real.log 2))^2 * upperConstant))).const_mul 4
  apply squeeze_zero' (Filter.Eventually.of_forall fun N => iidPoissonDistance_nonneg _ _ _) _ hlim
  filter_upwards [hcritical,eventually_ge_atTop Nzero] with N hc hn
  exact hzero N hn (L N) (W N) hc.1 hc.2.1 hc.2.2

/-- Exact common-target triangulation of the two actual infinite field laws. -/
theorem dictionary_iid_distance_le (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    massTotalVariation (infiniteDictionaryLaw N L W) (infiniteIidFieldLaw N L W) ≤
      dictionaryDistance N L W + iidPoissonDistance N L W := by
  rw [infiniteIidFieldLaw_eq_iidFieldLaw]
  have h := massTotalVariation_triangle (hasSum_infiniteDictionaryLaw N L W).summable
    (summable_poissonFieldMass (allWordRates N L W (dyadicBlock N))) (hasSum_iidFieldLaw N L W).summable
    (infiniteDictionaryLaw_nonneg N L W) (poissonFieldMass_nonneg _) (iidFieldLaw_nonneg N L W)
  rw [massTotalVariation_comm (poissonFieldMass _) (iidFieldLaw N L W)] at h
  exact h

/-- Corollary 5.2 for the complete site-and-word-labelled fields of the two real source models. -/
theorem corollary_five_two (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (C delta : ℝ) (hdelta : 0 < delta) (L : ℕ → ℕ)
    (W : ∀ N : ℕ, Finset (Fin (L N+1) → F₂))
    (hcritical : ∀ᶠ N : ℕ in atTop, (W N).Nonempty ∧
      ((W N).card : ℝ) ≤ (N : ℝ) ^ (1/2-delta) ∧
      |(L N+1 : ℝ) - Real.log ((N : ℝ)*(W N).card) / Real.log 2| ≤ C)
    (hoverlap : Tendsto (fun N => overlapWeight (W N)) atTop (𝓝 0)) :
    Tendsto (fun N => massTotalVariation
      (infiniteDictionaryLaw N (L N) (W N)) (infiniteIidFieldLaw N (L N) (W N))) atTop (𝓝 0) := by
  have hm := (dictionary_field_critical_convergence hAGG hPNT C delta hdelta L W hcritical hoverlap).2
  have hi := iid_field_critical_convergence hAGG C delta hdelta L W hcritical hoverlap
  have hlim := hm.add hi
  simp only [add_zero] at hlim
  exact squeeze_zero' (Filter.Eventually.of_forall fun N => massTotalVariation_nonneg _ _)
    (Filter.Eventually.of_forall fun N => dictionary_iid_distance_le N (L N) (W N)) hlim

/-- The vector of actual individual-word counts converges to the stated independent Poisson vector. -/
theorem corollary_five_two_word_counts (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (C delta : ℝ) (hdelta : 0 < delta) (L : ℕ → ℕ)
    (W : ∀ N : ℕ, Finset (Fin (L N+1) → F₂))
    (hcritical : ∀ᶠ N : ℕ in atTop, (W N).Nonempty ∧
      ((W N).card : ℝ) ≤ (N : ℝ) ^ (1/2-delta) ∧
      |(L N+1 : ℝ) - Real.log ((N : ℝ)*(W N).card) / Real.log 2| ≤ C)
    (hoverlap : Tendsto (fun N => overlapWeight (W N)) atTop (𝓝 0)) :
    Tendsto (fun N => massTotalVariation
      (fun b => (infiniteRademacherMeasure {omega |
        dictionaryWordCounts (W N) (infiniteDictionaryField N (L N) (W N) omega) = b}).toReal)
      (poissonFieldMass (fun _ : {b // b ∈ W N} => individualWordCountRate N (L N)))) atTop (𝓝 0) := by
  have hm := (dictionary_field_critical_convergence hAGG hPNT C delta hdelta L W hcritical hoverlap).2
  exact squeeze_zero' (Filter.Eventually.of_forall fun N => massTotalVariation_nonneg _ _)
    (Filter.Eventually.of_forall fun N => infinite_dictionary_word_counts_distance_le N (L N) (W N)) hm

end
end PaperC.V282.IidWordComparison
