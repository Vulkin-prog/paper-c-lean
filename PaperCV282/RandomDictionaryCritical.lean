import PaperCV282.RandomDictionaryOverlap
import PaperCV282.DictionaryCriticalWindow
import PaperCV282.DictionaryFieldCritical

/-!
# The exceptional fraction in the critical dictionary window

The auxiliary uniform law is on the actual subsets of prescribed cardinality.
Its exceptional fraction is controlled before selecting any dictionary, and
all remaining dictionaries receive the already proved actual-field estimate.
-/
namespace PaperC.V282.RandomDictionaryCritical

open Filter Topology RandomDictionary RandomDictionaryOverlap WordOverlapSum
open DictionaryCriticalWindow CriticalRunWindow DictionaryFieldCritical
open DictionaryFieldInfinite DictionaryRateConvergence HardPoissonRates
open SaddleParameters SaddleScales PrimeEulerPNT ProcessAGGInput

noncomputable section

/-- The exact Markov bound at the manuscript's threshold, expressed via the true intensity. -/
theorem exceptional_fraction_le_intensity {N B m : ℕ} {K : ℝ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmB : m ≤ 2^B)
    (hlambda : (N : ℝ) * m / (2 : ℝ)^B ≤ K) :
    dictionaryFraction B m (fun W => (N : ℝ)^(-(1 / (2 : ℝ))) < overlapWeight W) ≤
      K * (B : ℝ) * (N : ℝ)^(-(1 / (2 : ℝ))) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let t := (N : ℝ)^(-(1 / (2 : ℝ)))
  have ht : 0 < t := Real.rpow_pos_of_pos hn _
  have htt : t*t = (N : ℝ)⁻¹ := by
    dsimp [t]
    rw [← Real.rpow_add hn]
    norm_num [Real.rpow_neg_one]
  have hNtt : (N : ℝ)*t*t=1 := by
    rw [mul_assoc,htt,mul_inv_cancel₀ hn.ne']
  have heq : ((m : ℝ) * (B-1 : ℕ) / (2 : ℝ)^B) / t =
      ((N : ℝ)*m/(2 : ℝ)^B) * (B-1 : ℕ) * t := by
    apply (div_eq_iff ht.ne').mpr
    calc
      _ = ((m : ℝ) * (B-1 : ℕ) / (2 : ℝ)^B) * ((N : ℝ)*t*t) := by rw [hNtt,mul_one]
      _ = _ := by ring
  have h := dictionaryFraction_overlapWeight_gt_le hm hmB ht
  rw [heq] at h
  have hK : 0 ≤ K := (by positivity : 0 ≤ (N : ℝ)*m/(2 : ℝ)^B).trans hlambda
  have hb : ((B-1 : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast Nat.sub_le B 1
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hlambda hb (by positivity) hK) ht.le)

/-- Corollary 5.3's exceptional-fraction bound, with a constant independent of B and m. -/
theorem corollary_five_three_exceptional_fraction (C delta : ℝ) (hdelta : 0 < delta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ B m : ℕ, 1 ≤ m → m ≤ 2^B →
      (m : ℝ) ≤ (N : ℝ)^(1 / 2 - delta) →
      |(B : ℝ) - Real.log ((N : ℝ)*m) / Real.log 2| ≤ C →
      dictionaryFraction B m (fun W => (N : ℝ)^(-(1 / (2 : ℝ))) < overlapWeight W) ≤
        (Real.exp (C * Real.log 2) * upperConstant) * Real.log N / (N : ℝ)^(1 / (2 : ℝ)) := by
  obtain ⟨Nzero,hzero⟩ := dictionary_critical_log_band_eventually C
  refine ⟨max Nzero 2,?_⟩
  intro N hN B m hm hmB hcard hwindow
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmhalf : (m : ℝ) ≤ (N : ℝ)^(1 / (2 : ℝ)) :=
    hcard.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hband := (hzero N (by omega) m hmone hmhalf B hwindow).2
  have hlambda := (dictionary_intensity_bounds hn hmpos hwindow).2
  have hfrac := exceptional_fraction_le_intensity (by omega : 0 < N) hm hmB hlambda
  apply hfrac.trans
  calc
    _ ≤ Real.exp (C * Real.log 2) * (upperConstant * Real.log N) * (N : ℝ)^(-(1 / (2 : ℝ))) := by
      gcongr
    _ = _ := by rw [Real.rpow_neg hn.le]; ring

/-- All deterministic dictionaries outside that actual exceptional event obey the field rate. -/
theorem nonexceptional_dictionary_field_rate (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C delta eta : ℝ)
    (hdelta : 0 < delta) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L m : ℕ, 1 ≤ m →
      (m : ℝ) ≤ (N : ℝ)^(1 / 2 - delta) →
      |(L+1 : ℝ) - Real.log ((N : ℝ)*m) / Real.log 2| ≤ C →
      ∀ W ∈ dictionaries (L+1) m,
      ¬(N : ℝ)^(-(1 / (2 : ℝ))) < overlapWeight W →
      dictionaryConditionalDistance N L (hardCutoff N) W ≤
        8 * criticalDictionaryConstant (Real.exp (C * Real.log 2)) *
          ((N : ℝ)^(-(1 / (2 : ℝ))) +
            Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) +
            (N : ℝ)^(-(delta / 2))) ∧
      dictionaryDistance N L W ≤
        8 * criticalDictionaryConstant (Real.exp (C * Real.log 2)) *
          ((N : ℝ)^(-(1 / (2 : ℝ))) +
            Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) +
            (N : ℝ)^(-(delta / 2))) := by
  obtain ⟨Nzero,hzero⟩ := equation_five_four hAGG hPNT C delta eta hdelta heta
  refine ⟨Nzero,?_⟩
  intro N hN L m hm hcard hwindow W hW hnot
  have hc : W.card = m := (mem_dictionaries W).mp hW
  have hw : W.Nonempty := Finset.card_pos.mp (by omega)
  have hfields := hzero N hN L W hw (by simpa only [hc] using hcard) (by simpa only [hc] using hwindow)
  have hcoef : 0 ≤ 8 * criticalDictionaryConstant (Real.exp (C * Real.log 2)) :=
    mul_nonneg (by norm_num) (criticalDictionaryConstant_nonneg (Real.exp_nonneg _))
  have hbound : 8 * criticalDictionaryConstant (Real.exp (C * Real.log 2)) *
        (overlapWeight W + Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) +
          (N : ℝ)^(-(delta / 2))) ≤
      8 * criticalDictionaryConstant (Real.exp (C * Real.log 2)) *
        ((N : ℝ)^(-(1 / (2 : ℝ))) +
          Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) +
          (N : ℝ)^(-(delta / 2))) := by
    apply mul_le_mul_of_nonneg_left _ hcoef
    linarith [le_of_not_gt hnot]
  exact ⟨hfields.1.trans hbound,hfields.2.trans hbound⟩

end
end PaperC.V282.RandomDictionaryCritical
