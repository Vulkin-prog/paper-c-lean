import PaperCPrel8.TypicalDictionaryTheorem
import PaperCV282.IidWordComparison

/-! # Comparison with the genuine independent-sign word field after selection averaging -/
namespace PaperC.Prel8.TypicalDictionaryIid
open PaperC.V282.RandomDictionary PaperC.V282.RandomDictionaryOverlap
open PaperC.V282.DictionaryFieldModel PaperC.V282.WordOverlapSum
open PaperC.V282.IidWordPoisson PaperC.V282.IidWordComparison PaperC.V282.IidWordInfinite
open PaperC.V282.DictionaryFieldInfinite PaperC.V282.FiniteFieldTotalVariation
open PaperC.V282.ProcessAGGInput
open PaperC.Prel8.DictionaryAverage PaperC.Prel8.TypicalDictionaryTheorem
noncomputable section

/-- The iid Poisson cost averaged over dictionaries is at most 8*a^2*N*B. -/
theorem averaged_iid_poisson_le (hAGG : ProcessAGGStatement) {N L m : ℕ}
    (hN : 1 ≤ N) (hm : 1 ≤ m) (hmb : m ≤ 2^(L+1)) :
    dictionaryAverage (L+1) m (iidPoissonDistance N L) ≤
      8*((m:ℝ)/(2:ℝ)^(L+1))^2*(N:ℝ)*(L+1:ℝ) := by
  have h := average_mono (B := L+1) (m := m) (f := iidPoissonDistance N L)
    (g := fun W => 4*((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1))*overlapWeight W+
      (N:ℝ)*(L+1:ℝ)*((m:ℝ)/(2:ℝ)^(L+1))^2)) (fun W hW => by
    have hc := (mem_dictionaries W).mp hW
    have hw : W.Nonempty := Finset.card_pos.mp (by rw [hc]; omega)
    simpa only [dictionaryRate_coe,hc] using iidPoissonDistance_le hAGG W hw hN)
  simp only [average_mul,average_add,average_const _ _ hmb,average_overlapWeight_eq hm hmb,
    Nat.add_sub_cancel] at h
  have he : (N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1))*((m:ℝ)*L/(2:ℝ)^(L+1)) =
      ((m:ℝ)/(2:ℝ)^(L+1))^2*(N:ℝ)*L := by ring
  nlinarith [he,mul_nonneg (sq_nonneg ((m:ℝ)/(2:ℝ)^(L+1))) (Nat.cast_nonneg N)]

/-- The two genuine infinite fields share their Poisson target before averaging distances. -/
theorem averaged_arithmetic_iid_le (hAGG : ProcessAGGStatement) {N L Y m : ℕ}
    (hN : 1 ≤ N) (hm : 1 ≤ m) (hmb : m ≤ 2^(L+1)) {r : ℝ}
    (hr : dictionaryAverage (L+1) m (dictionaryConditionalDistance N L Y) ≤ r) :
    dictionaryAverage (L+1) m (fun W =>
      massTotalVariation (infiniteDictionaryLaw N L W) (infiniteIidFieldLaw N L W)) ≤
      r+8*((m:ℝ)/(2:ℝ)^(L+1))^2*(N:ℝ)*(L+1:ℝ) := by
  have h := average_mono (fun W (_ : W ∈ dictionaries (L+1) m) => dictionary_iid_distance_le N L W)
  rw [average_add] at h
  exact h.trans (add_le_add (mean_unconditional_le hr) (averaged_iid_poisson_le hAGG hN hm hmb))

/-- The displayed iid remainder is precisely O(Lambda^2*B/N). -/
theorem iid_remainder_normalized {N L m : ℕ} (hN : 0 < N) :
    8*((m:ℝ)/(2:ℝ)^(L+1))^2*(N:ℝ)*(L+1:ℝ) =
      8*((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))^2*(L+1:ℝ)/(N:ℝ) := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  field_simp

end
end PaperC.Prel8.TypicalDictionaryIid
