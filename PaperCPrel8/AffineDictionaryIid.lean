import PaperCPrel8.AffineDictionaryExceptional
import PaperCPrel8.TypicalDictionaryIid
import PaperCV282.IidWordComparison

/-! # Comparison with the genuine independent-sign word field after selection averaging -/
namespace PaperC.Prel8.AffineDictionaryIid
open PaperC.V282.RandomDictionary PaperC.V282.RandomDictionaryOverlap
open PaperC.V282.DictionaryFieldModel PaperC.V282.WordOverlapSum
open PaperC.V282.IidWordPoisson PaperC.V282.IidWordComparison PaperC.V282.IidWordInfinite
open PaperC.V282.DictionaryFieldInfinite PaperC.V282.FiniteFieldTotalVariation
open PaperC.V282.ProcessAGGInput
open PaperC.Prel8.AffineDictionarySample PaperC.Prel8.AffineDictionaryInclusion
open PaperC.Prel8.AffineDictionaryMoments PaperC.Prel8.AffineDictionaryCosts
open PaperC.Prel8.AffineDictionaryExceptional
noncomputable section

/-- The iid Poisson cost averaged over dictionaries is at most 8*a^2*N*B. -/
theorem averaged_iid_poisson_le (hAGG : ProcessAGGStatement) {N L r : ℕ}
    (hN : 1 ≤ N) (hrank : r ≤ L+1) :
    affineAverage (L+1) r (iidPoissonDistance N L) ≤
      8*((((2^(L+1-r):ℕ):ℝ))/(2:ℝ)^(L+1))^2*(N:ℝ)*(L+1:ℝ) := by
  have h := affine_mono hrank (f := iidPoissonDistance N L)
    (g := fun W => 4*((N:ℝ)*((((2^(L+1-r):ℕ):ℝ))/(2:ℝ)^(L+1))*overlapWeight W+
      (N:ℝ)*(L+1:ℝ)*((((2^(L+1-r):ℕ):ℝ))/(2:ℝ)^(L+1))^2)) (fun s => by
    have hw : (dictionary s).Nonempty := Finset.card_pos.mp (by rw [card_dictionary]; positivity)
    simpa only [dictionaryRate_coe,card_dictionary] using iidPoissonDistance_le hAGG (dictionary s) hw hN)
  simp only [affine_mul,affine_add,affine_const hrank,affine_overlap (by omega) hrank,
    Nat.add_sub_cancel] at h
  have he : (N:ℝ)*((((2^(L+1-r):ℕ):ℝ))/(2:ℝ)^(L+1))*((((2^(L+1-r):ℕ):ℝ))*L/(2:ℝ)^(L+1)) =
      ((((2^(L+1-r):ℕ):ℝ))/(2:ℝ)^(L+1))^2*(N:ℝ)*L := by ring
  nlinarith [he,mul_nonneg (sq_nonneg ((((2^(L+1-r):ℕ):ℝ))/(2:ℝ)^(L+1))) (Nat.cast_nonneg N)]

/-- The two genuine infinite fields share their Poisson target before averaging distances. -/
theorem averaged_arithmetic_iid_le (hAGG : ProcessAGGStatement) {N L Y r : ℕ}
    (hN : 1 ≤ N) (hrank : r ≤ L+1) {R : ℝ}
    (hr : affineAverage (L+1) r (dictionaryConditionalDistance N L Y) ≤ R) :
    affineAverage (L+1) r (fun W =>
      massTotalVariation (infiniteDictionaryLaw N L W) (infiniteIidFieldLaw N L W)) ≤
      R+8*((((2^(L+1-r):ℕ):ℝ))/(2:ℝ)^(L+1))^2*(N:ℝ)*(L+1:ℝ) := by
  have h := affine_mono hrank (f := fun W => massTotalVariation (infiniteDictionaryLaw N L W) (infiniteIidFieldLaw N L W)) (g := fun W => dictionaryDistance N L W+iidPoissonDistance N L W) (fun s => dictionary_iid_distance_le N L (dictionary s))
  rw [affine_add] at h
  exact h.trans (add_le_add (mean_unconditional_le hrank hr) (averaged_iid_poisson_le hAGG hN hrank))

end
end PaperC.Prel8.AffineDictionaryIid
