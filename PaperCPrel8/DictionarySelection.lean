import PaperCV282.RandomDictionaryOverlap
import PaperCV282.SteinFiniteExpectation

/-! # Averaging dictionary selection before arithmetic pair estimates

The selected dictionary stays fixed inside each source probability.
These are the exact finite identities behind 3PREL8 (5.3), not yet the
arithmetic estimate or its asymptotic conclusion.
-/
namespace PaperC.Prel8.DictionarySelection
open PaperC.V282.RandomDictionary PaperC.V282.RandomDictionaryOverlap
open PaperC.ArratiaGoldsteinGordonInput PaperC.Affine
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Probability of including one specified word in the actual uniform subset sample. -/
def oneInclusion (B m : ℕ) : ℝ :=
  ((2^B-1).choose (m-1) : ℝ) / ((2^B).choose m : ℝ)

/-- Probability of including two distinct words, including the singleton dictionary case. -/
def twoInclusion (B m : ℕ) : ℝ :=
  ((if 2 ≤ m then (2^B-2).choose (m-2) else 0 : ℕ) : ℝ) /
    ((2^B).choose m : ℝ)

theorem pair_selection {B m : ℕ} (hm : 1 ≤ m) (u v : Fin B → F₂) :
    dictionaryFraction B m (fun W => u ∈ W ∧ v ∈ W) =
      twoInclusion B m + (oneInclusion B m - twoInclusion B m) *
        (if u=v then 1 else 0) := by
  unfold dictionaryFraction
  rw [card_dictionaries]
  by_cases h : u=v
  · subst v
    simp only [and_self, ite_true, mul_one, add_sub_cancel]
    rw [card_dictionaries_containing hm]
    rfl
  · simp only [h, ite_false, mul_zero, add_zero]
    by_cases hm2 : 2 ≤ m
    · have hc := card_dictionaries_containing_pair hm2 u v h
      unfold twoInclusion
      rw [ite_eq_left hm2]
      congr 1
      convert congrArg (fun n : ℕ => (n : ℝ)) hc using 1; congr!
    · have hc := card_dictionaries_containing_pair_of_lt (m := m) (by omega) u v h
      unfold twoInclusion
      rw [ite_eq_right hm2]
      congr 1
      convert congrArg (fun n : ℕ => (n : ℝ)) hc using 1; congr!

/-- Exact first-inclusion probability, with a nonempty dictionary sample. -/
theorem oneInclusion_eq {B m : ℕ} (hm : 1 ≤ m) (hmb : m ≤ 2^B) :
    oneInclusion B m = (m : ℝ) / (2 : ℝ)^B := by
  have hn : 1 ≤ 2^B := Nat.one_le_pow _ _ (by decide)
  have hc : (0 : ℝ) < ((2^B).choose m : ℕ) := by exact_mod_cast Nat.choose_pos hmb
  have hp : (0 : ℝ) < (2 : ℝ)^B := by positivity
  have hi := one_inclusion_count_identity hn hm
  have hi' : (2 : ℝ)^B * ((2^B-1).choose (m-1) : ℕ) =
      (((2^B).choose m : ℕ) : ℝ) * m := by exact_mod_cast hi
  unfold oneInclusion
  apply (div_eq_div_iff (ne_of_gt hc) (ne_of_gt hp)).mpr
  nlinarith

/-- The mean pair probability is the collision identity, for any finite source law. -/
theorem averaged_pair_probability {B m : ℕ} (hm : 1 ≤ m) (hmb : m ≤ 2^B)
    {Ω : Type*} [Fintype Ω] (μ : FinitePMF Ω) (u v : Ω → Fin B → F₂) :
    dictionaryAverage B m (fun W => eventProbability μ (fun ω => u ω ∈ W ∧ v ω ∈ W)) =
      twoInclusion B m + (oneInclusion B m - twoInclusion B m) *
        eventProbability μ (fun ω => u ω = v ω) := by
  have hc : (0 : ℝ) < ((2^B).choose m : ℕ) := by exact_mod_cast Nat.choose_pos hmb
  unfold dictionaryAverage eventProbability
  rw [Finset.sum_comm]
  have hs (ω : Ω) := sum_pair_indicator hm (u ω) (v ω) (μ.prob ω)
  trans (∑ ω, (if u ω=v ω then ((2^B-1).choose (m-1) : ℝ)*μ.prob ω else
        ((if 2 ≤ m then (2^B-2).choose (m-2) else 0 : ℕ) : ℝ)*μ.prob ω)) /
      ((dictionaries B m).card : ℝ)
  · congr 1
    apply Finset.sum_congr rfl
    intro ω _
    convert hs ω using 1; congr!
  rw [Finset.sum_div]
  have hpoint (ω : Ω) :
      (if u ω = v ω then ((2^B-1).choose (m-1) : ℝ) * μ.prob ω
       else ((if 2 ≤ m then (2^B-2).choose (m-2) else 0 : ℕ) : ℝ) * μ.prob ω) /
          ((dictionaries B m).card : ℝ) =
      μ.prob ω * twoInclusion B m + (oneInclusion B m - twoInclusion B m) *
        (if u ω = v ω then μ.prob ω else 0) := by
    rw [card_dictionaries]
    by_cases h : u ω = v ω <;> simp only [h, ite_true, ite_false]
    · unfold oneInclusion twoInclusion
      ring
    · unfold twoInclusion
      ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, μ.sum_prob, one_mul, ← Finset.mul_sum]
  congr!

end
end PaperC.Prel8.DictionarySelection
