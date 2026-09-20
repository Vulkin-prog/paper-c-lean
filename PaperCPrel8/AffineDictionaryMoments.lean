import PaperCPrel8.AffineDictionaryInclusion

/-! # Exact matching of all degree-two dictionary-selection costs -/
namespace PaperC.Prel8.AffineDictionaryMoments
open PaperC PaperC.SectionThirteenFiniteBound PaperC.ConditionalAGGAverage
open PaperC.ArratiaGoldsteinGordonInput
open PaperC.V282.RandomDictionary PaperC.V282.RandomDictionaryOverlap
open PaperC.V282.DictionaryPairCosts
open PaperC.Prel8.AffineDictionarySample PaperC.Prel8.AffineDictionaryInclusion
open PaperC.Prel8.DictionarySelection PaperC.Prel8.DictionarySamplingBounds
open PaperC.Prel8.DictionaryAverage
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem sample_size_bounds {B r : ℕ} (hr : r ≤ B) : 1 ≤ 2^(B-r) ∧ 2^(B-r) ≤ 2^B :=
  ⟨Nat.one_le_pow _ _ (by decide),Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)⟩

/-- Exactly the same pair inclusion probabilities as uniform dictionaries of size m=2^(B-r). -/
theorem pair_probability_matches {B r : ℕ} (hB : 1 ≤ B) (hr : r ≤ B) (u v : Word B) :
    affineAverage B r (fun W => if u ∈ W ∧ v ∈ W then 1 else 0)=
      dictionaryAverage B (2^(B-r)) (fun W => if u ∈ W ∧ v ∈ W then 1 else 0) := by
  have hm := sample_size_bounds hr
  have hprod : (2:ℝ)^(B-r)*(2:ℝ)^r=(2:ℝ)^B := by rw [← pow_add,Nat.sub_add_cancel hr]
  have hQ : (1:ℝ)<(2:ℝ)^B := one_lt_pow₀ (by norm_num) (by omega)
  have hrhs : dictionaryAverage B (2^(B-r)) (fun W => if u ∈ W ∧ v ∈ W then (1:ℝ) else 0)=
      dictionaryFraction B (2^(B-r)) (fun W => u ∈ W ∧ v ∈ W) := by
    simp [dictionaryAverage,dictionaryFraction,← Finset.sum_filter]
    congr 3
    ext W
    simp
  rw [pair_probability_kernel,hrhs,pair_selection hm.1]
  by_cases huv : u=v
  · subst v
    simp only [sub_self,kernelFrequency_zero hr,ite_true,mul_one,add_sub_cancel,oneInclusion_eq hm.1 hm.2,Nat.cast_pow,Nat.cast_ofNat]
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  · rw [kernelFrequency_eq hB hr (u-v) (sub_ne_zero.mpr huv),ite_eq_right huv]
    simp only [mul_zero,add_zero,twoInclusion_eq hB hm.1 hm.2,Nat.cast_pow,Nat.cast_ofNat]
    field_simp [show (2:ℝ)^B-1 ≠ 0 by linarith]
    nlinarith [congrArg (fun x : ℝ => x*((2:ℝ)^(B-r)-1)) hprod]

/-- Constants are averaged over the genuine nonempty affine sample. -/
theorem affine_const {B r : ℕ} (hr : r ≤ B) (c : ℝ) : affineAverage B r (fun _ => c)=c := by
  letI : Nonempty (Surjection B r) := surjection_nonempty hr
  exact environment_const c

theorem affine_add (B r : ℕ) (f g : Finset (Word B) → ℝ) :
    affineAverage B r (fun W => f W+g W)=affineAverage B r f+affineAverage B r g := environment_add _ _

theorem affine_mul (B r : ℕ) (c : ℝ) (f : Finset (Word B) → ℝ) :
    affineAverage B r (fun W => c*f W)=c*affineAverage B r f := environment_mul _ _

theorem affine_sum {B r : ℕ} {T : Type*} (S : Finset T) (f : T → Finset (Word B) → ℝ) :
    affineAverage B r (fun W => ∑ i ∈ S, f i W)=∑ i ∈ S, affineAverage B r (f i) :=
  average_finset_sum S _

theorem affine_mono {B r : ℕ} (hr : r ≤ B) {f g : Finset (Word B) → ℝ}
    (h : ∀ s : Sample B r, f (dictionary s) ≤ g (dictionary s)) : affineAverage B r f ≤ affineAverage B r g := by
  letI : Nonempty (Surjection B r) := surjection_nonempty hr
  exact finiteUniformAverage_mono h

/-- Every fixed pair weight has the same selection average; the two ensembles need not be equal. -/
theorem pair_weight_matches {B r : ℕ} (hB : 1 ≤ B) (hr : r ≤ B) (u v : Word B) (c : ℝ) :
    affineAverage B r (fun W => if u ∈ W ∧ v ∈ W then c else 0)=
      dictionaryAverage B (2^(B-r)) (fun W => if u ∈ W ∧ v ∈ W then c else 0) := by
  have he (W : Finset (Word B)) : (if u ∈ W ∧ v ∈ W then c else 0)=c*(if u ∈ W ∧ v ∈ W then 1 else 0) := by split_ifs <;> simp
  simp_rw [he]
  rw [affine_mul,average_mul,pair_probability_matches hB hr]

/-- All quadratic word sums, including local overlap and arithmetic joint masses, match. -/
theorem pair_sum_matches {B r : ℕ} (hB : 1 ≤ B) (hr : r ≤ B) (f : Word B → Word B → ℝ) :
    affineAverage B r (fun W => ∑ u ∈ W, ∑ v ∈ W, f u v)=
      dictionaryAverage B (2^(B-r)) (fun W => ∑ u ∈ W, ∑ v ∈ W, f u v) := by
  have he := funext (fun W : Finset (Word B) => pair_sum_eq_indicators W f)
  rw [he]
  rw [affine_sum,dictionaryAverage_finset_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [affine_sum,dictionaryAverage_finset_sum]
  exact Finset.sum_congr rfl (fun v _ => pair_weight_matches hB hr u v (f u v))

/-- The same moment matching holds with an arbitrary fixed finite source law. -/
theorem event_pair_matches {B r : ℕ} (hB : 1 ≤ B) (hr : r ≤ B)
    {Ω : Type*} [Fintype Ω] (mu : FinitePMF Ω) (u v : Ω → Word B) :
    affineAverage B r (fun W => eventProbability mu (fun omega => u omega ∈ W ∧ v omega ∈ W))=
      dictionaryAverage B (2^(B-r)) (fun W => eventProbability mu (fun omega => u omega ∈ W ∧ v omega ∈ W)) := by
  unfold eventProbability
  rw [affine_sum,dictionaryAverage_finset_sum]
  apply Finset.sum_congr rfl
  intro omega _
  convert pair_weight_matches hB hr (u omega) (v omega) (mu.prob omega) using 1 <;> congr!

theorem event_single_matches {B r : ℕ} (hB : 1 ≤ B) (hr : r ≤ B)
    {Ω : Type*} [Fintype Ω] (mu : FinitePMF Ω) (u : Ω → Word B) :
    affineAverage B r (fun W => eventProbability mu (fun omega => u omega ∈ W))=
      dictionaryAverage B (2^(B-r)) (fun W => eventProbability mu (fun omega => u omega ∈ W)) := by
  simpa only [and_self] using event_pair_matches hB hr mu u u

end
end PaperC.Prel8.AffineDictionaryMoments
