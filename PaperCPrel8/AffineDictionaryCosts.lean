import PaperCPrel8.AffineDictionaryMoments
import PaperCPrel8.TypicalDictionaryTransfer

/-! # Matching the actual deletion, overlap and arithmetic pair costs -/
namespace PaperC.Prel8.AffineDictionaryCosts
open PaperC PaperC.ConditionalStartProbability PaperC.SectionThirteenFiniteBound
open PaperC.V282.RandomDictionary PaperC.V282.RandomDictionaryOverlap
open PaperC.V282.DictionaryPairCosts PaperC.V282.WordOverlapSum
open PaperC.V282.MaskedArithmeticGeometry PaperC.SectionTwelveMoments
open PaperC.Prel8.AffineDictionarySample PaperC.Prel8.AffineDictionaryInclusion
open PaperC.Prel8.AffineDictionaryMoments PaperC.Prel8.DictionaryAverage
open PaperC.Prel8.TypicalDictionaryDeletion
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem affine_congr {B r : ℕ} {f g : Finset (Word B) → ℝ}
    (h : ∀ s : Sample B r, f (dictionary s)=g (dictionary s)) : affineAverage B r f=affineAverage B r g := by
  unfold affineAverage finiteUniformAverage
  rw [Finset.sum_congr rfl (fun s _ => h s)]

theorem affine_environment_commute {B r : ℕ} {Ω : Type*} [Fintype Ω]
    (f : Finset (Word B) → Ω → ℝ) :
    affineAverage B r (fun W => finiteUniformAverage (f W))=
      finiteUniformAverage (fun omega => affineAverage B r (fun W => f W omega)) := by
  unfold affineAverage finiteUniformAverage
  rw [← Finset.sum_div,← Finset.sum_div,Finset.sum_comm]
  ring

/-- Real source deletion has the identical mean on each prime fibre, not merely after conditioning. -/
theorem deletion_matches {N L Y r : ℕ} (hr : r ≤ L+1) (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (sigma : SmallSample (dyadicCutoff N L) Y) :
    affineAverage (L+1) r (fun W => deletedMass N L Y mask W sigma)=
      dictionaryAverage (L+1) (2^(L+1-r)) (fun W => deletedMass N L Y mask W sigma) := by
  simp_rw [deletedMass_eq N L Y mask hmask]
  rw [affine_sum,dictionaryAverage_finset_sum]
  exact Finset.sum_congr rfl (fun x _ => event_single_matches (by omega) hr _ _)

/-- The literal arithmetic pair-mask cost uses only the proved two-word selection moments. -/
theorem pairMass_matches (M L r : ℕ) (hr : r ≤ L+1) (S : Finset (ℕ × ℕ)) :
    affineAverage (L+1) r (fun W => dictionaryPairMass M L W S)=
      dictionaryAverage (L+1) (2^(L+1-r)) (fun W => dictionaryPairMass M L W S) := by
  simp_rw [dictionaryPairMass_eq_labelled_sum]
  rw [affine_sum,dictionaryAverage_finset_sum]
  exact Finset.sum_congr rfl (fun xy _ => pair_sum_matches (by omega) hr _)

/-- The fixed dictionary cardinality makes the normalized overlap a quadratic cost. -/
theorem overlap_matches {B r : ℕ} (hB : 1 ≤ B) (hr : r ≤ B) :
    affineAverage B r overlapWeight=dictionaryAverage B (2^(B-r)) overlapWeight := by
  let f : Word B → Word B → ℝ := fun u v => ∑ d ∈ Finset.Icc 1 (B-1), directedOverlapWeight d u v
  let g : Finset (Word B) → ℝ := fun W => (1/((2^(B-r):ℕ):ℝ))*∑ u ∈ W, ∑ v ∈ W, f u v
  have ha : affineAverage B r overlapWeight=affineAverage B r g := by
    apply affine_congr
    intro s
    unfold overlapWeight
    rw [card_dictionary]
    dsimp [g,f]
    ring
  have hd : dictionaryAverage B (2^(B-r)) overlapWeight=dictionaryAverage B (2^(B-r)) g := by
    apply average_congr
    intro W hW
    unfold overlapWeight
    rw [(mem_dictionaries W).mp hW]
    dsimp [g,f]
    ring
  rw [ha,hd]
  dsimp [g]
  rw [affine_mul,average_mul,pair_sum_matches hB hr]

/-- The exact affine mean overlap is m*(B-1)/2^B, including full-rank singleton dictionaries. -/
theorem affine_overlap {B r : ℕ} (hB : 1 ≤ B) (hr : r ≤ B) :
    affineAverage B r overlapWeight=(2^(B-r):ℕ)*(B-1:ℕ)/(2:ℝ)^B := by
  rw [overlap_matches hB hr]
  exact average_overlapWeight_eq (sample_size_bounds hr).1 (sample_size_bounds hr).2

end
end PaperC.Prel8.AffineDictionaryCosts
