import PaperCV282.DictionaryMarginalCap
import PaperCV282.DictionaryFieldModel
import PaperCV282.CappedRelationMass
import PaperCV282.MaskedPairGeometry

/-!
# Actual dictionary pair costs and the literal capped full-value mass

The cap is established on each actual joint event before the pair sum.
Uniform conditioning averages give precisely the same finite-cylinder
joint probabilities. All finite pair masks and dictionary labels remain
explicit; separation is a specialization rather than a hidden hypothesis.
-/

namespace PaperC.V282.DictionaryPairCosts

open Affine PrescribedValues WindowValues InfiniteWordTransfer
open ConditionalStartProbability ConditionalAGGInstantiation ConditionalAGGAverage
open ArratiaGoldsteinGordonInput SectionThirteenCouplings SectionThirteenFiniteBound
open DictionaryMarginalCap DictionaryFieldModel TwoWindowParity CappedRelationMass
open MaskedArithmeticGeometry LargePrimeDependencyGraph
open MaskedPairGeometry
open scoped BigOperators NNReal

noncomputable section

set_option maxHeartbeats 1200000

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The actual sum of grouped pair probabilities on a finite ordered mask. -/
def dictionaryPairMass (M L : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (s : Finset (ℕ × ℕ)) : ℝ :=
  ∑ xy ∈ s, dictionaryJointProbability M xy.1 xy.2 (L + 1) W

/-- The same grouped pair sum on a literal small-prime fibre. -/
def conditionalDictionaryPairMass (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (s : Finset (ℕ × ℕ)) (sigma : SmallSample (dyadicCutoff N L) Y) : ℝ :=
  ∑ xy ∈ s, eventProbability (largeUniformPMF (dyadicCutoff N L) Y) (fun eta =>
    dictionaryIndicator (dyadicCutoff N L) xy.1 (L + 1) W (assemble _ _ sigma eta) = true ∧
    dictionaryIndicator (dyadicCutoff N L) xy.2 (L + 1) W (assemble _ _ sigma eta) = true)

/-- The generic density agrees with the common parameter of the actual labelled field. -/
theorem dictionaryRate_eq_density (L : ℕ) (W : Finset (Fin (L + 1) → F₂)) :
    (dictionaryRate L W : ℝ) = dictionaryDensity (L + 1) W := dictionaryRate_coe L W

/-- Grouping the actual Boolean word indicators still gives a single indicator. -/
theorem sum_finiteWordIndicator_eq_dictionary (M x B : ℕ) (W : Finset (Fin B → F₂))
    (omega : SampleSpace M) :
    (∑ b ∈ W, if finiteWordIndicator M x B b omega = true then (1 : ℕ) else 0) =
      if dictionaryIndicator M x B W omega = true then 1 else 0 := by
  simpa only [finiteWordIndicator_eq_true_iff] using sum_word_indicators_eq_dictionary M x B W omega

/-- The unconditional grouped sum keeps every dictionary label exactly once. -/
theorem dictionaryPairMass_eq_labelled_sum (M L : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (s : Finset (ℕ × ℕ)) :
    dictionaryPairMass M L W s =
      ∑ xy ∈ s, ∑ u ∈ W, ∑ v ∈ W, wordJointProbability M xy.1 xy.2 (L + 1) u v := by
  simp only [dictionaryPairMass, dictionaryJointProbability_eq_sum]

/-- Finite averages commute with arbitrary finite sums, with their literal normalization. -/
theorem average_finset_sum {Omega T : Type*} [Fintype Omega]
    (s : Finset T) (f : Omega → T → ℝ) :
    finiteUniformAverage (fun omega => ∑ t ∈ s, f omega t) =
      ∑ t ∈ s, finiteUniformAverage (fun omega => f omega t) := by
  unfold finiteUniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

/-- Averaging a specified word pair gives its actual full-cylinder probability. -/
theorem average_word_joint_eq (M Y x y B : ℕ) (u v : Fin B → F₂) :
    finiteUniformAverage (fun sigma : SmallSample M Y =>
      eventProbability (largeUniformPMF M Y) (fun eta =>
        assemble M Y sigma eta ∈ finiteWordEvent M x B u ∧
        assemble M Y sigma eta ∈ finiteWordEvent M y B v)) =
      wordJointProbability M x y B u v := by
  rw [wordJointProbability, eventProbability_fullUniformPMF_eq,
    finiteUniformProbability_eq_uniformEventProbability]
  exact finiteUniformAverage_largeEventProbability_eq_full M Y
    (fun omega => omega ∈ finiteWordEvent M x B u ∧ omega ∈ finiteWordEvent M y B v)

/-- The field's actual conditional joint marginal has the same affine interpretation. -/
theorem average_jointMarginal_eq_wordJointProbability (N L Y : ℕ)
    (W : Finset (Fin (L + 1) → F₂)) (i j : DictionaryIndex N L W) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      jointMarginal (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedWordIndicator N L Y W sigma) i j) =
      wordJointProbability (dyadicCutoff N L) i.1.val j.1.val (L + 1) i.2.val j.2.val := by
  simpa only [jointMarginal,conditionedWordIndicator_eq_true_iff] using
    average_word_joint_eq (dyadicCutoff N L) Y i.1.val j.1.val (L + 1) i.2.val j.2.val

/-- Grouping also commutes with each actual conditional law, before any estimate. -/
theorem conditionalDictionaryPairMass_eq_labelled_sum (N L Y : ℕ)
    (W : Finset (Fin (L + 1) → F₂)) (s : Finset (ℕ × ℕ))
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    conditionalDictionaryPairMass N L Y W s sigma =
      ∑ xy ∈ s, ∑ u ∈ W, ∑ v ∈ W,
        eventProbability (largeUniformPMF (dyadicCutoff N L) Y) (fun eta =>
          assemble _ _ sigma eta ∈ finiteWordEvent (dyadicCutoff N L) xy.1 (L + 1) u ∧
          assemble _ _ sigma eta ∈ finiteWordEvent (dyadicCutoff N L) xy.2 (L + 1) v) := by
  unfold conditionalDictionaryPairMass
  apply Finset.sum_congr rfl
  intro xy _
  simp only [dictionaryIndicator_eq_true]
  have h := eventProbability_joint_mem_eq_sum (largeUniformPMF (dyadicCutoff N L) Y)
    (fun eta => valueSystem (dyadicCutoff N L) (vertex xy.1 (L + 1)) (assemble _ _ sigma eta))
    (fun eta => valueSystem (dyadicCutoff N L) (vertex xy.2 (L + 1)) (assemble _ _ sigma eta)) W
  simpa only [valueSystem_eq_iff, finiteWordEvent, Set.mem_setOf_eq] using h

/-- The complete labelled fibre average is exactly the actual unconditional grouped sum. -/
theorem average_dictionaryPairMass_eq (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (s : Finset (ℕ × ℕ)) :
    finiteUniformAverage (conditionalDictionaryPairMass N L Y W s) =
      dictionaryPairMass (dyadicCutoff N L) L W s := by
  change finiteUniformAverage (fun sigma => conditionalDictionaryPairMass N L Y W s sigma) = _
  simp_rw [conditionalDictionaryPairMass_eq_labelled_sum]
  rw [average_finset_sum]
  simp_rw [average_finset_sum, average_word_joint_eq]
  exact (dictionaryPairMass_eq_labelled_sum _ _ _ _).symm

/-- The natural relation defect used by the capped profile has its exact real value. -/
theorem two_pow_sub_one_cast (r : ℕ) :
    ((2 ^ r - 1 : ℕ) : ℝ) = (2 : ℝ) ^ r - 1 := by
  rw [Nat.cast_sub Nat.one_le_two_pow]
  norm_num

/-- Finite pair summation with the same full-value mass and real ceiling as Proposition 3.27. -/
theorem dictionaryPairMass_le_cappedValueMass {M L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (s : Finset (ℕ × ℕ)) (hLY : L + 1 ≤ Y)
    (hpair : ∀ xy ∈ s, 2 ≤ xy.1 ∧ 1 ≤ xy.2 ∧ xy.1 - 1 + (L + 1) ≤ M + 1 ∧
      ∀ i : Fin (L + 1), ¬DefectivePredicate.HDefective Y (vertex xy.1 (L + 1) i)) :
    dictionaryPairMass M L W s ≤ (dictionaryRate L W : ℝ) ^ 2 *
      ((s.card : ℝ) + cappedValueMass M L (1 / (dictionaryRate L W : ℝ)) s) := by
  rw [dictionaryRate_eq_density]
  unfold dictionaryPairMass
  calc
    _ ≤ ∑ xy ∈ s, dictionaryDensity (L + 1) W ^ 2 *
        (1 + min (1 / dictionaryDensity (L + 1) W)
          ((2 ^ relationRho (twoValueSystem M xy.1 xy.2 L) - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro xy hxy
      obtain ⟨hx,hy,hcut,hgood⟩ := hpair xy hxy
      have h := (dictionary_joint_cap (y := xy.2) hx hcut hLY hgood W).2
      simpa only [jointValueSystem_eq_twoValueSystem (by omega : 1 ≤ xy.1) hy,
        two_pow_sub_one_cast] using h
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, cappedValueMass]

/-- Every ordered mask on actually retained dyadic sites receives the literal capped budget. -/
theorem good_dictionaryPairMass_le_capped {N L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hLY : L + 1 ≤ Y) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ (fullGoodMask N L Y mask) ×ˢ (fullGoodMask N L Y mask)) :
    dictionaryPairMass (dyadicCutoff N L) L W s ≤ (dictionaryRate L W : ℝ) ^ 2 *
      ((s.card : ℝ) + cappedValueMass (dyadicCutoff N L) L (1 / (dictionaryRate L W : ℝ)) s) := by
  apply dictionaryPairMass_le_cappedValueMass W s hLY
  intro xy hxy
  obtain ⟨hxg,hyg⟩ := Finset.mem_product.mp (hs hxy)
  have hxb := hmask (mem_fullGoodMask.mp hxg).1
  have hyb := hmask (mem_fullGoodMask.mp hyg).1
  have hx := two_le_of_mem_dyadicBlock hN hxb
  have hy := two_le_of_mem_dyadicBlock hN hyb
  refine ⟨hx,by omega,?_,?_⟩
  · have hi := Finset.mem_Ico.mp hxb
    unfold dyadicCutoff
    omega
  · intro i
    exact not_defective_of_mem_fullGoodMask hmask hxg (vertex_mem_startTreeSupport (by omega) i)

/-- The same budget controls the mean conditional pair cost on the actual small-prime fibres. -/
theorem average_good_dictionaryPairMass_le_capped {N L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hLY : L + 1 ≤ Y) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ (fullGoodMask N L Y mask) ×ˢ (fullGoodMask N L Y mask)) :
    finiteUniformAverage (conditionalDictionaryPairMass N L Y W s) ≤
      (dictionaryRate L W : ℝ) ^ 2 *
        ((s.card : ℝ) + cappedValueMass (dyadicCutoff N L) L (1 / (dictionaryRate L W : ℝ)) s) := by
  rw [average_dictionaryPairMass_eq]
  exact good_dictionaryPairMass_le_capped W mask hmask hN hLY s hs

/-- In particular, the manuscript's separated retained pairs use the identical pair mask and cap. -/
theorem separated_dictionary_pair_cost_le {N L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hLY : L + 1 ≤ Y) :
    finiteUniformAverage (conditionalDictionaryPairMass N L Y W
      (separatedPairs (fullGoodMask N L Y mask) L)) ≤
      (dictionaryRate L W : ℝ) ^ 2 *
        (((separatedPairs (fullGoodMask N L Y mask) L).card : ℝ) +
          cappedValueMass (dyadicCutoff N L) L (1 / (dictionaryRate L W : ℝ))
            (separatedPairs (fullGoodMask N L Y mask) L)) := by
  apply average_good_dictionaryPairMass_le_capped W mask hmask hN hLY
  exact Finset.filter_subset _ _

/-- Separated retained graph edges pay the actual all-site edge count and the capped relation mass.
The two support inclusions concern finite populations, not assumed probability costs. -/
theorem good_graph_dictionaryPairMass_le_capped {N L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hLY : L + 1 ≤ Y) (s : Finset (ℕ × ℕ))
    (hgood : s ⊆ (fullGoodMask N L Y mask) ×ˢ (fullGoodMask N L Y mask))
    (hedges : s ⊆ maskedSupportEdges L Y mask) (hseparated : s ⊆ separatedPairs mask L) :
    dictionaryPairMass (dyadicCutoff N L) L W s ≤ (dictionaryRate L W : ℝ) ^ 2 *
      (((maskedSupportEdges L Y mask).card : ℝ) +
        cappedValueMass (dyadicCutoff N L) L (1 / (dictionaryRate L W : ℝ)) (separatedPairs mask L)) := by
  apply (good_dictionaryPairMass_le_capped W mask hmask hN hLY s hgood).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply add_le_add
  · exact_mod_cast Finset.card_le_card hedges
  · exact cappedValueMass_mono_mask _ _ (by positivity) hseparated

/-- The literal separated part of the retained support graph satisfies both inclusions. -/
theorem separated_fullMaskedEdges_dictionary_cost_le {N L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hLY : L + 1 ≤ Y) :
    dictionaryPairMass (dyadicCutoff N L) L W
      ((fullMaskedEdges N L Y mask).filter (fun xy => L < Nat.dist xy.1 xy.2)) ≤
      (dictionaryRate L W : ℝ) ^ 2 *
        (((maskedSupportEdges L Y mask).card : ℝ) +
          cappedValueMass (dyadicCutoff N L) L (1 / (dictionaryRate L W : ℝ)) (separatedPairs mask L)) := by
  apply good_graph_dictionaryPairMass_le_capped W mask hmask hN hLY
  · intro xy hxy
    obtain ⟨hx,hy,_⟩ := mem_fullMaskedEdges.mp (Finset.mem_filter.mp hxy).1
    exact Finset.mem_product.mpr ⟨hx,hy⟩
  · intro xy hxy
    obtain ⟨hx,hy,hlarge⟩ := mem_fullMaskedEdges.mp (Finset.mem_filter.mp hxy).1
    exact mem_maskedSupportEdges.mpr ⟨(mem_fullGoodMask.mp hx).1,(mem_fullGoodMask.mp hy).1,hlarge⟩
  · intro xy hxy
    obtain ⟨he,hd⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy,_⟩ := mem_fullMaskedEdges.mp he
    exact mem_separatedPairs _ _ _ _ |>.mpr ⟨(mem_fullGoodMask.mp hx).1,(mem_fullGoodMask.mp hy).1,hd⟩

end
end PaperC.V282.DictionaryPairCosts
