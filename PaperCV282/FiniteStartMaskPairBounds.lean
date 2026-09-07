import PaperCV282.FiniteStartMaskAverages
import PaperCV282.MacroscopicMaskGeometry
import PaperCV282.GoodTouchingProbability
import PaperCV282.HostRankMass
import PaperC.Probability.ExactLengthConditionalRank

/-! # Actual pair probabilities on arbitrary finite start populations

Strict overlaps vanish. Retained touching pairs cost at most the independent
baseline. Only separated pairs pay their actual affine relation weight,
computed in any adequate prime cylinder.
-/
namespace PaperC.V282.FiniteStartMaskPairBounds

open Affine SectionTwelveMoments LargePrimeDependencyGraph
open FiniteStartMaskModel FiniteStartMaskAverages MacroscopicMaskGeometry
open MaskedPairGeometry GoodTouchingProbability TwoWindowParity HostRankMass
open scoped BigOperators

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exact scalar affine identification, with no dyadic lower endpoint. -/
theorem uniform_start_eq_affine (C L x : ℕ) (hL : 0<L) :
    uniformEventProbability (fun omega : SampleSpace C => startAt omega x L) =
      uniformSolutionProbability (startSystem C x L) (startRhs L) := by
  classical
  unfold uniformEventProbability uniformSolutionProbability
  congr 1
  rw [Fintype.card_subtype]
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext omega
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact (startSystem_eq_startRhs_iff_startAt omega hL).symm

/-- Exact joint affine identification at an arbitrary cylinder cutoff. -/
theorem uniform_joint_eq_affine (C L x y : ℕ) (hL : 0<L) :
    uniformEventProbability (fun omega : SampleSpace C => startAt omega x L ∧ startAt omega y L) =
      uniformSolutionProbability (twoStartSystem C x y L) (twoStartRhs L) := by
  classical
  unfold uniformEventProbability uniformSolutionProbability
  congr 1
  rw [Fintype.card_subtype]
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext omega
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact (twoStartSystem_eq_twoStartRhs_iff omega hL).symm

/-- The actual relation dimension supplies the full joint upper bound. -/
theorem uniform_joint_le_relation (C L x y : ℕ) (hL : 0<L) :
    uniformEventProbability (fun omega : SampleSpace C => startAt omega x L ∧ startAt omega y L) ≤
      (2 : ℚ)^relationRho (twoStartSystem C x y L)/(2 : ℚ)^(2*L) := by
  rw [uniform_joint_eq_affine C L x y hL]
  simpa [Fintype.card_sum,two_mul] using
    ExactLengthConditionalRank.uniformSolutionProbability_le_two_pow_relation_bound
      (twoStartSystem C x y L) (twoStartRhs L) (le_refl _)

/-- Strictly overlapping distinct starts are incompatible on every cylinder. -/
theorem uniform_joint_overlap {C L x y : ℕ} (hxy : x≠y) (hd : Nat.dist x y<L) :
    uniformEventProbability (fun omega : SampleSpace C => startAt omega x L ∧ startAt omega y L)=0 := by
  classical
  unfold uniformEventProbability
  have hempty : (Finset.univ.filter fun omega : SampleSpace C =>
      startAt omega x L ∧ startAt omega y L)=∅ := by
    ext omega
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
    exact startEvents_disjoint_of_dist_lt hxy hd
  rw [hempty]
  simp

/-- A good distinct pair pays its relation weight only in the separated range. -/
theorem uniform_joint_good_le {C L Y x y : ℕ} {mask : Finset ℕ}
    (hL : 0<L) (hY : 2*L≤Y) (hpos : ∀ x∈mask,2≤x) (hcut : ∀ x∈mask,x+L≤C)
    (hx : x∈goodMask L Y mask) (hy : y∈goodMask L Y mask) (hxy : x≠y) :
    uniformEventProbability (fun omega : SampleSpace C => startAt omega x L ∧ startAt omega y L) ≤
      (1 + if L<Nat.dist x y then ((2^relationRho (twoStartSystem C x y L)-1 : ℕ) : ℚ) else 0) /
        (2 : ℚ)^(2*L) := by
  by_cases hs : L<Nat.dist x y
  · rw [if_pos hs]
    have heq : (1 : ℚ)+((2^relationRho (twoStartSystem C x y L)-1 : ℕ) : ℚ) =
        (2 : ℚ)^relationRho (twoStartSystem C x y L) := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      ring
    rw [heq]
    exact uniform_joint_le_relation C L x y hL
  · rw [if_neg hs]
    by_cases ho : Nat.dist x y<L
    · rw [uniform_joint_overlap hxy ho]
      positivity
    · have hd : Nat.dist x y=L := by omega
      have hr := twoStartRho_eq_zero_of_touching_good
        (hpos x (goodMask_subset L Y mask hx)) (hpos y (goodMask_subset L Y mask hy)) hL hY hd
        ⟨hcut x (goodMask_subset L Y mask hx),hcut y (goodMask_subset L Y mask hy)⟩
        (fun i => not_defective_of_good hx (mem_startTreeSupport.mpr (Or.inr ⟨i.val,i.isLt,rfl⟩)))
        (fun i => not_defective_of_good hy (mem_startTreeSupport.mpr (Or.inr ⟨i.val,i.isLt,rfl⟩)))
      simpa only [hr,pow_zero,add_zero] using uniform_joint_le_relation C L x y hL

/-- The edge subpopulation lies in the same separated pair mask. -/
theorem separated_goodEdges_subset (L Y : ℕ) (mask : Finset ℕ) :
    (goodEdges L Y mask).filter (fun xy => L<Nat.dist xy.1 xy.2) ⊆ separatedPairs mask L := by
  intro xy hxy
  obtain ⟨hg,hd⟩ := Finset.mem_filter.mp hxy
  obtain ⟨hx,hy,_⟩ := mem_goodEdges.mp hg
  exact (mem_separatedPairs _ _ _ _).mpr
    ⟨goodMask_subset L Y mask hx,goodMask_subset L Y mask hy,hd⟩

/-- Actual joint mass of all retained edges, at a free adequate cylinder. -/
theorem sum_joint_goodEdges_le {C L Y : ℕ} (mask : Finset ℕ)
    (hL : 0<L) (hY : 2*L≤Y) (hpos : ∀ x∈mask,2≤x) (hcut : ∀ x∈mask,x+L≤C) :
    (∑ xy∈goodEdges L Y mask, uniformEventProbability
      (fun omega : SampleSpace C => startAt omega xy.1 L ∧ startAt omega xy.2 L)) ≤
      (((maskedSupportEdges L Y mask).card : ℚ) +
        (relationWeightMass C L (separatedPairs mask L) : ℚ))/(2 : ℚ)^(2*L) := by
  classical
  calc
    _ ≤ ∑ xy∈goodEdges L Y mask,
        (1 + if L<Nat.dist xy.1 xy.2 then
          ((2^relationRho (twoStartSystem C xy.1 xy.2 L)-1 : ℕ) : ℚ) else 0)/(2 : ℚ)^(2*L) := by
      apply Finset.sum_le_sum
      intro xy hxy
      obtain ⟨hx,hy,ha⟩ := mem_goodEdges.mp hxy
      exact uniform_joint_good_le hL hY hpos hcut hx hy ha.1
    _ = (((goodEdges L Y mask).card : ℚ) +
        (relationWeightMass C L ((goodEdges L Y mask).filter (fun xy => L<Nat.dist xy.1 xy.2)) : ℚ)) /
          (2 : ℚ)^(2*L) := by
      rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.sum_filter]
      simp [relationWeightMass]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact add_le_add (by exact_mod_cast Finset.card_le_card (goodEdges_subset_support L Y mask))
        (by exact_mod_cast relationWeightMass_mono C L (separated_goodEdges_subset L Y mask))

end
end PaperC.V282.FiniteStartMaskPairBounds
