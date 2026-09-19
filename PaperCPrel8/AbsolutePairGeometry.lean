import PaperCPrel8.AbsolutePairLedger
import PaperCPrel8.RoughPairHostSaddle

/-! # Geometric counts for the absolute conditional pair activity -/
namespace PaperC.Prel8.AbsolutePairGeometry
open Finset AbsolutePairLedger ActualSignedPalm TwoBlockRegularity RoughKernelRegularity
open MicroscopicFiniteLedger MicroscopicRelationExcess MicroscopicFootprintLedger LargeOddKernel OddPrimePivot
open ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E n : ℕ} {G : Finset ℕ}

theorem sum_sites (D : Finset ℕ) (f : ℕ → ℝ) :
    (∑ j : Site D, f j.val)=∑ j∈D, f j :=
  (sum_subtype D (fun _ ↦ Iff.rfl) f).symm

theorem sum_pairs (D : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ j : Site D, ∑ k : Site D, f j.val k.val)=∑ j∈D,∑ k∈D, f j k := by
  rw [← sum_subtype D (fun _ ↦ Iff.rfl) (fun j ↦ ∑ k : Site D, f j k.val)]
  apply sum_congr rfl
  intro j hj
  exact (sum_subtype D (fun _ ↦ Iff.rfl) (f j)).symm

theorem close_pairs_count (G : Finset ℕ) (Q : ℕ) :
    (∑ j : Site G, ∑ k : Site G, if Nat.dist j.val k.val≤Q then (1:ℝ) else 0)≤
      (G.card:ℝ)*(2*Q+1) := by
  have hh (j : Site G) : (∑ k : Site G, if Nat.dist j.val k.val≤Q then (1:ℝ) else 0)≤2*Q+1 := by
    let D := G.filter (fun k ↦ Nat.dist j.val k≤Q)
    have he := count_subtype_members D (filter_subset _ _)
    have he' : (∑ k : Site G, if Nat.dist j.val k.val≤Q then (1:ℝ) else 0)=(D.card:ℝ) := by
      rw [← he]
      apply sum_congr rfl
      intro k hk
      simp only [D,mem_filter,k.property,true_and]
    rw [he']
    exact_mod_cast distance_filter_card_le G j.val Q
  calc
    _ ≤ ∑ _j : Site G, (2*(Q:ℝ)+1) := sum_le_sum (fun j _ ↦ hh j)
    _ = _ := by simp [Site]; ring

theorem bad_pairs_sum (G : Finset ℕ) (Q Y : ℕ) :
    (∑ j : Site G, ∑ k : Site G, if Regular Q Y ![j.val,k.val] then (0:ℝ) else 1)=
      ((badPairs G Q Y).card:ℝ) := by
  rw [sum_pairs G (fun j k ↦ if Regular Q Y ![j,k] then (0:ℝ) else 1)]
  rw [← sum_product G G (fun z : ℕ×ℕ ↦ if Regular Q Y ![z.1,z.2] then (0:ℝ) else 1)]
  simp only [badPairs,card_filter]
  push_cast
  apply sum_congr rfl
  intro z hz
  split_ifs <;> simp_all

theorem good_kernel_large (h : GoodGeometry C Y L E G) (j : ℕ) (hj : j∈G)
    (a : Fin (L+E+2)) : 1<largeOddKernel Y (j+a.val) := by
  have h1 := one_le_largeOddKernel Y (j+a.val)
  have hn := h.good j hj a
  have hne : largeOddKernel Y (j+a.val)≠1 := by
    intro he
    have hh := (largestOddPrime_le_iff h.cutoff_pos).mpr
      ((largeOddKernel_eq_one_iff_hDefective Y (j+a.val)).mp he)
    omega
  omega

theorem weights_le_counts (G : Finset ℕ) (C Y L E : ℕ) :
    (∑ j : Site G, ∑ k : Site G, pairWeight C Y L E j.val k.val)≤
      4*(G.card:ℝ)*(2*(L+E+1:ℝ)+1)+separatedExcess C L E G+
        2*((badPairs G (L+E+1) Y).card:ℝ) := by
  simp only [pairWeight,sum_add_distrib,← mul_sum]
  rw [bad_pairs_sum]
  have hh := close_pairs_count G (L+E+1)
  push_cast at hh
  change 4*_+separatedExcess C L E G+_≤_
  linarith

/-- The three costs are local neighbours, full-value excess, and rough hosts. -/
theorem activity_le_counts (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2)≤Y)
    (hG : G⊆Icc 1 n) (A : SmallSample C Y → Prop)
    (hA : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w))) :
    activity (sourceLaw A hA) L E G≤(1/(2:ℝ)^L)^2*
      (4*(G.card:ℝ)*(2*(L+E+1:ℝ)+1)+separatedExcess C L E G+
        4*((RoughPairHosts.hostedPairs n (L+E+1) Y).card:ℝ))/
          eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)) := by
  apply (activity_le_weights h hY A hA).trans
  apply div_le_div_of_nonneg_right _ hA.le
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hb := bad_pairs_count G hG (show L+E+1<Y by omega) (good_kernel_large h)
  have hb' : ((badPairs G (L+E+1) Y).card:ℝ)≤2*(RoughPairHosts.hostedPairs n (L+E+1) Y).card := by
    exact_mod_cast hb
  have hw := weights_le_counts G C Y L E
  linarith

/-- Enlarging the retained set only increases its nonnegative relation profile. -/
theorem separatedExcess_mono {G D : Finset ℕ} (hGD : G⊆D) :
    separatedExcess C L E G≤separatedExcess C L E D := by
  unfold separatedExcess
  rw [sum_pairs G (fun j k ↦ if L+E+1<Nat.dist j k then valueExcess C L E j k else 0),
    sum_pairs D (fun j k ↦ if L+E+1<Nat.dist j k then valueExcess C L E j k else 0)]
  apply (sum_le_sum_of_subset_of_nonneg hGD (fun j _ _ ↦ by
    apply sum_nonneg
    intro k hk
    split_ifs
    · exact valueExcess_nonneg _ _ _ _ _
    · exact le_refl 0)).trans
  apply sum_le_sum
  intro j hj
  apply sum_le_sum_of_subset_of_nonneg hGD
  intro k hk hkg
  split_ifs
  · exact valueExcess_nonneg _ _ _ _ _
  · exact le_refl 0

end
end PaperC.Prel8.AbsolutePairGeometry
