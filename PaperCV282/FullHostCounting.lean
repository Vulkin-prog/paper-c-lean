import PaperCV282.FullPrimeAssignment
import PaperCV282.TwoWindowSquareHosts
import PaperC.Combinatorics.RelationalHosts

/-!
# Counting unrestricted square-product hosts by the retained CRT cover

The old congruence classes and their counting bounds do not require block
parity. A nonempty square-product subset supplies an arbitrary selected
occurrence and equations at every prime. The new full-coefficient assignment
lemmas place the opposite start in the same retained certificate cover.
This proves an explicit finite dyadic host bound, before any asymptotic
estimate of the weighted kernel sum.
-/

namespace PaperC.V282.FullHostCounting

open Affine LargeKernelAssignments RelationalHosts
open TwoWindowParity TwoWindowSquareHosts ValueSquareRelations
open scoped BigOperators

noncomputable section

/-- Every unrestricted square-product host lies in the retained congruence cover.
No separation or block-parity hypothesis is needed for this inclusion. -/
theorem squareProductHosts_subset_certificateCover
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ dyadicBlock N ×ˢ dyadicBlock N) :
    squareProductHosts L s ⊆ certificateCover N L := by
  classical
  intro xy hxy
  obtain ⟨hxy, t, ht, r, hr⟩ := Finset.mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hs hxy)
  let c : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂ :=
    fun i => if i ∈ t then 1 else 0
  have hsupport : relationSupport c = t := by
    ext i
    simp [relationSupport, c]
  have hpositive : ∀ i ∈ t, twoStartCompleteVertexLabel xy.1 xy.2 L i ≠ 0 := by
    intro i _
    cases i with
    | inl i =>
        have h := (Finset.mem_Icc.mp (selectedLabel_mem_Icc hN hL hx i)).1
        simpa only [twoStartCompleteVertexLabel] using Nat.ne_of_gt h
    | inr i =>
        have h := (Finset.mem_Icc.mp (selectedLabel_mem_Icc hN hL hy i)).1
        simpa only [twoStartCompleteVertexLabel] using Nat.ne_of_gt h
  have hsum := sum_parityVec_eq_zero_of_prod_eq_sq t
    (twoStartCompleteVertexLabel xy.1 xy.2 L) hpositive hr
  have hEq : ∀ p : ℕ, p.Prime →
      ∑ i, c i * parityVec (twoStartCompleteVertexLabel xy.1 xy.2 L i) p = 0 := by
    intro p _
    have h := DFunLike.congr_fun hsum p
    simp only [Finsupp.finsetSum_apply, Finsupp.zero_apply] at h
    rw [← hsupport, sum_relationSupport_eq_dotProduct] at h
    exact h
  obtain ⟨i, hi⟩ := ht
  cases i with
  | inl v =>
      let n := startCompleteVertexLabel xy.1 L v
      have hn : n ∈ Finset.Icc 1 (3 * N) := selectedLabel_mem_Icc hN hL hx v
      have hyCert : xy.2 ∈ startsForSomeAssignment N L n := by
        apply FullPrimeAssignment.right_mem_startsForSomeAssignment_of_selected_left
          hN hx hy c hEq v
        simp [c, hi]
      have hxLabel : xy.1 ∈ startsWithSelectedLabel N L n v := by
        rw [mem_startsWithSelectedLabel]
        exact ⟨hx, rfl⟩
      simp only [certificateCover, Finset.mem_biUnion]
      refine ⟨n, hn, v, Finset.mem_univ v, ?_⟩
      rw [Finset.mem_union]
      exact Or.inl (Finset.mem_product.mpr ⟨hxLabel, hyCert⟩)
  | inr v =>
      let n := startCompleteVertexLabel xy.2 L v
      have hn : n ∈ Finset.Icc 1 (3 * N) := selectedLabel_mem_Icc hN hL hy v
      have hxCert : xy.1 ∈ startsForSomeAssignment N L n := by
        apply FullPrimeAssignment.left_mem_startsForSomeAssignment_of_selected_right
          hN hx hy c hEq v
        simp [c, hi]
      have hyLabel : xy.2 ∈ startsWithSelectedLabel N L n v := by
        rw [mem_startsWithSelectedLabel]
        exact ⟨hy, rfl⟩
      simp only [certificateCover, Finset.mem_biUnion]
      refine ⟨n, hn, v, Finset.mem_univ v, ?_⟩
      rw [Finset.mem_union]
      exact Or.inr (Finset.mem_product.mpr ⟨hxCert, hyLabel⟩)

/-- The retained cover itself satisfies the assignment-sum bound. -/
theorem card_certificateCover_cast_le_assignmentSum
    {N L : ℕ} (hN : 2 ≤ N) :
    ((certificateCover N L).card : ℚ) ≤
      2 * (L + 1 : ℚ) * ∑ n ∈ Finset.Icc 1 (3 * N), assignmentCountBound N L n := by
  classical
  have hcoverNat : (certificateCover N L).card ≤
      ∑ n ∈ Finset.Icc 1 (3 * N), ∑ v : Fin (L + 1),
        (leftCertificates N L n v ∪ rightCertificates N L n v).card := by
    unfold certificateCover
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (3 * N),
          ((Finset.univ : Finset (Fin (L + 1))).biUnion fun v =>
            leftCertificates N L n v ∪ rightCertificates N L n v).card :=
        Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum fun n _ => Finset.card_biUnion_le
  have hcover : ((certificateCover N L).card : ℚ) ≤
      ∑ n ∈ Finset.Icc 1 (3 * N), ∑ v : Fin (L + 1),
        ((leftCertificates N L n v ∪ rightCertificates N L n v).card : ℚ) := by
    exact_mod_cast hcoverNat
  calc
    _ ≤ _ := hcover
    _ ≤ ∑ n ∈ Finset.Icc 1 (3 * N), ∑ _v : Fin (L + 1),
        2 * assignmentCountBound N L n := by
      exact Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun v _ =>
        card_certificate_union_cast_le hN v
    _ = _ := by
      simp
      rw [Finset.mul_sum]
      ring

/-- An explicit finite assignment bound for unrestricted square-product hosts. -/
theorem card_squareProductHosts_cast_le_assignmentSum
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ dyadicBlock N ×ˢ dyadicBlock N) :
    ((squareProductHosts L s).card : ℚ) ≤
      2 * (L + 1 : ℚ) * ∑ n ∈ Finset.Icc 1 (3 * N), assignmentCountBound N L n := by
  have hcover : ((squareProductHosts L s).card : ℚ) ≤ (certificateCover N L).card := by
    exact_mod_cast Finset.card_le_card
      (squareProductHosts_subset_certificateCover hN hL s hs)
  exact hcover.trans (card_certificateCover_cast_le_assignmentSum hN)

/-- The finite dyadic kernel-sum bound now applies without block-parity restrictions. -/
theorem card_squareProductHosts_cast_le_kernelSumQ
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ dyadicBlock N ×ˢ dyadicBlock N) :
    ((squareProductHosts L s).card : ℚ) ≤
      8 * (L + 1 : ℚ) * (N : ℚ) *
        ∑ n ∈ Finset.Icc 1 (3 * N), largeKernelWeightQ (L + 1) n := by
  calc
    _ ≤ 2 * (L + 1 : ℚ) * ∑ n ∈ Finset.Icc 1 (3 * N), assignmentCountBound N L n :=
      card_squareProductHosts_cast_le_assignmentSum hN hL s hs
    _ ≤ 2 * (L + 1 : ℚ) * ∑ n ∈ Finset.Icc 1 (3 * N),
        4 * (N : ℚ) * largeKernelWeightQ (L + 1) n := by
      gcongr with n hn
      exact assignmentCountBound_le_four_mul_kernelWeightQ hn
    _ = _ := by
      rw [← Finset.mul_sum]
      ring

/-- Specialization to the actual ordered separated pairs of a dyadic block. -/
theorem card_separated_squareProductHosts_cast_le_kernelSumQ
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) :
    ((squareProductHosts L (separatedPairs (dyadicBlock N) L)).card : ℚ) ≤
      8 * (L + 1 : ℚ) * (N : ℚ) *
        ∑ n ∈ Finset.Icc 1 (3 * N), largeKernelWeightQ (L + 1) n :=
  card_squareProductHosts_cast_le_kernelSumQ hN hL _ (Finset.filter_subset _ _)

end
end PaperC.V282.FullHostCounting
