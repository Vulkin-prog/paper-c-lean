import PaperCV282.FullIntervalPrimeAssignment
import PaperCV282.TwoWindowSquareHosts
import PaperC.Combinatorics.BoundedRatioRelationalHosts

/-!
# Unrestricted square-product hosts on full intervals

The full-coefficient assignment wrappers put every square-product host in
an interval certificate cover. Its retained counting argument is valid on
any interval `[A,Z)`. A separate global assignment bound applies on
`[2,M+1)` for every `L ≤ M`, including lengths larger than the lower endpoint.
No separation, parity or bounded-ratio hypothesis enters the global result.
-/

namespace PaperC.V282.FullIntervalHostCounting

open Affine LargeKernelAssignments BoundedRatioRelationalHosts BoundedRatioGeometry
open TwoWindowParity TwoWindowSquareHosts ValueSquareRelations
open scoped BigOperators

noncomputable section

/-- Every unrestricted square-product host lies in the retained congruence cover.
No separation, block parity, ratio bound or condition `L ≤ A` is needed. -/
theorem squareProductHosts_subset_certificateCover
    {A Z L : ℕ} (hA : 2 ≤ A) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ boundedRatioBlock A Z ×ˢ boundedRatioBlock A Z) :
    squareProductHosts L s ⊆ certificateCover A Z L := by
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
        have h := (Finset.mem_Icc.mp (selectedLabel_mem_Icc hA hx i)).1
        simpa only [twoStartCompleteVertexLabel] using Nat.ne_of_gt h
    | inr i =>
        have h := (Finset.mem_Icc.mp (selectedLabel_mem_Icc hA hy i)).1
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
      have hn : n ∈ Finset.Icc 1 (Z + L) := selectedLabel_mem_Icc hA hx v
      have hyCert : xy.2 ∈ startsForSomeAssignment A Z L n := by
        apply FullIntervalPrimeAssignment.right_mem_boundedAssignment_of_selected_left
          hA hx hy c hEq v
        simp [c, hi]
      have hxLabel : xy.1 ∈ startsWithSelectedLabel A Z L n v := by
        rw [mem_startsWithSelectedLabel]
        exact ⟨hx, rfl⟩
      simp only [certificateCover, Finset.mem_biUnion]
      refine ⟨n, hn, v, Finset.mem_univ v, ?_⟩
      rw [Finset.mem_union]
      exact Or.inl (Finset.mem_product.mpr ⟨hxLabel, hyCert⟩)
  | inr v =>
      let n := startCompleteVertexLabel xy.2 L v
      have hn : n ∈ Finset.Icc 1 (Z + L) := selectedLabel_mem_Icc hA hy v
      have hxCert : xy.1 ∈ startsForSomeAssignment A Z L n := by
        apply FullIntervalPrimeAssignment.left_mem_boundedAssignment_of_selected_right
          hA hx hy c hEq v
        simp [c, hi]
      have hyLabel : xy.2 ∈ startsWithSelectedLabel A Z L n v := by
        rw [mem_startsWithSelectedLabel]
        exact ⟨hy, rfl⟩
      simp only [certificateCover, Finset.mem_biUnion]
      refine ⟨n, hn, v, Finset.mem_univ v, ?_⟩
      rw [Finset.mem_union]
      exact Or.inr (Finset.mem_product.mpr ⟨hxCert, hyLabel⟩)

/-- The retained cover itself satisfies the assignment-sum bound. -/
theorem card_certificateCover_cast_le_assignmentSum
    {A Z L : ℕ} (hA : 2 ≤ A) (hAZ : A ≤ Z) :
    ((certificateCover A Z L).card : ℚ) ≤
      2 * (L + 1 : ℚ) * ∑ n ∈ Finset.Icc 1 (Z + L), assignmentCountBound A Z L n := by
  classical
  have hcoverNat : (certificateCover A Z L).card ≤
      ∑ n ∈ Finset.Icc 1 (Z + L), ∑ v : Fin (L + 1),
        (leftCertificates A Z L n v ∪ rightCertificates A Z L n v).card := by
    unfold certificateCover
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (Z + L),
          ((Finset.univ : Finset (Fin (L + 1))).biUnion fun v =>
            leftCertificates A Z L n v ∪ rightCertificates A Z L n v).card :=
        Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum fun n _ => Finset.card_biUnion_le
  have hcover : ((certificateCover A Z L).card : ℚ) ≤
      ∑ n ∈ Finset.Icc 1 (Z + L), ∑ v : Fin (L + 1),
        ((leftCertificates A Z L n v ∪ rightCertificates A Z L n v).card : ℚ) := by
    exact_mod_cast hcoverNat
  calc
    _ ≤ _ := hcover
    _ ≤ ∑ n ∈ Finset.Icc 1 (Z + L), ∑ _v : Fin (L + 1),
        2 * assignmentCountBound A Z L n := by
      exact Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun v _ =>
        card_certificate_union_cast_le hA hAZ v
    _ = _ := by
      simp
      rw [Finset.mul_sum]
      ring

/-- An explicit finite assignment bound for unrestricted square-product hosts. -/
theorem card_squareProductHosts_cast_le_assignmentSum
    {A Z L : ℕ} (hA : 2 ≤ A) (hAZ : A ≤ Z) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ boundedRatioBlock A Z ×ˢ boundedRatioBlock A Z) :
    ((squareProductHosts L s).card : ℚ) ≤
      2 * (L + 1 : ℚ) * ∑ n ∈ Finset.Icc 1 (Z + L), assignmentCountBound A Z L n := by
  have hcover : ((squareProductHosts L s).card : ℚ) ≤ (certificateCover A Z L).card := by
    exact_mod_cast Finset.card_le_card
      (squareProductHosts_subset_certificateCover hA s hs)
  exact hcover.trans (card_certificateCover_cast_le_assignmentSum hA hAZ)

/-- On the global interval, the kernel is at most `3M` and the width is at
most `M`; this absorbs the CRT `+1` without any condition `L ≤ 2`. -/
theorem assignmentCountBound_global_le
    {M L n : ℕ} (hM : 2 ≤ M) (hL : L ≤ M)
    (hn : n ∈ Finset.Icc 1 (M + 1 + L)) :
    assignmentCountBound 2 (M + 1) L n ≤
      4 * (M : ℚ) * RelationalHosts.largeKernelWeightQ (L + 1) n := by
  have hnPos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hKBound : LargeOddKernel.largeOddKernel (L + 1) n ≤ 3 * M := by
    have hKle := LargeOddKernel.largeOddKernel_le (B := L + 1) hnPos
    have hnUpper := (Finset.mem_Icc.mp hn).2
    omega
  have hKpos : (0 : ℚ) < (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero (LargeOddKernel.largeOddKernel_ne_zero (L + 1) n)
  have hpartner :
      (((M + 1 : ℕ) : ℚ) - 2) /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) + 1 ≤
        4 * (M : ℚ) / (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) := by
    apply (le_div_iff₀ hKpos).2
    calc
      _ = (((M + 1 : ℕ) : ℚ) - 2) +
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) := by field_simp
      _ ≤ 4 * (M : ℚ) := by
        have hKcast : (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) ≤ 3 * (M : ℚ) := by
          exact_mod_cast hKBound
        push_cast
        linarith
  unfold assignmentCountBound RelationalHosts.largeKernelWeightQ
  let a : ℚ := (((L + 1) ^
    (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card : ℕ) : ℚ)
  change a * ((((M + 1 : ℕ) : ℚ) - 2) /
      (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) + 1) ≤
    4 * (M : ℚ) * (a / (LargeOddKernel.largeOddKernel (L + 1) n : ℚ))
  calc
    _ ≤ a * (4 * (M : ℚ) / (LargeOddKernel.largeOddKernel (L + 1) n : ℚ)) :=
      mul_le_mul_of_nonneg_left hpartner (by dsimp [a]; positivity)
    _ = _ := by ring

/-- A full-interval host bound for arbitrary masks of starts from `2` through
`M`, with no separation, parity or lower-endpoint length restriction. -/
theorem card_squareProductHosts_Icc_cast_le_kernelSumQ
    {M L : ℕ} (hM : 2 ≤ M) (hL : L ≤ M)
    (s : Finset (ℕ × ℕ))
    (hs : s ⊆ Finset.Icc 2 M ×ˢ Finset.Icc 2 M) :
    ((squareProductHosts L s).card : ℚ) ≤
      8 * (L + 1 : ℚ) * (M : ℚ) *
        ∑ n ∈ Finset.Icc 1 (3 * M), RelationalHosts.largeKernelWeightQ (L + 1) n := by
  have hs' : s ⊆ boundedRatioBlock 2 (M + 1) ×ˢ boundedRatioBlock 2 (M + 1) := by
    intro xy hxy
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hs hxy)
    apply Finset.mem_product.mpr
    constructor
    · exact mem_boundedRatioBlock.mpr ⟨(Finset.mem_Icc.mp hx).1,
        Nat.lt_succ_of_le (Finset.mem_Icc.mp hx).2⟩
    · exact mem_boundedRatioBlock.mpr ⟨(Finset.mem_Icc.mp hy).1,
        Nat.lt_succ_of_le (Finset.mem_Icc.mp hy).2⟩
  have hsubset : Finset.Icc 1 (M + 1 + L) ⊆ Finset.Icc 1 (3 * M) := by
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨hnlo, by omega⟩
  have hsum :
      (∑ n ∈ Finset.Icc 1 (M + 1 + L), RelationalHosts.largeKernelWeightQ (L + 1) n) ≤
        ∑ n ∈ Finset.Icc 1 (3 * M), RelationalHosts.largeKernelWeightQ (L + 1) n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro n _ _
    unfold RelationalHosts.largeKernelWeightQ
    positivity
  calc
    _ ≤ 2 * (L + 1 : ℚ) * ∑ n ∈ Finset.Icc 1 (M + 1 + L),
        assignmentCountBound 2 (M + 1) L n :=
      card_squareProductHosts_cast_le_assignmentSum (by omega) (by omega) s hs'
    _ ≤ 2 * (L + 1 : ℚ) * ∑ n ∈ Finset.Icc 1 (M + 1 + L),
        4 * (M : ℚ) * RelationalHosts.largeKernelWeightQ (L + 1) n := by
      gcongr with n hn
      exact assignmentCountBound_global_le hM hL hn
    _ = 8 * (L + 1 : ℚ) * (M : ℚ) *
        ∑ n ∈ Finset.Icc 1 (M + 1 + L), RelationalHosts.largeKernelWeightQ (L + 1) n := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

end
end PaperC.V282.FullIntervalHostCounting
