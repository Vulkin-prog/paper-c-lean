import PaperC.Combinatorics.LargeKernelAssignments

set_option maxHeartbeats 1600000

/-!
# Relational hosts and their finite certificate cover

This module defines the separated relational hosts from Lemma 4.2 and chooses,
for each host, one nonzero relation and its canonical first boundary
occurrence.  The prime-assignment theorem then places the opposite start in
one of the CRT classes counted in `LargeKernelAssignments`.

The resulting certificate cover is indexed by:

* the selected integer `n ≤ 3N`;
* its orientation (left or right block);
* one of `B = L+1` selected offsets;
* an assignment of the large odd primes of `n` to opposite offsets.
-/

namespace PaperC
namespace RelationalHosts

open scoped BigOperators
open Affine
open LargeKernelAssignments

noncomputable section

/-- Ordered separated pairs in the dyadic block whose joint row system has a
nontrivial relation. -/
def relationalHosts (N L : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun pair ↦
    L < Nat.dist pair.1 pair.2 ∧
      0 < relationRho
        (twoStartSystem (dyadicCutoff N L) pair.1 pair.2 L)

@[simp]
theorem mem_relationalHosts
    {N L x y : ℕ} :
    (x, y) ∈ relationalHosts N L ↔
      x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧
        L < Nat.dist x y ∧
        0 < relationRho
          (twoStartSystem (dyadicCutoff N L) x y L) := by
  classical
  simp only [relationalHosts, Finset.mem_filter,
    Finset.mem_product]
  tauto

/-- Positive relation defect is equivalent to existence of a nonzero
relation vector. -/
theorem exists_nonzero_relation_of_rho_pos
    {M x y L : ℕ}
    (h :
      0 < relationRho (twoStartSystem M x y L)) :
    ∃ u : RelationSpace (twoStartSystem M x y L), u ≠ 0 := by
  rw [relationRho, Module.finrank_pos_iff_exists_ne_zero] at h
  exact h

/-- A deterministic nonzero relation whenever the joint defect is positive;
zero otherwise. -/
noncomputable def chosenRelation
    (N L : ℕ) (pair : ℕ × ℕ) :
    RelationSpace
      (twoStartSystem (dyadicCutoff N L) pair.1 pair.2 L) :=
  if h :
      0 < relationRho
        (twoStartSystem (dyadicCutoff N L) pair.1 pair.2 L)
  then Classical.choose (exists_nonzero_relation_of_rho_pos h)
  else 0

theorem chosenRelation_ne_zero
    {N L : ℕ} {pair : ℕ × ℕ}
    (h :
      0 < relationRho
        (twoStartSystem (dyadicCutoff N L) pair.1 pair.2 L)) :
    chosenRelation N L pair ≠ 0 := by
  rw [chosenRelation, dif_pos h]
  exact Classical.choose_spec (exists_nonzero_relation_of_rho_pos h)

/-- Canonical first selected occurrence of the chosen relation. -/
noncomputable def selectedOccurrence
    (N L : ℕ) (pair : ℕ × ℕ) :
    Sum (Fin (L + 1)) (Fin (L + 1)) :=
  if h : chosenRelation N L pair ≠ 0 then
    relationCanonicalSelectedOccurrence
      (chosenRelation N L pair) h
  else
    Sum.inl (startRootVertex L)

theorem selectedOccurrence_ne_zero
    {N L : ℕ} {pair : ℕ × ℕ}
    (h :
      0 < relationRho
        (twoStartSystem (dyadicCutoff N L) pair.1 pair.2 L)) :
    twoStartCompleteBoundary L
        (chosenRelation N L pair :
          Sum (Fin L) (Fin L) → F₂)
        (selectedOccurrence N L pair) ≠
      0 := by
  have hu := chosenRelation_ne_zero h
  rw [selectedOccurrence, dif_pos hu]
  exact relationCanonicalSelectedOccurrence_ne_zero
    (chosenRelation N L pair) hu

/-- Starts in the dyadic block realizing one fixed selected label and offset. -/
def startsWithSelectedLabel
    (N L n : ℕ) (v : Fin (L + 1)) :
    Finset ℕ :=
  (dyadicBlock N).filter fun x ↦
    startCompleteVertexLabel x L v = n

@[simp]
theorem mem_startsWithSelectedLabel
    {N L n x : ℕ} {v : Fin (L + 1)} :
    x ∈ startsWithSelectedLabel N L n v ↔
      x ∈ dyadicBlock N ∧
        startCompleteVertexLabel x L v = n := by
  simp [startsWithSelectedLabel]

/-- For `N ≥ 2`, one label and one offset determine at most one start. -/
theorem card_startsWithSelectedLabel_le_one
    {N L n : ℕ} (hN : 2 ≤ N) (v : Fin (L + 1)) :
    (startsWithSelectedLabel N L n v).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  have hxData := mem_startsWithSelectedLabel.mp hx
  have hyData := mem_startsWithSelectedLabel.mp hy
  have hxTwo := two_le_of_mem_dyadicBlock hN hxData.1
  have hyTwo := two_le_of_mem_dyadicBlock hN hyData.1
  have hlabels := hxData.2.trans hyData.2.symm
  simp only [startCompleteVertexLabel] at hlabels
  split at hlabels <;> omega

/-- Certificates with the selected occurrence in the left block. -/
def leftCertificates
    (N L n : ℕ) (v : Fin (L + 1)) :
    Finset (ℕ × ℕ) :=
  (startsWithSelectedLabel N L n v) ×ˢ
    (startsForSomeAssignment N L n)

/-- Certificates with the selected occurrence in the right block. -/
def rightCertificates
    (N L n : ℕ) (v : Fin (L + 1)) :
    Finset (ℕ × ℕ) :=
  (startsForSomeAssignment N L n) ×ˢ
    (startsWithSelectedLabel N L n v)

/-- All certificate pairs with selected label in `[1,3N]`. -/
def certificateCover (N L : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.Icc 1 (3 * N)).biUnion fun n ↦
    (Finset.univ : Finset (Fin (L + 1))).biUnion fun v ↦
      leftCertificates N L n v ∪ rightCertificates N L n v

/-- A complete label based at `x ∈ [N,2N)` lies in `[1,3N]` when `N ≥ 2`
and `L ≤ N`. -/
theorem selectedLabel_mem_Icc
    {N L x : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hx : x ∈ dyadicBlock N) (v : Fin (L + 1)) :
    startCompleteVertexLabel x L v ∈ Finset.Icc 1 (3 * N) := by
  have hxTwo := two_le_of_mem_dyadicBlock hN hx
  have hupper :=
    startCompleteVertexLabel_le_dyadicCutoff hx v
  have hcutoff : dyadicCutoff N L ≤ 3 * N := by
    unfold dyadicCutoff
    omega
  rw [Finset.mem_Icc]
  constructor
  · simp only [startCompleteVertexLabel]
    split_ifs <;> omega
  · exact hupper.trans hcutoff

/--
Every separated relational host belongs to the finite certificate cover.
This is the formal bridge from `ρ(x,y)>0` to the CRT count.
-/
theorem relationalHosts_subset_certificateCover
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) :
    relationalHosts N L ⊆ certificateCover N L := by
  classical
  intro pair hpair
  obtain ⟨hx, hy, _hsep, hrho⟩ :=
    mem_relationalHosts.mp hpair
  let u := chosenRelation N L pair
  have hu : u ≠ 0 := chosenRelation_ne_zero hrho
  have hselected :
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂)
          (selectedOccurrence N L pair) ≠
        0 := by
    simpa [u] using selectedOccurrence_ne_zero hrho
  cases hs : selectedOccurrence N L pair with
  | inl v =>
      let n := startCompleteVertexLabel pair.1 L v
      have hn : n ∈ Finset.Icc 1 (3 * N) :=
        selectedLabel_mem_Icc hN hL hx v
      have hyCert :
          pair.2 ∈ startsForSomeAssignment N L n := by
        apply right_mem_startsForSomeAssignment_of_selected_left
          hN hx hy u v
        simpa [hs] using hselected
      have hxLabel :
          pair.1 ∈ startsWithSelectedLabel N L n v := by
        rw [mem_startsWithSelectedLabel]
        exact ⟨hx, rfl⟩
      simp only [certificateCover, Finset.mem_biUnion]
      refine ⟨n, hn, v, Finset.mem_univ v, ?_⟩
      rw [Finset.mem_union]
      exact Or.inl (Finset.mem_product.mpr ⟨hxLabel, hyCert⟩)
  | inr v =>
      let n := startCompleteVertexLabel pair.2 L v
      have hn : n ∈ Finset.Icc 1 (3 * N) :=
        selectedLabel_mem_Icc hN hL hy v
      have hxCert :
          pair.1 ∈ startsForSomeAssignment N L n := by
        apply left_mem_startsForSomeAssignment_of_selected_right
          hN hx hy u v
        simpa [hs] using hselected
      have hyLabel :
          pair.2 ∈ startsWithSelectedLabel N L n v := by
        rw [mem_startsWithSelectedLabel]
        exact ⟨hy, rfl⟩
      simp only [certificateCover, Finset.mem_biUnion]
      refine ⟨n, hn, v, Finset.mem_univ v, ?_⟩
      rw [Finset.mem_union]
      exact Or.inr (Finset.mem_product.mpr ⟨hxCert, hyLabel⟩)

/-- The assignment-count bound attached to one selected integer. -/
noncomputable def assignmentCountBound
    (N L n : ℕ) : ℚ :=
  (((L + 1) ^
      (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card : ℕ) : ℚ) *
    ((N : ℚ) /
        (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
      1)

theorem card_leftCertificates_cast_le
    {N L n : ℕ} (hN : 2 ≤ N) (v : Fin (L + 1)) :
    ((leftCertificates N L n v).card : ℚ) ≤
      assignmentCountBound N L n := by
  rw [leftCertificates, Finset.card_product, Nat.cast_mul]
  have hselected :
      ((startsWithSelectedLabel N L n v).card : ℚ) ≤ 1 := by
    exact_mod_cast card_startsWithSelectedLabel_le_one hN v
  have hopposite :=
    card_startsForSomeAssignment_cast_le
      (N := N) (L := L) (n := n) (by omega)
  unfold assignmentCountBound
  calc
    ((startsWithSelectedLabel N L n v).card : ℚ) *
          ((startsForSomeAssignment N L n).card : ℚ)
        ≤ 1 * ((startsForSomeAssignment N L n).card : ℚ) := by
      gcongr
    _ ≤ 1 *
        ((((L + 1) ^
            (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card :
              ℕ) : ℚ) *
          ((N : ℚ) /
              (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
            1)) := by
      gcongr
      simpa [Nat.cast_pow] using hopposite
    _ = (((L + 1) ^
          (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card :
            ℕ) : ℚ) *
        ((N : ℚ) /
            (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
          1) := by ring

theorem card_rightCertificates_cast_le
    {N L n : ℕ} (hN : 2 ≤ N) (v : Fin (L + 1)) :
    ((rightCertificates N L n v).card : ℚ) ≤
      assignmentCountBound N L n := by
  rw [rightCertificates, Finset.card_product, Nat.cast_mul]
  have hselected :
      ((startsWithSelectedLabel N L n v).card : ℚ) ≤ 1 := by
    exact_mod_cast card_startsWithSelectedLabel_le_one hN v
  have hopposite :=
    card_startsForSomeAssignment_cast_le
      (N := N) (L := L) (n := n) (by omega)
  unfold assignmentCountBound
  calc
    ((startsForSomeAssignment N L n).card : ℚ) *
          ((startsWithSelectedLabel N L n v).card : ℚ)
        ≤ ((startsForSomeAssignment N L n).card : ℚ) * 1 := by
      gcongr
    _ ≤
        ((((L + 1) ^
            (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card :
              ℕ) : ℚ) *
          ((N : ℚ) /
              (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
            1)) * 1 := by
      gcongr
      simpa [Nat.cast_pow] using hopposite
    _ = (((L + 1) ^
          (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card :
            ℕ) : ℚ) *
        ((N : ℚ) /
            (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
          1) := by ring

theorem card_certificate_union_cast_le
    {N L n : ℕ} (hN : 2 ≤ N) (v : Fin (L + 1)) :
    (((leftCertificates N L n v ∪
        rightCertificates N L n v).card : ℕ) : ℚ) ≤
      2 * assignmentCountBound N L n := by
  have hunion :
      ((leftCertificates N L n v ∪
          rightCertificates N L n v).card : ℚ) ≤
        (leftCertificates N L n v).card +
          (rightCertificates N L n v).card := by
    exact_mod_cast
      Finset.card_union_le
        (leftCertificates N L n v)
        (rightCertificates N L n v)
  calc
    ((leftCertificates N L n v ∪
        rightCertificates N L n v).card : ℚ)
        ≤ (leftCertificates N L n v).card +
          (rightCertificates N L n v).card := hunion
    _ ≤ assignmentCountBound N L n +
          assignmentCountBound N L n :=
      add_le_add
        (card_leftCertificates_cast_le hN v)
        (card_rightCertificates_cast_le hN v)
    _ = 2 * assignmentCountBound N L n := by ring

/--
Exact finite certificate bound before replacing `N/K + 1` by `4N/K`.
-/
theorem card_relationalHosts_cast_le_assignmentSum
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) :
    ((relationalHosts N L).card : ℚ) ≤
      2 * (L + 1 : ℚ) *
        ∑ n ∈ Finset.Icc 1 (3 * N),
          assignmentCountBound N L n := by
  classical
  have hhostCover :
      ((relationalHosts N L).card : ℚ) ≤
        (certificateCover N L).card := by
    exact_mod_cast Finset.card_le_card
      (relationalHosts_subset_certificateCover hN hL)
  have hcoverNat :
      (certificateCover N L).card ≤
        ∑ n ∈ Finset.Icc 1 (3 * N),
          ∑ v ∈ (Finset.univ : Finset (Fin (L + 1))),
            (leftCertificates N L n v ∪
              rightCertificates N L n v).card := by
    unfold certificateCover
    calc
      ((Finset.Icc 1 (3 * N)).biUnion fun n ↦
          (Finset.univ : Finset (Fin (L + 1))).biUnion fun v ↦
            leftCertificates N L n v ∪ rightCertificates N L n v).card
          ≤ ∑ n ∈ Finset.Icc 1 (3 * N),
              ((Finset.univ : Finset (Fin (L + 1))).biUnion
                fun v ↦ leftCertificates N L n v ∪
                  rightCertificates N L n v).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ n ∈ Finset.Icc 1 (3 * N),
            ∑ v ∈ (Finset.univ : Finset (Fin (L + 1))),
              (leftCertificates N L n v ∪
                rightCertificates N L n v).card := by
        exact Finset.sum_le_sum fun n _ ↦
          Finset.card_biUnion_le
  have hcover :
      ((certificateCover N L).card : ℚ) ≤
        ∑ n ∈ Finset.Icc 1 (3 * N),
          ∑ v ∈ (Finset.univ : Finset (Fin (L + 1))),
            (((leftCertificates N L n v ∪
              rightCertificates N L n v).card : ℕ) : ℚ) := by
    exact_mod_cast hcoverNat
  calc
    ((relationalHosts N L).card : ℚ)
        ≤ (certificateCover N L).card := hhostCover
    _ ≤ ∑ n ∈ Finset.Icc 1 (3 * N),
          ∑ v ∈ (Finset.univ : Finset (Fin (L + 1))),
            (((leftCertificates N L n v ∪
              rightCertificates N L n v).card : ℕ) : ℚ) := hcover
    _ ≤ ∑ n ∈ Finset.Icc 1 (3 * N),
          ∑ _v ∈ (Finset.univ : Finset (Fin (L + 1))),
            2 * assignmentCountBound N L n := by
      exact Finset.sum_le_sum fun n _ ↦
        Finset.sum_le_sum fun v _ ↦
          card_certificate_union_cast_le hN v
    _ = 2 * (L + 1 : ℚ) *
          ∑ n ∈ Finset.Icc 1 (3 * N),
            assignmentCountBound N L n := by
      simp
      rw [Finset.mul_sum]
      ring

/-- Rational form of the manuscript weight `B^ω(K_B(n))/K_B(n)`. -/
noncomputable def largeKernelWeightQ (B n : ℕ) : ℚ :=
  (((B ^
      (LargeOddKernel.largeOddPrimeSupport B n).card : ℕ) : ℚ) /
    (LargeOddKernel.largeOddKernel B n : ℚ))

/--
For `n ≤ 3N`, the soft bound `N/K + 1 ≤ 4N/K` converts one assignment
contribution to four times the manuscript kernel weight.
-/
theorem assignmentCountBound_le_four_mul_kernelWeightQ
    {N L n : ℕ} (hn : n ∈ Finset.Icc 1 (3 * N)) :
    assignmentCountBound N L n ≤
      4 * (N : ℚ) * largeKernelWeightQ (L + 1) n := by
  have hnPos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1
  have hKleN :
      LargeOddKernel.largeOddKernel (L + 1) n ≤ n :=
    LargeOddKernel.largeOddKernel_le hnPos
  have hKleThree :
      LargeOddKernel.largeOddKernel (L + 1) n ≤ 3 * N :=
    hKleN.trans (Finset.mem_Icc.mp hn).2
  have hKpos :
      (0 : ℚ) <
        (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (LargeOddKernel.largeOddKernel_ne_zero (L + 1) n)
  have hpartner :
      (N : ℚ) /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
        1 ≤
      4 * (N : ℚ) /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) := by
    apply (le_div_iff₀ hKpos).2
    calc
      ((N : ℚ) /
            (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
          1) *
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) =
        (N : ℚ) +
          LargeOddKernel.largeOddKernel (L + 1) n := by
            field_simp
      _ ≤ 4 * (N : ℚ) := by
        exact_mod_cast (by omega : N +
          LargeOddKernel.largeOddKernel (L + 1) n ≤ 4 * N)
  unfold assignmentCountBound largeKernelWeightQ
  let A : ℚ :=
    (((L + 1) ^
      (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card :
        ℕ) : ℚ)
  have hA : 0 ≤ A := by positivity
  change
    A * ((N : ℚ) /
        (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) + 1) ≤
      4 * (N : ℚ) *
        (A /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ))
  calc
    A * ((N : ℚ) /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) + 1)
        ≤ A * (4 * (N : ℚ) /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ)) :=
      mul_le_mul_of_nonneg_left hpartner hA
    _ = 4 * (N : ℚ) *
        (A /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ)) := by
      ring

/--
The explicit finite estimate displayed in Lemma 4.2:

`H₂(N,L) ≤ 8 (L+1) N ∑_{1≤n≤3N} (L+1)^ω(K)/K`.
-/
theorem card_relationalHosts_cast_le_kernelSumQ
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) :
    ((relationalHosts N L).card : ℚ) ≤
      8 * (L + 1 : ℚ) * (N : ℚ) *
        ∑ n ∈ Finset.Icc 1 (3 * N),
          largeKernelWeightQ (L + 1) n := by
  calc
    ((relationalHosts N L).card : ℚ)
        ≤ 2 * (L + 1 : ℚ) *
          ∑ n ∈ Finset.Icc 1 (3 * N),
            assignmentCountBound N L n :=
      card_relationalHosts_cast_le_assignmentSum hN hL
    _ ≤ 2 * (L + 1 : ℚ) *
          ∑ n ∈ Finset.Icc 1 (3 * N),
            (4 * (N : ℚ) *
              largeKernelWeightQ (L + 1) n) := by
      gcongr with n hn
      exact assignmentCountBound_le_four_mul_kernelWeightQ
        hn
    _ = 8 * (L + 1 : ℚ) * (N : ℚ) *
          ∑ n ∈ Finset.Icc 1 (3 * N),
            largeKernelWeightQ (L + 1) n := by
      rw [← Finset.mul_sum]
      ring

end

end RelationalHosts
end PaperC
