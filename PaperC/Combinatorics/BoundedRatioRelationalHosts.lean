import PaperC.Combinatorics.BoundedRatioGeometry
import PaperC.Combinatorics.RelationalHosts

set_option maxHeartbeats 1800000

/-!
# Relational hosts on a bounded-ratio interval

This module transports the finite certificate argument of Lemma 4.2 from
the dyadic block `[N,2N)` to the literal interval `[N,M)` used in Section 17.
The relation space is formed at the exact adequate cutoff `M + L`.

The proof does not cover `[N,M)` by dyadic shells: pairs crossing two shells
are treated directly.  For one selected boundary label, the opposite start
still lies in one residue class modulo the large odd kernel.  Only the length
of the interval changes, from `N` to `M-N`.
-/

namespace PaperC
namespace BoundedRatioRelationalHosts

open scoped BigOperators Function
open Finset
open Affine
open BoundedRatioGeometry
open LargeKernelAssignments

noncomputable section

/-! ## The literal population and its selected relation -/

/-- Ordered separated pairs in `[N,M)` with a nontrivial relation at cutoff
`M+L`. -/
def boundedRelationalHosts (N M L : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    ((boundedRatioBlock N M) ×ˢ (boundedRatioBlock N M)).filter fun pair ↦
      L < Nat.dist pair.1 pair.2 ∧
        0 < relationRho (twoStartSystem (M + L) pair.1 pair.2 L)

@[simp]
theorem mem_boundedRelationalHosts
    {N M L x y : ℕ} :
    (x, y) ∈ boundedRelationalHosts N M L ↔
      x ∈ boundedRatioBlock N M ∧
      y ∈ boundedRatioBlock N M ∧
      L < Nat.dist x y ∧
      0 < relationRho (twoStartSystem (M + L) x y L) := by
  classical
  simp only [boundedRelationalHosts, Finset.mem_filter,
    Finset.mem_product]
  tauto

/-- A deterministic nonzero relation for a bounded-interval host. -/
noncomputable def chosenRelation
    (M L : ℕ) (pair : ℕ × ℕ) :
    RelationSpace (twoStartSystem (M + L) pair.1 pair.2 L) :=
  if h :
      0 < relationRho (twoStartSystem (M + L) pair.1 pair.2 L)
  then
    Classical.choose
      (RelationalHosts.exists_nonzero_relation_of_rho_pos h)
  else 0

theorem chosenRelation_ne_zero
    {M L : ℕ} {pair : ℕ × ℕ}
    (h :
      0 < relationRho (twoStartSystem (M + L) pair.1 pair.2 L)) :
    chosenRelation M L pair ≠ 0 := by
  rw [chosenRelation, dif_pos h]
  exact
    Classical.choose_spec
      (RelationalHosts.exists_nonzero_relation_of_rho_pos h)

/-- Canonical first nonzero complete-boundary occurrence. -/
noncomputable def selectedOccurrence
    (M L : ℕ) (pair : ℕ × ℕ) :
    Sum (Fin (L + 1)) (Fin (L + 1)) :=
  if h : chosenRelation M L pair ≠ 0 then
    relationCanonicalSelectedOccurrence (chosenRelation M L pair) h
  else
    Sum.inl (startRootVertex L)

theorem selectedOccurrence_ne_zero
    {M L : ℕ} {pair : ℕ × ℕ}
    (h :
      0 < relationRho (twoStartSystem (M + L) pair.1 pair.2 L)) :
    twoStartCompleteBoundary L
        (chosenRelation M L pair :
          Sum (Fin L) (Fin L) → F₂)
        (selectedOccurrence M L pair) ≠ 0 := by
  have hu := chosenRelation_ne_zero h
  rw [selectedOccurrence, dif_pos hu]
  exact
    relationCanonicalSelectedOccurrence_ne_zero
      (chosenRelation M L pair) hu

/-! ## Starts realizing labels and large-prime assignments -/

/-- Starts in `[N,M)` realizing one selected label at one fixed offset. -/
def startsWithSelectedLabel
    (N M L n : ℕ) (v : Fin (L + 1)) : Finset ℕ :=
  (boundedRatioBlock N M).filter fun x ↦
    startCompleteVertexLabel x L v = n

@[simp]
theorem mem_startsWithSelectedLabel
    {N M L n x : ℕ} {v : Fin (L + 1)} :
    x ∈ startsWithSelectedLabel N M L n v ↔
      x ∈ boundedRatioBlock N M ∧
      startCompleteVertexLabel x L v = n := by
  simp [startsWithSelectedLabel]

/-- One label and one offset determine at most one positive start. -/
theorem card_startsWithSelectedLabel_le_one
    {N M L n : ℕ} (hN : 2 ≤ N) (v : Fin (L + 1)) :
    (startsWithSelectedLabel N M L n v).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  have hxData := mem_startsWithSelectedLabel.mp hx
  have hyData := mem_startsWithSelectedLabel.mp hy
  have hxTwo : 2 ≤ x :=
    hN.trans (mem_boundedRatioBlock.mp hxData.1).1
  have hyTwo : 2 ≤ y :=
    hN.trans (mem_boundedRatioBlock.mp hyData.1).1
  have hlabels := hxData.2.trans hyData.2.symm
  simp only [startCompleteVertexLabel] at hlabels
  split at hlabels <;> omega

/-- Starts in `[N,M)` realizing one fixed large-prime assignment. -/
def startsForAssignment
    (N M L n : ℕ) (assignment : LargePrimeAssignment L n) :
    Finset ℕ := by
  classical
  exact (boundedRatioBlock N M).filter fun y ↦
    ∀ p : LargePrimeIndex L n,
      parityVec
          (startCompleteVertexLabel y L (assignment p))
          p.1 ≠ 0

@[simp]
theorem mem_startsForAssignment
    {N M L n y : ℕ} {assignment : LargePrimeAssignment L n} :
    y ∈ startsForAssignment N M L n assignment ↔
      y ∈ boundedRatioBlock N M ∧
      ∀ p : LargePrimeIndex L n,
        parityVec
            (startCompleteVertexLabel y L (assignment p))
            p.1 ≠ 0 := by
  classical
  simp [startsForAssignment]

/-- Two starts realizing one assignment are congruent modulo the complete
large odd kernel. -/
theorem pairwise_modEq_largeOddKernel
    {N M L n : ℕ} (hN : 1 ≤ N)
    (assignment : LargePrimeAssignment L n)
    {y z : ℕ}
    (hy : y ∈ startsForAssignment N M L n assignment)
    (hz : z ∈ startsForAssignment N M L n assignment) :
    y ≡ z [MOD LargeOddKernel.largeOddKernel (L + 1) n] := by
  classical
  have hyBlock := (mem_startsForAssignment.mp hy).1
  have hzBlock := (mem_startsForAssignment.mp hz).1
  have hyOne : 1 ≤ y :=
    hN.trans (mem_boundedRatioBlock.mp hyBlock).1
  have hzOne : 1 ≤ z :=
    hN.trans (mem_boundedRatioBlock.mp hzBlock).1
  have hperPrime :
      ∀ p ∈
          (LargeOddKernel.largeOddPrimeSupport (L + 1) n).toList,
        y ≡ z [MOD p] := by
    intro p hp
    let pIndex : LargePrimeIndex L n :=
      ⟨p, by simpa using hp⟩
    have hyParity :=
      (mem_startsForAssignment.mp hy).2 pIndex
    have hzParity :=
      (mem_startsForAssignment.mp hz).2 pIndex
    exact
      LargeKernelAssignments.start_modEq_of_assigned_labels_dvd
        hyOne hzOne (assignment pIndex)
        (Affine.RelationalPrimeAssignment.dvd_of_parityVec_ne_zero
          hyParity)
        (Affine.RelationalPrimeAssignment.dvd_of_parityVec_ne_zero
          hzParity)
  have hcrt :=
    (Nat.modEq_list_prod_iff
      (LargeKernelAssignments.largeSupport_toList_pairwise_coprime L n)).mpr
      (fun i ↦ hperPrime
        ((LargeOddKernel.largeOddPrimeSupport (L + 1) n).toList.get i)
        ((LargeOddKernel.largeOddPrimeSupport (L + 1) n).toList.get_mem i))
  simpa [LargeOddKernel.largeOddKernel] using hcrt

/-- One assignment contributes at most one residue class in `[N,M)`. -/
theorem card_startsForAssignment_cast_le
    {N M L n : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M)
    (assignment : LargePrimeAssignment L n) :
    ((startsForAssignment N M L n assignment).card : ℚ) ≤
      ((M : ℚ) - (N : ℚ)) /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
        1 := by
  classical
  by_cases hempty : startsForAssignment N M L n assignment = ∅
  · simp [hempty]
    have hwidth : (0 : ℚ) ≤ (M : ℚ) - (N : ℚ) := by
      exact sub_nonneg.mpr (by exact_mod_cast hNM)
    positivity
  · have hnonempty :
        (startsForAssignment N M L n assignment).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let z : ℕ := (startsForAssignment N M L n assignment).min' hnonempty
    have hz : z ∈ startsForAssignment N M L n assignment :=
      Finset.min'_mem _ _
    have hsubset :
        startsForAssignment N M L n assignment ⊆
          {y ∈ Finset.Ico N M |
            y ≡ z [MOD
              LargeOddKernel.largeOddKernel (L + 1) n]} := by
      intro y hy
      have hyBlock := (mem_startsForAssignment.mp hy).1
      simp only [Finset.mem_filter]
      exact
        ⟨by simpa [boundedRatioBlock] using hyBlock,
          pairwise_modEq_largeOddKernel hN assignment hy hz⟩
    have hcard :
        ((startsForAssignment N M L n assignment).card : ℚ) ≤
          ((#{y ∈ Finset.Ico N M |
              y ≡ z [MOD
                LargeOddKernel.largeOddKernel (L + 1) n]} : ℕ) : ℚ) := by
      exact_mod_cast Finset.card_le_card hsubset
    refine hcard.trans ?_
    have hinterval :=
      card_nat_Ico_modEq_cast_le_div_add_one
        N M z
        (LargeOddKernel.largeOddKernel (L + 1) n)
        (Nat.pos_of_ne_zero
          (LargeOddKernel.largeOddKernel_ne_zero (L + 1) n))
        hNM
    have hlength :
        (((((M : ℤ) - (N : ℤ)) : ℤ) : ℚ)) =
          (M : ℚ) - (N : ℚ) := by
      push_cast
      ring
    rw [hlength] at hinterval
    exact hinterval

/-- Union over every large-prime assignment. -/
def startsForSomeAssignment (N M L n : ℕ) : Finset ℕ :=
  (allAssignments L n).biUnion
    (startsForAssignment N M L n)

@[simp]
theorem mem_startsForSomeAssignment
    {N M L n y : ℕ} :
    y ∈ startsForSomeAssignment N M L n ↔
      ∃ assignment : LargePrimeAssignment L n,
        y ∈ startsForAssignment N M L n assignment := by
  classical
  simp [startsForSomeAssignment, allAssignments]

/-- Assignment count on an interval of arbitrary nonnegative length. -/
noncomputable def assignmentCountBound
    (N M L n : ℕ) : ℚ :=
  (((L + 1) ^
      (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card : ℕ) : ℚ) *
    (((M : ℚ) - (N : ℚ)) /
        (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
      1)

theorem card_startsForSomeAssignment_cast_le
    {N M L n : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    ((startsForSomeAssignment N M L n).card : ℚ) ≤
      assignmentCountBound N M L n := by
  classical
  calc
    ((startsForSomeAssignment N M L n).card : ℚ)
        ≤ (∑ assignment ∈ allAssignments L n,
            (startsForAssignment N M L n assignment).card : ℕ) := by
          exact_mod_cast Finset.card_biUnion_le
    _ = ∑ assignment ∈ allAssignments L n,
          ((startsForAssignment N M L n assignment).card : ℚ) := by
      norm_cast
    _ ≤ ∑ _assignment ∈ allAssignments L n,
          (((M : ℚ) - (N : ℚ)) /
              (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
            1) := by
      exact Finset.sum_le_sum fun assignment _ ↦
        card_startsForAssignment_cast_le hN hNM assignment
    _ = ((allAssignments L n).card : ℚ) *
          (((M : ℚ) - (N : ℚ)) /
              (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
            1) := by
      simp
      ring
    _ = assignmentCountBound N M L n := by
      rw [card_allAssignments]
      simp only [assignmentCountBound]

/-! ## Relation-to-certificate transport -/

/-- Every complete label of a start in `[N,M)` is represented at cutoff
`M+L`. -/
theorem startCompleteVertexLabel_le_cutoff
    {N M L x : ℕ}
    (hx : x ∈ boundedRatioBlock N M)
    (v : Fin (L + 1)) :
    startCompleteVertexLabel x L v ≤ M + L := by
  have hxData := mem_boundedRatioBlock.mp hx
  simp only [startCompleteVertexLabel]
  split_ifs <;> omega

/-- A selected label belongs to the exact indexing interval `[1,M+L]`. -/
theorem selectedLabel_mem_Icc
    {N M L x : ℕ} (hN : 2 ≤ N)
    (hx : x ∈ boundedRatioBlock N M)
    (v : Fin (L + 1)) :
    startCompleteVertexLabel x L v ∈ Finset.Icc 1 (M + L) := by
  rw [Finset.mem_Icc]
  constructor
  · have hxTwo : 2 ≤ x :=
      hN.trans (mem_boundedRatioBlock.mp hx).1
    simp only [startCompleteVertexLabel]
    split_ifs <;> omega
  · exact startCompleteVertexLabel_le_cutoff hx v

/-- Left-selected relation transport to a bounded-interval assignment. -/
theorem right_mem_startsForSomeAssignment_of_selected_left
    {N M L x y : ℕ} (hN : 2 ≤ N)
    (hx : x ∈ boundedRatioBlock N M)
    (hy : y ∈ boundedRatioBlock N M)
    (u : RelationSpace (twoStartSystem (M + L) x y L))
    (v : Fin (L + 1))
    (hvSelected :
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inl v) ≠ 0) :
    y ∈ startsForSomeAssignment N M L
      (startCompleteVertexLabel x L v) := by
  classical
  have hxTwo : 2 ≤ x :=
    hN.trans (mem_boundedRatioBlock.mp hx).1
  have hyTwo : 2 ≤ y :=
    hN.trans (mem_boundedRatioBlock.mp hy).1
  let assignment :
      LargePrimeAssignment L (startCompleteVertexLabel x L v) :=
    fun p ↦ Classical.choose
      (Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_left
        hxTwo hyTwo u v hvSelected
        (startCompleteVertexLabel_le_cutoff hx v) p.2)
  rw [mem_startsForSomeAssignment]
  refine ⟨assignment, ?_⟩
  rw [mem_startsForAssignment]
  refine ⟨hy, ?_⟩
  intro p
  exact
    (Classical.choose_spec
      (Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_left
        hxTwo hyTwo u v hvSelected
        (startCompleteVertexLabel_le_cutoff hx v) p.2)).1.2

/-- Symmetric right-selected relation transport. -/
theorem left_mem_startsForSomeAssignment_of_selected_right
    {N M L x y : ℕ} (hN : 2 ≤ N)
    (hx : x ∈ boundedRatioBlock N M)
    (hy : y ∈ boundedRatioBlock N M)
    (u : RelationSpace (twoStartSystem (M + L) x y L))
    (v : Fin (L + 1))
    (hvSelected :
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inr v) ≠ 0) :
    x ∈ startsForSomeAssignment N M L
      (startCompleteVertexLabel y L v) := by
  classical
  have hxTwo : 2 ≤ x :=
    hN.trans (mem_boundedRatioBlock.mp hx).1
  have hyTwo : 2 ≤ y :=
    hN.trans (mem_boundedRatioBlock.mp hy).1
  let assignment :
      LargePrimeAssignment L (startCompleteVertexLabel y L v) :=
    fun p ↦ Classical.choose
      (Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_right
        hxTwo hyTwo u v hvSelected
        (startCompleteVertexLabel_le_cutoff hy v) p.2)
  rw [mem_startsForSomeAssignment]
  refine ⟨assignment, ?_⟩
  rw [mem_startsForAssignment]
  refine ⟨hx, ?_⟩
  intro p
  exact
    (Classical.choose_spec
      (Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_right
        hxTwo hyTwo u v hvSelected
        (startCompleteVertexLabel_le_cutoff hy v) p.2)).1.2

/-! ## The finite certificate cover -/

def leftCertificates
    (N M L n : ℕ) (v : Fin (L + 1)) :
    Finset (ℕ × ℕ) :=
  (startsWithSelectedLabel N M L n v) ×ˢ
    (startsForSomeAssignment N M L n)

def rightCertificates
    (N M L n : ℕ) (v : Fin (L + 1)) :
    Finset (ℕ × ℕ) :=
  (startsForSomeAssignment N M L n) ×ˢ
    (startsWithSelectedLabel N M L n v)

/-- All certificates indexed by the exact adequate cutoff. -/
def certificateCover (N M L : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.Icc 1 (M + L)).biUnion fun n ↦
    (Finset.univ : Finset (Fin (L + 1))).biUnion fun v ↦
      leftCertificates N M L n v ∪ rightCertificates N M L n v

/-- Every bounded relational host is covered by a selected-label
certificate. -/
theorem boundedRelationalHosts_subset_certificateCover
    {N M L : ℕ} (hN : 2 ≤ N) :
    boundedRelationalHosts N M L ⊆ certificateCover N M L := by
  classical
  intro pair hpair
  obtain ⟨hx, hy, _hsep, hrho⟩ :=
    mem_boundedRelationalHosts.mp hpair
  let u := chosenRelation M L pair
  have hu : u ≠ 0 := chosenRelation_ne_zero hrho
  have hselected :
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂)
          (selectedOccurrence M L pair) ≠ 0 := by
    simpa [u] using selectedOccurrence_ne_zero hrho
  cases hs : selectedOccurrence M L pair with
  | inl v =>
      let n := startCompleteVertexLabel pair.1 L v
      have hn : n ∈ Finset.Icc 1 (M + L) :=
        selectedLabel_mem_Icc hN hx v
      have hyCert :
          pair.2 ∈ startsForSomeAssignment N M L n := by
        apply right_mem_startsForSomeAssignment_of_selected_left
          hN hx hy u v
        simpa [hs] using hselected
      have hxLabel :
          pair.1 ∈ startsWithSelectedLabel N M L n v := by
        rw [mem_startsWithSelectedLabel]
        exact ⟨hx, rfl⟩
      simp only [certificateCover, Finset.mem_biUnion]
      refine ⟨n, hn, v, Finset.mem_univ v, ?_⟩
      rw [Finset.mem_union]
      exact Or.inl (Finset.mem_product.mpr ⟨hxLabel, hyCert⟩)
  | inr v =>
      let n := startCompleteVertexLabel pair.2 L v
      have hn : n ∈ Finset.Icc 1 (M + L) :=
        selectedLabel_mem_Icc hN hy v
      have hxCert :
          pair.1 ∈ startsForSomeAssignment N M L n := by
        apply left_mem_startsForSomeAssignment_of_selected_right
          hN hx hy u v
        simpa [hs] using hselected
      have hyLabel :
          pair.2 ∈ startsWithSelectedLabel N M L n v := by
        rw [mem_startsWithSelectedLabel]
        exact ⟨hy, rfl⟩
      simp only [certificateCover, Finset.mem_biUnion]
      refine ⟨n, hn, v, Finset.mem_univ v, ?_⟩
      rw [Finset.mem_union]
      exact Or.inr (Finset.mem_product.mpr ⟨hxCert, hyLabel⟩)

theorem card_leftCertificates_cast_le
    {N M L n : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M)
    (v : Fin (L + 1)) :
    ((leftCertificates N M L n v).card : ℚ) ≤
      assignmentCountBound N M L n := by
  rw [leftCertificates, Finset.card_product, Nat.cast_mul]
  have hselected :
      ((startsWithSelectedLabel N M L n v).card : ℚ) ≤ 1 := by
    exact_mod_cast card_startsWithSelectedLabel_le_one hN v
  have hopposite :=
    card_startsForSomeAssignment_cast_le
      (N := N) (M := M) (L := L) (n := n)
      (by omega) hNM
  calc
    ((startsWithSelectedLabel N M L n v).card : ℚ) *
          ((startsForSomeAssignment N M L n).card : ℚ)
        ≤ 1 * ((startsForSomeAssignment N M L n).card : ℚ) := by
      gcongr
    _ ≤ 1 * assignmentCountBound N M L n := by
      gcongr
    _ = assignmentCountBound N M L n := by ring

theorem card_rightCertificates_cast_le
    {N M L n : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M)
    (v : Fin (L + 1)) :
    ((rightCertificates N M L n v).card : ℚ) ≤
      assignmentCountBound N M L n := by
  rw [rightCertificates, Finset.card_product, Nat.cast_mul]
  have hselected :
      ((startsWithSelectedLabel N M L n v).card : ℚ) ≤ 1 := by
    exact_mod_cast card_startsWithSelectedLabel_le_one hN v
  have hopposite :=
    card_startsForSomeAssignment_cast_le
      (N := N) (M := M) (L := L) (n := n)
      (by omega) hNM
  calc
    ((startsForSomeAssignment N M L n).card : ℚ) *
          ((startsWithSelectedLabel N M L n v).card : ℚ)
        ≤ ((startsForSomeAssignment N M L n).card : ℚ) * 1 := by
      gcongr
    _ ≤ assignmentCountBound N M L n * 1 := by
      gcongr
    _ = assignmentCountBound N M L n := by ring

theorem card_certificate_union_cast_le
    {N M L n : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M)
    (v : Fin (L + 1)) :
    ((leftCertificates N M L n v ∪
        rightCertificates N M L n v).card : ℚ) ≤
      2 * assignmentCountBound N M L n := by
  have hunion :
      ((leftCertificates N M L n v ∪
          rightCertificates N M L n v).card : ℚ) ≤
        (leftCertificates N M L n v).card +
          (rightCertificates N M L n v).card := by
    exact_mod_cast
      Finset.card_union_le
        (leftCertificates N M L n v)
        (rightCertificates N M L n v)
  calc
    ((leftCertificates N M L n v ∪
        rightCertificates N M L n v).card : ℚ)
        ≤ (leftCertificates N M L n v).card +
          (rightCertificates N M L n v).card := hunion
    _ ≤ assignmentCountBound N M L n +
          assignmentCountBound N M L n :=
      add_le_add
        (card_leftCertificates_cast_le hN hNM v)
        (card_rightCertificates_cast_le hN hNM v)
    _ = 2 * assignmentCountBound N M L n := by ring

/-- Exact finite cover bound, before using `M ≤ κ₀N`. -/
theorem card_boundedRelationalHosts_cast_le_assignmentSum
    {N M L : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((boundedRelationalHosts N M L).card : ℚ) ≤
      2 * (L + 1 : ℚ) *
        ∑ n ∈ Finset.Icc 1 (M + L),
          assignmentCountBound N M L n := by
  classical
  have hhostCover :
      ((boundedRelationalHosts N M L).card : ℚ) ≤
        (certificateCover N M L).card := by
    exact_mod_cast Finset.card_le_card
      (boundedRelationalHosts_subset_certificateCover hN)
  have hcoverNat :
      (certificateCover N M L).card ≤
        ∑ n ∈ Finset.Icc 1 (M + L),
          ∑ v ∈ (Finset.univ : Finset (Fin (L + 1))),
            (leftCertificates N M L n v ∪
              rightCertificates N M L n v).card := by
    unfold certificateCover
    calc
      ((Finset.Icc 1 (M + L)).biUnion fun n ↦
          (Finset.univ : Finset (Fin (L + 1))).biUnion fun v ↦
            leftCertificates N M L n v ∪
              rightCertificates N M L n v).card
          ≤ ∑ n ∈ Finset.Icc 1 (M + L),
              ((Finset.univ : Finset (Fin (L + 1))).biUnion fun v ↦
                leftCertificates N M L n v ∪
                  rightCertificates N M L n v).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ n ∈ Finset.Icc 1 (M + L),
            ∑ v ∈ (Finset.univ : Finset (Fin (L + 1))),
              (leftCertificates N M L n v ∪
                rightCertificates N M L n v).card := by
        exact Finset.sum_le_sum fun n _ ↦
          Finset.card_biUnion_le
  have hcover :
      ((certificateCover N M L).card : ℚ) ≤
        ∑ n ∈ Finset.Icc 1 (M + L),
          ∑ v ∈ (Finset.univ : Finset (Fin (L + 1))),
            ((leftCertificates N M L n v ∪
              rightCertificates N M L n v).card : ℚ) := by
    exact_mod_cast hcoverNat
  calc
    ((boundedRelationalHosts N M L).card : ℚ)
        ≤ (certificateCover N M L).card := hhostCover
    _ ≤ ∑ n ∈ Finset.Icc 1 (M + L),
          ∑ v ∈ (Finset.univ : Finset (Fin (L + 1))),
            ((leftCertificates N M L n v ∪
              rightCertificates N M L n v).card : ℚ) := hcover
    _ ≤ ∑ n ∈ Finset.Icc 1 (M + L),
          ∑ _v ∈ (Finset.univ : Finset (Fin (L + 1))),
            2 * assignmentCountBound N M L n := by
      exact Finset.sum_le_sum fun n _ ↦
        Finset.sum_le_sum fun v _ ↦
          card_certificate_union_cast_le hN hNM v
    _ = 2 * (L + 1 : ℚ) *
          ∑ n ∈ Finset.Icc 1 (M + L),
            assignmentCountBound N M L n := by
      simp
      rw [Finset.mul_sum]
      ring

/-! ## Uniform finite kernel-sum estimate -/

/-- Under `M ≤ κ₀N` and `L ≤ N`, the interval assignment cost is at most
`2(κ₀+1)N` times the canonical kernel weight. -/
theorem assignmentCountBound_le_ratio_mul_kernelWeightQ
    {κ₀ N M L n : ℕ}
    (hNM : N ≤ M) (hMκ : M ≤ κ₀ * N) (hL : L ≤ N)
    (hn : n ∈ Finset.Icc 1 (M + L)) :
    assignmentCountBound N M L n ≤
      (2 * (κ₀ + 1) : ℚ) * (N : ℚ) *
        RelationalHosts.largeKernelWeightQ (L + 1) n := by
  have hnPos : 0 < n :=
    Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1
  have hKleN :
      LargeOddKernel.largeOddKernel (L + 1) n ≤ n :=
    LargeOddKernel.largeOddKernel_le hnPos
  have hKBound :
      LargeOddKernel.largeOddKernel (L + 1) n ≤
        (κ₀ + 1) * N := by
    calc
      LargeOddKernel.largeOddKernel (L + 1) n ≤ n := hKleN
      _ ≤ M + L := (Finset.mem_Icc.mp hn).2
      _ ≤ (κ₀ + 1) * N := by
        calc
          M + L ≤ κ₀ * N + N := Nat.add_le_add hMκ hL
          _ = (κ₀ + 1) * N := by ring
  have hwidth :
      (M : ℚ) - (N : ℚ) ≤ (κ₀ : ℚ) * (N : ℚ) := by
    have hMN : M - N ≤ κ₀ * N := (Nat.sub_le M N).trans hMκ
    have hcast : ((M - N : ℕ) : ℚ) ≤ (κ₀ * N : ℕ) := by
      exact_mod_cast hMN
    simpa [Nat.cast_mul, Nat.cast_sub hNM] using hcast
  have hKpos :
      (0 : ℚ) <
        (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) := by
    exact_mod_cast
      Nat.pos_of_ne_zero
        (LargeOddKernel.largeOddKernel_ne_zero (L + 1) n)
  have hpartner :
      ((M : ℚ) - (N : ℚ)) /
            (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
          1 ≤
        (2 * (κ₀ + 1) : ℚ) * (N : ℚ) /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) := by
    apply (le_div_iff₀ hKpos).2
    calc
      (((M : ℚ) - (N : ℚ)) /
              (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
            1) *
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) =
        ((M : ℚ) - (N : ℚ)) +
          LargeOddKernel.largeOddKernel (L + 1) n := by
        field_simp
      _ ≤ (κ₀ : ℚ) * (N : ℚ) +
          (κ₀ + 1 : ℚ) * (N : ℚ) := by
        gcongr
        exact_mod_cast hKBound
      _ ≤ (2 * (κ₀ + 1) : ℚ) * (N : ℚ) := by
        have hNnonneg : (0 : ℚ) ≤ (N : ℚ) := by positivity
        nlinarith
  unfold assignmentCountBound RelationalHosts.largeKernelWeightQ
  let A : ℚ :=
    (((L + 1) ^
      (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card : ℕ) : ℚ)
  have hA : 0 ≤ A := by positivity
  change
    A * (((M : ℚ) - (N : ℚ)) /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) + 1) ≤
      (2 * (κ₀ + 1) : ℚ) * (N : ℚ) *
        (A /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ))
  calc
    A * (((M : ℚ) - (N : ℚ)) /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) + 1)
        ≤ A * ((2 * (κ₀ + 1) : ℚ) * (N : ℚ) /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ)) :=
      mul_le_mul_of_nonneg_left hpartner hA
    _ = (2 * (κ₀ + 1) : ℚ) * (N : ℚ) *
        (A /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ)) := by
      ring

/-- Finite bounded-ratio version of the kernel-sum estimate in Lemma 4.2. -/
theorem card_boundedRelationalHosts_cast_le_kernelSumQ
    {κ₀ N M L : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) :
    ((boundedRelationalHosts N M L).card : ℚ) ≤
      4 * (κ₀ + 1 : ℚ) * (L + 1 : ℚ) * (N : ℚ) *
        ∑ n ∈ Finset.Icc 1 (M + L),
          RelationalHosts.largeKernelWeightQ (L + 1) n := by
  calc
    ((boundedRelationalHosts N M L).card : ℚ)
        ≤ 2 * (L + 1 : ℚ) *
          ∑ n ∈ Finset.Icc 1 (M + L),
            assignmentCountBound N M L n :=
      card_boundedRelationalHosts_cast_le_assignmentSum hN hNM
    _ ≤ 2 * (L + 1 : ℚ) *
          ∑ n ∈ Finset.Icc 1 (M + L),
            ((2 * (κ₀ + 1) : ℚ) * (N : ℚ) *
              RelationalHosts.largeKernelWeightQ (L + 1) n) := by
      gcongr with n hn
      exact
        assignmentCountBound_le_ratio_mul_kernelWeightQ
          hNM hMκ hL hn
    _ = 4 * (κ₀ + 1 : ℚ) * (L + 1 : ℚ) * (N : ℚ) *
          ∑ n ∈ Finset.Icc 1 (M + L),
            RelationalHosts.largeKernelWeightQ (L + 1) n := by
      rw [← Finset.mul_sum]
      ring

end

end BoundedRatioRelationalHosts
end PaperC
