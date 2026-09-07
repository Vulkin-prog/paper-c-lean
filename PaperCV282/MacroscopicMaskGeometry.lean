import PaperCV282.MaskedPairGeometry
import PaperCV282.BadStartRankin
import PaperCV282.MacroscopicGeometry

/-! # Complete-support deletion on arbitrary position masks -/
namespace PaperC.V282.MacroscopicMaskGeometry

open LargePrimeDependencyGraph DefectivePredicate MaskedPairGeometry
open MacroscopicGeometry BadStartRankin
open scoped BigOperators

noncomputable section

def badMask (L Y : ℕ) (mask : Finset ℕ) : Finset ℕ := by
  classical
  exact mask.filter fun x => ∃ n ∈ startTreeSupport x L, HDefective Y n

def goodMask (L Y : ℕ) (mask : Finset ℕ) : Finset ℕ := mask \ badMask L Y mask

def goodEdges (L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  maskedSupportEdges L Y (goodMask L Y mask)

def closedPairs (L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  (goodMask L Y mask).diag ∪ goodEdges L Y mask

theorem mem_badMask {L Y x : ℕ} {mask : Finset ℕ} :
    x ∈ badMask L Y mask ↔ x ∈ mask ∧ ∃ n ∈ startTreeSupport x L, HDefective Y n := by
  classical
  simp [badMask]

theorem mem_goodMask {L Y x : ℕ} {mask : Finset ℕ} :
    x ∈ goodMask L Y mask ↔ x ∈ mask ∧ x ∉ badMask L Y mask := by
  simp [goodMask]

theorem badMask_subset (L Y : ℕ) (mask : Finset ℕ) : badMask L Y mask ⊆ mask := by
  classical
  exact Finset.filter_subset _ _

theorem goodMask_subset (L Y : ℕ) (mask : Finset ℕ) : goodMask L Y mask ⊆ mask :=
  Finset.sdiff_subset

theorem good_union_bad (L Y : ℕ) (mask : Finset ℕ) :
    goodMask L Y mask ∪ badMask L Y mask = mask :=
  Finset.sdiff_union_of_subset (badMask_subset L Y mask)

theorem disjoint_good_bad (L Y : ℕ) (mask : Finset ℕ) :
    Disjoint (goodMask L Y mask) (badMask L Y mask) := Finset.sdiff_disjoint

theorem card_good_add_bad (L Y : ℕ) (mask : Finset ℕ) :
    (goodMask L Y mask).card + (badMask L Y mask).card = mask.card := by
  rw [← Finset.card_union_of_disjoint (disjoint_good_bad L Y mask), good_union_bad]

theorem not_defective_of_good {L Y x n : ℕ} {mask : Finset ℕ}
    (hx : x ∈ goodMask L Y mask) (hn : n ∈ startTreeSupport x L) : ¬ HDefective Y n := by
  intro hd
  exact (mem_goodMask.mp hx).2 (mem_badMask.mpr ⟨(mem_goodMask.mp hx).1, n, hn, hd⟩)

theorem goodMask_mono {L Y : ℕ} {s t : Finset ℕ} (hst : s ⊆ t) :
    goodMask L Y s ⊆ goodMask L Y t := by
  intro x hx
  obtain ⟨hxs, hgood⟩ := mem_goodMask.mp hx
  refine mem_goodMask.mpr ⟨hst hxs, ?_⟩
  intro hbad
  exact hgood (mem_badMask.mpr ⟨hxs, (mem_badMask.mp hbad).2⟩)

theorem badMask_mono {L Y : ℕ} {s t : Finset ℕ} (hst : s ⊆ t) :
    badMask L Y s ⊆ badMask L Y t := by
  intro x hx
  exact mem_badMask.mpr ⟨hst (mem_badMask.mp hx).1, (mem_badMask.mp hx).2⟩

theorem mem_goodEdges {L Y : ℕ} {mask : Finset ℕ} {xy : ℕ × ℕ} :
    xy ∈ goodEdges L Y mask ↔ xy.1 ∈ goodMask L Y mask ∧ xy.2 ∈ goodMask L Y mask ∧
      LargePrimeAdjacent L Y xy.1 xy.2 := mem_maskedSupportEdges

theorem goodEdges_subset_support (L Y : ℕ) (mask : Finset ℕ) :
    goodEdges L Y mask ⊆ maskedSupportEdges L Y mask :=
  maskedSupportEdges_mono (goodMask_subset L Y mask)

theorem card_closedPairs (L Y : ℕ) (mask : Finset ℕ) :
    (closedPairs L Y mask).card = (goodMask L Y mask).card + (goodEdges L Y mask).card := by
  have hd : Disjoint (goodMask L Y mask).diag (goodEdges L Y mask) := by
    apply Finset.disjoint_left.mpr
    intro xy hd he
    exact (mem_goodEdges.mp he).2.2.1 (Finset.mem_diag.mp hd).2
  rw [closedPairs, Finset.card_union_of_disjoint hd, Finset.diag_card]

theorem card_mask_le {M : ℕ} {mask : Finset ℕ} (hmask : mask ⊆ Finset.Icc 2 M) :
    mask.card ≤ M := by
  have h := Finset.card_le_card hmask
  rw [Nat.card_Icc] at h
  omega

theorem tree_vertex_bounds {M L x n : ℕ} (hL : L ≤ M) (hx : x ∈ Finset.Icc 2 M)
    (hn : n ∈ startTreeSupport x L) : 0 < n ∧ n ≤ 3 * M := by
  have hxr := Finset.mem_Icc.mp hx
  obtain ⟨i, hi, heq⟩ := tree_vertex_eq_complete_offset (by omega) hn
  constructor <;> omega

/-- The closed macroscopic mask embeds at twice the ambient scale, without a ratio
condition on individual sites. This handles the upper endpoint M literally. -/
theorem closed_macroscopic_subset_twice {M : ℕ} (hM : 2 ≤ M) {delta : ℝ} (hdelta : 0 < delta) :
    Finset.Icc ⌈(M : ℝ) ^ delta⌉₊ M ⊆ macroscopicStarts (2 * M) (delta / 2) := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hx
  apply (mem_macroscopicStarts_iff_real _ _ _).mpr
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hpow : ((2 * M : ℕ) : ℝ) ^ (delta / 2) ≤ (M : ℝ) ^ delta := by
    calc
      _ ≤ ((M : ℝ) ^ (2 : ℕ)) ^ (delta / 2) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        push_cast
        nlinarith
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ M)]
        congr 1
        ring
  exact ⟨hpow.trans ((Nat.le_ceil _).trans (by exact_mod_cast hlo)), by omega⟩

end
end PaperC.V282.MacroscopicMaskGeometry
