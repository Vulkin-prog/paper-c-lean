import PaperCV282.WordOverlapProbability

/-!
# The directed dictionary overlap budget

The dictionary is a finite set of distinct words. The local probability
mass retains both orientations of each pair of distinct sites.
-/

namespace PaperC.V282.WordOverlapSum

open ConditionalStartProbability ConditionalAGGInstantiation ArratiaGoldsteinGordonInput
open InfiniteWordTransfer WindowValues WordOverlap WordOverlapProbability
open scoped BigOperators

noncomputable section

/-- Directed compatibility weight at one shift, including self-overlaps. -/
def directedOverlapWeight {B : ℕ} (d : ℕ) (w v : Fin B → F₂) : ℝ := by
  classical
  exact if Compatible d w v then 1 / (2 : ℝ)^d else 0

/-- Equation (5.1), normalized by the number of distinct dictionary words. -/
def overlapWeight {B : ℕ} (W : Finset (Fin B → F₂)) : ℝ :=
  (∑ w ∈ W, ∑ v ∈ W, ∑ d ∈ Finset.Icc 1 (B-1), directedOverlapWeight d w v) /
    (W.card : ℝ)

/-- The actual ordered local joint mass on a deterministic mask. -/
def orderedLocalMass (M Y B : ℕ) (s : Finset ℕ)
    (W : Finset (Fin B → F₂)) (sigma : SmallSample M Y) : ℝ := by
  classical
  exact ∑ x ∈ s, ∑ y ∈ s, if x ≠ y ∧ Nat.dist x y < B then
    ∑ w ∈ W, ∑ v ∈ W,
      eventProbability (largeUniformPMF M Y) (fun eta =>
        assemble M Y sigma eta ∈ finiteWordEvent M x B w ∧
        assemble M Y sigma eta ∈ finiteWordEvent M y B v) else 0

theorem directedOverlapWeight_nonneg {B : ℕ} (d : ℕ) (w v : Fin B → F₂) :
    0 ≤ directedOverlapWeight d w v := by
  unfold directedOverlapWeight
  split_ifs <;> positivity

theorem overlapWeight_nonneg {B : ℕ} (W : Finset (Fin B → F₂)) :
    0 ≤ overlapWeight W := by
  unfold overlapWeight
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun v _ =>
    Finset.sum_nonneg fun d _ => directedOverlapWeight_nonneg d w v

/-- Reindexing a forward local neighbour by its positive shift is exact. -/
theorem sum_forward_shifts (s : Finset ℕ) (K : ℕ → ℕ → ℝ) (x B : ℕ) :
    (∑ y ∈ s, if x < y ∧ Nat.dist x y < B then K x y else 0) =
      ∑ d ∈ Finset.Icc 1 (B-1), if x+d ∈ s then K x (x+d) else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun y _ => y-x)
  · intro y hy
    obtain ⟨hys,hxy,hdist⟩ := Finset.mem_filter.mp hy
    rw [Nat.dist_eq_sub_of_le hxy.le] at hdist
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Icc.mpr (by omega)
    · simpa only [Nat.add_sub_of_le hxy.le] using hys
  · intro y hy z hz heq
    have hyx := (Finset.mem_filter.mp hy).2.1
    have hzx := (Finset.mem_filter.mp hz).2.1
    omega
  · intro d hd
    obtain ⟨hdIcc,hds⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdpos,hdB⟩ := Finset.mem_Icc.mp hdIcc
    refine ⟨x+d, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨hds, by omega, ?_⟩
    rw [Nat.dist_eq_sub_of_le (by omega : x ≤ x+d)]
    omega
  · intro y hy
    have hxy := (Finset.mem_filter.mp hy).2.1
    congr 1
    omega

/-- Symmetric joint masses count two directed orientations of each local pair. -/
theorem sum_ordered_local_eq_two_forward (s : Finset ℕ) (B : ℕ)
    (K : ℕ → ℕ → ℝ) (hsymm : ∀ x y, K x y = K y x) :
    (∑ x ∈ s, ∑ y ∈ s, if x ≠ y ∧ Nat.dist x y < B then K x y else 0) =
      2 * ∑ x ∈ s, ∑ d ∈ Finset.Icc 1 (B-1),
        if x+d ∈ s then K x (x+d) else 0 := by
  classical
  have hsplit : ∀ x y : ℕ,
      (if x ≠ y ∧ Nat.dist x y < B then K x y else 0) =
        (if x < y ∧ Nat.dist x y < B then K x y else 0) +
        (if y < x ∧ Nat.dist y x < B then K x y else 0) := by
    intro x y
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · simp [hxy, ne_of_lt hxy, not_lt.mpr hxy.le]
    · subst y
      simp
    · simp [hxy, ne_of_gt hxy, not_lt.mpr hxy.le, Nat.dist_comm]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hreverse :
      (∑ x ∈ s, ∑ y ∈ s, if y < x ∧ Nat.dist y x < B then K x y else 0) =
        ∑ x ∈ s, ∑ y ∈ s, if x < y ∧ Nat.dist x y < B then K x y else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    rw [hsymm x y]
  rw [hreverse]
  simp_rw [sum_forward_shifts]
  ring

/-- Summing specified local words keeps their directed compatibility weights. -/
theorem local_dictionary_probability_eq {M Y x B d : ℕ}
    (hx : 2 ≤ x) (hdpos : 1 ≤ d) (hd : d < B)
    (hcut : x-1+(B+d) ≤ M+1) (hY : 2*B ≤ Y)
    (hgoodx : ∀ i : Fin B, ¬ DefectivePredicate.HDefective Y (vertex x B i))
    (hgoody : ∀ i : Fin B, ¬ DefectivePredicate.HDefective Y (vertex (x+d) B i))
    (W : Finset (Fin B → F₂)) (sigma : SmallSample M Y) :
    (∑ w ∈ W, ∑ v ∈ W,
      eventProbability (largeUniformPMF M Y) (fun eta =>
        assemble M Y sigma eta ∈ finiteWordEvent M x B w ∧
        assemble M Y sigma eta ∈ finiteWordEvent M (x+d) B v)) =
      (1 / (2 : ℝ)^B) * ∑ w ∈ W, ∑ v ∈ W, directedOverlapWeight d w v := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [equation_five_five_finite hx hdpos hd hcut hY hgoodx hgoody]
  unfold directedOverlapWeight
  by_cases hc : Compatible d w v
  · simp only [hc, if_true, pow_add]
    field_simp
  · simp [hc]

/-- The shift sum has exactly the normalization used in equation (5.1). -/
theorem summed_overlap_normalization {B : ℕ} (W : Finset (Fin B → F₂))
    (hW : W.Nonempty) :
    (∑ d ∈ Finset.Icc 1 (B-1),
      (1 / (2 : ℝ)^B) * ∑ w ∈ W, ∑ v ∈ W, directedOverlapWeight d w v) =
      ((W.card : ℝ) / (2 : ℝ)^B) * overlapWeight W := by
  have hswap :
      (∑ d ∈ Finset.Icc 1 (B-1), ∑ w ∈ W, ∑ v ∈ W, directedOverlapWeight d w v) =
        ∑ w ∈ W, ∑ v ∈ W, ∑ d ∈ Finset.Icc 1 (B-1), directedOverlapWeight d w v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_comm]
  rw [← Finset.mul_sum, hswap, overlapWeight]
  have hcard : (W.card : ℝ) ≠ 0 := by exact_mod_cast hW.card_pos.ne'
  field_simp

/-- The two orientations of the actual local joint mass cost at most 2 Lambda Omega.
Both windows are required good only when their starts belong to the mask. -/
theorem orderedLocalMass_le {M Y B : ℕ} (s : Finset ℕ)
    (W : Finset (Fin B → F₂)) (hW : W.Nonempty)
    (hs : ∀ x ∈ s, 2 ≤ x) (hcut : ∀ x ∈ s, x-1+B ≤ M+1)
    (hY : 2*B ≤ Y)
    (hgood : ∀ x ∈ s, ∀ i : Fin B,
      ¬ DefectivePredicate.HDefective Y (vertex x B i))
    (sigma : SmallSample M Y) :
    orderedLocalMass M Y B s W sigma ≤
      2 * ((s.card : ℝ) * (W.card : ℝ) / (2 : ℝ)^B) * overlapWeight W := by
  classical
  let K : ℕ → ℕ → ℝ := fun x y => ∑ w ∈ W, ∑ v ∈ W,
    eventProbability (largeUniformPMF M Y) (fun eta =>
      assemble M Y sigma eta ∈ finiteWordEvent M x B w ∧
      assemble M Y sigma eta ∈ finiteWordEvent M y B v)
  have hsymm : ∀ x y, K x y = K y x := by
    intro x y
    dsimp [K]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    congr 1
    funext eta
    exact propext and_comm
  change (∑ x ∈ s, ∑ y ∈ s, if x ≠ y ∧ Nat.dist x y < B then K x y else 0) ≤ _
  rw [sum_ordered_local_eq_two_forward s B K hsymm]
  have hforward :
      (∑ x ∈ s, ∑ d ∈ Finset.Icc 1 (B-1), if x+d ∈ s then K x (x+d) else 0) ≤
        ∑ x ∈ s, ∑ d ∈ Finset.Icc 1 (B-1),
          (1 / (2 : ℝ)^B) * ∑ w ∈ W, ∑ v ∈ W, directedOverlapWeight d w v := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro d hdIcc
    obtain ⟨hdpos,hdtop⟩ := Finset.mem_Icc.mp hdIcc
    by_cases hxd : x+d ∈ s
    · simp only [hxd, if_true]
      have hxpos := hs x hx
      have hycut := hcut (x+d) hxd
      exact le_of_eq (local_dictionary_probability_eq hxpos hdpos (by omega)
        (by omega) hY (hgood x hx) (hgood (x+d) hxd) W sigma)
    · simp only [hxd, if_false]
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun v _ =>
        directedOverlapWeight_nonneg d w v
  apply (mul_le_mul_of_nonneg_left hforward (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  simp_rw [summed_overlap_normalization W hW]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

end
end PaperC.V282.WordOverlapSum
