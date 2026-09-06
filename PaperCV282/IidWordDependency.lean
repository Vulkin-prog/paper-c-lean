import PaperCV282.IidWordField

/-!
# Exact local dependency of independent-bit word occurrences

Only windows sharing integer coordinates are joined. Independence is proved
from an explicit split of the finite product, against the complete outside
Boolean pattern, and not merely pairwise independence.
-/
namespace PaperC.V282.IidWordDependency

open IidWordField DictionaryFieldModel WordOverlap WindowValues
open ArratiaGoldsteinGordonInput ConditionalDependencyGraph SectionTwelveMoments
open ConditionalStartProbability ConditionalAGGAverage

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Integer coordinates of one word present in the finite iid prefix. -/
def iidSupport (C x B : ℕ) : Finset (Fin C) :=
  Finset.univ.filter (fun q => x-1 ≤ q.val ∧ q.val < x-1+B)

theorem mem_iidSupport {C x B : ℕ} (q : Fin C) :
    q ∈ iidSupport C x B ↔ x-1 ≤ q.val ∧ q.val < x-1+B := by
  simp [iidSupport]

/-- Exact factorization into the coordinates of one window and their complement. -/
def iidCoordinateSplit (C x B : ℕ) : IidSample C ≃
    ({q : Fin C // q ∈ iidSupport C x B} → F₂) ×
    ({q : Fin C // q ∉ iidSupport C x B} → F₂) where
  toFun omega := (fun q => omega q.val,fun q => omega q.val)
  invFun z q := if h : q ∈ iidSupport C x B then z.1 ⟨q,h⟩ else z.2 ⟨q,h⟩
  left_inv omega := by funext q; by_cases h : q ∈ iidSupport C x B <;> simp [h]
  right_inv z := by apply Prod.ext <;> funext q <;> simp [q.property]

/-- The word event reads only its actual integer coordinates. -/
theorem iidWordIndicator_eq_of_eqOn {C x B : ℕ} (b : Fin B → F₂)
    (omega theta : IidSample C)
    (heq : ∀ q ∈ iidSupport C x B, omega q = theta q) :
    iidWordIndicator C x B b omega = iidWordIndicator C x B b theta := by
  unfold iidWordIndicator
  apply Bool.decide_congr
  have hbit (i : Fin B) : iidSequence C omega (vertex x B i) = iidSequence C theta (vertex x B i) := by
    by_cases hc : vertex x B i < C
    · simp only [iidSequence,dif_pos hc]
      apply heq
      rw [mem_iidSupport]
      have hi := i.isLt
      simp only [vertex]
      omega
    · simp [iidSequence,hc]
  simp only [Occurs]
  simp_rw [hbit]

/-- Nonoverlapping positive-start windows have disjoint coordinate supports. -/
theorem disjoint_iidSupport {C x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hfar : L < Nat.dist x y) : Disjoint (iidSupport C x (L+1)) (iidSupport C y (L+1)) := by
  apply Finset.disjoint_left.mpr
  intro q hq hq'
  obtain ⟨hxl,hxu⟩ := (mem_iidSupport q).mp hq
  obtain ⟨hyl,hyu⟩ := (mem_iidSupport q).mp hq'
  rcases le_total x y with hxy | hyx
  · rw [Nat.dist_eq_sub_of_le hxy] at hfar
    omega
  · rw [Nat.dist_eq_sub_of_le_right hyx] at hfar
    omega

/-- The local graph retains same-site word conflicts but no arithmetic prime edges. -/
def iidWordGraph (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) : SimpleGraph (DictionaryIndex N L W) where
  Adj i j := i ≠ j ∧ Nat.dist i.1.val j.1.val ≤ L
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,by simpa only [Nat.dist_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem mem_closedNeighborhood_iidWordGraph (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (i j : DictionaryIndex N L W) :
    j ∈ closedNeighborhood (iidWordGraph N L W) i ↔ Nat.dist i.1.val j.1.val ≤ L := by
  rw [mem_closedNeighborhood]
  constructor
  · rintro (he | ha)
    · subst j
      simp
    · exact ha.2
  · intro hd
    by_cases he : i = j
    · exact Or.inl he.symm
    · exact Or.inr ⟨he,hd⟩

/-- Exact full-pattern dependency for the genuine finite independent-sign field. -/
theorem hasExactDependencyGraph_iidWordField {N L : ℕ}
    (W : Finset (Fin (L+1) → F₂)) (hN : 1 ≤ N) :
    HasExactDependencyGraph (iidUniformPMF (dyadicCutoff N L + 1))
      (iidFieldIndicator N L W) (iidWordGraph N L W) := by
  intro alpha value pattern
  rw [eventProbability_iidUniformPMF_eq,eventProbability_iidUniformPMF_eq,eventProbability_iidUniformPMF_eq]
  norm_cast
  let C := dyadicCutoff N L + 1
  let e := iidCoordinateSplit C alpha.1.val (L+1)
  let P : IidSample C → Prop := fun omega => iidFieldIndicator N L W alpha omega = value
  let Q : IidSample C → Prop := fun omega => HasOutsidePattern (iidFieldIndicator N L W)
    (iidWordGraph N L W) alpha pattern omega
  let PA : ({q : Fin C // q ∈ iidSupport C alpha.1.val (L+1)} → F₂) → Prop :=
    fun a => P (e.symm (a,0))
  let QB : ({q : Fin C // q ∉ iidSupport C alpha.1.val (L+1)} → F₂) → Prop :=
    fun b => Q (e.symm (0,b))
  apply finiteUniformProbability_and_eq_mul_of_product_support e P Q PA QB
  · intro omega
    dsimp only [P,PA]
    have heq : iidFieldIndicator N L W alpha omega =
        iidFieldIndicator N L W alpha (e.symm ((e omega).1,0)) := by
      apply iidWordIndicator_eq_of_eqOn
      intro q hq
      change omega q = if q ∈ iidSupport C alpha.1.val (L+1) then omega q else 0
      rw [if_pos hq]
    rw [heq]
  · intro omega
    dsimp only [Q,QB]
    let theta := e.symm (0,(e omega).2)
    have heq (beta : OutsideIndex (iidWordGraph N L W) alpha) :
        iidFieldIndicator N L W beta.val omega = iidFieldIndicator N L W beta.val theta := by
      have hfar := beta.property
      rw [mem_closedNeighborhood_iidWordGraph] at hfar
      have hxa : 1 ≤ alpha.1.val := hN.trans (Finset.mem_Ico.mp alpha.1.property).1
      have hxb : 1 ≤ beta.val.1.val := hN.trans (Finset.mem_Ico.mp beta.val.1.property).1
      have hdis := disjoint_iidSupport (C := C) hxa hxb (Nat.lt_of_not_ge hfar)
      apply iidWordIndicator_eq_of_eqOn
      intro q hq
      have hn : q ∉ iidSupport C alpha.1.val (L+1) := fun ha => Finset.disjoint_left.mp hdis ha hq
      change omega q = if q ∈ iidSupport C alpha.1.val (L+1) then 0 else omega q
      rw [if_neg hn]
    constructor
    · intro h beta
      rw [← heq beta]
      exact h beta
    · intro h beta
      rw [heq beta]
      exact h beta

end
end PaperC.V282.IidWordDependency
