import PaperCV282.ExactMarkedValueProbability
import PaperCV282.ExactMarkedLocalGeometry

/-!
# Exact conditional local probabilities of signed excess marks

All four cases use actual marked supports, inside the two good maximal
supports. Shared absolute values give factors four and two, respectively.
-/
namespace PaperC.V282.ExactMarkedLocalProbability

open ExactMarkedModel SignedExactMarks ExactMarkedLocalGeometry ExactMarkedValueProbability
open MixedLengthAffine MarkedLocalGeometry WindowValues DefectivePredicate
open ConditionalStartProbability ConditionalAGGInstantiation ArratiaGoldsteinGordonInput

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Actual union cardinality gives the exact conditional probability, including compatibility. -/
theorem conditioned_signed_pair_probability {C Y x L E e f d : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E) (hd : d ≤ L+E+1)
    (hcut : (x+d)-1+(L+E+2) ≤ C+1) (hY : 2*(L+E+2) ≤ Y)
    (hgoodx : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (hgoody : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex (x+d) (L+E+2) i))
    (s t : F₂) (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      SignedExactMark (valueBit (assemble C Y sigma eta)) x L e s ∧
      SignedExactMark (valueBit (assemble C Y sigma eta)) (x+d) L f t) =
      if MarkCompatible x (x+d) L e f s t then
        1/(2 : ℝ)^(markSupport x L e ∪ markSupport (x+d) L f).card else 0 := by
  simp_rw [signed_pair_iff_union (by omega : 1 ≤ x) (by omega : 1 ≤ x+d) hL]
  by_cases hc : MarkCompatible x (x+d) L e f s t
  · simp only [hc,true_and,if_true]
    have henv : x-1+(d+(L+E+2)) ≤ C+1 := by omega
    have hsubset : ∀ n ∈ markSupport x L e ∪ markSupport (x+d) L f,
        x-1 ≤ n ∧ n < x-1+(d+(L+E+2)) := by
      intro n hn
      simp only [Finset.mem_union,markSupport,Finset.mem_Icc] at hn
      omega
    have hgood : ∀ n ∈ markSupport x L e ∪ markSupport (x+d) L f, ¬HDefective Y n := by
      intro n hn
      rcases Finset.mem_union.mp hn with hn | hn
      · simp only [markSupport,Finset.mem_Icc] at hn
        let i : Fin (L+E+2) := ⟨n-(x-1),by omega⟩
        have hv : vertex x (L+E+2) i = n := by dsimp [vertex,i];omega
        simpa only [hv] using hgoodx i
      · simp only [markSupport,Finset.mem_Icc] at hn
        let i : Fin (L+E+2) := ⟨n-((x+d)-1),by omega⟩
        have hv : vertex (x+d) (L+E+2) i = n := by dsimp [vertex,i];omega
        simpa only [hv] using hgoody i
    have hp := conditioned_selected_values_probability hx henv (by omega)
      (markSupport x L e ∪ markSupport (x+d) L f) hsubset hgood
      (fun n => unionAssignment x (x+d) L e f s t n.val) sigma
    simpa only [Subtype.forall] using hp
  · simp [hc,eventProbability]

/-- A second start inside the constant part is impossible in every source assignment. -/
theorem conditioned_signed_pair_eq_zero {C Y x L e f d : ℕ}
    (hdpos : 0 < d) (hd : d < L+e) (s t : F₂) (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      SignedExactMark (valueBit (assemble C Y sigma eta)) x L e s ∧
      SignedExactMark (valueBit (assemble C Y sigma eta)) (x+d) L f t) = 0 := by
  have hn (eta : LargeSample C Y) : ¬(
      SignedExactMark (valueBit (assemble C Y sigma eta)) x L e s ∧
      SignedExactMark (valueBit (assemble C Y sigma eta)) (x+d) L f t) := by
    rintro ⟨hh,hk⟩
    exact exactLengthEvents_excess_incompatible_of_left_overlap (by omega)
      (by omega) hh.1 hk.1
  simp [eventProbability,hn]

/-- Two shared boundary values multiply the signed product rate by four. -/
theorem conditioned_signed_pair_boundary {C Y x L E e f : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E)
    (hcut : (x+(L+e))-1+(L+E+2) ≤ C+1) (hY : 2*(L+E+2) ≤ Y)
    (hgoodx : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (hgoody : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex (x+(L+e)) (L+E+2) i))
    (s t : F₂) (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      SignedExactMark (valueBit (assemble C Y sigma eta)) x L e s ∧
      SignedExactMark (valueBit (assemble C Y sigma eta)) (x+(L+e)) L f t) =
      if t=1+s then 4*(signedMarkRate L e : ℝ)*(signedMarkRate L f : ℝ) else 0 := by
  rw [conditioned_signed_pair_probability hx hL he hf (by omega) hcut hY hgoodx hgoody,
    markCompatible_boundary (by omega) hL,card_markSupport_union_boundary (by omega) hL]
  split_ifs
  · simp only [signedMarkRate_coe,pow_add]
    norm_num
    field_simp
  · rfl

/-- One shared boundary value multiplies the signed product rate by two. -/
theorem conditioned_signed_pair_touching {C Y x L E e f : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E)
    (hcut : (x+(L+e+1))-1+(L+E+2) ≤ C+1) (hY : 2*(L+E+2) ≤ Y)
    (hgoodx : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (hgoody : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex (x+(L+e+1)) (L+E+2) i))
    (s t : F₂) (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      SignedExactMark (valueBit (assemble C Y sigma eta)) x L e s ∧
      SignedExactMark (valueBit (assemble C Y sigma eta)) (x+(L+e+1)) L f t) =
      if t=s then 2*(signedMarkRate L e : ℝ)*(signedMarkRate L f : ℝ) else 0 := by
  rw [conditioned_signed_pair_probability hx hL he hf (by omega) hcut hY hgoodx hgoody,
    markCompatible_touching (by omega) hL,card_markSupport_union_touching (by omega) hL]
  split_ifs
  · simp only [signedMarkRate_coe,pow_add]
    norm_num
    field_simp
    ring
  · rfl

/-- Disjoint real supports are independent even within the maximal-support local graph. -/
theorem conditioned_signed_pair_separated {C Y x L E e f d : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E)
    (hdlow : L+e+1 < d) (hd : d ≤ L+E+1)
    (hcut : (x+d)-1+(L+E+2) ≤ C+1) (hY : 2*(L+E+2) ≤ Y)
    (hgoodx : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (hgoody : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex (x+d) (L+E+2) i))
    (s t : F₂) (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      SignedExactMark (valueBit (assemble C Y sigma eta)) x L e s ∧
      SignedExactMark (valueBit (assemble C Y sigma eta)) (x+d) L f t) =
      (signedMarkRate L e : ℝ)*(signedMarkRate L f : ℝ) := by
  rw [conditioned_signed_pair_probability hx hL he hf hd hcut hY hgoodx hgoody,
    if_pos (markCompatible_separated hdlow s t),card_markSupport_union_separated (by omega) hdlow]
  simp only [signedMarkRate_coe,pow_add]
  norm_num
  field_simp
  ring

/-- Uniform local envelope, with no factor for the number of excess labels. -/
theorem conditioned_signed_pair_le_four {C Y x L E e f d : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E) (hdpos : 0 < d) (hd : d ≤ L+E+1)
    (hcut : (x+d)-1+(L+E+2) ≤ C+1) (hY : 2*(L+E+2) ≤ Y)
    (hgoodx : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (hgoody : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex (x+d) (L+E+2) i))
    (s t : F₂) (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      SignedExactMark (valueBit (assemble C Y sigma eta)) x L e s ∧
      SignedExactMark (valueBit (assemble C Y sigma eta)) (x+d) L f t) ≤
      4*(signedMarkRate L e : ℝ)*(signedMarkRate L f : ℝ) := by
  have hp : 0 ≤ (signedMarkRate L e : ℝ)*(signedMarkRate L f : ℝ) := by positivity
  by_cases hdlt : d < L+e
  · rw [conditioned_signed_pair_eq_zero hdpos hdlt]
    positivity
  · by_cases heq : d=L+e
    · subst d
      rw [conditioned_signed_pair_boundary hx hL he hf hcut hY hgoodx hgoody]
      split_ifs
      · exact le_rfl
      · positivity
    · by_cases heq' : d=L+e+1
      · subst d
        rw [conditioned_signed_pair_touching hx hL he hf hcut hY hgoodx hgoody]
        split_ifs <;> nlinarith only [hp]
      · rw [conditioned_signed_pair_separated hx hL he hf (by omega) hd hcut hY hgoodx hgoody]
        nlinarith only [hp]

end
end PaperC.V282.ExactMarkedLocalProbability
