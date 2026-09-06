import PaperCV282.UnsignedMarkedRelations
import PaperCV282.ExactMarkedValueProbability
import PaperCV282.ExactMarkedLocalGeometry
import PaperCV282.ExactMarkedLocalProbability

/-!
# Unsigned local factor at the exact printed cutoff 2Q<Y

The signs are summed at fixed excesses after counting the actual union.
The enclosing union has at most 2Q+1 values; hence the hypothesis 2Q<Y suffices.
-/
namespace PaperC.V282.UnsignedLocalProbability

open UnsignedMarkedRelations ExactMarkedModel SignedExactMarks ExactMarkedLocalGeometry ExactMarkedValueProbability
open ExactLengthDecomposition MixedLengthAffine MarkedLocalGeometry WindowValues DefectivePredicate
open ConditionalStartProbability ConditionalAGGInstantiation ArratiaGoldsteinGordonInput

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Actual union cardinality gives the exact conditional probability, including compatibility. -/
theorem conditioned_signed_pair_probability {C Y x L E e f d : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E) (hd : d ≤ L+E+1)
    (hcut : (x+d)-1+(L+E+2) ≤ C+1) (hY : 2*(L+E+1) < Y)
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


/-- The actual unsigned joint has the printed local factor two, at every 2Q<Y. -/
theorem conditioned_exact_pair_le_two {C Y x L E e f d : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E)
    (hdpos : 0 < d) (hd : d ≤ L+E+1)
    (hcut : (x+d)-1+(L+E+2) ≤ C+1) (hY : 2*(L+E+1) < Y)
    (hgoodx : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (hgoody : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex (x+d) (L+E+2) i))
    (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e) ∧
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) (x+d) (excessRowCount L f)) ≤
      2*(exactMarkRate L e : ℝ)*(exactMarkRate L f : ℝ) := by
  rw [← sum_signed_joint_eq_exact]
  by_cases hlt : d < L+e
  · simp_rw [ExactMarkedLocalProbability.conditioned_signed_pair_eq_zero hdpos hlt]
    simp
    positivity
  · simp_rw [conditioned_signed_pair_probability hx hL he hf hd hcut hY hgoodx hgoody]
    by_cases hbd : d=L+e
    · subst d
      simp_rw [markCompatible_boundary (by omega : 1≤x) hL,
        card_markSupport_union_boundary (by omega : 1≤x) hL]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_const,
        Finset.card_univ,ZMod.card,nsmul_eq_mul,exactMarkRate_coe]
      simp only [pow_add]
      norm_num
      field_simp
      nlinarith
    · by_cases htouch : d=L+e+1
      · subst d
        simp_rw [markCompatible_touching (by omega : 1≤x) hL,
          card_markSupport_union_touching (by omega : 1≤x) hL]
        simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_const,
          Finset.card_univ,ZMod.card,nsmul_eq_mul,exactMarkRate_coe]
        simp only [pow_add]
        norm_num
        field_simp
        nlinarith [show (0 : ℝ)≤2^L*2^e*2^L*2^f by positivity]
      · have hsep : L+e+1<d := by omega
        simp_rw [markCompatible_separated hsep,if_true,
          card_markSupport_union_separated (by omega : 1≤x) hsep]
        simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,exactMarkRate_coe]
        simp only [pow_add]
        norm_num
        field_simp
        nlinarith [show (0 : ℝ)≤2^L*2^e*2^L*2^f by positivity]

end
end PaperC.V282.UnsignedLocalProbability
