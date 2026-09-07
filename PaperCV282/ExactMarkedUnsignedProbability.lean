import PaperCV282.ExactMarkedLocalProbability

/-!
# Removing the sign label in exact local probabilities

The two signs are disjoint alternatives, so summing their actual joint
probabilities gives the unsigned event without a union-bound loss.
-/
namespace PaperC.V282.ExactMarkedUnsignedProbability

open ExactMarkedModel SignedExactMarks ExactMarkedLocalProbability MixedLengthAffine
open ConditionalStartProbability ConditionalAGGInstantiation ArratiaGoldsteinGordonInput
open WindowValues DefectivePredicate
open scoped BigOperators

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exact finite partition of an event according to any finite-valued label. -/
theorem sum_label_eventProbability {Omega K : Type*} [Fintype Omega] [Fintype K]
    (mu : FinitePMF Omega) (label : Omega → K) (P : Omega → Prop) :
    (∑ k : K, eventProbability mu (fun omega => P omega ∧ label omega=k)) = eventProbability mu P := by
  classical
  unfold eventProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  rw [Finset.sum_eq_single (label omega)]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

/-- The true unsigned marginal is the sum of the two disjoint signed marginals. -/
theorem sum_signed_eventProbability {Omega : Type*} [Fintype Omega]
    (mu : FinitePMF Omega) (g : Omega → ℕ → F₂) (x L e : ℕ) :
    (∑ s : F₂, eventProbability mu (fun omega => SignedExactMark (g omega) x L e s)) =
      eventProbability mu (fun omega => ExactLengthEvent (g omega) x (excessRowCount L e)) :=
  sum_label_eventProbability mu (fun omega => g omega x) _

/-- Summing both signs gives the exact unsigned joint mass. -/
theorem sum_signed_pair_eventProbability {Omega : Type*} [Fintype Omega]
    (mu : FinitePMF Omega) (g : Omega → ℕ → F₂) (x y L e f : ℕ) :
    (∑ s : F₂, ∑ t : F₂, eventProbability mu (fun omega =>
      SignedExactMark (g omega) x L e s ∧ SignedExactMark (g omega) y L f t)) =
      eventProbability mu (fun omega =>
        ExactLengthEvent (g omega) x (excessRowCount L e) ∧
        ExactLengthEvent (g omega) y (excessRowCount L f)) := by
  have h := sum_label_eventProbability mu (fun omega => (g omega x,g omega y))
    (fun omega => ExactLengthEvent (g omega) x (excessRowCount L e) ∧
      ExactLengthEvent (g omega) y (excessRowCount L f))
  simpa only [Fintype.sum_prod_type,Prod.mk.injEq,SignedExactMark,and_assoc,and_left_comm,and_comm] using h

/-- Actual unsigned conditional marginal at every good maximal support. -/
theorem conditioned_exactMark_probability {C Y x L E e : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E)
    (hcut : x-1+(L+E+2) ≤ C+1) (hY : L+E+2 ≤ Y)
    (hgood : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e)) = (exactMarkRate L e : ℝ) := by
  rw [← sum_signed_eventProbability]
  simp_rw [conditioned_signedMark_probability hx hL he hcut hY hgood]
  exact sum_signedMarkRate L e

/-- The factor four signed boundary becomes factor two after summing signs. -/
theorem conditioned_exactMark_pair_boundary {C Y x L E e f : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E)
    (hcut : (x+(L+e))-1+(L+E+2) ≤ C+1) (hY : 2*(L+E+2) ≤ Y)
    (hgoodx : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (hgoody : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex (x+(L+e)) (L+E+2) i))
    (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e) ∧
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) (x+(L+e)) (excessRowCount L f)) =
      2*(exactMarkRate L e : ℝ)*(exactMarkRate L f : ℝ) := by
  rw [← sum_signed_pair_eventProbability]
  simp_rw [conditioned_signed_pair_boundary hx hL he hf hcut hY hgoodx hgoody]
  simp [signedMarkRate_coe,exactMarkRate_coe,pow_add]
  field_simp
  ring

/-- The one-value touching case has the unsigned product rate. -/
theorem conditioned_exactMark_pair_touching {C Y x L E e f : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E)
    (hcut : (x+(L+e+1))-1+(L+E+2) ≤ C+1) (hY : 2*(L+E+2) ≤ Y)
    (hgoodx : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (hgoody : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex (x+(L+e+1)) (L+E+2) i))
    (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e) ∧
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) (x+(L+e+1)) (excessRowCount L f)) =
      (exactMarkRate L e : ℝ)*(exactMarkRate L f : ℝ) := by
  rw [← sum_signed_pair_eventProbability]
  simp_rw [conditioned_signed_pair_touching hx hL he hf hcut hY hgoodx hgoody]
  simp [signedMarkRate_coe,exactMarkRate_coe,pow_add]
  field_simp

/-- Unsigned local pairs with disjoint real supports have the product marginal. -/
theorem conditioned_exactMark_pair_separated {C Y x L E e f d : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E)
    (hdlow : L+e+1 < d) (hd : d ≤ L+E+1)
    (hcut : (x+d)-1+(L+E+2) ≤ C+1) (hY : 2*(L+E+2) ≤ Y)
    (hgoodx : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (hgoody : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex (x+d) (L+E+2) i))
    (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e) ∧
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) (x+d) (excessRowCount L f)) =
      (exactMarkRate L e : ℝ)*(exactMarkRate L f : ℝ) := by
  rw [← sum_signed_pair_eventProbability]
  simp_rw [conditioned_signed_pair_separated hx hL he hf hdlow hd hcut hY hgoodx hgoody]
  simp [signedMarkRate_coe,exactMarkRate_coe,pow_add]
  field_simp

/-- The unsigned local envelope keeps the sharp boundary factor two. -/
theorem conditioned_exactMark_pair_le_two {C Y x L E e f d : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E) (hdpos : 0 < d) (hd : d ≤ L+E+1)
    (hcut : (x+d)-1+(L+E+2) ≤ C+1) (hY : 2*(L+E+2) ≤ Y)
    (hgoodx : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (hgoody : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex (x+d) (L+E+2) i))
    (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e) ∧
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) (x+d) (excessRowCount L f)) ≤
      2*(exactMarkRate L e : ℝ)*(exactMarkRate L f : ℝ) := by
  have hp : 0 ≤ (exactMarkRate L e : ℝ)*(exactMarkRate L f : ℝ) := by positivity
  by_cases hdlt : d < L+e
  · rw [← sum_signed_pair_eventProbability]
    simp_rw [conditioned_signed_pair_eq_zero hdpos hdlt]
    simp only [Finset.sum_const_zero]
    positivity
  · by_cases heq : d=L+e
    · subst d
      rw [conditioned_exactMark_pair_boundary hx hL he hf hcut hY hgoodx hgoody]
    · by_cases heq' : d=L+e+1
      · subst d
        rw [conditioned_exactMark_pair_touching hx hL he hf hcut hY hgoodx hgoody]
        nlinarith only [hp]
      · rw [conditioned_exactMark_pair_separated hx hL he hf (by omega) hd hcut hY hgoodx hgoody]
        nlinarith only [hp]

end
end PaperC.V282.ExactMarkedUnsignedProbability
