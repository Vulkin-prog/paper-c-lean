import PaperCV282.WordOverlap
import PaperCV282.InfiniteConditionalWords
import PaperC.Probability.ConditionalAGGInstantiation

/-!
# Exact local word probabilities

Equation (5.5) is obtained by prescribing the actual union word. Goodness
means an odd valuation at a prime above Y at every vertex, including x-1.
The infinite conditional identities use literal positive prime atoms.
-/

namespace PaperC.V282.WordOverlapProbability

open MeasureTheory Set
open Affine ConditionalStartProbability ConditionalDependencyGraph
open ConditionalAGGInstantiation ArratiaGoldsteinGordonInput
open InfiniteRademacher InfiniteCylinderTransfer
open PrescribedValues WindowValues InfiniteWordTransfer InfiniteConditionalWords
open WordOverlap
open scoped ENNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

local instance instDecidableCompatible {B : ℕ} (d : ℕ) (w v : Fin B → F₂) :
    Decidable (WordOverlap.Compatible d w v) := Classical.propDecidable _

/-- Finite event intersection is the true union word, or the empty event. -/
theorem finiteWordEvent_inter {M B d x : ℕ} (hx : 1 ≤ x) (hd : d ≤ B)
    (w v : Fin B → F₂) :
    finiteWordEvent M x B w ∩ finiteWordEvent M (x+d) B v =
      if WordOverlap.Compatible d w v then
        finiteWordEvent M x (B+d) (mergedWord d hd w v) else ∅ := by
  classical
  ext omega
  have h := occurs_pair_iff hx hd (valueBit omega) w v
  change (Occurs (valueBit omega) x w ∧ Occurs (valueBit omega) (x+d) v) ↔ _
  rw [h]
  by_cases hc : WordOverlap.Compatible d w v <;> simp [hc, Occurs, finiteWordEvent]

/-- The same event identity holds in the infinite multiplicative source. -/
theorem infiniteWordEvent_inter {B d x : ℕ} (hx : 1 ≤ x) (hd : d ≤ B)
    (w v : Fin B → F₂) :
    infiniteWordEvent x B w ∩ infiniteWordEvent (x+d) B v =
      if WordOverlap.Compatible d w v then
        infiniteWordEvent x (B+d) (mergedWord d hd w v) else ∅ := by
  classical
  ext omega
  have h := occurs_pair_iff hx hd (infiniteValueBit omega) w v
  change (Occurs (infiniteValueBit omega) x w ∧
    Occurs (infiniteValueBit omega) (x+d) v) ↔ _
  rw [h]
  by_cases hc : WordOverlap.Compatible d w v <;> simp [hc, Occurs, infiniteWordEvent]

/-- Distinct labels at one finite-cylinder site are disjoint. -/
theorem finiteWordEvent_disjoint_same_site (M x B : ℕ) (w v : Fin B → F₂)
    (hne : w ≠ v) : Disjoint (finiteWordEvent M x B w) (finiteWordEvent M x B v) := by
  rw [Set.disjoint_left]
  intro omega hw hv
  exact not_occurs_pair_same_site (valueBit omega) w v hne ⟨hw,hv⟩

/-- Distinct labels at one source site are disjoint. -/
theorem infiniteWordEvent_disjoint_same_site (x B : ℕ) (w v : Fin B → F₂)
    (hne : w ≠ v) : Disjoint (infiniteWordEvent x B w) (infiniteWordEvent x B v) := by
  rw [Set.disjoint_left]
  intro omega hw hv
  exact not_occurs_pair_same_site (infiniteValueBit omega) w v hne ⟨hw,hv⟩

/-- Uniform large-prime sampling is exactly the conditional affine fiber count. -/
theorem finiteUniformProbability_conditionedWord_eq (M Y x B : ℕ)
    (w : Fin B → F₂) (sigma : SmallSample M Y) :
    finiteUniformProbability (fun eta : LargeSample M Y =>
      assemble M Y sigma eta ∈ finiteWordEvent M x B w) =
      uniformSolutionProbability (largeValueSystem M Y (vertex x B))
        (conditionedValueRhs M Y (vertex x B) w sigma) := by
  classical
  letI instSolutionFintype : Fintype (Solution (largeValueSystem M Y (vertex x B))
      (conditionedValueRhs M Y (vertex x B) w sigma)) :=
    Affine.probabilitySolutionFintype _ _
  unfold finiteUniformProbability uniformSolutionProbability
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  congr 1
  apply congrArg (fun n : ℕ => (n : ℚ))
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun eta : LargeSample M Y =>
    (valueSystem_eq_iff M (vertex x B) w (assemble M Y sigma eta)).symm.trans
      (assemble_solves_values_iff M Y (vertex x B) w sigma eta)))

/-- A good union is uniform for every fixed small-prime assignment. -/
theorem conditionedWord_probability_eq_baseline {M Y x B : ℕ}
    (hx : 2 ≤ x) (hcut : x-1+B ≤ M+1) (hBY : B ≤ Y)
    (hgood : ∀ i : Fin B, ¬ DefectivePredicate.HDefective Y (vertex x B i))
    (w : Fin B → F₂) (sigma : SmallSample M Y) :
    eventProbability (largeUniformPMF M Y) (fun eta =>
      assemble M Y sigma eta ∈ finiteWordEvent M x B w) = 1 / (2 : ℝ)^B := by
  rw [eventProbability_largeUniformPMF_eq, finiteUniformProbability_conditionedWord_eq,
    corollary_two_six_conditioned hx hcut hBY hgood]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]

/-- Equation (5.5) in the exact finite conditional probability model. -/
theorem equation_five_five_finite {M Y x B d : ℕ}
    (hx : 2 ≤ x) (_hdpos : 1 ≤ d) (hd : d < B)
    (hcut : x-1+(B+d) ≤ M+1) (hY : 2*B ≤ Y)
    (hgoodx : ∀ i : Fin B, ¬ DefectivePredicate.HDefective Y (vertex x B i))
    (hgoody : ∀ i : Fin B, ¬ DefectivePredicate.HDefective Y (vertex (x+d) B i))
    (w v : Fin B → F₂) (sigma : SmallSample M Y) :
    eventProbability (largeUniformPMF M Y) (fun eta =>
      assemble M Y sigma eta ∈ finiteWordEvent M x B w ∧
      assemble M Y sigma eta ∈ finiteWordEvent M (x+d) B v) =
      if WordOverlap.Compatible d w v then 1 / (2 : ℝ)^(B+d) else 0 := by
  classical
  have hevent := finiteWordEvent_inter (M := M) (by omega : 1 ≤ x) hd.le w v
  change eventProbability _ (fun eta => assemble M Y sigma eta ∈
    finiteWordEvent M x B w ∩ finiteWordEvent M (x+d) B v) = _
  rw [hevent]
  by_cases hc : WordOverlap.Compatible d w v
  · simp only [hc, if_true]
    exact conditionedWord_probability_eq_baseline hx hcut (by omega)
      (union_vertex_property (by omega : 1 ≤ x) hd.le
        (fun n => ¬ DefectivePredicate.HDefective Y n) hgoodx hgoody) _ sigma
  · simp [hc, eventProbability]

/-- Equation (5.5) as a ratio of actual infinite source measures on each F_Y atom. -/
theorem equation_five_five_infinite {M Y x B d : ℕ}
    (hx : 2 ≤ x) (_hdpos : 1 ≤ d) (hd : d < B)
    (hcut : x-1+(B+d) ≤ M+1) (hYM : Y ≤ M) (hY : 2*B ≤ Y)
    (hgoodx : ∀ i : Fin B, ¬ DefectivePredicate.HDefective Y (vertex x B i))
    (hgoody : ∀ i : Fin B, ¬ DefectivePredicate.HDefective Y (vertex (x+d) B i))
    (w v : Fin B → F₂) (sigma : SmallSample M Y) :
    infiniteRademacherMeasure
        ((infiniteWordEvent x B w ∩ infiniteWordEvent (x+d) B v) ∩
          infiniteSmallPrimeAtom M Y sigma) /
      infiniteRademacherMeasure (infiniteSmallPrimeAtom M Y sigma) =
      if WordOverlap.Compatible d w v then 1 / (2 : ℝ≥0∞)^(B+d) else 0 := by
  classical
  rw [infiniteWordEvent_inter (by omega : 1 ≤ x) hd.le w v]
  by_cases hc : WordOverlap.Compatible d w v
  · simp only [hc, if_true]
    exact corollary_two_six_conditioned_infinite hx hcut hYM (by omega)
      (union_vertex_property (by omega : 1 ≤ x) hd.le
        (fun n => ¬ DefectivePredicate.HDefective Y n) hgoodx hgoody) _ sigma
  · simp [hc]

/-- Real-valued form of the exact source conditional probability. -/
theorem equation_five_five_infinite_real {M Y x B d : ℕ}
    (hx : 2 ≤ x) (hdpos : 1 ≤ d) (hd : d < B)
    (hcut : x-1+(B+d) ≤ M+1) (hYM : Y ≤ M) (hY : 2*B ≤ Y)
    (hgoodx : ∀ i : Fin B, ¬ DefectivePredicate.HDefective Y (vertex x B i))
    (hgoody : ∀ i : Fin B, ¬ DefectivePredicate.HDefective Y (vertex (x+d) B i))
    (w v : Fin B → F₂) (sigma : SmallSample M Y) :
    infiniteRademacherMeasure.real
        ((infiniteWordEvent x B w ∩ infiniteWordEvent (x+d) B v) ∩
          infiniteSmallPrimeAtom M Y sigma) /
      infiniteRademacherMeasure.real (infiniteSmallPrimeAtom M Y sigma) =
      if WordOverlap.Compatible d w v then 1 / (2 : ℝ)^(B+d) else 0 := by
  classical
  have h := congrArg ENNReal.toReal
    (equation_five_five_infinite hx hdpos hd hcut hYM hY hgoodx hgoody w v sigma)
  simpa only [Measure.real, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_one, ENNReal.toReal_ofNat, ENNReal.toReal_zero, apply_ite] using h

end
end PaperC.V282.WordOverlapProbability
