import PaperC.Probability.ExactLengthDecomposition

/-!
# Deterministic local geometry of exact-length marks

This module formalizes the zero-probability cases in the local geometry
discussion following Lemma 14.7.

* two distinct exact lengths at the same start are incompatible;
* if `x < y` and the left exact run has not yet reached its right change at
  `y`, then the left boundary change required at `y` is incompatible with
  the constancy of the run from `x`.

These statements are deterministic consequences of the event definitions.
They do not use a probability model or a literature input.
-/

namespace PaperC
namespace MarkedLocalGeometry

open ExactLengthDecomposition
open MixedLengthAffine

/-- Vertex support of an exact-length system with `q` rows. -/
def exactLengthSupport (x q : ℕ) : Finset ℕ :=
  Finset.Icc (x - 1) (x + q - 1)

@[simp]
theorem mem_exactLengthSupport {x q n : ℕ} :
    n ∈ exactLengthSupport x q ↔
      x - 1 ≤ n ∧ n ≤ x + q - 1 := by
  simp [exactLengthSupport]

/-- The source convention `diam V_{x,e} = q` for a positive start. -/
theorem exactLengthSupport_diameter
    {x q : ℕ} (hx : 1 ≤ x) :
    (x + q - 1) - (x - 1) = q := by
  omega

/-- Every offset strictly before the right boundary of an exact run has the
same value as the start, including offset zero. -/
theorem exactLengthEvent_eq_start_of_before_right
    {g : ℕ → F₂} {x q j : ℕ}
    (hExact : ExactLengthEvent g x q)
    (hj : j + 1 < q) :
    g x = g (x + j) := by
  by_cases hj0 : j = 0
  · simp [hj0]
  · exact hExact.2.1 j (Nat.zero_lt_of_ne_zero hj0) hj

/--
Distinct exact lengths cannot occur at the same start.  At the earlier right
boundary, the shorter event requires a change while the longer event still
requires constancy.
-/
theorem exactLengthEvents_same_start_incompatible
    {g : ℕ → F₂} {x q r : ℕ}
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hqr : q ≠ r)
    (hExactQ : ExactLengthEvent g x q)
    (hExactR : ExactLengthEvent g x r) :
    False := by
  rcases lt_or_gt_of_ne hqr with hqrLt | hrqLt
  · have hchange :
        g x ≠ g (x + (q - 1)) :=
      (add_eq_one_iff_ne _ _).mp hExactQ.2.2
    have hconstant :
        g x = g (x + (q - 1)) :=
      exactLengthEvent_eq_start_of_before_right hExactR (by omega)
    exact hchange hconstant
  · have hchange :
        g x ≠ g (x + (r - 1)) :=
      (add_eq_one_iff_ne _ _).mp hExactR.2.2
    have hconstant :
        g x = g (x + (r - 1)) :=
      exactLengthEvent_eq_start_of_before_right hExactQ (by omega)
    exact hchange hconstant

/--
Strictly overlapping starts are incompatible.  If `x < y` and `y` occurs
before the right boundary `x + q - 1`, both `y - 1` and `y` are in the
constant part of the run from `x`, whereas the event at `y` requires them to
have opposite values.
-/
theorem exactLengthEvents_incompatible_of_strict_overlap
    {g : ℕ → F₂} {x y q r : ℕ}
    (hxy : x < y) (hoverlap : y < x + (q - 1))
    (hExactX : ExactLengthEvent g x q)
    (hExactY : ExactLengthEvent g y r) :
    False := by
  let d : ℕ := y - x
  have hdpos : 0 < d := by
    exact Nat.sub_pos_of_lt hxy
  have hxd : x + d = y := by
    exact Nat.add_sub_of_le hxy.le
  have hdq : d + 1 < q := by
    dsimp only [d]
    omega
  have hvalueY : g x = g y := by
    simpa only [hxd] using
      exactLengthEvent_eq_start_of_before_right hExactX hdq
  have hpredOffset : x + (d - 1) = y - 1 := by
    dsimp only [d]
    omega
  have hpredBefore : (d - 1) + 1 < q := by
    omega
  have hvaluePred : g x = g (y - 1) := by
    simpa only [hpredOffset] using
      exactLengthEvent_eq_start_of_before_right hExactX hpredBefore
  have hleftChange : g (y - 1) ≠ g y :=
    (add_eq_one_iff_ne _ _).mp hExactY.1
  exact hleftChange (hvaluePred.symm.trans hvalueY)

/--
Source-indexed form of the preceding incompatibility.  For the exact mark
`e`, the right boundary lies at offset `L + e`; hence a second start at
distance strictly smaller than `L + e` cannot coexist with it.
-/
theorem exactLengthEvents_excess_incompatible_of_left_overlap
    {g : ℕ → F₂} {x y L e f : ℕ}
    (hxy : x < y) (hd : y - x < L + e)
    (hExactX :
      ExactLengthEvent g x (excessRowCount L e))
    (hExactY :
      ExactLengthEvent g y (excessRowCount L f)) :
    False := by
  apply exactLengthEvents_incompatible_of_strict_overlap
    hxy (q := excessRowCount L e) (r := excessRowCount L f)
    (hExactX := hExactX) (hExactY := hExactY)
  simp only [excessRowCount]
  omega

/-! ## Zero joint masses in a finite prime cylinder -/

/-- Distinct marks at one start have exactly zero joint probability. -/
theorem mixedExactLengthProbability_same_start_eq_zero
    {M x q r : ℕ}
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hqr : q ≠ r) :
    mixedExactLengthProbability M x x q r = 0 := by
  classical
  unfold mixedExactLengthProbability uniformEventProbability
  have hempty :
      Finset.univ.filter
          (fun ω : SampleSpace M =>
            exactLengthAt ω x q ∧ exactLengthAt ω x r) =
        ∅ := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.not_mem_empty, iff_false]
    rintro ⟨hExactQ, hExactR⟩
    exact exactLengthEvents_same_start_incompatible
      hq hr hqr hExactQ hExactR
  rw [hempty]
  simp

/--
Strictly overlapping starts have exactly zero mixed joint probability.
-/
theorem mixedExactLengthProbability_eq_zero_of_strict_overlap
    {M x y q r : ℕ}
    (hxy : x < y) (hoverlap : y < x + (q - 1)) :
    mixedExactLengthProbability M x y q r = 0 := by
  classical
  unfold mixedExactLengthProbability uniformEventProbability
  have hempty :
      Finset.univ.filter
          (fun ω : SampleSpace M =>
            exactLengthAt ω x q ∧ exactLengthAt ω y r) =
        ∅ := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.not_mem_empty, iff_false]
    rintro ⟨hExactX, hExactY⟩
    exact exactLengthEvents_incompatible_of_strict_overlap
      hxy hoverlap hExactX hExactY
  rw [hempty]
  simp

/--
Source-indexed strict-overlap case: if the right start is at distance below
`L+e`, the joint mass of marks `e,f` vanishes.
-/
theorem mixedExactLengthProbability_excess_eq_zero_of_left_overlap
    {M x y L e f : ℕ}
    (hxy : x < y) (hd : y - x < L + e) :
    mixedExactLengthProbability M x y
      (excessRowCount L e) (excessRowCount L f) = 0 := by
  apply mixedExactLengthProbability_eq_zero_of_strict_overlap
    hxy
  simp only [excessRowCount]
  omega

/-! ## Arithmetic of the two local compatible offsets -/

/--
At distance `q - 1`, the two supports meet in the two vertices surrounding
the shared boundary change.  This is the support-level source of the
one-cycle (triangle) case.
-/
theorem exactLengthSupport_inter_eq_boundaryPair
    {x y q r : ℕ} (hx : 1 ≤ x) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hy : y = x + (q - 1)) :
    exactLengthSupport x q ∩ exactLengthSupport y r =
      {y - 1, y} := by
  subst y
  ext n
  simp only [Finset.mem_inter, mem_exactLengthSupport,
    Finset.mem_insert, Finset.mem_singleton]
  omega

/--
At distance `q`, the two supports touch in exactly one vertex.  This is the
support-level tree case of the manuscript.
-/
theorem exactLengthSupport_inter_eq_singleton
    {x y q r : ℕ} (hx : 1 ≤ x) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hy : y = x + q) :
    exactLengthSupport x q ∩ exactLengthSupport y r =
      {y - 1} := by
  subst y
  ext n
  simp only [Finset.mem_inter, mem_exactLengthSupport,
    Finset.mem_singleton]
  omega

/-- Beyond distance `q`, the two exact-length supports are disjoint. -/
theorem exactLengthSupport_disjoint_of_separated
    {x y q r : ℕ} (hx : 1 ≤ x) (hq : 2 ≤ q)
    (hsep : x + q < y) :
    Disjoint (exactLengthSupport x q) (exactLengthSupport y r) := by
  rw [Finset.disjoint_left]
  intro n hnx hny
  rw [mem_exactLengthSupport] at hnx hny
  omega

end MarkedLocalGeometry
end PaperC
