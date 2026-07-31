import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditional Evertse--Silverman input

Lemma 9.1 of Paper C uses Theorem 1(b) of Evertse--Silverman. That external
theorem is not reproved here. Its specialization bounding the possible
abscissae `X` is represented by the explicit proposition
`EvertseSilvermanAbscissaStatement`.

The public theorem of this file is an implication from that external
statement to the shifted-product equation occurring in the manuscript.
Lean proves that each admissible `X` gives at most two nonzero ordinates,
counts the at most `d` zero solutions, and then applies the injective
substitution `(X, Y) ↦ (X, e * Y)`. Consequently the external dependency
remains a visible hypothesis of every downstream result that uses it.
-/

namespace PaperC
namespace EvertseSilvermanInput

open scoped BigOperators

/--
`HasAtMostSolutions P M` is a finitary formulation of the assertion that the
predicate `P` has at most `M` solutions. It avoids choosing an enumeration of
an a priori unbounded Diophantine solution set.
-/
def HasAtMostSolutions
    {α : Type*} [DecidableEq α]
    (P : α → Prop) (M : ℕ) : Prop :=
  ∀ s : Finset α, (∀ z ∈ s, P z) → s.card ≤ M

/-- The shifted split product `∏ᵣ (X + hᵣ)`. -/
def shiftedProduct
    {d : ℕ} (shift : Fin d → ℤ) (X : ℤ) : ℤ :=
  ∏ r, (X + shift r)

/--
The product of the pairwise differences of the roots, with one orientation
for each unordered pair. Its prime support is the finite part of the
discriminant support relevant to the split polynomial.
-/
def pairDifferenceProduct
    {d : ℕ} (shift : Fin d → ℤ) : ℕ :=
  ∏ r : Fin d, ∏ s : Fin d,
    if r < s then (shift r - shift s).natAbs else 1

/--
Number of bad places used in the explicit Evertse--Silverman specialization:
the archimedean place plus the primes dividing
`2 * e * ∏_{r<s} (hᵣ-hₛ)`.
-/
noncomputable def badPlaceCount
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) : ℕ :=
  1 +
    (2 * e.natAbs * pairDifferenceProduct shift).primeFactors.card

/-- The Evertse--Silverman bound `7^(4 + 9|S|)` for possible abscissae. -/
noncomputable def explicitAbscissaBound
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) : ℕ :=
  7 ^ (4 + 9 * badPlaceCount shift e)

/-- The pair bound `2 * 7^(4 + 9|S|)` displayed in equation (9.2). -/
noncomputable def explicitBound
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) : ℕ :=
  2 * explicitAbscissaBound shift e

/-- Squarefreeness for a possibly negative integer, via its absolute value. -/
def IsSquarefreeInteger (e : ℤ) : Prop :=
  Squarefree e.natAbs

/-- The split equation `Z² = e ∏ᵣ (X+hᵣ)` to which the cited theorem applies. -/
def splitQuadraticEquation
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ)
    (solution : ℤ × ℤ) : Prop :=
  solution.2 ^ 2 =
    e * shiftedProduct shift solution.1

/-- The shifted-product equation of Lemma 9.1, `∏ᵣ (X+hᵣ) = eY²`. -/
def shiftedSquareEquation
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ)
    (solution : ℤ × ℤ) : Prop :=
  shiftedProduct shift solution.1 =
    e * solution.2 ^ 2

/-- The nonzero branch appearing literally in equation (9.2). -/
def nonzeroSplitQuadraticEquation
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ)
    (solution : ℤ × ℤ) : Prop :=
  solution.2 ≠ 0 ∧ splitQuadraticEquation shift e solution

/--
The abscissa predicate to which the external bridge is applied.
-/
def nonzeroSplitQuadraticAbscissa
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ) (X : ℤ) : Prop :=
  ∃ Z : ℤ,
    Z ≠ 0 ∧ splitQuadraticEquation shift e (X, Z)

/--
External bridge used by Lemma 9.1: the specialized Evertse--Silverman
abscissa count.

For at least three distinct shifts and nonzero squarefree `e`, the number of
possible integers `X` for which there is a nonzero `Z` with
`Z² = e ∏ᵣ (X+hᵣ)` is at most `7^(4 + 9|S|)`.

The factor two for the two possible ordinates and the elementary contribution
of the zero solutions are deliberately absent from this hypothesis and are
proved below.
-/
/- AUDIT_BRIDGE
{
  "id": "ES86-T1b-Q-split-n2",
  "kind": "external",
  "status": "open",
  "lean_name": "PaperC.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement",
  "citation": {
    "authors": ["J.-H. Evertse", "J. H. Silverman"],
    "title": "Uniform bounds for the number of solutions to Y^n = f(X)",
    "journal": "Mathematical Proceedings of the Cambridge Philosophical Society 100 (1986), 237–248",
    "doi": "10.1017/S0305004100066068",
    "locator": "Theorem 1(b), p. 238"
  },
  "source_statement": {
    "verbatim": "Let d ≥ 3, and assume that L contains at least three zeros of f. Then #V(R_S,f,2) ≤ 7^{M(4m+9s)} · 4^{κ₂(L)}.",
    "source_url": "https://doi.org/10.1017/S0305004100066068",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Lemma 9.1",
    "equation": "(9.2)",
    "pages": "27–28"
  },
  "formalization_relation": "specialization to K = L = ℚ, a split polynomial, n = 2, and the abscissa count before the elementary factor two"
}
AUDIT_BRIDGE -/
def EvertseSilvermanAbscissaStatement : Prop :=
  ∀ {d : ℕ} (shift : Fin d → ℤ) (e : ℤ),
    3 ≤ d →
    Function.Injective shift →
    e ≠ 0 →
    IsSquarefreeInteger e →
    HasAtMostSolutions
      (nonzeroSplitQuadraticAbscissa shift e)
      (explicitAbscissaBound shift e)

/-- Substitution from the manuscript variable `Y` to the external variable `Z`. -/
def toSplitQuadratic (e : ℤ) (solution : ℤ × ℤ) : ℤ × ℤ :=
  (solution.1, e * solution.2)

private theorem toSplitQuadratic_injective
    {e : ℤ} (he : e ≠ 0) :
    Function.Injective (toSplitQuadratic e) := by
  intro u v huv
  have hfirst :
      (toSplitQuadratic e u).1 =
        (toSplitQuadratic e v).1 :=
    congrArg (fun z : ℤ × ℤ => z.1) huv
  change u.1 = v.1 at hfirst
  have hsecondScaled :
      (toSplitQuadratic e u).2 =
        (toSplitQuadratic e v).2 :=
    congrArg (fun z : ℤ × ℤ => z.2) huv
  change e * u.2 = e * v.2 at hsecondScaled
  have hsecond : u.2 = v.2 :=
    mul_left_cancel₀ he hsecondScaled
  exact Prod.ext_iff.mpr ⟨hfirst, hsecond⟩

private theorem shiftedSquareEquation_maps_to_split
    {d : ℕ} {shift : Fin d → ℤ} {e : ℤ}
    {solution : ℤ × ℤ}
    (hsolution : shiftedSquareEquation shift e solution) :
    splitQuadraticEquation shift e
      (toSplitQuadratic e solution) := by
  change
    (e * solution.2) ^ 2 =
      e * shiftedProduct shift solution.1
  rw [hsolution]
  ring

private theorem hasAtMostSolutions_of_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {P : β → Prop} {Q : α → Prop} {M : ℕ}
    (hP : HasAtMostSolutions P M)
    (f : α → β)
    (hf : Function.Injective f)
    (hmap : ∀ z, Q z → P (f z)) :
    HasAtMostSolutions Q M := by
  intro s hs
  have himage :
      ∀ z ∈ s.image f, P z := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact hmap w (hs w hw)
  calc
    s.card = (s.image f).card :=
      (Finset.card_image_of_injective s hf).symm
    _ ≤ M := hP (s.image f) himage

private theorem pair_eq_of_same_first_and_same_strict_sign
    {d : ℕ} {shift : Fin d → ℤ} {e : ℤ}
    {u v : ℤ × ℤ}
    (hu : splitQuadraticEquation shift e u)
    (hv : splitQuadraticEquation shift e v)
    (hfirst : u.1 = v.1)
    (hsign :
      (0 < u.2 ∧ 0 < v.2) ∨
        (u.2 < 0 ∧ v.2 < 0)) :
    u = v := by
  apply Prod.ext hfirst
  have hsquares : u.2 ^ 2 = v.2 ^ 2 := by
    calc
      u.2 ^ 2 =
          e * shiftedProduct shift u.1 :=
        hu
      _ =
          e * shiftedProduct shift v.1 := by
        rw [hfirst]
      _ = v.2 ^ 2 :=
        hv.symm
  rcases hsign with hpositive | hnegative
  · nlinarith
  · nlinarith

private theorem nonzeroSplitQuadraticEquation_atMost
    (hES : EvertseSilvermanAbscissaStatement)
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ)
    (hd : 3 ≤ d)
    (hshift : Function.Injective shift)
    (he : e ≠ 0)
    (hsquarefree : IsSquarefreeInteger e) :
    HasAtMostSolutions
      (nonzeroSplitQuadraticEquation shift e)
      (explicitBound shift e) := by
  intro s hs
  let positiveSolutions :=
    s.filter (fun solution => 0 < solution.2)
  let nonpositiveSolutions :=
    s.filter (fun solution => ¬0 < solution.2)
  have habscissae :=
    hES shift e hd hshift he hsquarefree
  have hpositive :
      positiveSolutions.card ≤
        explicitAbscissaBound shift e := by
    have hinjective :
        Set.InjOn Prod.fst
          (↑positiveSolutions : Set (ℤ × ℤ)) := by
      intro u hu v hv hfirst
      have hu' := Finset.mem_filter.mp hu
      have hv' := Finset.mem_filter.mp hv
      exact pair_eq_of_same_first_and_same_strict_sign
        (hs u hu'.1).2
        (hs v hv'.1).2
        hfirst
        (Or.inl ⟨hu'.2, hv'.2⟩)
    have himage :
        ∀ X ∈ positiveSolutions.image Prod.fst,
          nonzeroSplitQuadraticAbscissa shift e X := by
      intro X hX
      obtain ⟨solution, hsolution, rfl⟩ :=
        Finset.mem_image.mp hX
      have hmem := Finset.mem_filter.mp hsolution
      exact
        ⟨solution.2, (hs solution hmem.1).1,
          (hs solution hmem.1).2⟩
    calc
      positiveSolutions.card =
          (positiveSolutions.image Prod.fst).card :=
        (Finset.card_image_of_injOn hinjective).symm
      _ ≤ explicitAbscissaBound shift e :=
        habscissae (positiveSolutions.image Prod.fst) himage
  have hnonpositive :
      nonpositiveSolutions.card ≤
        explicitAbscissaBound shift e := by
    have hinjective :
        Set.InjOn Prod.fst
          (↑nonpositiveSolutions : Set (ℤ × ℤ)) := by
      intro u hu v hv hfirst
      have hu' := Finset.mem_filter.mp hu
      have hv' := Finset.mem_filter.mp hv
      have huNonzero := (hs u hu'.1).1
      have hvNonzero := (hs v hv'.1).1
      have huNegative :
          u.2 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hu'.2) huNonzero
      have hvNegative :
          v.2 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hv'.2) hvNonzero
      exact pair_eq_of_same_first_and_same_strict_sign
        (hs u hu'.1).2
        (hs v hv'.1).2
        hfirst
        (Or.inr ⟨huNegative, hvNegative⟩)
    have himage :
        ∀ X ∈ nonpositiveSolutions.image Prod.fst,
          nonzeroSplitQuadraticAbscissa shift e X := by
      intro X hX
      obtain ⟨solution, hsolution, rfl⟩ :=
        Finset.mem_image.mp hX
      have hmem := Finset.mem_filter.mp hsolution
      exact
        ⟨solution.2, (hs solution hmem.1).1,
          (hs solution hmem.1).2⟩
    calc
      nonpositiveSolutions.card =
          (nonpositiveSolutions.image Prod.fst).card :=
        (Finset.card_image_of_injOn hinjective).symm
      _ ≤ explicitAbscissaBound shift e :=
        habscissae
          (nonpositiveSolutions.image Prod.fst) himage
  have hpartition :
      positiveSolutions.card + nonpositiveSolutions.card =
        s.card := by
    simpa only [positiveSolutions, nonpositiveSolutions] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := s) (fun solution : ℤ × ℤ => 0 < solution.2))
  calc
    s.card =
        positiveSolutions.card + nonpositiveSolutions.card :=
      hpartition.symm
    _ ≤
        explicitAbscissaBound shift e +
          explicitAbscissaBound shift e :=
      Nat.add_le_add hpositive hnonpositive
    _ = explicitBound shift e := by
      simp [explicitBound, two_mul]

private theorem zeroSplitQuadraticEquation_atMost
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ)
    (he : e ≠ 0) :
    HasAtMostSolutions
      (fun solution : ℤ × ℤ =>
        solution.2 = 0 ∧
          splitQuadraticEquation shift e solution)
      d := by
  intro s hs
  have hfst :
      Set.InjOn Prod.fst (↑s : Set (ℤ × ℤ)) := by
    intro u hu v hv hfirst
    apply Prod.ext hfirst
    rw [(hs u hu).1, (hs v hv).1]
  have hcard :
      (s.image Prod.fst).card = s.card :=
    Finset.card_image_of_injOn hfst
  have hsubset :
      s.image Prod.fst ⊆
        (Finset.univ : Finset (Fin d)).image
          (fun r => -shift r) := by
    intro X hX
    obtain ⟨solution, hsolution, rfl⟩ :=
      Finset.mem_image.mp hX
    have hzero := (hs solution hsolution).1
    have hequation := (hs solution hsolution).2
    have hmul :
        e * shiftedProduct shift solution.1 = 0 := by
      have :
          (0 : ℤ) =
            e * shiftedProduct shift solution.1 := by
        simpa [splitQuadraticEquation, hzero] using hequation
      exact this.symm
    have hproduct :
        shiftedProduct shift solution.1 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left he
    have hroot :
        ∃ r : Fin d, solution.1 + shift r = 0 := by
      simpa only [shiftedProduct, Finset.prod_eq_zero_iff,
        Finset.mem_univ, true_and] using hproduct
    obtain ⟨r, hr⟩ := hroot
    apply Finset.mem_image.mpr
    refine ⟨r, Finset.mem_univ r, ?_⟩
    linarith
  calc
    s.card = (s.image Prod.fst).card := hcard.symm
    _ ≤
        ((Finset.univ : Finset (Fin d)).image
          (fun r => -shift r)).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset (Fin d)).card :=
      Finset.card_image_le
    _ = d := by simp

private theorem splitQuadraticEquation_atMost
    (hES : EvertseSilvermanAbscissaStatement)
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ)
    (hd : 3 ≤ d)
    (hshift : Function.Injective shift)
    (he : e ≠ 0)
    (hsquarefree : IsSquarefreeInteger e) :
    HasAtMostSolutions
      (splitQuadraticEquation shift e)
      (d + explicitBound shift e) := by
  intro s hs
  let zeroSolutions :=
    s.filter (fun solution => solution.2 = 0)
  let nonzeroSolutions :=
    s.filter (fun solution => solution.2 ≠ 0)
  have hzero :
      zeroSolutions.card ≤ d := by
    apply
      zeroSplitQuadraticEquation_atMost shift e he
        zeroSolutions
    intro solution hsolution
    have hmem := Finset.mem_filter.mp hsolution
    exact ⟨hmem.2, hs solution hmem.1⟩
  have hnonzero :
      nonzeroSolutions.card ≤ explicitBound shift e := by
    apply
      nonzeroSplitQuadraticEquation_atMost
        hES shift e hd hshift he hsquarefree
        nonzeroSolutions
    intro solution hsolution
    have hmem := Finset.mem_filter.mp hsolution
    exact ⟨hmem.2, hs solution hmem.1⟩
  have hpartition :
      zeroSolutions.card + nonzeroSolutions.card = s.card := by
    simpa only [zeroSolutions, nonzeroSolutions] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := s) (fun solution : ℤ × ℤ => solution.2 = 0))
  calc
    s.card =
        zeroSolutions.card + nonzeroSolutions.card :=
      hpartition.symm
    _ ≤ d + explicitBound shift e :=
      Nat.add_le_add hzero hnonzero

/--
Conditional formalization of Lemma 9.1.

Assuming exactly the named Evertse--Silverman specialization above, the
integer solutions of

`∏ᵣ (X + hᵣ) = eY²`

are bounded by `d + 2 * 7^(4 + 9|S|)`. The cited result remains an ordinary
hypothesis, so this theorem introduces no hidden mathematical postulate.
-/
theorem shiftedSquareEquation_atMost_of_evertseSilverman
    (hES : EvertseSilvermanAbscissaStatement)
    {d : ℕ} (shift : Fin d → ℤ) (e : ℤ)
    (hd : 3 ≤ d)
    (hshift : Function.Injective shift)
    (he : e ≠ 0)
    (hsquarefree : IsSquarefreeInteger e) :
    HasAtMostSolutions
      (shiftedSquareEquation shift e)
      (d + explicitBound shift e) := by
  apply hasAtMostSolutions_of_injective
    (splitQuadraticEquation_atMost
      hES shift e hd hshift he hsquarefree)
    (toSplitQuadratic e)
    (toSplitQuadratic_injective he)
  intro solution hsolution
  exact shiftedSquareEquation_maps_to_split hsolution

end EvertseSilvermanInput
end PaperC
