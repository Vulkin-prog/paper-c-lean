import PaperC.Diophantine.EvertseSilvermanInput
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Uniform generalized-Pell interface

Lemma 9.2 of Paper C counts integral solutions of

`A z² - C w² = e`

in a polynomial box.  Mathlib 4.19 contains useful material about the
homogeneous Pell equation, but not the ideal-divisor, unit-orbit and uniform
divisor-bound package used here for an arbitrary right-hand side.

This file isolates that package in the explicit proposition
`GeneralizedPellPolynomialBoxStatement`.  `GeneralizedPell` discharges it
from two narrow classical literature inputs.  Lean proves the algebraic reduction

`(z, w) ↦ (A z, w)`, `D = A C`, `M = A e`,

including injectivity, the nonsquare condition, all polynomial height bounds
and the transfer of the finite count.  The public result in this core file is
the integer-exponent version of Lemma 9.2.  `PellRealExponent` supplies the
fixed positive real-exponent interface by passing to an integer ceiling.
-/

namespace PaperC
namespace PellInput

/--
`HasAtMostSolutionsReal P B` says that every finite family of solutions of
`P` has cardinality at most the real number `B`.
-/
def HasAtMostSolutionsReal
    {α : Type*} [DecidableEq α]
    (P : α → Prop) (B : ℝ) : Prop :=
  ∀ s : Finset α, (∀ x ∈ s, P x) → (s.card : ℝ) ≤ B

/-- The explicit representative of `exp (O(log N / log log N))`. -/
noncomputable def expLogLogBound (c : ℝ) (N : ℕ) : ℝ :=
  Real.exp
    (c * Real.log (N : ℝ) /
      Real.log (Real.log (N : ℝ)))

/-- The equation `A z² - C w² = e`. -/
def pellEquation
    (A C : ℕ) (e : ℤ) (solution : ℤ × ℤ) : Prop :=
  (A : ℤ) * solution.1 ^ 2 -
      (C : ℤ) * solution.2 ^ 2 =
    e

/-- The original equation together with a symmetric integral height box. -/
def pellBox
    (A C : ℕ) (e : ℤ) (H : ℕ)
    (solution : ℤ × ℤ) : Prop :=
  pellEquation A C e solution ∧
    solution.1.natAbs ≤ H ∧
    solution.2.natAbs ≤ H

/-- The normalized generalized Pell equation and its height box. -/
def generalizedPellBox
    (D : ℕ) (M : ℤ) (H : ℕ)
    (solution : ℤ × ℤ) : Prop :=
  solution.1 ^ 2 -
      (D : ℤ) * solution.2 ^ 2 =
    M ∧
    solution.1.natAbs ≤ H ∧
    solution.2.natAbs ≤ H

/--
Internal bridge for the ideal-divisor and unit-orbit count in the proof of
Lemma 9.2.  Its source is the target manuscript itself, so it records a
remaining formalization obligation rather than a citation to an independently
published theorem.

For every fixed positive integer polynomial exponent, generalized Pell
equations with nonsquare positive coefficient and polynomially bounded
coefficient, right-hand side and height have
`exp (O(log N / log log N))` solutions.

The source quotation below records the exact point of the target manuscript
encapsulated by this bridge.  Checking that the quoted classical argument
really establishes this uniform proposition remains a mathematical review
obligation, not a kernel check.
-/
/- AUDIT_BRIDGE
{
  "id": "PCv07c-L9.2-generalized-Pell",
  "kind": "internal",
  "status": "discharged",
  "lean_name": "PaperC.PellInput.GeneralizedPellPolynomialBoxStatement",
  "discharged_by": [
    "PaperC.PellInput.generalizedPellPolynomialBox_of_quadraticOrder_nicolasRobin",
    "PaperC.PellInput.generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound"
  ],
  "citation": {
    "authors": ["Brice Pouly"],
    "title": "Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue",
    "version": "7c, juillet 2026",
    "target_pdf_sha256": "23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336",
    "locator": "Lemme 9.2, démonstration, pp. 28–29"
  },
  "source_statement": {
    "verbatim": "Ainsi le nombre de solutions est au plus O_{K₀}(τ(|M|)² log N). Comme |M| ≤ N^{O_{K₀}(1)}, la borne divisorielle standard donne (9.3).",
    "source_url": "paper_C_complete_v07c.pdf#page=29",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Lemma 9.2",
    "equation": "(9.3)",
    "pages": "28–29"
  },
  "formalization_relation": "legacy manuscript-facing interface, discharged in Lean at the source-shaped boundary by generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound; its only open upstream assumptions are the conductor-two comparison HK13-QO-conductor-fibres and the direct Nicolas--Robin logarithmic inequality NR83-T1-divisor-log-bound. The maximal-order ideal-divisor count, unit orbits, height control, finite counting, squarefree-kernel reduction, polynomial substitution and logarithmic-factor absorption are proved internally"
}
AUDIT_BRIDGE -/
def GeneralizedPellPolynomialBoxStatement : Prop :=
  ∀ K : ℕ, 0 < K →
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (D : ℕ) (M : ℤ),
        0 < D →
        ¬ IsSquare (D : ℚ) →
        M ≠ 0 →
        D ≤ N ^ K →
        M.natAbs ≤ N ^ K →
        HasAtMostSolutionsReal
          (generalizedPellBox D M (N ^ K))
          (expLogLogBound c N)

/--
Integer-polynomial-exponent formulation of Lemma 9.2.  Squarefreeness is
retained verbatim from the manuscript, although the stronger generalized
bridge below does not need it in the elementary reduction.
-/
def PellPolynomialBoxStatement : Prop :=
  ∀ K : ℕ, 0 < K →
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A C : ℕ) (e : ℤ),
        0 < A →
        0 < C →
        Squarefree A →
        Squarefree C →
        ¬ IsSquare ((A : ℚ) / (C : ℚ)) →
        e ≠ 0 →
        A ≤ N ^ K →
        C ≤ N ^ K →
        e.natAbs ≤ N ^ K →
        HasAtMostSolutionsReal
          (pellBox A C e (N ^ K))
          (expLogLogBound c N)

private theorem product_not_isSquare_of_ratio_not_isSquare
    {A C : ℕ} (hC : 0 < C)
    (hratio : ¬ IsSquare ((A : ℚ) / (C : ℚ))) :
    ¬ IsSquare ((A * C : ℕ) : ℚ) := by
  intro hproduct
  rcases hproduct with ⟨q, hq⟩
  apply hratio
  refine ⟨q / (C : ℚ), ?_⟩
  have hCne : (C : ℚ) ≠ 0 := by
    exact_mod_cast hC.ne'
  have hq' : (A : ℚ) * (C : ℚ) = q * q := by
    simpa only [Nat.cast_mul, pow_two] using hq
  calc
    (A : ℚ) / (C : ℚ) =
        ((A : ℚ) * (C : ℚ)) /
          ((C : ℚ) * (C : ℚ)) := by
      field_simp
      ring
    _ = (q * q) / ((C : ℚ) * (C : ℚ)) := by
      rw [hq']
    _ = (q / (C : ℚ)) * (q / (C : ℚ)) := by
      field_simp

private theorem originalToGeneralized_injective
    {A : ℕ} (hA : 0 < A) :
    Function.Injective
      (fun solution : ℤ × ℤ =>
        ((A : ℤ) * solution.1, solution.2)) := by
  intro u v huv
  have hfirstImage :
      ((fun solution : ℤ × ℤ =>
        ((A : ℤ) * solution.1, solution.2)) u).1 =
      ((fun solution : ℤ × ℤ =>
        ((A : ℤ) * solution.1, solution.2)) v).1 :=
    congrArg (fun z : ℤ × ℤ => z.1) huv
  change (A : ℤ) * u.1 = (A : ℤ) * v.1 at hfirstImage
  have hsecondImage :
      ((fun solution : ℤ × ℤ =>
        ((A : ℤ) * solution.1, solution.2)) u).2 =
      ((fun solution : ℤ × ℤ =>
        ((A : ℤ) * solution.1, solution.2)) v).2 :=
    congrArg (fun z : ℤ × ℤ => z.2) huv
  change u.2 = v.2 at hsecondImage
  have hAne : (A : ℤ) ≠ 0 := by
    exact_mod_cast hA.ne'
  have hfirst : u.1 = v.1 :=
    mul_left_cancel₀ hAne hfirstImage
  exact Prod.ext_iff.mpr ⟨hfirst, hsecondImage⟩

private theorem pow_le_doubled_pow
    {N K : ℕ} (hN : 1 ≤ N) :
    N ^ K ≤ N ^ (2 * K) := by
  have hone : 1 ≤ N ^ K := one_le_pow₀ hN
  calc
    N ^ K ≤ N ^ K * N ^ K := by
      exact Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt hone)
    _ = N ^ (K + K) := by rw [← pow_add]
    _ = N ^ (2 * K) := by ring_nf

private theorem original_maps_to_generalized
    {K N A C : ℕ} {e : ℤ} {solution : ℤ × ℤ}
    (hN : 1 ≤ N)
    (hA : A ≤ N ^ K)
    (hsolution : pellBox A C e (N ^ K) solution) :
    generalizedPellBox
      (A * C) ((A : ℤ) * e) (N ^ (2 * K))
      ((A : ℤ) * solution.1, solution.2) := by
  rcases hsolution with ⟨hequation, hz, hw⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      ((A : ℤ) * solution.1) ^ 2 -
          ((A * C : ℕ) : ℤ) * solution.2 ^ 2 =
          (A : ℤ) *
            ((A : ℤ) * solution.1 ^ 2 -
              (C : ℤ) * solution.2 ^ 2) := by
            push_cast
            ring
      _ = (A : ℤ) * e := by
        rw [hequation]
  · have hproduct :
        A * solution.1.natAbs ≤
          N ^ K * N ^ K :=
      Nat.mul_le_mul hA hz
    calc
      ((A : ℤ) * solution.1).natAbs =
          A * solution.1.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_ofNat]
      _ ≤ N ^ K * N ^ K := hproduct
      _ = N ^ (K + K) := by rw [← pow_add]
      _ = N ^ (2 * K) := by ring_nf
  · exact hw.trans (pow_le_doubled_pow hN)

/--
Conditional formalization of Lemma 9.2 for a positive integer polynomial
exponent.

Lean proves the reduction to generalized Pell and the exact transfer of the
finite count.  The only unproved assumption is the named internal bridge
`GeneralizedPellPolynomialBoxStatement`.
-/
theorem pellPolynomialBox_of_generalizedPell
    (hPell : GeneralizedPellPolynomialBoxStatement) :
    PellPolynomialBoxStatement := by
  intro K hK
  obtain ⟨c, hc, N₀, hN₀⟩ := hPell (2 * K) (by omega)
  refine ⟨c, hc, max N₀ 1, ?_⟩
  intro N hN A C e hApos hCpos _hAsq _hCsq
    hratio he hA hC heBound
  have hNN₀ : N₀ ≤ N :=
    (le_max_left N₀ 1).trans hN
  have hNone : 1 ≤ N :=
    (le_max_right N₀ 1).trans hN
  have hD :
      A * C ≤ N ^ (2 * K) := by
    calc
      A * C ≤ N ^ K * N ^ K :=
        Nat.mul_le_mul hA hC
      _ = N ^ (K + K) := by rw [← pow_add]
      _ = N ^ (2 * K) := by ring_nf
  have hM :
      ((A : ℤ) * e).natAbs ≤ N ^ (2 * K) := by
    have hbound :
        A * e.natAbs ≤ N ^ K * N ^ K :=
      Nat.mul_le_mul hA heBound
    calc
      ((A : ℤ) * e).natAbs =
          A * e.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_ofNat]
      _ ≤ N ^ K * N ^ K := hbound
      _ = N ^ (K + K) := by rw [← pow_add]
      _ = N ^ (2 * K) := by ring_nf
  have hMne : (A : ℤ) * e ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hApos.ne'
    · exact he
  have hgeneralized :=
    hN₀ N hNN₀ (A * C) ((A : ℤ) * e)
      (Nat.mul_pos hApos hCpos)
      (product_not_isSquare_of_ratio_not_isSquare hCpos hratio)
      hMne hD hM
  intro s hs
  let f : ℤ × ℤ → ℤ × ℤ :=
    fun solution => ((A : ℤ) * solution.1, solution.2)
  have hf : Function.Injective f := by
    simpa only [f] using originalToGeneralized_injective hApos
  have himage :
      ∀ solution ∈ s.image f,
        generalizedPellBox
          (A * C) ((A : ℤ) * e) (N ^ (2 * K))
          solution := by
    intro solution hsolution
    obtain ⟨original, horiginal, rfl⟩ :=
      Finset.mem_image.mp hsolution
    simpa only [f] using
      original_maps_to_generalized
        hNone hA (hs original horiginal)
  have hcount := hgeneralized (s.image f) himage
  simpa only [Finset.card_image_of_injective _ hf] using hcount

end PellInput
end PaperC
