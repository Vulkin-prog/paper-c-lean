import PaperC.Diophantine.PellInput
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Two defective values in one block

This file formalizes the Pell reduction in Lemma 9.8.  For fixed squarefree
coefficients and two offsets, a witness

`x + i₁ = d₁ u²`, `x + i₂ = d₂ v²`

maps to

`d₁ u² - d₂ v² = i₁ - i₂`.

The map remembers `(u,v)` only, but it is injective on witnesses because the
first displayed equation then determines `x`.  Consequently every finite
Pell bound transfers exactly to the number of start witnesses.  The final
theorem exposes the already registered generalized-Pell bridge directly.

The equal-coefficient divisor branch and the summation over all smooth
squarefree `d₁,d₂` remain separate obligations.
-/

namespace PaperC
namespace MultipleDefects

/-- A start together with the two square parameters. -/
structure TwoDefectWitness where
  start : ℕ
  leftRoot : ℕ
  rightRoot : ℕ
deriving DecidableEq

/--
The two defect representations at fixed offsets, with a common height bound
for their square parameters.
-/
def twoDefectWitnessBox
    (d₁ d₂ i₁ i₂ H : ℕ)
    (w : TwoDefectWitness) : Prop :=
  w.start + i₁ = d₁ * w.leftRoot ^ 2 ∧
    w.start + i₂ = d₂ * w.rightRoot ^ 2 ∧
    w.leftRoot ≤ H ∧
    w.rightRoot ≤ H

/-- Forget the determined start and cast the two square parameters to `ℤ`. -/
def witnessToPell
    (w : TwoDefectWitness) : ℤ × ℤ :=
  (w.leftRoot, w.rightRoot)

/--
The two representations subtract to the generalized Pell equation used in
Lemma 9.8.
-/
theorem twoDefectWitness_maps_to_pell
    {d₁ d₂ i₁ i₂ H : ℕ}
    {w : TwoDefectWitness}
    (hw : twoDefectWitnessBox d₁ d₂ i₁ i₂ H w) :
    PellInput.pellBox
      d₁ d₂ ((i₁ : ℤ) - (i₂ : ℤ)) H
      (witnessToPell w) := by
  rcases hw with ⟨hleft, hright, hu, hv⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold PellInput.pellEquation witnessToPell
    have hleftZ :
        (w.start : ℤ) + (i₁ : ℤ) =
          (d₁ : ℤ) * (w.leftRoot : ℤ) ^ 2 := by
      exact_mod_cast hleft
    have hrightZ :
        (w.start : ℤ) + (i₂ : ℤ) =
          (d₂ : ℤ) * (w.rightRoot : ℤ) ^ 2 := by
      exact_mod_cast hright
    nlinarith
  · simpa [witnessToPell] using hu
  · simpa [witnessToPell] using hv

/--
Although `witnessToPell` forgets `x`, it is injective on any family of
actual two-defect witnesses.
-/
theorem witnessToPell_injective_on
    {d₁ d₂ i₁ i₂ H : ℕ}
    {u v : TwoDefectWitness}
    (hu : twoDefectWitnessBox d₁ d₂ i₁ i₂ H u)
    (hv : twoDefectWitnessBox d₁ d₂ i₁ i₂ H v)
    (huv : witnessToPell u = witnessToPell v) :
    u = v := by
  have hleftRootZ :
      (u.leftRoot : ℤ) = (v.leftRoot : ℤ) :=
    congrArg (fun z : ℤ × ℤ ↦ z.1) huv
  have hrightRootZ :
      (u.rightRoot : ℤ) = (v.rightRoot : ℤ) :=
    congrArg (fun z : ℤ × ℤ ↦ z.2) huv
  have hleftRoot : u.leftRoot = v.leftRoot := by
    exact_mod_cast hleftRootZ
  have hrightRoot : u.rightRoot = v.rightRoot := by
    exact_mod_cast hrightRootZ
  have hstart : u.start = v.start := by
    have huEq := hu.1
    have hvEq := hv.1
    rw [hleftRoot] at huEq
    omega
  cases u
  cases v
  simp_all

/-- Any finite Pell count transfers to the original start witnesses. -/
theorem twoDefectWitnessBox_atMost
    {d₁ d₂ i₁ i₂ H : ℕ} {R : ℝ}
    (hPell :
      PellInput.HasAtMostSolutionsReal
        (PellInput.pellBox
          d₁ d₂ ((i₁ : ℤ) - (i₂ : ℤ)) H)
        R) :
    PellInput.HasAtMostSolutionsReal
      (twoDefectWitnessBox d₁ d₂ i₁ i₂ H)
      R := by
  intro s hs
  let f : TwoDefectWitness → ℤ × ℤ :=
    witnessToPell
  have himage :
      ∀ z ∈ s.image f,
        PellInput.pellBox
          d₁ d₂ ((i₁ : ℤ) - (i₂ : ℤ)) H z := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact twoDefectWitness_maps_to_pell (hs w hw)
  have hcount := hPell (s.image f) himage
  have hcard :
      (s.image f).card = s.card := by
    rw [Finset.card_image_iff]
    intro u hu v hv huv
    exact witnessToPell_injective_on
      (hs u hu) (hs v hv) huv
  rw [hcard] at hcount
  exact hcount

/--
Polynomial-box formulation of the distinct-squareclass branch of Lemma 9.8.
The nonsquare quotient is stated explicitly in the form consumed by
`PellPolynomialBoxStatement`.
-/
def TwoDefectPolynomialBoxStatement : Prop :=
  ∀ K : ℕ, 0 < K →
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ∀ (d₁ d₂ i₁ i₂ : ℕ),
          0 < d₁ →
          0 < d₂ →
          Squarefree d₁ →
          Squarefree d₂ →
          ¬ IsSquare ((d₁ : ℚ) / (d₂ : ℚ)) →
          i₁ ≠ i₂ →
          d₁ ≤ N ^ K →
          d₂ ≤ N ^ K →
          Int.natAbs ((i₁ : ℤ) - (i₂ : ℤ)) ≤ N ^ K →
          PellInput.HasAtMostSolutionsReal
            (twoDefectWitnessBox d₁ d₂ i₁ i₂ (N ^ K))
            (PellInput.expLogLogBound c N)

/-- The polynomial Pell statement implies the two-defect witness count. -/
theorem twoDefectPolynomialBox_of_pell
    (hPell : PellInput.PellPolynomialBoxStatement) :
    TwoDefectPolynomialBoxStatement := by
  intro K hK
  obtain ⟨c, hc, N₀, hN₀⟩ := hPell K hK
  refine ⟨c, hc, N₀, ?_⟩
  intro N hN d₁ d₂ i₁ i₂ hd₁ hd₂
    hd₁Squarefree hd₂Squarefree hnonsquare hi
    hd₁Bound hd₂Bound hdeltaBound
  have hdelta :
      (i₁ : ℤ) - (i₂ : ℤ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hi)
  have hcount :=
    hN₀ N hN d₁ d₂ ((i₁ : ℤ) - (i₂ : ℤ))
      hd₁ hd₂ hd₁Squarefree hd₂Squarefree
      hnonsquare hdelta hd₁Bound hd₂Bound hdeltaBound
  exact twoDefectWitnessBox_atMost hcount

/--
Registered-bridge version of the distinct-squareclass branch.  The internal
dependency remains explicit in the theorem signature.
-/
theorem twoDefectPolynomialBox_of_generalizedPell
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    TwoDefectPolynomialBoxStatement :=
  twoDefectPolynomialBox_of_pell
    (PellInput.pellPolynomialBox_of_generalizedPell hPell)

/-! ## Equal-squareclass branch -/

/--
When `d₁=d₂=d`, subtraction first shows `d ∣ i₁-i₂` over the integers.
-/
theorem coefficient_dvd_offset_difference
    {d i₁ i₂ : ℕ} {u v : ℤ}
    (h :
      (d : ℤ) * u ^ 2 - (d : ℤ) * v ^ 2 =
        (i₁ : ℤ) - (i₂ : ℤ)) :
    (d : ℤ) ∣ (i₁ : ℤ) - (i₂ : ℤ) := by
  refine ⟨u ^ 2 - v ^ 2, ?_⟩
  nlinarith

/--
After dividing by the common coefficient, the equal-squareclass branch
factors as `(u-v)(u+v)`.
-/
theorem equal_coefficient_factorization
    {d delta u v : ℤ}
    (hd : d ≠ 0)
    (h : d * u ^ 2 - d * v ^ 2 = delta) :
    (u - v) * (u + v) = delta / d := by
  have hfactor :
      d * ((u - v) * (u + v)) = delta := by
    nlinarith
  symm
  apply Int.ediv_eq_of_eq_mul_left hd
  calc
    delta = d * ((u - v) * (u + v)) := hfactor.symm
    _ = ((u - v) * (u + v)) * d := by ring

end MultipleDefects
end PaperC
