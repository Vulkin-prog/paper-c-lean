import PaperC.Diophantine.PellInput
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real polynomial exponents in the generalized-Pell input

The bridge registered for Lemma 9.2 is stated with a positive natural
polynomial exponent.  The manuscript allows an arbitrary fixed real exponent
`K₀ > 0`.  This file closes that harmless interface mismatch: for `N ≥ 1`,
every real box of size `N ^ K₀` is contained in the natural-power box with
exponent `⌈K₀⌉₊`.

No new Diophantine assumption is introduced.  Every public derivation takes
the already registered `GeneralizedPellPolynomialBoxStatement` explicitly.
-/

namespace PaperC
namespace PellInput

noncomputable section

/--
Generalized-Pell counting with an arbitrary positive real polynomial
exponent and an independently supplied integral height bound.
-/
def GeneralizedPellRealPolynomialBoxStatement : Prop :=
  ∀ K : ℝ, 0 < K →
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (D : ℕ) (M : ℤ) (H : ℕ),
        0 < D →
        ¬ IsSquare (D : ℚ) →
        M ≠ 0 →
        (D : ℝ) ≤ (N : ℝ) ^ K →
        (M.natAbs : ℝ) ≤ (N : ℝ) ^ K →
        (H : ℝ) ≤ (N : ℝ) ^ K →
        HasAtMostSolutionsReal
          (generalizedPellBox D M H)
          (expLogLogBound c N)

/--
Integral-height variant of `A z² - C w² = e` with an arbitrary positive
real polynomial exponent.  The source-exact real-height formulation is
given below.
-/
def PellRealPolynomialBoxStatement : Prop :=
  ∀ K : ℝ, 0 < K →
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A C : ℕ) (e : ℤ) (H : ℕ),
        0 < A →
        0 < C →
        Squarefree A →
        Squarefree C →
        ¬ IsSquare ((A : ℚ) / (C : ℚ)) →
        e ≠ 0 →
        (A : ℝ) ≤ (N : ℝ) ^ K →
        (C : ℝ) ≤ (N : ℝ) ^ K →
        (e.natAbs : ℝ) ≤ (N : ℝ) ^ K →
        (H : ℝ) ≤ (N : ℝ) ^ K →
        HasAtMostSolutionsReal
          (pellBox A C e H)
          (expLogLogBound c N)

/--
The literal solution predicate in Lemma 17.19.  Unlike `pellBox`, its two
height inequalities use the real bound `N ^ K` appearing in the manuscript,
with no intermediate integral radius.
-/
def pellRealExponentBox
    (A C : ℕ) (e : ℤ) (N : ℕ) (K : ℝ)
    (solution : ℤ × ℤ) : Prop :=
  pellEquation A C e solution ∧
    (solution.1.natAbs : ℝ) ≤ (N : ℝ) ^ K ∧
    (solution.2.natAbs : ℝ) ≤ (N : ℝ) ^ K

/--
Source-exact formulation of Lemma 17.19: for every fixed `K > 0`, the
number of integral solutions of `A z² - C w² = e` in the literal real box
`|z|, |w| ≤ N ^ K` is bounded by
`exp (c * log N / log log N)`, uniformly in the polynomially bounded
coefficients.
-/
def PellSourceExactRealPolynomialBoxStatement : Prop :=
  ∀ K : ℝ, 0 < K →
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A C : ℕ) (e : ℤ),
        0 < A →
        0 < C →
        Squarefree A →
        Squarefree C →
        ¬ IsSquare ((A : ℚ) / (C : ℚ)) →
        e ≠ 0 →
        (A : ℝ) ≤ (N : ℝ) ^ K →
        (C : ℝ) ≤ (N : ℝ) ^ K →
        (e.natAbs : ℝ) ≤ (N : ℝ) ^ K →
        HasAtMostSolutionsReal
          (pellRealExponentBox A C e N K)
          (expLogLogBound c N)

private theorem realPolynomialBound_le_natCeilPow
    {K : ℝ} {N n : ℕ} (hN : 1 ≤ N)
    (hn : (n : ℝ) ≤ (N : ℝ) ^ K) :
    n ≤ N ^ ⌈K⌉₊ := by
  have hbase : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hexponent : K ≤ (⌈K⌉₊ : ℝ) :=
    Nat.le_ceil K
  have hpow :
      (N : ℝ) ^ K ≤ (N : ℝ) ^ (⌈K⌉₊ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexponent
  have hcast :
      (n : ℝ) ≤ (N ^ ⌈K⌉₊ : ℕ) := by
    calc
      (n : ℝ) ≤ (N : ℝ) ^ K := hn
      _ ≤ (N : ℝ) ^ (⌈K⌉₊ : ℝ) := hpow
      _ = ((N : ℝ) ^ ⌈K⌉₊) := Real.rpow_natCast _ _
      _ = (N ^ ⌈K⌉₊ : ℕ) := by norm_num
  exact_mod_cast hcast

/--
The registered natural-exponent bridge implies the literal real-exponent
generalized-Pell formulation.
-/
theorem generalizedPellRealPolynomialBox_of_generalizedPell
    (hPell : GeneralizedPellPolynomialBoxStatement) :
    GeneralizedPellRealPolynomialBoxStatement := by
  intro K hK
  let J : ℕ := ⌈K⌉₊
  have hJ : 0 < J := by
    exact Nat.ceil_pos.mpr hK
  obtain ⟨c, hc, N₀, hN₀⟩ := hPell J hJ
  refine ⟨c, hc, max N₀ 1, ?_⟩
  intro N hN D M H hDpos hDsquare hMne hD hM hH
  have hNN₀ : N₀ ≤ N :=
    (le_max_left N₀ 1).trans hN
  have hNone : 1 ≤ N :=
    (le_max_right N₀ 1).trans hN
  have hDnat : D ≤ N ^ J := by
    simpa only [J] using
      realPolynomialBound_le_natCeilPow hNone hD
  have hMnat : M.natAbs ≤ N ^ J := by
    simpa only [J] using
      realPolynomialBound_le_natCeilPow hNone hM
  have hHnat : H ≤ N ^ J := by
    simpa only [J] using
      realPolynomialBound_le_natCeilPow hNone hH
  have hlarge :=
    hN₀ N hNN₀ D M hDpos hDsquare hMne hDnat hMnat
  intro s hs
  apply hlarge s
  intro solution hsolution
  rcases hs solution hsolution with
    ⟨hequation, hfirst, hsecond⟩
  exact
    ⟨hequation, hfirst.trans hHnat, hsecond.trans hHnat⟩

/--
The original Pell formulation also inherits the real-exponent interface from
the same registered generalized-Pell bridge.
-/
theorem pellRealPolynomialBox_of_generalizedPell
    (hPell : GeneralizedPellPolynomialBoxStatement) :
    PellRealPolynomialBoxStatement := by
  have hInteger : PellPolynomialBoxStatement :=
    pellPolynomialBox_of_generalizedPell hPell
  intro K hK
  let J : ℕ := ⌈K⌉₊
  have hJ : 0 < J := by
    exact Nat.ceil_pos.mpr hK
  obtain ⟨c, hc, N₀, hN₀⟩ := hInteger J hJ
  refine ⟨c, hc, max N₀ 1, ?_⟩
  intro N hN A C e H hApos hCpos hAsq hCsq
    hratio he hA hC heBound hH
  have hNN₀ : N₀ ≤ N :=
    (le_max_left N₀ 1).trans hN
  have hNone : 1 ≤ N :=
    (le_max_right N₀ 1).trans hN
  have hAnat : A ≤ N ^ J := by
    simpa only [J] using
      realPolynomialBound_le_natCeilPow hNone hA
  have hCnat : C ≤ N ^ J := by
    simpa only [J] using
      realPolynomialBound_le_natCeilPow hNone hC
  have henat : e.natAbs ≤ N ^ J := by
    simpa only [J] using
      realPolynomialBound_le_natCeilPow hNone heBound
  have hHnat : H ≤ N ^ J := by
    simpa only [J] using
      realPolynomialBound_le_natCeilPow hNone hH
  have hlarge :=
    hN₀ N hNN₀ A C e hApos hCpos hAsq hCsq
      hratio he hAnat hCnat henat
  intro s hs
  apply hlarge s
  intro solution hsolution
  rcases hs solution hsolution with
    ⟨hequation, hfirst, hsecond⟩
  exact
    ⟨hequation, hfirst.trans hHnat, hsecond.trans hHnat⟩

/--
The registered generalized-Pell input implies the source-exact real-box
formulation of Lemma 17.19.  The input remains an explicit theorem argument:
the passage to the natural radius `⌊N ^ K⌋₊` introduces no additional
Diophantine assumption.
-/
theorem pellSourceExactRealPolynomialBox_of_generalizedPell
    (hPell : GeneralizedPellPolynomialBoxStatement) :
    PellSourceExactRealPolynomialBoxStatement := by
  have hIntegralHeight : PellRealPolynomialBoxStatement :=
    pellRealPolynomialBox_of_generalizedPell hPell
  intro K hK
  obtain ⟨c, hc, N₀, hN₀⟩ := hIntegralHeight K hK
  refine ⟨c, hc, N₀, ?_⟩
  intro N hN A C e hApos hCpos hAsq hCsq
    hratio he hA hC heBound
  let H : ℕ := ⌊(N : ℝ) ^ K⌋₊
  have hpowerNonneg : 0 ≤ (N : ℝ) ^ K := by
    positivity
  have hH : (H : ℝ) ≤ (N : ℝ) ^ K := by
    dsimp only [H]
    exact Nat.floor_le hpowerNonneg
  have hcount :=
    hN₀ N hN A C e H hApos hCpos hAsq hCsq
      hratio he hA hC heBound hH
  intro s hs
  apply hcount s
  intro solution hsolution
  rcases hs solution hsolution with
    ⟨hequation, hfirst, hsecond⟩
  refine ⟨hequation, ?_, ?_⟩
  · exact Nat.le_floor hfirst
  · exact Nat.le_floor hsecond

end

end PellInput
end PaperC
