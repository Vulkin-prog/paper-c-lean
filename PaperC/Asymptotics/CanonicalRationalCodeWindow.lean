import PaperC.Affine.CanonicalRationalCode
import PaperC.Asymptotics.CanonicalChannelWindow

/-!
# Lemma 5.2 in the critical window

This module combines the explicit determinant threshold with the rational
code constructed in Lemma 5.1.  It records the literal uniform statement:
for fixed `A,C` and all sufficiently large `N`, every nonzero systematic
channel code belonging to a pair in the dyadic block is the canonical
rational code.
-/

namespace PaperC
namespace CanonicalRationalCodeWindow

open Affine
open Affine.RationalChannelCode
open Affine.CanonicalRationalCode

/--
Uniform coverage clause of Lemma 5.2.  The cutoff `M` is left arbitrary, so
the result applies in particular to `M = dyadicCutoff N L`.
-/
theorem canonicalRationalCode_eq_of_nonzero_eventually
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N,
        ∃ hxTwo : 2 ≤ x, ∃ hyTwo : 2 ≤ y,
          ∀ M a b,
            ∀ (ha : 0 < a) (hb : 0 < b),
            a.Coprime b →
            rationalCode M x y L a b
                (pairChannelError x y a b)
                ha hb hxTwo hyTwo (by rfl) ≠ ⊥ →
              canonicalRationalCode M A x y L hxTwo hyTwo =
                rationalCode M x y L a b
                  (pairChannelError x y a b)
                  ha hb hxTwo hyTwo (by rfl) := by
  obtain ⟨Nthreshold, hthreshold⟩ :=
    CanonicalChannelWindow.determinantThreshold_eventually hC A
  refine ⟨max 2 Nthreshold, ?_⟩
  intro N hN L hrun x hx y hy
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 Nthreshold).trans hN
  have hxLower : N ≤ x :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).1
  have hyLower : N ≤ y :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hy)).1
  have hxTwo : 2 ≤ x := hNtwo.trans hxLower
  have hyTwo : 2 ≤ y := hNtwo.trans hyLower
  have hNth :
      Nthreshold ≤ N :=
    (le_max_right 2 Nthreshold).trans hN
  have hxThreshold :
      4 * ((L + 1) ^ A) ^ 2 * (L + 1) < x :=
    (hthreshold N hNth L hrun).trans_le hxLower
  refine ⟨hxTwo, hyTwo, ?_⟩
  intro M a b ha hb hab hcode
  exact canonicalRationalCode_eq_of_rationalCode_ne_bot
    hxTwo hyTwo ha hb hab hA hxThreshold hcode

end CanonicalRationalCodeWindow
end PaperC
