import Mathlib.Data.Nat.Dist
import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

/-!
# Starts of constant runs

This module formalizes the deterministic local geometry used in Lemma 3.4(i)
of Paper C.  A sign is encoded additively by an element of `ZMod 2`: two
signs are opposite exactly when their sum is `1`.
-/

namespace PaperC

/-- Additive encoding of a sign.  The bits `0` and `1` represent the two
possible signs. -/
abbrev Bit := ZMod 2

/-- `StartEvent g x L` says that `x` starts a constant run of length at least
`L`: the value immediately to its left is opposite to `g x`, and all values
at `x, ..., x + L - 1` equal `g x`.

For `x = 0`, truncated subtraction makes the first equation inconsistent, so
the event is automatically false.  All starts used in the paper are positive.
-/
def StartEvent (g : ℕ → Bit) (x L : ℕ) : Prop :=
  g (x - 1) + g x = 1 ∧
    ∀ j : ℕ, j < L → g (x + j) = g x

namespace StartEvent

variable {g : ℕ → Bit} {x y L n : ℕ}

/-- Extract the affine constraint at the left boundary of a start. -/
theorem left_boundary (h : StartEvent g x L) :
    g (x - 1) + g x = 1 :=
  h.1

/-- Extract a constant-run constraint at a given offset. -/
theorem eq_at_offset (h : StartEvent g x L) {j : ℕ} (hj : j < L) :
    g (x + j) = g x :=
  h.2 j hj

/-- The value at the start itself is the run value. -/
@[simp]
theorem eq_at_zero (h : StartEvent g x L) (hL : 0 < L) :
    g (x + 0) = g x :=
  h.eq_at_offset hL

/-- Every index in the half-open run interval has value `g x`. -/
theorem eq_on_run (h : StartEvent g x L) (hxn : x ≤ n)
    (hn : n < x + L) :
    g n = g x := by
  have hj : n - x < L := by omega
  simpa [Nat.add_sub_of_le hxn] using h.eq_at_offset hj

/-- Any two indices in the half-open run interval have the same value. -/
theorem eq_of_mem_run (h : StartEvent g x L)
    (hxn : x ≤ n) (hn : n < x + L)
    (hxy : x ≤ y) (hy : y < x + L) :
    g n = g y :=
  (h.eq_on_run hxn hn).trans (h.eq_on_run hxy hy).symm

/-- The two values at the left boundary of a start are distinct. -/
theorem left_ne (h : StartEvent g x L) :
    g (x - 1) ≠ g x := by
  intro heq
  have hbad : g x + g x = (1 : Bit) := by
    simpa [heq] using h.left_boundary
  rw [← two_mul, show (2 : Bit) = 0 from ZMod.natCast_self 2, zero_mul] at hbad
  exact zero_ne_one hbad

end StartEvent

/-- Oriented form of Lemma 3.4(i): if `x < y < x + L`, starts at `x` and
`y` cannot coexist. -/
theorem startEvents_disjoint_of_lt
    {g : ℕ → Bit} {x y L : ℕ}
    (hxy : x < y) (hy : y < x + L) :
    ¬(StartEvent g x L ∧ StartEvent g y L) := by
  rintro ⟨hx, hyStart⟩
  have hleft : g (y - 1) = g x :=
    hx.eq_on_run (by omega) (by omega)
  have hright : g y = g x :=
    hx.eq_on_run (by omega) hy
  exact hyStart.left_ne (hleft.trans hright.symm)

/-- Implication form of the oriented local-exclusion lemma. -/
theorem StartEvent.not_of_lt
    {g : ℕ → Bit} {x y L : ℕ}
    (hx : StartEvent g x L) (hxy : x < y) (hy : y < x + L) :
    ¬StartEvent g y L := by
  intro hyStart
  exact startEvents_disjoint_of_lt hxy hy ⟨hx, hyStart⟩

/-- Symmetric form of Lemma 3.4(i), stated with natural-number distance. -/
theorem startEvents_disjoint_of_dist_lt
    {g : ℕ → Bit} {x y L : ℕ}
    (hxy : x ≠ y) (hdist : Nat.dist x y < L) :
    ¬(StartEvent g x L ∧ StartEvent g y L) := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  ·
    rw [Nat.dist_eq_sub_of_le hlt.le] at hdist
    exact startEvents_disjoint_of_lt hlt (by omega)
  ·
    rw [Nat.dist_eq_sub_of_le_right hgt.le] at hdist
    intro hstarts
    exact
      startEvents_disjoint_of_lt (g := g) (x := y) (y := x) (L := L)
        hgt (by omega) ⟨hstarts.2, hstarts.1⟩

end PaperC
