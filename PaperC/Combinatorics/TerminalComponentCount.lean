import PaperC.Combinatorics.PinnedGraphResolution
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

set_option maxHeartbeats 800000

/-!
# Terminal component count

This file formalizes the elementary combinatorial conclusion in
Proposition 9.11.  Suppose a family has `B - s` components, every component
has at least two vertices, and altogether they use at most `2B` vertices.
Every component larger than two consumes at least one unit of the `2s`
excess budget.  Consequently at most `2s` components are large and at
least `B - 3s` components have size exactly two.

The statement is deliberately independent of the graph model: it applies
to any finite family equipped with a size function, and hence directly to
the supports of connected components.
-/

namespace PaperC
namespace TerminalComponentCount

open Finset

variable {ι : Type*}

/-- Components in the family whose support has exactly two vertices. -/
def pairComponents
    (components : Finset ι) (size : ι → ℕ) : Finset ι :=
  components.filter fun C ↦ size C = 2

/-- Components in the family whose support has more than two vertices. -/
def largeComponents
    (components : Finset ι) (size : ι → ℕ) : Finset ι :=
  components.filter fun C ↦ 3 ≤ size C

@[simp]
theorem mem_pairComponents
    {components : Finset ι} {size : ι → ℕ} {C : ι} :
    C ∈ pairComponents components size ↔
      C ∈ components ∧ size C = 2 := by
  simp [pairComponents]

@[simp]
theorem mem_largeComponents
    {components : Finset ι} {size : ι → ℕ} {C : ι} :
    C ∈ largeComponents components size ↔
      C ∈ components ∧ 3 ≤ size C := by
  simp [largeComponents]

/--
Every component has size two or at least three, so these two filtered
families partition a family whose members all have size at least two.
-/
theorem pair_union_large_eq
    [DecidableEq ι]
    {components : Finset ι} {size : ι → ℕ}
    (hsize : ∀ C ∈ components, 2 ≤ size C) :
    pairComponents components size ∪
        largeComponents components size =
      components := by
  ext C
  simp only [pairComponents, largeComponents, mem_union, mem_filter]
  constructor
  · rintro (⟨hC, _⟩ | ⟨hC, _⟩) <;> exact hC
  · intro hC
    have htwo := hsize C hC
    by_cases heq : size C = 2
    · exact Or.inl ⟨hC, heq⟩
    · exact Or.inr ⟨hC, by omega⟩

/-- The two classes in the preceding partition are disjoint. -/
theorem disjoint_pairComponents_largeComponents
    [DecidableEq ι]
    (components : Finset ι) (size : ι → ℕ) :
    Disjoint
      (pairComponents components size)
      (largeComponents components size) := by
  rw [Finset.disjoint_left]
  intro C hpair hlarge
  rw [mem_pairComponents] at hpair
  rw [mem_largeComponents] at hlarge
  omega

/--
The vertex budget bounds the number of components larger than two.

We use `components.card + s = B`, the cancellation-safe natural-number
form of `components.card = B - s`.
-/
theorem card_largeComponents_le_two_mul
    {components : Finset ι} {size : ι → ℕ} {B s : ℕ}
    (hcard : components.card + s = B)
    (hsize : ∀ C ∈ components, 2 ≤ size C)
    (hbudget : (∑ C ∈ components, size C) ≤ 2 * B) :
    (largeComponents components size).card ≤ 2 * s := by
  have hpoint :
      ∀ C ∈ components,
        2 + (if 3 ≤ size C then 1 else 0) ≤ size C := by
    intro C hC
    by_cases hlarge : 3 ≤ size C
    · simp [hlarge]
    · have htwo := hsize C hC
      simp [hlarge]
      omega
  have hsum :
      (∑ C ∈ components,
          (2 + (if 3 ≤ size C then 1 else 0))) ≤
        ∑ C ∈ components, size C :=
    Finset.sum_le_sum fun C hC ↦ hpoint C hC
  have hindicator :
      (∑ C ∈ components, (if 3 ≤ size C then 1 else 0)) =
        (largeComponents components size).card := by
    classical
    simpa only [largeComponents] using
      (Finset.sum_boole
        (α := ℕ) (fun C : ι ↦ 3 ≤ size C) components)
  have hexcess :
      2 * components.card +
          (largeComponents components size).card ≤
        2 * B := by
    calc
      2 * components.card +
            (largeComponents components size).card =
          ∑ C ∈ components,
            (2 + (if 3 ≤ size C then 1 else 0)) := by
              rw [Finset.sum_add_distrib]
              simp [hindicator, Nat.mul_comm]
      _ ≤ ∑ C ∈ components, size C := hsum
      _ ≤ 2 * B := hbudget
  omega

/--
Proposition 9.11, terminal-population combinatorics: at least `B - 3s`
members of the family are isolated two-vertex components.
-/
theorem card_pairComponents_ge_sub_three_mul
    [DecidableEq ι]
    {components : Finset ι} {size : ι → ℕ} {B s : ℕ}
    (hcard : components.card + s = B)
    (hsize : ∀ C ∈ components, 2 ≤ size C)
    (hbudget : (∑ C ∈ components, size C) ≤ 2 * B) :
    B - 3 * s ≤ (pairComponents components size).card := by
  have hlarge :=
    card_largeComponents_le_two_mul hcard hsize hbudget
  have hpartition :=
    Finset.card_union_of_disjoint
      (disjoint_pairComponents_largeComponents components size)
  rw [pair_union_large_eq hsize] at hpartition
  omega

/--
Bundled form of the two numerical conclusions used to define the terminal
population in Proposition 9.11.
-/
theorem terminal_component_count
    [DecidableEq ι]
    {components : Finset ι} {size : ι → ℕ} {B s : ℕ}
    (hcard : components.card + s = B)
    (hsize : ∀ C ∈ components, 2 ≤ size C)
    (hbudget : (∑ C ∈ components, size C) ≤ 2 * B) :
    (largeComponents components size).card ≤ 2 * s ∧
      B - 3 * s ≤ (pairComponents components size).card :=
  ⟨card_largeComponents_le_two_mul hcard hsize hbudget,
    card_pairComponents_ge_sub_three_mul hcard hsize hbudget⟩

/--
Literal `c = B - s` form of the terminal-component conclusion.  The
side-condition `s ≤ B` records the range in which natural subtraction
agrees with the manuscript's integer calculation.
-/
theorem terminal_component_count_of_card_eq_sub
    [DecidableEq ι]
    {components : Finset ι} {size : ι → ℕ} {B s : ℕ}
    (hsB : s ≤ B)
    (hcard : components.card = B - s)
    (hsize : ∀ C ∈ components, 2 ≤ size C)
    (hbudget : (∑ C ∈ components, size C) ≤ 2 * B) :
    (largeComponents components size).card ≤ 2 * s ∧
      B - 3 * s ≤ (pairComponents components size).card := by
  apply terminal_component_count (B := B) (s := s)
  · omega
  · exact hsize
  · exact hbudget

/-!
## Connected-component specialization
-/

/--
Graph-facing form of the terminal component count.  Here `size C` is the
literal cardinality of the support of the connected component `C`.
-/
theorem connectedComponent_terminal_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {components : Finset G.ConnectedComponent} {B s : ℕ}
    (hcard : components.card + s = B)
    (hsize :
      ∀ C ∈ components, 2 ≤ Fintype.card C.supp)
    (hbudget :
      (∑ C ∈ components, Fintype.card C.supp) ≤ 2 * B) :
    (largeComponents components
          (fun C ↦ Fintype.card C.supp)).card ≤ 2 * s ∧
      B - 3 * s ≤
        (pairComponents components
          (fun C ↦ Fintype.card C.supp)).card := by
  classical
  exact terminal_component_count hcard hsize hbudget

end TerminalComponentCount
end PaperC
