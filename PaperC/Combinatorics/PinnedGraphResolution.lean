import PaperC.Arithmetic.ParityVector
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option maxHeartbeats 800000

/-!
# Resolution of a finite graph with pinned vertices

This is the exact linear-algebraic core of Lemma 6.1.  A binary function on
the vertices is required to be constant across every edge and to vanish at
the pinned vertices.  Such a function is constant on connected components,
and it vanishes on every component containing a pin.  Evaluation at one
representative of each unpinned component therefore gives a linear
equivalence with the full function space on the unpinned components.
-/

namespace PaperC
namespace PinnedGraphResolution

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
Binary vertex functions which are constant along edges and zero at every
pinned vertex.
-/
def PinnedGraphSpace (G : SimpleGraph V) (pins : Finset V) :
    Submodule F₂ (V → F₂) where
  carrier := {f |
    (∀ ⦃u v : V⦄, G.Adj u v → f u = f v) ∧
      ∀ v ∈ pins, f v = 0}
  zero_mem' := by
    constructor <;> simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro u v huv
      simp only [Pi.add_apply]
      rw [hf.1 huv, hg.1 huv]
    · intro v hv
      simp [hf.2 v hv, hg.2 v hv]
  smul_mem' := by
    intro a f hf
    constructor
    · intro u v huv
      simp only [Pi.smul_apply]
      rw [hf.1 huv]
    · intro v hv
      simp [hf.2 v hv]

@[simp]
theorem mem_pinnedGraphSpace
    {pins : Finset V} {f : V → F₂} :
    f ∈ PinnedGraphSpace G pins ↔
      (∀ ⦃u v : V⦄, G.Adj u v → f u = f v) ∧
        ∀ v ∈ pins, f v = 0 :=
  Iff.rfl

/-- A solution is constant along every walk. -/
theorem eq_of_walk
    {pins : Finset V}
    (f : PinnedGraphSpace G pins)
    {u v : V} (p : G.Walk u v) :
    f.1 u = f.1 v := by
  induction p with
  | nil => rfl
  | cons huv p ih =>
      exact (f.2.1 huv).trans ih

/-- A solution is constant at reachable vertices. -/
theorem eq_of_reachable
    {pins : Finset V}
    (f : PinnedGraphSpace G pins)
    {u v : V} (h : G.Reachable u v) :
    f.1 u = f.1 v :=
  h.elim fun p ↦ eq_of_walk G f p

/-- A solution is constant on each connected component. -/
theorem eq_of_connectedComponentMk_eq
    {pins : Finset V}
    (f : PinnedGraphSpace G pins)
    {u v : V}
    (h :
      G.connectedComponentMk u =
        G.connectedComponentMk v) :
    f.1 u = f.1 v :=
  eq_of_reachable G f (ConnectedComponent.exact h)

/-- A connected component is pinned if it contains a pinned vertex. -/
def ComponentPinned
    (pins : Finset V) (c : G.ConnectedComponent) : Prop :=
  ∃ v ∈ pins, G.connectedComponentMk v = c

/-- The subtype of connected components containing no pin. -/
abbrev UnpinnedComponent (pins : Finset V) :=
  {c : G.ConnectedComponent // ¬ComponentPinned G pins c}

noncomputable instance instFintypeUnpinnedComponent
    (pins : Finset V) :
    Fintype (UnpinnedComponent G pins) :=
  Fintype.ofFinite _

/-- Every solution vanishes on an entire component as soon as it contains a pin. -/
theorem eq_zero_of_componentPinned
    {pins : Finset V}
    (f : PinnedGraphSpace G pins)
    {v : V}
    (hv :
      ComponentPinned G pins
        (G.connectedComponentMk v)) :
    f.1 v = 0 := by
  obtain ⟨w, hwPin, hwComp⟩ := hv
  calc
    f.1 v = f.1 w :=
      eq_of_connectedComponentMk_eq G f hwComp.symm
    _ = 0 := f.2.2 w hwPin

/--
Evaluation at the quotient representative of every unpinned component.
The quotient representative is the only choice made in the equivalence.
-/
noncomputable def componentRestriction
    (pins : Finset V) :
    PinnedGraphSpace G pins →ₗ[F₂]
      (UnpinnedComponent G pins → F₂) where
  toFun f c := f.1 c.1.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Component restriction is injective. -/
theorem componentRestriction_injective
    (pins : Finset V) :
    Function.Injective (componentRestriction G pins) := by
  intro f g hfg
  apply Subtype.ext
  funext v
  let c := G.connectedComponentMk v
  by_cases hc : ComponentPinned G pins c
  · exact
      (eq_zero_of_componentPinned G f hc).trans
        (eq_zero_of_componentPinned G g hc).symm
  · let cu : UnpinnedComponent G pins := ⟨c, hc⟩
    have hvc :
        G.connectedComponentMk v =
          G.connectedComponentMk c.out := by
      simpa only [c] using c.out_eq.symm
    calc
      f.1 v = f.1 c.out :=
        eq_of_connectedComponentMk_eq G f hvc
      _ = componentRestriction G pins f cu := rfl
      _ = componentRestriction G pins g cu :=
        congrFun hfg cu
      _ = g.1 c.out := rfl
      _ = g.1 v :=
        (eq_of_connectedComponentMk_eq G g hvc).symm

/--
Extend arbitrary values on unpinned components by zero on all pinned
components.
-/
noncomputable def componentExtension
    (pins : Finset V)
    (g : UnpinnedComponent G pins → F₂) :
    V → F₂ := by
  classical
  exact fun v ↦
    if h : ComponentPinned G pins (G.connectedComponentMk v) then
        0
      else
        g ⟨G.connectedComponentMk v, h⟩

theorem componentExtension_eq_of_adj
    (pins : Finset V)
    (g : UnpinnedComponent G pins → F₂)
    {u v : V} (huv : G.Adj u v) :
    componentExtension G pins g u =
      componentExtension G pins g v := by
  have hcomp :
      G.connectedComponentMk u =
        G.connectedComponentMk v :=
    ConnectedComponent.connectedComponentMk_eq_of_adj huv
  unfold componentExtension
  by_cases hu :
      ComponentPinned G pins (G.connectedComponentMk u)
  · have hv :
        ComponentPinned G pins (G.connectedComponentMk v) := by
      rwa [← hcomp]
    rw [dif_pos hu, dif_pos hv]
  · have hv :
        ¬ComponentPinned G pins (G.connectedComponentMk v) := by
      rwa [← hcomp]
    rw [dif_neg hu, dif_neg hv]
    congr 1
    exact Subtype.ext hcomp

theorem componentExtension_eq_zero_of_mem
    (pins : Finset V)
    (g : UnpinnedComponent G pins → F₂)
    {v : V} (hv : v ∈ pins) :
    componentExtension G pins g v = 0 := by
  unfold componentExtension
  rw [dif_pos]
  exact ⟨v, hv, rfl⟩

/-- Component restriction is surjective. -/
theorem componentRestriction_surjective
    (pins : Finset V) :
    Function.Surjective (componentRestriction G pins) := by
  classical
  intro g
  let f : PinnedGraphSpace G pins :=
    ⟨componentExtension G pins g,
      ⟨fun _ _ huv ↦
          componentExtension_eq_of_adj G pins g huv,
        fun v hv ↦
          componentExtension_eq_zero_of_mem G pins g hv⟩⟩
  refine ⟨f, ?_⟩
  funext c
  change componentExtension G pins g c.1.out = g c
  have hc :
      ¬ComponentPinned G pins
        (G.connectedComponentMk c.1.out) := by
    intro h
    apply c.2
    simpa only [connectedComponentMk, c.1.out_eq] using h
  rw [componentExtension, dif_neg hc]
  congr 1
  exact Subtype.ext c.1.out_eq

/--
Canonical linear equivalence, after the quotient's fixed choice of one
representative in each connected component.
-/
noncomputable def pinnedGraphLinearEquiv
    (pins : Finset V) :
    PinnedGraphSpace G pins ≃ₗ[F₂]
      (UnpinnedComponent G pins → F₂) :=
  LinearEquiv.ofBijective (componentRestriction G pins)
    ⟨componentRestriction_injective G pins,
      componentRestriction_surjective G pins⟩

/-- Exact dimension formula from Lemma 6.1. -/
theorem finrank_pinnedGraphSpace
    (pins : Finset V) :
    Module.finrank F₂ (PinnedGraphSpace G pins) =
      Fintype.card (UnpinnedComponent G pins) := by
  classical
  calc
    Module.finrank F₂ (PinnedGraphSpace G pins) =
        Module.finrank F₂
          (UnpinnedComponent G pins → F₂) :=
      LinearEquiv.finrank_eq (pinnedGraphLinearEquiv G pins)
    _ = Fintype.card (UnpinnedComponent G pins) :=
      Module.finrank_pi F₂

/-! ## Isolated and nontrivial unpinned components -/

/--
The disjoint union of the vertex supports of all connected components is
canonically equivalent to the original vertex type.
-/
def componentSupportSigmaEquiv :
    (Σ c : G.ConnectedComponent, c.supp) ≃ V where
  toFun x := x.2.1
  invFun v :=
    ⟨G.connectedComponentMk v,
      ⟨v, ConnectedComponent.connectedComponentMk_mem⟩⟩
  left_inv := by
    rintro ⟨c, ⟨v, hv⟩⟩
    change
      (⟨G.connectedComponentMk v,
          ⟨v, ConnectedComponent.connectedComponentMk_mem⟩⟩ :
        Σ c : G.ConnectedComponent, c.supp) =
        ⟨c, ⟨v, hv⟩⟩
    subst c
    rfl
  right_inv _ := rfl

/-- The component supports partition the finite vertex set. -/
theorem sum_card_component_support :
    (∑ c : G.ConnectedComponent, Fintype.card c.supp) =
      Fintype.card V := by
  classical
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (componentSupportSigmaEquiv G)

/-- An unpinned connected component consisting of a single vertex. -/
def IsIsolatedUnpinnedComponent
    (pins : Finset V) (c : G.ConnectedComponent) : Prop :=
  ¬ComponentPinned G pins c ∧ Fintype.card c.supp = 1

/-- An unpinned connected component containing at least two vertices. -/
def IsNontrivialUnpinnedComponent
    (pins : Finset V) (c : G.ConnectedComponent) : Prop :=
  ¬ComponentPinned G pins c ∧ 2 ≤ Fintype.card c.supp

/-- The finite set of isolated unpinned connected components. -/
noncomputable def isolatedUnpinnedComponents
    (pins : Finset V) : Finset G.ConnectedComponent := by
  classical
  exact Finset.univ.filter (IsIsolatedUnpinnedComponent G pins)

/-- The finite set of nontrivial unpinned connected components. -/
noncomputable def nontrivialUnpinnedComponents
    (pins : Finset V) : Finset G.ConnectedComponent := by
  classical
  exact Finset.univ.filter (IsNontrivialUnpinnedComponent G pins)

@[simp]
theorem mem_isolatedUnpinnedComponents
    {pins : Finset V} {c : G.ConnectedComponent} :
    c ∈ isolatedUnpinnedComponents G pins ↔
      IsIsolatedUnpinnedComponent G pins c := by
  classical
  simp [isolatedUnpinnedComponents]

@[simp]
theorem mem_nontrivialUnpinnedComponents
    {pins : Finset V} {c : G.ConnectedComponent} :
    c ∈ nontrivialUnpinnedComponents G pins ↔
      IsNontrivialUnpinnedComponent G pins c := by
  classical
  simp [nontrivialUnpinnedComponents]

noncomputable local instance instDecidableEqConnectedComponent :
    DecidableEq G.ConnectedComponent :=
  Classical.decEq _

/-- The finite set of all connected components containing no pin. -/
noncomputable def unpinnedComponents
    (pins : Finset V) : Finset G.ConnectedComponent := by
  classical
  exact Finset.univ.filter fun c ↦
    ¬ComponentPinned G pins c

@[simp]
theorem mem_unpinnedComponents
    {pins : Finset V} {c : G.ConnectedComponent} :
    c ∈ unpinnedComponents G pins ↔
      ¬ComponentPinned G pins c := by
  classical
  simp [unpinnedComponents]

/--
The subtype used by the linear equivalence has the same cardinality as the
finite set of unpinned components.
-/
noncomputable def unpinnedComponentEquivFinset
    (pins : Finset V) :
    UnpinnedComponent G pins ≃
      {c // c ∈ unpinnedComponents G pins} where
  toFun c :=
    ⟨c.1, (mem_unpinnedComponents G).mpr c.2⟩
  invFun c :=
    ⟨c.1, (mem_unpinnedComponents G).mp c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_unpinnedComponents
    (pins : Finset V) :
    Fintype.card (UnpinnedComponent G pins) =
      (unpinnedComponents G pins).card := by
  classical
  calc
    Fintype.card (UnpinnedComponent G pins) =
        Fintype.card
          {c // c ∈ unpinnedComponents G pins} :=
      Fintype.card_congr
        (unpinnedComponentEquivFinset G pins)
    _ = (unpinnedComponents G pins).card := by
      exact Fintype.card_coe (unpinnedComponents G pins)

/--
Every unpinned component is uniquely either a singleton component or a
component containing at least two vertices.
-/
theorem isolated_union_nontrivial_eq_unpinned
    (pins : Finset V) :
    isolatedUnpinnedComponents G pins ∪
        nontrivialUnpinnedComponents G pins =
      unpinnedComponents G pins := by
  classical
  ext c
  simp only [Finset.mem_union,
    mem_isolatedUnpinnedComponents G,
    mem_nontrivialUnpinnedComponents G,
    mem_unpinnedComponents G,
    IsIsolatedUnpinnedComponent, IsNontrivialUnpinnedComponent]
  constructor
  · rintro (⟨hfree, _hcard⟩ | ⟨hfree, _hcard⟩)
    · exact hfree
    · exact hfree
  · intro hfree
    have hnonempty : c.supp.Nonempty :=
      ConnectedComponent.nonempty_supp c
    have hpositive :
        0 < Fintype.card c.supp :=
      Fintype.card_pos_iff.mpr
        ⟨⟨hnonempty.some, hnonempty.some_mem⟩⟩
    by_cases hone : Fintype.card c.supp = 1
    · exact Or.inl ⟨hfree, hone⟩
    · exact Or.inr ⟨hfree, by omega⟩

/-- The isolated and nontrivial unpinned families are disjoint. -/
theorem disjoint_isolated_nontrivial
    (pins : Finset V) :
    Disjoint
      (isolatedUnpinnedComponents G pins)
      (nontrivialUnpinnedComponents G pins) := by
  classical
  rw [Finset.disjoint_left]
  intro c hcIsolated hcNontrivial
  have hisolated :=
    (mem_isolatedUnpinnedComponents G).mp hcIsolated
  have hnontrivial :=
    (mem_nontrivialUnpinnedComponents G).mp hcNontrivial
  rw [IsIsolatedUnpinnedComponent] at hisolated
  rw [IsNontrivialUnpinnedComponent] at hnontrivial
  omega

/-- Exact splitting of the free-component count as `D+c`. -/
theorem card_unpinnedComponent_eq_isolated_add_nontrivial
    (pins : Finset V) :
    Fintype.card (UnpinnedComponent G pins) =
      (isolatedUnpinnedComponents G pins).card +
        (nontrivialUnpinnedComponents G pins).card := by
  classical
  rw [card_unpinnedComponents]
  rw [← isolated_union_nontrivial_eq_unpinned]
  exact
    Finset.card_union_of_disjoint
      (disjoint_isolated_nontrivial G pins)

/--
If `D` is the number of isolated unpinned components and `c` the number
of nontrivial unpinned components, then `D + 2c ≤ |V|`.
-/
theorem card_isolated_add_twice_card_nontrivial_le
    (pins : Finset V) :
    (isolatedUnpinnedComponents G pins).card +
        2 * (nontrivialUnpinnedComponents G pins).card ≤
      Fintype.card V := by
  classical
  let I : G.ConnectedComponent → Prop :=
    IsIsolatedUnpinnedComponent G pins
  let N : G.ConnectedComponent → Prop :=
    IsNontrivialUnpinnedComponent G pins
  have hpoint (c : G.ConnectedComponent) :
      (if I c then 1 else 0) +
          2 * (if N c then 1 else 0) ≤
        Fintype.card c.supp := by
    by_cases hi : I c
    · have hsize : Fintype.card c.supp = 1 := hi.2
      have hn : ¬N c := by
        intro hn
        have hnsize : 2 ≤ Fintype.card c.supp := hn.2
        omega
      simp [hi, hn, hsize]
    · by_cases hn : N c
      · simpa [hi, hn] using hn.2
      · simp [hi, hn]
  calc
    (isolatedUnpinnedComponents G pins).card +
          2 * (nontrivialUnpinnedComponents G pins).card =
        (∑ c : G.ConnectedComponent, if I c then 1 else 0) +
          2 * (∑ c : G.ConnectedComponent, if N c then 1 else 0) := by
            simp [isolatedUnpinnedComponents,
              nontrivialUnpinnedComponents, I, N]
    _ = ∑ c : G.ConnectedComponent,
          ((if I c then 1 else 0) +
            2 * (if N c then 1 else 0)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ c : G.ConnectedComponent, Fintype.card c.supp :=
      Finset.sum_le_sum fun c _ ↦ hpoint c
    _ = Fintype.card V :=
      sum_card_component_support G

end PinnedGraphResolution
end PaperC
