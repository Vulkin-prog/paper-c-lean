import PaperC.Affine.RationalChannelCode
import PaperC.Arithmetic.ExactUnitLargeKernel
import PaperC.Combinatorics.LargePrimeGraphResolution

set_option maxHeartbeats 1800000

/-!
# Isolation of exact rational units in the large-prime graph

This module specializes the arithmetic kernel theorem to the two complete
start boundaries.  It formalizes Lemma 6.3: an exact unit whose primitive
coefficients lie below the cutoff has the same large-prime parity at its two
occurrences.  If the common kernel is one, both occurrences are defective.
Otherwise they form an isolated, nonpinned component of size two.
-/

namespace PaperC
namespace ExactUnitIsolation

open Affine
open Affine.RationalChannelCode
open ExactUnitLargeKernel
open LargePrimeOccurrences
open LargePrimeGraph
open LargePrimeGraphResolution
open PinnedGraphResolution

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/--
Primitive cross-product equality produces the factorization
`X=b*t`, `Y=a*t` used in Lemma 6.3.
-/
theorem exists_exactUnitFactorization_of_crossProduct
    {B a b X Y : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (hX : 0 < X) (_hY : 0 < Y)
    (hab : a.Coprime b)
    (hheight : Nat.max a b < B)
    (hcross : a * X = b * Y) :
    ∃ t : ℕ,
      ExactUnitFactorization B a b t X Y := by
  have hbdvdMul : b ∣ a * X :=
    ⟨Y, hcross⟩
  have hbdvdX : b ∣ X :=
    (hab.symm.dvd_mul_left).mp hbdvdMul
  obtain ⟨t, hXt⟩ := hbdvdX
  have ht : 0 < t := by
    by_contra ht
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
    subst t
    simp at hXt
    omega
  have hYt : Y = a * t := by
    have heq : b * (a * t) = b * Y := by
      calc
        b * (a * t) = a * (b * t) := by ac_rfl
        _ = a * X := by rw [hXt]
        _ = b * Y := hcross
    exact (mul_left_cancel₀ hb.ne' heq).symm
  exact
    ⟨t,
      ⟨ha, hb, ht, hab, hheight, hXt, hYt⟩⟩

/--
Every exact channel unit supplies the canonical common-factor data.
-/
theorem channelUnit_exactUnitFactorization
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hsmall : Nat.max a b < L + 1)
    (unit : ChannelUnit L a b h) :
    ∃ t : ℕ,
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L unit.1.1)
        (startCompleteVertexLabel y L unit.1.2) := by
  apply exists_exactUnitFactorization_of_crossProduct
  · exact ha
  · exact hb
  · exact startCompleteVertexLabel_pos hx unit.1.1
  · exact startCompleteVertexLabel_pos hy unit.1.2
  · exact hab
  · exact hsmall
  · exact channelUnit_label_mul_eq
      (show 1 ≤ x by omega) (show 1 ≤ y by omega)
      hheight unit

/-- Graph defectivity is exactly the arithmetic predicate `HDefective`. -/
theorem isDefective_iff_hDefective
    (x y L : ℕ) (v : Occurrence L) :
    IsDefective x y L v ↔
      DefectivePredicate.HDefective
        (L + 1)
        (twoStartCompleteVertexLabel x y L v) := by
  constructor
  · intro hv p hpPrime hpLarge
    exact
      LargePrimeComponents.parityVec_eq_zero_of_not_mem_primeOccurrences
        (hv p ⟨hpPrime, hpLarge⟩)
  · intro hv p hp hvp
    have hzero :=
      hv p hp.1 hp.2
    have hone :=
      mem_primeOccurrences.mp hvp
    rw [hzero] at hone
    exact zero_ne_one hone

/-- Large-prime occurrence at the left endpoint iff occurrence at the right. -/
theorem left_mem_primeOccurrences_iff_right_mem
    {x y L a b t : ℕ}
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w))
    {p : ℕ} (hp : p.Prime) (hpLarge : L + 1 < p) :
    Sum.inl v ∈ primeOccurrences x y L p ↔
      Sum.inr w ∈ primeOccurrences x y L p := by
  rw [mem_primeOccurrences, mem_primeOccurrences]
  have hparity :=
    exactUnit_large_parity_eq h hp hpLarge
  change
    parityVec (startCompleteVertexLabel x L v) p = 1 ↔
      parityVec (startCompleteVertexLabel y L w) p = 1
  rw [hparity.1, hparity.2]

/-- Neither endpoint of an exact unit can be pinned on its own. -/
theorem not_isPinned_left
    {x y L a b t : ℕ}
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w)) :
    ¬IsPinned x y L (Sum.inl v) := by
  rintro ⟨p, hp, hset⟩
  have hv :
      Sum.inl v ∈ primeOccurrences x y L p := by
    rw [hset]
    simp
  have hw :=
    (left_mem_primeOccurrences_iff_right_mem
      h hp.1 hp.2).mp hv
  rw [hset] at hw
  simp at hw

/-- The right endpoint of an exact unit cannot be pinned on its own. -/
theorem not_isPinned_right
    {x y L a b t : ℕ}
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w)) :
    ¬IsPinned x y L (Sum.inr w) := by
  rintro ⟨p, hp, hset⟩
  have hw :
      Sum.inr w ∈ primeOccurrences x y L p := by
    rw [hset]
    simp
  have hv :=
    (left_mem_primeOccurrences_iff_right_mem
      h hp.1 hp.2).mpr hw
  rw [hset] at hv
  simp at hv

/-- Every neighbor of the left endpoint is the right endpoint. -/
theorem eq_right_of_adj_left
    {x y L a b t : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w))
    {z : Occurrence L}
    (hz : (largePrimeGraph x y L).Adj (Sum.inl v) z) :
    z = Sum.inr w := by
  obtain ⟨hzNe, p, hp, hv, hzMem⟩ := hz
  have hw :=
    (left_mem_primeOccurrences_iff_right_mem
      h hp.1 hp.2).mp hv
  have hset :=
    primeOccurrences_eq_pair_of_mem
      hx hy hp hv hw (by simp)
  rw [hset] at hzMem
  have hcases :
      z = Sum.inl v ∨ z = Sum.inr w := by
    simpa only [Finset.mem_insert,
      Finset.mem_singleton] using hzMem
  exact hcases.resolve_left (fun hEq ↦ hzNe hEq.symm)

/-- Every neighbor of the right endpoint is the left endpoint. -/
theorem eq_left_of_adj_right
    {x y L a b t : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w))
    {z : Occurrence L}
    (hz : (largePrimeGraph x y L).Adj (Sum.inr w) z) :
    z = Sum.inl v := by
  obtain ⟨hzNe, p, hp, hw, hzMem⟩ := hz
  have hv :=
    (left_mem_primeOccurrences_iff_right_mem
      h hp.1 hp.2).mpr hw
  have hset :=
    primeOccurrences_eq_pair_of_mem
      hx hy hp hv hw (by simp)
  rw [hset] at hzMem
  have hcases :
      z = Sum.inl v ∨ z = Sum.inr w := by
    simpa only [Finset.mem_insert,
      Finset.mem_singleton] using hzMem
  exact hcases.resolve_right (fun hEq ↦ hzNe hEq.symm)

/--
Every walk starting at one endpoint of an exact unit stays inside its
two-element pair.
-/
theorem walk_from_left_stays_in_pair
    {x y L a b t : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w))
    {z : Occurrence L}
    (walk :
      (largePrimeGraph x y L).Walk
        (Sum.inl v) z) :
    z = Sum.inl v ∨ z = Sum.inr w := by
  have hclosed :
      ∀ ⦃u z : Occurrence L⦄,
        (u = Sum.inl v ∨ u = Sum.inr w) →
        (largePrimeGraph x y L).Adj u z →
        (z = Sum.inl v ∨ z = Sum.inr w) := by
    intro u z hu huz
    rcases hu with rfl | rfl
    · exact Or.inr
        (eq_right_of_adj_left hx hy h huz)
    · exact Or.inl
        (eq_left_of_adj_right hx hy h huz)
  have hwalk :
      ∀ ⦃u z : Occurrence L⦄,
        (p : (largePrimeGraph x y L).Walk u z) →
        (u = Sum.inl v ∨ u = Sum.inr w) →
        (z = Sum.inl v ∨ z = Sum.inr w) := by
    intro u z p
    induction p with
    | nil =>
        intro hu
        exact hu
    | cons huz p ih =>
        intro hu
        exact ih (hclosed hu huz)
  exact hwalk walk (Or.inl rfl)

/--
In the nondefective branch, the two exact-unit occurrences form an edge.
-/
theorem exactUnit_endpoints_adj
    {x y L a b t : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w))
    (hk : LargeOddKernel.largeOddKernel (L + 1) t ≠ 1) :
    (largePrimeGraph x y L).Adj
      (Sum.inl v) (Sum.inr w) := by
  obtain ⟨p, hpPrime, hpLarge, hleft, _ht,
      hright, _hpKernel, _hpX, _hpt, _hpY⟩ :=
    exists_common_large_odd_prime h hk
  have hnonzero_eq_one :
      ∀ z : F₂, z ≠ 0 → z = 1 := by
    decide
  exact
    ⟨by simp, p, ⟨hpPrime, hpLarge⟩,
      mem_primeOccurrences.mpr
        (hnonzero_eq_one _
          (by simpa only [twoStartCompleteVertexLabel]
            using hleft)),
      mem_primeOccurrences.mpr
        (hnonzero_eq_one _
          (by simpa only [twoStartCompleteVertexLabel]
            using hright))⟩

/-- Reachability from the left endpoint stays inside the exact pair. -/
theorem reachable_from_left_stays_in_pair
    {x y L a b t : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w))
    {z : Occurrence L}
    (hreach :
      (largePrimeGraph x y L).Reachable
        (Sum.inl v) z) :
    z = Sum.inl v ∨ z = Sum.inr w :=
  hreach.elim fun walk ↦
    walk_from_left_stays_in_pair hx hy h walk

/-- The component of a nondefective exact unit contains no pin. -/
theorem exactUnit_component_unpinned
    {x y L a b t : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w)) :
    ¬ComponentPinned
      (largePrimeGraph x y L)
      (pinnedVertices x y L)
      ((largePrimeGraph x y L).connectedComponentMk
        (Sum.inl v)) := by
  rintro ⟨z, hzPin, hzComponent⟩
  have hreach :
      (largePrimeGraph x y L).Reachable
        (Sum.inl v) z :=
    SimpleGraph.ConnectedComponent.exact
      hzComponent.symm
  have hzCases :=
    reachable_from_left_stays_in_pair hx hy h hreach
  rcases hzCases with rfl | rfl
  · exact not_isPinned_left h
      (mem_pinnedVertices.mp hzPin)
  · exact not_isPinned_right h
      (mem_pinnedVertices.mp hzPin)

/-- The isolated exact-unit component has exactly two vertices. -/
theorem exactUnit_component_card_eq_two
    {x y L a b t : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w))
    (hk : LargeOddKernel.largeOddKernel (L + 1) t ≠ 1) :
    Fintype.card
        ((largePrimeGraph x y L).connectedComponentMk
          (Sum.inl v)).supp =
      2 := by
  let C :=
    (largePrimeGraph x y L).connectedComponentMk
      (Sum.inl v)
  have hadj :=
    exactUnit_endpoints_adj hx hy h hk
  have hrightComponent :
      (largePrimeGraph x y L).connectedComponentMk
          (Sum.inr w) =
        C := by
    dsimp [C]
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hadj).symm
  let leftIn : C.supp :=
    ⟨Sum.inl v, by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]⟩
  let rightIn : C.supp :=
    ⟨Sum.inr w, by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact hrightComponent⟩
  have hleftRight : leftIn ≠ rightIn := by
    intro heq
    have := congrArg Subtype.val heq
    simp [leftIn, rightIn] at this
  letI : Nontrivial C.supp :=
    ⟨⟨leftIn, rightIn, hleftRight⟩⟩
  have hlower :
      2 ≤ Fintype.card C.supp := by
    have hone :=
      Fintype.one_lt_card (α := C.supp)
    omega
  have hvertexCases (z : C.supp) :
      z.1 = Sum.inl v ∨ z.1 = Sum.inr w := by
    have hcomponent :
        (largePrimeGraph x y L).connectedComponentMk
            z.1 =
          C := by
      simpa only [
        SimpleGraph.ConnectedComponent.mem_supp_iff]
        using z.2
    have hreach :
        (largePrimeGraph x y L).Reachable
          (Sum.inl v) z.1 :=
      SimpleGraph.ConnectedComponent.exact
        (by simpa [C] using hcomponent.symm)
    exact
      reachable_from_left_stays_in_pair hx hy h hreach
  have hblockInjective :
      Function.Injective
        (fun z : C.supp ↦
          occurrenceBlock z.1) := by
    intro z z' hblock
    change
      occurrenceBlock z.1 =
        occurrenceBlock z'.1 at hblock
    apply Subtype.ext
    rcases hvertexCases z with hz | hz <;>
      rcases hvertexCases z' with hz' | hz'
    · exact hz.trans hz'.symm
    · exfalso
      rw [hz, hz'] at hblock
      simpa [occurrenceBlock] using hblock
    · exfalso
      rw [hz, hz'] at hblock
      simpa [occurrenceBlock] using hblock
    · exact hz.trans hz'.symm
  have hupper :
      Fintype.card C.supp ≤ 2 := by
    have hle :=
      Fintype.card_le_of_injective
        (fun z : C.supp ↦ occurrenceBlock z.1)
        hblockInjective
    simpa using hle
  change Fintype.card C.supp = 2
  omega

/--
The nontrivial branch of Lemma 6.3 gives an isolated nonpinned component of
size two.
-/
theorem exactUnit_nontrivial_component
    {x y L a b t : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w))
    (hk : LargeOddKernel.largeOddKernel (L + 1) t ≠ 1) :
    IsNontrivialUnpinnedComponent
      (largePrimeGraph x y L)
      (pinnedVertices x y L)
      ((largePrimeGraph x y L).connectedComponentMk
        (Sum.inl v)) ∧
    Fintype.card
        ((largePrimeGraph x y L).connectedComponentMk
          (Sum.inl v)).supp =
      2 := by
  have hcard :=
    exactUnit_component_card_eq_two hx hy h hk
  exact
    ⟨⟨exactUnit_component_unpinned hx hy h,
        by omega⟩,
      hcard⟩

/--
Lemma 6.3 in its two graph-theoretic branches.
-/
theorem exactUnit_graph_dichotomy
    {x y L a b t : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v w : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w)) :
    (IsDefective x y L (Sum.inl v) ∧
        IsDefective x y L (Sum.inr w)) ∨
      ((largePrimeGraph x y L).Adj
          (Sum.inl v) (Sum.inr w) ∧
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L)
          ((largePrimeGraph x y L).connectedComponentMk
            (Sum.inl v)) ∧
        Fintype.card
            ((largePrimeGraph x y L).connectedComponentMk
              (Sum.inl v)).supp =
          2) := by
  rcases exactUnit_defect_dichotomy h with
      ⟨_hk, hleft, _ht, hright⟩ |
      ⟨hk, _hleft, _ht, _hright⟩
  · left
    constructor
    · rw [isDefective_iff_hDefective]
      simpa only [twoStartCompleteVertexLabel]
        using hleft
    · rw [isDefective_iff_hDefective]
      simpa only [twoStartCompleteVertexLabel]
        using hright
  · right
    have hkNe : LargeOddKernel.largeOddKernel (L + 1) t ≠ 1 := by
      omega
    exact
      ⟨exactUnit_endpoints_adj hx hy h hkNe,
        exactUnit_nontrivial_component hx hy h hkNe⟩

/-! ## Distinct exact units -/

/-- Distinct units of a positive channel cannot share their left occurrence. -/
theorem channelUnit_left_ne_of_ne
    {L a b : ℕ} {h : ℤ}
    (hb : 0 < b)
    {unit₁ unit₂ : ChannelUnit L a b h}
    (hne : unit₁ ≠ unit₂) :
    unit₁.1.1 ≠ unit₂.1.1 := by
  intro heq
  exact hne
    (channelUnit_left_injective hb heq)

/-- Distinct units of a positive channel cannot share their right occurrence. -/
theorem channelUnit_right_ne_of_ne
    {L a b : ℕ} {h : ℤ}
    (ha : 0 < a)
    {unit₁ unit₂ : ChannelUnit L a b h}
    (hne : unit₁ ≠ unit₂) :
    unit₁.1.2 ≠ unit₂.1.2 := by
  intro heq
  exact hne
    (channelUnit_right_injective ha heq)

/-- The two occurrence vertices carried by one exact channel unit. -/
def channelUnitOccurrencePair
    {L a b : ℕ} {h : ℤ}
    (unit : ChannelUnit L a b h) :
    Finset (Occurrence L) :=
  {Sum.inl unit.1.1, Sum.inr unit.1.2}

@[simp]
theorem mem_channelUnitOccurrencePair
    {L a b : ℕ} {h : ℤ}
    {unit : ChannelUnit L a b h}
    {z : Occurrence L} :
    z ∈ channelUnitOccurrencePair unit ↔
      z = Sum.inl unit.1.1 ∨
        z = Sum.inr unit.1.2 := by
  simp [channelUnitOccurrencePair]

/--
The two-vertex occurrence pairs of distinct units of a positive channel are
disjoint.
-/
theorem channelUnitOccurrencePair_disjoint
    {L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    {unit₁ unit₂ : ChannelUnit L a b h}
    (hne : unit₁ ≠ unit₂) :
    Disjoint
      (channelUnitOccurrencePair unit₁)
      (channelUnitOccurrencePair unit₂) := by
  classical
  have hleft :=
    channelUnit_left_ne_of_ne hb hne
  have hright :=
    channelUnit_right_ne_of_ne ha hne
  rw [Finset.disjoint_left]
  intro z hz₁ hz₂
  rw [mem_channelUnitOccurrencePair] at hz₁ hz₂
  rcases hz₁ with hz₁ | hz₁ <;>
    rcases hz₂ with hz₂ | hz₂
  · exact hleft
      (Sum.inl.inj (hz₁.symm.trans hz₂))
  · have hcontra :
        (Sum.inl unit₁.1.1 : Occurrence L) =
          Sum.inr unit₂.1.2 :=
      hz₁.symm.trans hz₂
    simp at hcontra
  · have hcontra :
        (Sum.inr unit₁.1.2 : Occurrence L) =
          Sum.inl unit₂.1.1 :=
      hz₁.symm.trans hz₂
    simp at hcontra
  · exact hright
      (Sum.inr.inj (hz₁.symm.trans hz₂))

/--
Once one exact pair is isolated by its factorization, any different left
occurrence lies in a different connected component.
-/
theorem exactUnit_left_components_ne
    {x y L a b t : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v w v' : Fin (L + 1)}
    (h :
      ExactUnitFactorization
        (L + 1) a b t
        (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel y L w))
    (hvv' : v ≠ v') :
    (largePrimeGraph x y L).connectedComponentMk
        (Sum.inl v) ≠
      (largePrimeGraph x y L).connectedComponentMk
        (Sum.inl v') := by
  intro hcomponent
  have hreach :
      (largePrimeGraph x y L).Reachable
        (Sum.inl v) (Sum.inl v') :=
    SimpleGraph.ConnectedComponent.exact hcomponent
  rcases
      reachable_from_left_stays_in_pair
        hx hy h hreach with hleft | hcross
  · exact hvv' (Sum.inl.inj hleft).symm
  · simp at hcross

/--
Distinct exact units of the same small primitive channel determine distinct
large-prime connected components.
-/
theorem distinct_channelUnits_components_ne
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hsmall : Nat.max a b < L + 1)
    {unit₁ unit₂ : ChannelUnit L a b h}
    (hne : unit₁ ≠ unit₂) :
    (largePrimeGraph x y L).connectedComponentMk
        (Sum.inl unit₁.1.1) ≠
      (largePrimeGraph x y L).connectedComponentMk
        (Sum.inl unit₂.1.1) := by
  obtain ⟨t, hfactor⟩ :=
    channelUnit_exactUnitFactorization
      ha hb hab hx hy hheight hsmall unit₁
  exact
    exactUnit_left_components_ne
      (by omega) (by omega) hfactor
      (channelUnit_left_ne_of_ne hb hne)

/--
In the nondefective branch, distinct exact units give distinct isolated
nonpinned two-vertex components.
-/
theorem distinct_channelUnits_nondefective_components
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hsmall : Nat.max a b < L + 1)
    {unit₁ unit₂ : ChannelUnit L a b h}
    (hne : unit₁ ≠ unit₂)
    (hnondef₁ :
      ¬IsDefective x y L (Sum.inl unit₁.1.1))
    (hnondef₂ :
      ¬IsDefective x y L (Sum.inl unit₂.1.1)) :
    let C₁ :=
      (largePrimeGraph x y L).connectedComponentMk
        (Sum.inl unit₁.1.1)
    let C₂ :=
      (largePrimeGraph x y L).connectedComponentMk
        (Sum.inl unit₂.1.1)
    C₁ ≠ C₂ ∧
      (IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C₁ ∧
        Fintype.card C₁.supp = 2) ∧
      (IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C₂ ∧
        Fintype.card C₂.supp = 2) := by
  dsimp only
  have hcomponents :=
    distinct_channelUnits_components_ne
      ha hb hab hx hy hheight hsmall hne
  obtain ⟨t₁, hfactor₁⟩ :=
    channelUnit_exactUnitFactorization
      ha hb hab hx hy hheight hsmall unit₁
  obtain ⟨t₂, hfactor₂⟩ :=
    channelUnit_exactUnitFactorization
      ha hb hab hx hy hheight hsmall unit₂
  have hbranch₁ :
      IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L)
          ((largePrimeGraph x y L).connectedComponentMk
            (Sum.inl unit₁.1.1)) ∧
        Fintype.card
            ((largePrimeGraph x y L).connectedComponentMk
              (Sum.inl unit₁.1.1)).supp =
          2 := by
    rcases
        exactUnit_graph_dichotomy
          (by omega) (by omega) hfactor₁ with
      hdef | hnontrivial
    · exact (hnondef₁ hdef.1).elim
    · exact ⟨hnontrivial.2.1, hnontrivial.2.2⟩
  have hbranch₂ :
      IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L)
          ((largePrimeGraph x y L).connectedComponentMk
            (Sum.inl unit₂.1.1)) ∧
        Fintype.card
            ((largePrimeGraph x y L).connectedComponentMk
              (Sum.inl unit₂.1.1)).supp =
          2 := by
    rcases
        exactUnit_graph_dichotomy
          (by omega) (by omega) hfactor₂ with
      hdef | hnontrivial
    · exact (hnondef₂ hdef.1).elim
    · exact ⟨hnontrivial.2.1, hnontrivial.2.2⟩
  exact ⟨hcomponents, hbranch₁, hbranch₂⟩

end

end ExactUnitIsolation
end PaperC
