import PaperC.Combinatorics.CanonicalResidualComponents
import PaperC.Combinatorics.SmallComponentExtraction

set_option maxHeartbeats 1000000

/-!
# A bounded component in a dense nonaligned core

This module isolates the finite pigeonhole step used at the beginning of
Lemma 9.6 and in Corollary 9.7.  It does **not** contain the subsequent
Diophantine estimate for the number of hosts.

If a family of nontrivial components has total support mass at most `2B`
and has positive density among `B` possible positions, one of its members
has uniformly bounded support.  Density is stated exactly over the natural
numbers:

* `B ≤ q * c` represents the reciprocal lower bound `c ≥ B / q`;
* `alphaNum * B ≤ alphaDen * c` represents
  `c / B ≥ alphaNum / alphaDen`.

Thus no real-number rounding enters the structural argument.
-/

namespace PaperC
namespace DeepCoreSmallComponent

open CanonicalResidualComponents
open LargePrimeOccurrences
open LargePrimeGraph
open LargePrimeGraphResolution
open PinnedGraphResolution
open SmallComponentExtraction

noncomputable section

/-! ## Finite families -/

variable {ι : Type*}

/--
Basic strict-average pigeonhole principle.  If the total mass is at most
`budget`, but `family.card * (K + 1)` is larger than that budget, some
member has size at most `K`.
-/
theorem exists_member_size_le_of_mass_lt
    (family : Finset ι) (size : ι → ℕ)
    (K budget : ℕ)
    (hmass : (∑ i ∈ family, size i) ≤ budget)
    (hstrict : budget < family.card * (K + 1)) :
    ∃ i ∈ family, size i ≤ K := by
  by_contra hnone
  have hlarge :
      ∀ i ∈ family, K + 1 ≤ size i := by
    intro i hi
    by_contra hnot
    have hsmall : size i ≤ K := by omega
    exact hnone ⟨i, hi, hsmall⟩
  have hlower :
      family.card * (K + 1) ≤
        ∑ i ∈ family, size i := by
    calc
      family.card * (K + 1) =
          ∑ _i ∈ family, (K + 1) := by simp
      _ ≤ ∑ i ∈ family, size i :=
        Finset.sum_le_sum fun i hi ↦ hlarge i hi
  omega

/--
Reciprocal-density form.  Under `B ≤ q * family.card` and total mass
`≤ 2B`, a component has size at most `2q`.
-/
theorem exists_small_of_reciprocal_density
    (family : Finset ι) (size : ι → ℕ)
    {B q : ℕ}
    (hB : 0 < B)
    (hdensity : B ≤ q * family.card)
    (hmass : (∑ i ∈ family, size i) ≤ 2 * B) :
    ∃ i ∈ family, size i ≤ 2 * q := by
  have hproduct : 0 < q * family.card :=
    hB.trans_le hdensity
  have hcard : 0 < family.card :=
    Nat.pos_of_mul_pos_left hproduct
  have hstrict :
      2 * B < family.card * (2 * q + 1) := by
    calc
      2 * B ≤ 2 * (q * family.card) :=
        Nat.mul_le_mul_left 2 hdensity
      _ = family.card * (2 * q) := by ac_rfl
      _ < family.card * (2 * q + 1) :=
        (Nat.mul_lt_mul_left hcard).2 (by omega)
  exact
    exists_member_size_le_of_mass_lt
      family size (2 * q) (2 * B) hmass hstrict

/--
The preceding result bundled with the assumption that every member is a
nontrivial component.
-/
theorem exists_nontrivial_small_of_reciprocal_density
    (family : Finset ι) (size : ι → ℕ)
    {B q : ℕ}
    (hB : 0 < B)
    (hnontrivial : ∀ i ∈ family, 2 ≤ size i)
    (hdensity : B ≤ q * family.card)
    (hmass : (∑ i ∈ family, size i) ≤ 2 * B) :
    ∃ i ∈ family, 2 ≤ size i ∧ size i ≤ 2 * q := by
  obtain ⟨i, hi, hsmall⟩ :=
    exists_small_of_reciprocal_density
      family size hB hdensity hmass
  exact ⟨i, hi, hnontrivial i hi, hsmall⟩

/--
Exact rational-density form.  The inequality

`alphaNum * B ≤ alphaDen * family.card`

encodes density at least `alphaNum / alphaDen`.  Any cutoff `K` satisfying
`2 * alphaDen < alphaNum * (K + 1)` then contains a member.
-/
theorem exists_small_of_rational_density
    (family : Finset ι) (size : ι → ℕ)
    {B alphaNum alphaDen K : ℕ}
    (hB : 0 < B)
    (hden : 0 < alphaDen)
    (hdensity :
      alphaNum * B ≤ alphaDen * family.card)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1))
    (hmass : (∑ i ∈ family, size i) ≤ 2 * B) :
    ∃ i ∈ family, size i ≤ K := by
  have hscaled :
      alphaDen * (2 * B) <
        alphaDen * (family.card * (K + 1)) := by
    calc
      alphaDen * (2 * B) =
          (2 * alphaDen) * B := by ac_rfl
      _ < (alphaNum * (K + 1)) * B :=
        (Nat.mul_lt_mul_right hB).2 hcutoff
      _ = (alphaNum * B) * (K + 1) := by ac_rfl
      _ ≤ (alphaDen * family.card) * (K + 1) :=
        Nat.mul_le_mul_right (K + 1) hdensity
      _ = alphaDen * (family.card * (K + 1)) := by ac_rfl
  have hstrict :
      2 * B < family.card * (K + 1) :=
    (Nat.mul_lt_mul_left hden).mp hscaled
  exact
    exists_member_size_le_of_mass_lt
      family size K (2 * B) hmass hstrict

/-- Rational-density form with nontriviality included in the conclusion. -/
theorem exists_nontrivial_small_of_rational_density
    (family : Finset ι) (size : ι → ℕ)
    {B alphaNum alphaDen K : ℕ}
    (hB : 0 < B)
    (hden : 0 < alphaDen)
    (hnontrivial : ∀ i ∈ family, 2 ≤ size i)
    (hdensity :
      alphaNum * B ≤ alphaDen * family.card)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1))
    (hmass : (∑ i ∈ family, size i) ≤ 2 * B) :
    ∃ i ∈ family, 2 ≤ size i ∧ size i ≤ K := by
  obtain ⟨i, hi, hsmall⟩ :=
    exists_small_of_rational_density
      family size hB hden hdensity hcutoff hmass
  exact ⟨i, hi, hnontrivial i hi, hsmall⟩

/-! ## Connected components -/

/--
Connected-component specialization of reciprocal density.  The ambient
vertex bound supplies the total-mass hypothesis.
-/
theorem exists_bounded_connectedComponent_of_reciprocal_density
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (family : Finset G.ConnectedComponent)
    {B q : ℕ}
    (hB : 0 < B)
    (hambient : Fintype.card V ≤ 2 * B)
    (hnontrivial :
      ∀ C ∈ family, 2 ≤ Fintype.card C.supp)
    (hdensity : B ≤ q * family.card) :
    ∃ C ∈ family,
      2 ≤ Fintype.card C.supp ∧
        Fintype.card C.supp ≤ 2 * q := by
  classical
  apply
    exists_nontrivial_small_of_reciprocal_density
      family (fun C ↦ Fintype.card C.supp)
      hB hnontrivial hdensity
  exact (sum_component_support_sizes_le G family).trans hambient

/-- Connected-component specialization for an arbitrary rational density. -/
theorem exists_bounded_connectedComponent_of_rational_density
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (family : Finset G.ConnectedComponent)
    {B alphaNum alphaDen K : ℕ}
    (hB : 0 < B)
    (hden : 0 < alphaDen)
    (hambient : Fintype.card V ≤ 2 * B)
    (hnontrivial :
      ∀ C ∈ family, 2 ≤ Fintype.card C.supp)
    (hdensity :
      alphaNum * B ≤ alphaDen * family.card)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    ∃ C ∈ family,
      2 ≤ Fintype.card C.supp ∧
        Fintype.card C.supp ≤ K := by
  classical
  apply
    exists_nontrivial_small_of_rational_density
      family (fun C ↦ Fintype.card C.supp)
      hB hden hnontrivial hdensity hcutoff
  exact (sum_component_support_sizes_le G family).trans hambient

/-! ## The concrete residual family -/

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/--
Reciprocal-density specialization to the residual component family
`C_res`.  This is the structural bounded-component conclusion used before
the host-counting argument of Lemma 9.6.
-/
theorem residualComponents_exists_bounded_of_reciprocal_density
    {x y L a b : ℕ} {h : ℤ} {q : ℕ}
    (hdensity :
      L + 1 ≤ q * (residualComponents x y L a b h).card) :
    ∃ C ∈ residualComponents x y L a b h,
      2 ≤ Fintype.card C.supp ∧
        Fintype.card C.supp ≤ 2 * q := by
  classical
  let family := residualComponents x y L a b h
  have hambient :
      Fintype.card (Occurrence L) ≤ 2 * (L + 1) := by
    rw [card_occurrence]
  apply
    exists_bounded_connectedComponent_of_reciprocal_density
      (largePrimeGraph x y L) family
      (Nat.succ_pos L) hambient
  · intro C hC
    exact
      (isNontrivialUnpinnedComponent_of_mem_residualComponents
        (show C ∈ residualComponents x y L a b h from hC)).2
  · exact hdensity

/--
Rational-density specialization to `C_res`.  The pair
`alphaNum / alphaDen` is the exact integer presentation of the fixed
positive density `α` in Corollary 9.7.
-/
theorem residualComponents_exists_bounded_of_rational_density
    {x y L a b : ℕ} {h : ℤ}
    {alphaNum alphaDen K : ℕ}
    (hden : 0 < alphaDen)
    (hdensity :
      alphaNum * (L + 1) ≤
        alphaDen * (residualComponents x y L a b h).card)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    ∃ C ∈ residualComponents x y L a b h,
      2 ≤ Fintype.card C.supp ∧
        Fintype.card C.supp ≤ K := by
  classical
  let family := residualComponents x y L a b h
  have hambient :
      Fintype.card (Occurrence L) ≤ 2 * (L + 1) := by
    rw [card_occurrence]
  apply
    exists_bounded_connectedComponent_of_rational_density
      (largePrimeGraph x y L) family
      (Nat.succ_pos L) hden hambient
  · intro C hC
    exact
      (isNontrivialUnpinnedComponent_of_mem_residualComponents
        (show C ∈ residualComponents x y L a b h from hC)).2
  · exact hdensity
  · exact hcutoff

end

end DeepCoreSmallComponent
end PaperC
