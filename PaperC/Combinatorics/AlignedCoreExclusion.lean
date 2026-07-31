import PaperC.Combinatorics.AlignedRungeBridge
import PaperC.Combinatorics.SmallComponentExtraction

set_option maxHeartbeats 1800000

/-!
# Finite exclusion theorem for an aligned deep core

This file assembles all finite steps of Paper C, Theorem 8.1:

1. delete the at most two residual components meeting an exact unit;
2. extract a large family of components of size at most `K`;
3. enumerate that family and build the two-parity matrix `Φ`;
4. obtain a short nonzero kernel word by Hamming;
5. turn it into distinct Runge roots and contradict the supplied numerical
   Runge range.

Only eventual numerical inequalities remain outside the final theorem.  In
particular, no graph, coding, square-product, or root-distinctness premise is
left to reconstruct.
-/

namespace PaperC
namespace AlignedCoreExclusion

open scoped BigOperators
open Affine.CanonicalRationalCode
open AlignedComponentCode
open AlignedExactFreeComponents
open AlignedRungeBridge
open CanonicalResidualComponents
open ComponentProductParity
open LargePrimeComponents
open LargePrimeGraph
open LargePrimeGraphResolution
open LargePrimeOccurrences
open PinnedGraphResolution
open ResidualComponentCounts
open SmallComponentExtraction

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-- Exact-free residual components supported on at most `K` vertices. -/
noncomputable def smallExactFreeResidualComponents
    (x y L a b : ℕ) (h : ℤ) (K : ℕ) :
    Finset (largePrimeGraph x y L).ConnectedComponent :=
  smallMembers
    (exactFreeResidualComponents x y L a b h)
    (fun C ↦ Fintype.card C.supp) K

@[simp]
theorem mem_smallExactFreeResidualComponents
    {x y L a b K : ℕ} {h : ℤ}
    {C : (largePrimeGraph x y L).ConnectedComponent} :
    C ∈ smallExactFreeResidualComponents x y L a b h K ↔
      C ∈ exactFreeResidualComponents x y L a b h ∧
        Fintype.card C.supp ≤ K := by
  exact mem_smallMembers

/--
After the two exact-unit exceptions and the component-size tail are paid,
the requested number of small exact-free components remains.
-/
theorem target_le_card_smallExactFreeResidualComponents
    {x y L a b K target : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hcount :
      target + 2 + (2 * (L + 1)) / (K + 1) ≤
        (residualComponents x y L a b h).card) :
    target ≤
      (smallExactFreeResidualComponents x y L a b h K).card := by
  have hcost :=
    card_residualComponents_le_card_exactFree_add_two
      (x := x) (y := y) (L := L)
      (a := a) (b := b) (h := h)
      ha hb hab hx hy hheight
  have hfamily :
      target + (2 * (L + 1)) / (K + 1) ≤
        (exactFreeResidualComponents x y L a b h).card := by
    omega
  have hextract :=
    target_small_components
      (largePrimeGraph x y L)
      (exactFreeResidualComponents x y L a b h)
      K target
  rw [card_occurrence] at hextract
  exact hextract hfamily

/--
Candidate-specialized extraction theorem.  Positivity, coprimality and the
height identity are discharged directly from membership in the canonical
finite candidate set.
-/
theorem target_le_card_smallExactFreeResidualComponents_of_candidate
    {x y L H K target : ℕ}
    (c : ReducedCandidate x y (L + 1) H)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hcount :
      target + 2 + (2 * (L + 1)) / (K + 1) ≤
        (residualComponents x y L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2)).card) :
    target ≤
      (smallExactFreeResidualComponents
        x y L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2) K).card := by
  exact
    target_le_card_smallExactFreeResidualComponents
      (candidate_fst_pos c) (candidate_snd_pos c)
      (candidate_coprime c) hx hy rfl hcount

/--
The fully assembled finite contradiction behind Theorem 8.1.

The four size assumptions are precisely those needed by the elementary
Hamming estimate.  `hRungeRange` is the final numerical statement that the
Runge upper bound is already below the chosen base throughout
`1 ≤ k ≤ K*t`.
-/
theorem no_aligned_core_of_finite_conditions
    {x y L a b K t R : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (ht : 1 ≤ t)
    (hmt :
      2 * t ≤
        (smallExactFreeResidualComponents
          x y L a b h K).card)
    (hrows :
      PrimesUpTo.count (L + 1) + 2 ≤
        (smallExactFreeResidualComponents
          x y L a b h K).card)
    (hHamming :
      2 * t *
          2 ^ ((PrimesUpTo.count (L + 1) + 2) / t + 1) ≤
        (smallExactFreeResidualComponents
          x y L a b h K).card)
    (hshiftBound :
      ∀ v : Occurrence L,
        |alignedShift a b h v| ≤ (R : ℤ))
    (hbase : 2 * R ≤ a * x)
    (hRungeRange :
      ∀ k : ℕ, 1 ≤ k → k ≤ K * t →
        (128 * (2 * k) * R) ^ (4 * k) < a * x) :
    False := by
  classical
  let family :=
    smallExactFreeResidualComponents x y L a b h K
  let m := family.card
  let enum : Fin m ≃ {C // C ∈ family} := by
    simpa only [m] using family.equivFin.symm
  let component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent :=
    fun i ↦ (enum i).1
  have hcomponent : Function.Injective component := by
    intro i j hij
    apply enum.injective
    exact Subtype.ext hij
  have hmem (i : Fin m) :
      component i ∈ family :=
    (enum i).2
  have hexact (i : Fin m) :
      IsExactFreeComponent x y L a b h (component i) := by
    apply isExactFreeComponent_of_mem
    exact
      (mem_smallExactFreeResidualComponents.mp (hmem i)).1
  have hnontrivialData (i : Fin m) :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) (component i) := by
    apply isNontrivialUnpinnedComponent_of_mem_exactFree
    exact
      (mem_smallExactFreeResidualComponents.mp (hmem i)).1
  have hnontrivial (i : Fin m) :
      2 ≤ Fintype.card (component i).supp :=
    (hnontrivialData i).2
  have hfree (i : Fin m) :
      ¬IsPinnedComponent x y L (component i) :=
    not_isPinnedComponent_of_isNontrivialUnpinned
      (hnontrivialData i)
  have hsmall (i : Fin m) :
      Fintype.card (component i).supp ≤ K :=
    (mem_smallExactFreeResidualComponents.mp (hmem i)).2
  have hmt' : 2 * t ≤ m := by
    simpa only [m, family] using hmt
  have hrows' : PrimesUpTo.count (L + 1) + 2 ≤ m := by
    simpa only [m, family] using hrows
  have hHamming' :
      2 * t *
          2 ^ ((PrimesUpTo.count (L + 1) + 2) / t + 1) ≤
        m := by
    simpa only [m, family] using hHamming
  obtain
      ⟨word, hword0, hword, hweight,
        hleft, hright, hsquare⟩ :=
    AlignedComponentHamming.exists_short_kernelWord_parity_package
      hx hy component hfree ht hmt' hrows' hHamming'
  have hleft' :
      Even (selectedLeftCount component word) := by
    simpa only [selectedLeftCount] using hleft
  have hright' :
      Even (selectedRightCount component word) := by
    simpa only [selectedRightCount] using hright
  obtain ⟨k, hk, hkKt, hRunge⟩ :=
    quantitative_runge_of_componentWord
      ha hb
      (show 1 ≤ x by omega) (show 1 ≤ y by omega)
      hheight component hcomponent hexact hnontrivial hsmall
      word hword0 hweight hleft' hright' hsquare
      hshiftBound hbase
  exact (Nat.not_lt_of_ge hRunge) (hRungeRange k hk hkKt)

/--
Paper-facing finite form of Theorem 8.1 for a bundled reduced candidate.

Compared with `no_aligned_core_of_finite_conditions`, all channel geometry
has disappeared: positivity and the identity for `h` come from the
candidate, while the uniform root radius is the canonical
`R = 3H(L+1)`.  Thus the remaining hypotheses are exactly the three Hamming
inequalities, the base-point separation, and the final elementary numerical
Runge comparison.
-/
theorem no_candidate_aligned_core_of_finite_conditions
    {x y L H K t : ℕ}
    (c : ReducedCandidate x y (L + 1) H)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (ht : 1 ≤ t)
    (hmt :
      2 * t ≤
        (smallExactFreeResidualComponents
          x y L c.1.1 c.1.2
            (pairChannelError x y c.1.1 c.1.2) K).card)
    (hrows :
      PrimesUpTo.count (L + 1) + 2 ≤
        (smallExactFreeResidualComponents
          x y L c.1.1 c.1.2
            (pairChannelError x y c.1.1 c.1.2) K).card)
    (hHamming :
      2 * t *
          2 ^ ((PrimesUpTo.count (L + 1) + 2) / t + 1) ≤
        (smallExactFreeResidualComponents
          x y L c.1.1 c.1.2
            (pairChannelError x y c.1.1 c.1.2) K).card)
    (hbase :
      2 * (3 * H * (L + 1)) ≤ c.1.1 * x)
    (hRungeRange :
      ∀ k : ℕ, 1 ≤ k → k ≤ K * t →
        (128 * (2 * k) * (3 * H * (L + 1))) ^ (4 * k) <
          c.1.1 * x) :
    False := by
  exact
    no_aligned_core_of_finite_conditions
      (candidate_fst_pos c) (candidate_snd_pos c)
      hx hy rfl ht hmt hrows hHamming
      (candidate_abs_alignedShift_le c) hbase hRungeRange

end

end AlignedCoreExclusion
end PaperC
