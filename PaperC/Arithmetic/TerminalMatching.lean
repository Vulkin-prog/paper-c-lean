import PaperC.Combinatorics.ComponentProductParity
import PaperC.Combinatorics.LargeKernelAssignments

set_option maxHeartbeats 1600000

/-!
# Arithmetic of the terminal matching

This file formalizes the exact arithmetic core of Lemma 9.12.  A
two-vertex unpinned component gives the same large odd kernel at its two
endpoints.  Kernels attached to distinct connected components are
coprime.  Their product therefore divides the cross determinant used in
the terminal matching argument (in fact, the divisibility itself does not
need coprimality).

The last part records the determinant's nonvanishing under the literal
nonalignment hypothesis and an explicit dyadic estimate

`|Δ| ≤ 6 N (L + 1)`.

Thus the unspecified manuscript constant `C₀` can be taken to be `6` for
complete-boundary offsets, provided `L + 1 ≤ N`.
-/

namespace PaperC
namespace TerminalMatching

open Affine
open LargeOddKernel
open LargePrimeComponents
open LargePrimeGraph
open LargePrimeOccurrences

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/--
The cross determinant of two left--right pairs:

`Δ = XₛYₜ - XₜYₛ`.
-/
def crossDeterminant
    (Xs Ys Xt Yt : ℕ) : ℤ :=
  (Xs : ℤ) * (Yt : ℤ) - (Xt : ℤ) * (Ys : ℤ)

/--
The determinant vanishes exactly for the literal cross-product alignment
of the two pairs.
-/
theorem crossDeterminant_eq_zero_iff
    {Xs Ys Xt Yt : ℕ} :
    crossDeterminant Xs Ys Xt Yt = 0 ↔
      Xs * Yt = Xt * Ys := by
  rw [crossDeterminant, sub_eq_zero]
  norm_cast

/-- Nonalignment gives the nonvanishing assertion in Lemma 9.12. -/
theorem crossDeterminant_ne_zero_of_nonaligned
    {Xs Ys Xt Yt : ℕ}
    (h : Xs * Yt ≠ Xt * Ys) :
    crossDeterminant Xs Ys Xt Yt ≠ 0 := by
  exact fun hzero ↦ h (crossDeterminant_eq_zero_iff.mp hzero)

/--
If `Rₛ` divides both labels of the first pair and `Rₜ` divides both labels
of the second pair, then `RₛRₜ` divides their cross determinant over the
integers.  No coprimality hypothesis is needed.
-/
theorem product_dvd_crossDeterminant
    {Rs Rt Xs Ys Xt Yt : ℕ}
    (hXs : Rs ∣ Xs) (hYs : Rs ∣ Ys)
    (hXt : Rt ∣ Xt) (hYt : Rt ∣ Yt) :
    ((Rs * Rt : ℕ) : ℤ) ∣
      crossDeterminant Xs Ys Xt Yt := by
  obtain ⟨a, rfl⟩ := hXs
  obtain ⟨b, rfl⟩ := hYs
  obtain ⟨c, rfl⟩ := hXt
  obtain ⟨d, rfl⟩ := hYt
  refine ⟨(a : ℤ) * d - c * b, ?_⟩
  simp only [crossDeterminant, Nat.cast_mul]
  ring

/--
Specialization to large odd kernels.  Equality of the kernels at the two
endpoints of each pair supplies all four divisibilities.
-/
theorem largeOddKernel_product_dvd_crossDeterminant
    {B Xs Ys Xt Yt : ℕ}
    (hs :
      largeOddKernel B Xs =
        largeOddKernel B Ys)
    (ht :
      largeOddKernel B Xt =
        largeOddKernel B Yt) :
    (((largeOddKernel B Xs) *
        (largeOddKernel B Xt) : ℕ) : ℤ) ∣
      crossDeterminant Xs Ys Xt Yt := by
  apply product_dvd_crossDeterminant
  · exact largeOddKernel_dvd B Xs
  · rw [hs]
    exact largeOddKernel_dvd B Ys
  · exact largeOddKernel_dvd B Xt
  · rw [ht]
    exact largeOddKernel_dvd B Yt

/-! ## Kernels carried by graph components -/

/--
For a complete-boundary vertex, membership in the large odd support is
exactly occurrence at that vertex of the corresponding graph prime.
-/
theorem mem_largeOddPrimeSupport_vertexLabel
    {x y L p : ℕ} {v : Occurrence L} :
    p ∈
        largeOddPrimeSupport (L + 1)
          (twoStartCompleteVertexLabel x y L v) ↔
      IsLargePrime L p ∧
        v ∈ primeOccurrences x y L p := by
  constructor
  · intro hp
    have hpData :=
      prime_and_large_of_mem_largeOddPrimeSupport hp
    have hpParity :=
      (mem_largeOddPrimeSupport_iff.mp hp).2
    have hbinary :
        ∀ z : F₂, z ≠ 0 → z = 1 := by
      decide
    exact
      ⟨⟨hpData.1, hpData.2⟩,
        mem_primeOccurrences.mpr
          (hbinary _ hpParity)⟩
  · rintro ⟨hp, hv⟩
    rw [mem_largeOddPrimeSupport_iff]
    exact
      ⟨hp.2, by
        rw [mem_primeOccurrences] at hv
        rw [hv]
        exact one_ne_zero⟩

/--
Two prescribed distinct vertices exhaust a component whose support has
cardinality two.
-/
theorem componentVertices_eq_pair_of_card_eq_two
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    {v w : Occurrence L}
    (hv : v ∈ componentVertices x y L C)
    (hw : w ∈ componentVertices x y L C)
    (hvw : v ≠ w)
    (hcard : Fintype.card C.supp = 2) :
    componentVertices x y L C = {v, w} := by
  classical
  have hsubset :
      ({v, w} : Finset (Occurrence L)) ⊆
        componentVertices x y L C := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hv
    · exact hw
  have hcomponentCard :
      (componentVertices x y L C).card = 2 := by
    rw [ComponentProductParity.card_componentVertices, hcard]
  have hpairCard :
      ({v, w} : Finset (Occurrence L)).card = 2 := by
    simp [hvw]
  exact
    (Finset.eq_of_subset_of_card_le hsubset
      (by rw [hcomponentCard, hpairCard])).symm

/--
In an unpinned two-vertex component, every large prime occurring at one
vertex also occurs at the other.
-/
theorem mem_primeOccurrences_other_of_two_vertex_component
    {x y L p : ℕ}
    (C : (largePrimeGraph x y L).ConnectedComponent)
    {v w : Occurrence L}
    (hv : v ∈ componentVertices x y L C)
    (hw : w ∈ componentVertices x y L C)
    (hvw : v ≠ w)
    (hcard : Fintype.card C.supp = 2)
    (hfree : ¬IsPinnedComponent x y L C)
    (hp : IsLargePrime L p)
    (hvp : v ∈ primeOccurrences x y L p) :
    w ∈ primeOccurrences x y L p := by
  classical
  by_contra hwp
  have hpair :=
    componentVertices_eq_pair_of_card_eq_two
      hv hw hvw hcard
  have hsubset :
      primeOccurrences x y L p ⊆ {v} := by
    intro z hzp
    by_cases hzv : z = v
    · simp [hzv]
    · have hadj :
          (largePrimeGraph x y L).Adj v z :=
        ⟨(fun hvz ↦ hzv hvz.symm), p, hp, hvp, hzp⟩
      have hcomponent :
          (largePrimeGraph x y L).connectedComponentMk z = C := by
        exact
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hadj).symm.trans
            (mem_componentVertices.mp hv)
      have hzC :
          z ∈ componentVertices x y L C :=
        mem_componentVertices.mpr hcomponent
      rw [hpair] at hzC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzC
      rcases hzC with hzv' | hzw
      · exact (hzv hzv').elim
      · exact (hwp (hzw ▸ hzp)).elim
  have hset :
      primeOccurrences x y L p = {v} := by
    apply Finset.Subset.antisymm hsubset
    simpa only [Finset.singleton_subset_iff] using hvp
  apply hfree
  exact ⟨v, hv, ⟨p, hp, hset⟩⟩

/--
The two endpoints of an unpinned component of cardinality two have the
same large odd kernel.
-/
theorem largeOddKernel_eq_of_two_vertex_component
    {x y L : ℕ}
    (C : (largePrimeGraph x y L).ConnectedComponent)
    {v w : Occurrence L}
    (hv : v ∈ componentVertices x y L C)
    (hw : w ∈ componentVertices x y L C)
    (hvw : v ≠ w)
    (hcard : Fintype.card C.supp = 2)
    (hfree : ¬IsPinnedComponent x y L C) :
    largeOddKernel (L + 1)
        (twoStartCompleteVertexLabel x y L v) =
      largeOddKernel (L + 1)
        (twoStartCompleteVertexLabel x y L w) := by
  have hsupport :
      largeOddPrimeSupport (L + 1)
          (twoStartCompleteVertexLabel x y L v) =
        largeOddPrimeSupport (L + 1)
          (twoStartCompleteVertexLabel x y L w) := by
    ext p
    rw [mem_largeOddPrimeSupport_vertexLabel,
      mem_largeOddPrimeSupport_vertexLabel]
    constructor
    · rintro ⟨hp, hvp⟩
      exact
        ⟨hp,
          mem_primeOccurrences_other_of_two_vertex_component
            C hv hw hvw hcard hfree hp hvp⟩
    · rintro ⟨hp, hwp⟩
      exact
        ⟨hp,
          mem_primeOccurrences_other_of_two_vertex_component
            C hw hv hvw.symm hcard hfree hp hwp⟩
  simp only [largeOddKernel, hsupport]

/--
The graph-theoretic defect predicate is exactly the assertion that the
large odd kernel of the vertex label is one.
-/
theorem largeOddKernel_eq_one_iff_isDefective
    {x y L : ℕ} {v : Occurrence L} :
    largeOddKernel (L + 1)
        (twoStartCompleteVertexLabel x y L v) = 1 ↔
      IsDefective x y L v := by
  rw [largeOddKernel_eq_one_iff_support_eq_empty]
  constructor
  · intro hempty p hp
    intro hvp
    have hmem :
        p ∈
          largeOddPrimeSupport (L + 1)
            (twoStartCompleteVertexLabel x y L v) :=
      mem_largeOddPrimeSupport_vertexLabel.mpr
        ⟨hp, hvp⟩
    rw [hempty] at hmem
    exact Finset.not_mem_empty p hmem
  · intro hdef
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro p hp
    have hpData :=
      mem_largeOddPrimeSupport_vertexLabel.mp hp
    exact hdef p hpData.1 hpData.2

/--
Any vertex sharing a connected component with a distinct vertex is
nondefective.  This makes the strict lower bound `R > 1` automatic for
each endpoint of a two-vertex component.
-/
theorem not_isDefective_of_distinct_mem_component
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    {v w : Occurrence L}
    (hv : v ∈ componentVertices x y L C)
    (hw : w ∈ componentVertices x y L C)
    (hvw : v ≠ w) :
    ¬IsDefective x y L v := by
  intro hdef
  have hcomponent :
      (largePrimeGraph x y L).connectedComponentMk v =
        (largePrimeGraph x y L).connectedComponentMk w :=
    (mem_componentVertices.mp hv).trans
      (mem_componentVertices.mp hw).symm
  have hreach :
      (largePrimeGraph x y L).Reachable v w :=
    SimpleGraph.ConnectedComponent.exact hcomponent
  have hwv :
      w = v :=
    LargePrimeGraphResolution.eq_of_reachable_of_no_adj
      (not_adj_of_isDefective hdef) hreach
  exact hvw hwv.symm

/-- A nondefective vertex carries a genuinely nontrivial large kernel. -/
theorem one_lt_largeOddKernel_of_not_isDefective
    {x y L : ℕ} {v : Occurrence L}
    (hv : ¬IsDefective x y L v) :
    1 <
      largeOddKernel (L + 1)
        (twoStartCompleteVertexLabel x y L v) := by
  have hne :
      largeOddKernel (L + 1)
          (twoStartCompleteVertexLabel x y L v) ≠ 1 := by
    intro hk
    exact hv (largeOddKernel_eq_one_iff_isDefective.mp hk)
  have hone :=
    one_le_largeOddKernel (L + 1)
      (twoStartCompleteVertexLabel x y L v)
  omega

/--
Large odd kernels carried by vertices in distinct connected components are
coprime.
-/
theorem largeOddKernel_coprime_of_distinct_components
    {x y L : ℕ} {v w : Occurrence L}
    (hcomponents :
      (largePrimeGraph x y L).connectedComponentMk v ≠
        (largePrimeGraph x y L).connectedComponentMk w) :
    Nat.Coprime
      (largeOddKernel (L + 1)
        (twoStartCompleteVertexLabel x y L v))
      (largeOddKernel (L + 1)
        (twoStartCompleteVertexLabel x y L w)) := by
  by_contra hcoprime
  obtain ⟨p, hpPrime, hpv, hpw⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hcoprime
  have hvSupport :
      p ∈
        largeOddPrimeSupport (L + 1)
          (twoStartCompleteVertexLabel x y L v) :=
    (prime_dvd_largeOddKernel_iff hpPrime).mp hpv
  have hwSupport :
      p ∈
        largeOddPrimeSupport (L + 1)
          (twoStartCompleteVertexLabel x y L w) :=
    (prime_dvd_largeOddKernel_iff hpPrime).mp hpw
  have hvData :=
    mem_largeOddPrimeSupport_vertexLabel.mp hvSupport
  have hwData :=
    mem_largeOddPrimeSupport_vertexLabel.mp hwSupport
  have hvw : v ≠ w := by
    intro hvw
    exact hcomponents (congrArg
      (largePrimeGraph x y L).connectedComponentMk hvw)
  have hadj :
      (largePrimeGraph x y L).Adj v w :=
    ⟨hvw, p, hvData.1, hvData.2, hwData.2⟩
  exact hcomponents
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hadj)

/--
The complete arithmetic package for two distinct two-vertex unpinned
components.  It gives the two endpoint equalities, strict nontriviality,
pairwise coprimality, and determinant divisibility from the concrete graph
alone.
-/
theorem two_vertex_components_kernel_package
    {x y L : ℕ}
    {Cs Ct : (largePrimeGraph x y L).ConnectedComponent}
    {vs ws vt wt : Occurrence L}
    (hvs : vs ∈ componentVertices x y L Cs)
    (hws : ws ∈ componentVertices x y L Cs)
    (hvsws : vs ≠ ws)
    (hcardS : Fintype.card Cs.supp = 2)
    (hfreeS : ¬IsPinnedComponent x y L Cs)
    (hvt : vt ∈ componentVertices x y L Ct)
    (hwt : wt ∈ componentVertices x y L Ct)
    (hvtwt : vt ≠ wt)
    (hcardT : Fintype.card Ct.supp = 2)
    (hfreeT : ¬IsPinnedComponent x y L Ct)
    (hST : Cs ≠ Ct) :
    let Xs := twoStartCompleteVertexLabel x y L vs
    let Ys := twoStartCompleteVertexLabel x y L ws
    let Xt := twoStartCompleteVertexLabel x y L vt
    let Yt := twoStartCompleteVertexLabel x y L wt
    let Rs := largeOddKernel (L + 1) Xs
    let Rt := largeOddKernel (L + 1) Xt
    Rs = largeOddKernel (L + 1) Ys ∧
      Rt = largeOddKernel (L + 1) Yt ∧
      1 < Rs ∧ 1 < Rt ∧
      Nat.Coprime Rs Rt ∧
      (((Rs * Rt : ℕ) : ℤ) ∣
        crossDeterminant Xs Ys Xt Yt) := by
  dsimp only
  have hs :=
    largeOddKernel_eq_of_two_vertex_component
      Cs hvs hws hvsws hcardS hfreeS
  have ht :=
    largeOddKernel_eq_of_two_vertex_component
      Ct hvt hwt hvtwt hcardT hfreeT
  have hsGt :
      1 <
        largeOddKernel (L + 1)
          (twoStartCompleteVertexLabel x y L vs) :=
    one_lt_largeOddKernel_of_not_isDefective
      (not_isDefective_of_distinct_mem_component
        hvs hws hvsws)
  have htGt :
      1 <
        largeOddKernel (L + 1)
          (twoStartCompleteVertexLabel x y L vt) :=
    one_lt_largeOddKernel_of_not_isDefective
      (not_isDefective_of_distinct_mem_component
        hvt hwt hvtwt)
  have hcomponents :
      (largePrimeGraph x y L).connectedComponentMk vs ≠
        (largePrimeGraph x y L).connectedComponentMk vt := by
    intro heq
    apply hST
    calc
      Cs =
          (largePrimeGraph x y L).connectedComponentMk vs :=
        (mem_componentVertices.mp hvs).symm
      _ =
          (largePrimeGraph x y L).connectedComponentMk vt :=
        heq
      _ = Ct :=
        mem_componentVertices.mp hvt
  have hcoprime :=
    largeOddKernel_coprime_of_distinct_components hcomponents
  have hdvd :=
    largeOddKernel_product_dvd_crossDeterminant hs ht
  exact ⟨hs, ht, hsGt, htGt, hcoprime, hdvd⟩

/-! ## Explicit determinant bounds -/

private theorem abs_natCast_sub_natCast_eq_dist
    (a b : ℕ) :
    |(a : ℤ) - (b : ℤ)| = (Nat.dist a b : ℤ) := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    rw [abs_of_nonpos (by omega)]
    push_cast [hab]
    ring
  · rw [Nat.dist_eq_sub_of_le_right hba]
    rw [abs_of_nonneg (by omega)]
    push_cast [hba]
    rfl

/--
A determinant estimate in terms of bounds for the first labels and the
within-block distances.
-/
theorem abs_crossDeterminant_le
    {Xs Ys Xt Yt A B : ℕ}
    (hXs : Xs ≤ A) (hYs : Ys ≤ A)
    (hXdist : Nat.dist Xt Xs ≤ B)
    (hYdist : Nat.dist Yt Ys ≤ B) :
    |crossDeterminant Xs Ys Xt Yt| ≤
      ((2 * A * B : ℕ) : ℤ) := by
  have hA : (0 : ℤ) ≤ A := by positivity
  have hB : (0 : ℤ) ≤ B := by positivity
  have hXs' : |(Xs : ℤ)| ≤ (A : ℤ) := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast hXs
  have hYs' : |(Ys : ℤ)| ≤ (A : ℤ) := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast hYs
  have hXdist' :
      |(Xt : ℤ) - (Xs : ℤ)| ≤ (B : ℤ) := by
    rw [abs_natCast_sub_natCast_eq_dist]
    exact_mod_cast hXdist
  have hYdist' :
      |(Yt : ℤ) - (Ys : ℤ)| ≤ (B : ℤ) := by
    rw [abs_natCast_sub_natCast_eq_dist]
    exact_mod_cast hYdist
  calc
    |crossDeterminant Xs Ys Xt Yt| =
        |(Xs : ℤ) * ((Yt : ℤ) - Ys) -
          (Ys : ℤ) * ((Xt : ℤ) - Xs)| := by
            apply congrArg abs
            simp only [crossDeterminant]
            ring
    _ ≤
        |(Xs : ℤ) * ((Yt : ℤ) - Ys)| +
          |(Ys : ℤ) * ((Xt : ℤ) - Xs)| :=
      abs_sub _ _
    _ =
        |(Xs : ℤ)| * |(Yt : ℤ) - Ys| +
          |(Ys : ℤ)| * |(Xt : ℤ) - Xs| := by
      rw [abs_mul, abs_mul]
    _ ≤ (A : ℤ) * B + (A : ℤ) * B := by
      gcongr
    _ = ((2 * A * B : ℕ) : ℤ) := by
      push_cast
      ring

/--
For two complete-boundary pairs with starts in `[N,2N)`, the determinant
is at most `6N(L+1)` when the complete boundary length is at most `N`.
-/
theorem abs_crossDeterminant_startCompleteVertexLabel_le
    {N L x y : ℕ}
    (hN : 2 ≤ N)
    (hLN : L + 1 ≤ N)
    (hx : x ∈ dyadicBlock N)
    (hy : y ∈ dyadicBlock N)
    (is it js jt : Fin (L + 1)) :
    |crossDeterminant
        (startCompleteVertexLabel x L is)
        (startCompleteVertexLabel y L js)
        (startCompleteVertexLabel x L it)
        (startCompleteVertexLabel y L jt)| ≤
      ((6 * N * (L + 1) : ℕ) : ℤ) := by
  have hxOne : 1 ≤ x := by
    have hxData :
        N ≤ x :=
      (Finset.mem_Ico.mp
        (by simpa [dyadicBlock] using hx)).1
    omega
  have hyOne : 1 ≤ y := by
    have hyData :
        N ≤ y :=
      (Finset.mem_Ico.mp
        (by simpa [dyadicBlock] using hy)).1
    omega
  have hbase :=
    abs_crossDeterminant_le
      (LargeKernelAssignments.startCompleteVertexLabel_le_dyadicCutoff
        hx is)
      (LargeKernelAssignments.startCompleteVertexLabel_le_dyadicCutoff
        hy js)
      (show
        Nat.dist
            (startCompleteVertexLabel x L it)
            (startCompleteVertexLabel x L is) ≤
          L + 1 by
        have hlt :=
          Affine.RelationalPrimeAssignment.startCompleteVertexLabel_dist_lt
            hxOne it is
        omega)
      (show
        Nat.dist
            (startCompleteVertexLabel y L jt)
            (startCompleteVertexLabel y L js) ≤
          L + 1 by
        have hlt :=
          Affine.RelationalPrimeAssignment.startCompleteVertexLabel_dist_lt
            hyOne jt js
        omega)
  refine hbase.trans ?_
  norm_cast
  unfold dyadicCutoff
  nlinarith

end

end TerminalMatching
end PaperC
