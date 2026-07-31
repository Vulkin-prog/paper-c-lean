import PaperC.Arithmetic.PrimeCountBridge
import PaperC.Combinatorics.CanonicalResidualCellMembership

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

/-!
# Prime support for canonical channels of small height

The prime-support estimate in Proposition 7.4 must also cover the
degenerate canonical-channel branches with zero or one exact unit.  The
support estimate from Lemma 7.2 assumes at least two exact cells, whereas
the defining inequality of a bundled canonical candidate already gives the
uniform bound needed here:

`|h + b*j - a*i| < 4 * max(a,b) * (L+1)`.

Consequently, every canonical residual certificate whose cell is not exact
has prime below that cutoff.  At most two exact certificates can remain in
the one-unit branch, by the exceptional-family part of Lemma 6.5.  This
yields the finite estimate

`c# ≤ 2 + π(4 * max(a,b) * (L+1))`.
-/

namespace PaperC
namespace SmallHeightResidualPrimeSupport

open Affine
open Affine.CanonicalRationalCode
open Affine.RationalChannelCode
open CanonicalResidualComponents
open LargePrimeGraph
open ResidualCertificates
open ResidualComponentCounts

noncomputable section

/--
The candidate inequality controls the residual expression on the complete
offset box, without any lower bound on the number of exact channel units.
-/
theorem abs_residualVertexExpression_lt_four_mul_max_of_candidate
    {A x y L : ℕ}
    (c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A))
    (cell : Fin (L + 1) × Fin (L + 1)) :
    |residualVertexExpression c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2) cell| <
      ((4 * Nat.max c.1.1 c.1.2 * (L + 1) : ℕ) : ℤ) := by
  obtain ⟨ha, hb, _haH, _hbH, _hab, hcandidate⟩ :=
    mem_reducedChannelCandidates.mp c.2
  unfold SatisfiesChannelInequality at hcandidate
  let i : ℤ := channelVertexOffset cell.1
  let j : ℤ := channelVertexOffset cell.2
  let q : ℕ := Nat.max c.1.1 c.1.2
  have hiMem : i ∈ offsetInterval L := by
    simpa only [i] using channelVertexOffset_mem_offsetInterval cell.1
  have hjMem : j ∈ offsetInterval L := by
    simpa only [j] using channelVertexOffset_mem_offsetInterval cell.2
  have hiAbs : |i| ≤ ((L + 1 : ℕ) : ℤ) := by
    rw [abs_le]
    have hiBounds := mem_offsetInterval.mp hiMem
    constructor <;> omega
  have hjAbs : |j| ≤ ((L + 1 : ℕ) : ℤ) := by
    rw [abs_le]
    have hjBounds := mem_offsetInterval.mp hjMem
    constructor <;> omega
  have haNonneg : (0 : ℤ) ≤ (c.1.1 : ℤ) := by positivity
  have hbNonneg : (0 : ℤ) ≤ (c.1.2 : ℤ) := by positivity
  have hBNonneg : (0 : ℤ) ≤ ((L + 1 : ℕ) : ℤ) := by positivity
  have haMax : (c.1.1 : ℤ) ≤ (q : ℤ) := by
    exact_mod_cast Nat.le_max_left c.1.1 c.1.2
  have hbMax : (c.1.2 : ℤ) ≤ (q : ℤ) := by
    exact_mod_cast Nat.le_max_right c.1.1 c.1.2
  have hfirst :
      |(c.1.1 : ℤ) * i| ≤
        (c.1.1 : ℤ) * ((L + 1 : ℕ) : ℤ) := by
    rw [abs_mul, abs_of_nonneg haNonneg]
    exact mul_le_mul_of_nonneg_left hiAbs haNonneg
  have hsecond :
      |(c.1.2 : ℤ) * j| ≤
        (c.1.2 : ℤ) * ((L + 1 : ℕ) : ℤ) := by
    rw [abs_mul, abs_of_nonneg hbNonneg]
    exact mul_le_mul_of_nonneg_left hjAbs hbNonneg
  have htriangle :
      |pairChannelError x y c.1.1 c.1.2 +
          (c.1.2 : ℤ) * j - (c.1.1 : ℤ) * i| ≤
        |pairChannelError x y c.1.1 c.1.2| +
          |(c.1.2 : ℤ) * j| +
            |(c.1.1 : ℤ) * i| := by
    calc
      |pairChannelError x y c.1.1 c.1.2 +
          (c.1.2 : ℤ) * j - (c.1.1 : ℤ) * i| ≤
          |pairChannelError x y c.1.1 c.1.2 +
            (c.1.2 : ℤ) * j| +
            |(c.1.1 : ℤ) * i| := abs_sub _ _
      _ ≤
          (|pairChannelError x y c.1.1 c.1.2| +
            |(c.1.2 : ℤ) * j|) +
            |(c.1.1 : ℤ) * i| :=
        add_le_add_right (abs_add _ _) _
  have hsum :
      |pairChannelError x y c.1.1 c.1.2 +
          (c.1.2 : ℤ) * j - (c.1.1 : ℤ) * i| <
        (4 : ℤ) * (q : ℤ) * ((L + 1 : ℕ) : ℤ) := by
    calc
      |pairChannelError x y c.1.1 c.1.2 +
          (c.1.2 : ℤ) * j - (c.1.1 : ℤ) * i| ≤
          |pairChannelError x y c.1.1 c.1.2| +
            |(c.1.2 : ℤ) * j| +
              |(c.1.1 : ℤ) * i| :=
        htriangle
      _ ≤
          |pairChannelError x y c.1.1 c.1.2| +
            (c.1.2 : ℤ) * ((L + 1 : ℕ) : ℤ) +
              (c.1.1 : ℤ) * ((L + 1 : ℕ) : ℤ) :=
        add_le_add
          (add_le_add_left hsecond _)
          hfirst
      _ <
          (((c.1.1 + c.1.2) * (L + 1) : ℕ) : ℤ) +
            (c.1.2 : ℤ) * ((L + 1 : ℕ) : ℤ) +
              (c.1.1 : ℤ) * ((L + 1 : ℕ) : ℤ) :=
        add_lt_add_right
          (add_lt_add_right hcandidate
            ((c.1.2 : ℤ) * ((L + 1 : ℕ) : ℤ)))
          ((c.1.1 : ℤ) * ((L + 1 : ℕ) : ℤ))
      _ ≤ (4 : ℤ) * (q : ℤ) * ((L + 1 : ℕ) : ℤ) := by
        push_cast
        nlinarith
  simpa only [residualVertexExpression_apply, i, j, q] using hsum

/--
Every nonexact canonical residual certificate has its selected prime below
the explicit candidate cutoff.  No multiplicity hypothesis is used.
-/
theorem canonicalResidualCertificates_prime_lt_four_mul_max_of_not_onChannel
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A))
    (C :
      {C : (largePrimeGraph x y L).ConnectedComponent //
        C ∈ canonicalResidualComponents A x y L})
    (hnonexact :
      ¬OnChannel c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)
        (canonicalResidualCertificates hx hy C).offsetCell) :
    (canonicalResidualCertificates hx hy C).prime <
      4 * Nat.max c.1.1 c.1.2 * (L + 1) := by
  let cert := canonicalResidualCertificates hx hy C
  have hne :
      residualVertexExpression c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2)
          (cert.left, cert.right) ≠ 0 := by
    rw [residualVertexExpression_apply]
    apply
      (not_onChannel_iff_residualExpression_ne
        c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)
        (channelVertexOffset cert.left)
        (channelVertexOffset cert.right)).mp
    simpa only [ComponentCertificate.offsetCell, cert] using hnonexact
  have hdiv :
      (cert.prime : ℤ) ∣
        residualVertexExpression c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2)
          (cert.left, cert.right) := by
    simpa only [cert] using
      canonicalResidualCertificates_prime_dvd_residualVertexExpression
        (a := c.1.1) (b := c.1.2) hx hy C
  have hpLe :
      cert.prime ≤
        Int.natAbs
          (residualVertexExpression c.1.1 c.1.2
            (pairChannelError x y c.1.1 c.1.2)
            (cert.left, cert.right)) :=
    Int.natAbs_le_of_dvd_ne_zero hdiv hne
  have habs :=
    abs_residualVertexExpression_lt_four_mul_max_of_candidate
      c (cert.left, cert.right)
  have hnatAbs :
      Int.natAbs
          (residualVertexExpression c.1.1 c.1.2
            (pairChannelError x y c.1.1 c.1.2)
            (cert.left, cert.right)) <
        4 * Nat.max c.1.1 c.1.2 * (L + 1) := by
    rw [Int.abs_eq_natAbs] at habs
    exact_mod_cast habs
  exact hpLe.trans_lt hnatAbs

/-- Canonical residual certificates whose chosen cell is exact. -/
noncomputable def exactCanonicalResidualCertificates
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)) :
    Finset
      {C : (largePrimeGraph x y L).ConnectedComponent //
        C ∈ canonicalResidualComponents A x y L} := by
  classical
  exact Finset.univ.filter fun C ↦
    OnChannel c.1.1 c.1.2
      (pairChannelError x y c.1.1 c.1.2)
      (canonicalResidualCertificates hx hy C).offsetCell

@[simp]
theorem mem_exactCanonicalResidualCertificates
    {A x y L : ℕ}
    {hx : 1 ≤ x} {hy : 1 ≤ y}
    {c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)}
    {C :
      {C : (largePrimeGraph x y L).ConnectedComponent //
        C ∈ canonicalResidualComponents A x y L}} :
    C ∈ exactCanonicalResidualCertificates hx hy c ↔
      OnChannel c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)
        (canonicalResidualCertificates hx hy C).offsetCell := by
  simp [exactCanonicalResidualCertificates]

/--
For the selected canonical candidate, at most two canonical certificates
can be exact.  The estimate is zero in the `m=0` and `m≥2` branches; in the
one-unit branch it is inherited from the exceptional family of Lemma 6.5.
-/
theorem card_exactCanonicalResidualCertificates_le_two_of_choice
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c) :
    (exactCanonicalResidualCertificates hx hy c).card ≤ 2 := by
  classical
  let m :=
    channelUnitCount L c.1.1 c.1.2
      (pairChannelError x y c.1.1 c.1.2)
  by_cases hmTwo : 2 ≤ m
  · have hempty :
        exactCanonicalResidualCertificates hx hy c = ∅ := by
      ext C
      simp only [mem_exactCanonicalResidualCertificates,
        Finset.not_mem_empty, iff_false]
      exact
        canonicalResidualCertificates_not_onChannel_of_choice
          hx hy c hchoice (by simpa only [m] using hmTwo) C
    simp [hempty]
  · have hmLe : m ≤ 1 := by omega
    by_cases hmZero : m = 0
    · have hempty :
          exactCanonicalResidualCertificates hx hy c = ∅ := by
        ext C
        simp only [mem_exactCanonicalResidualCertificates,
          Finset.not_mem_empty, iff_false]
        intro hexact
        have hunit :
            ((canonicalResidualCertificates hx hy C).left,
                (canonicalResidualCertificates hx hy C).right) ∈
              rationalChannelUnits L c.1.1 c.1.2
                (pairChannelError x y c.1.1 c.1.2) := by
          rw [mem_rationalChannelUnits]
          simpa only [ComponentCertificate.offsetCell] using hexact
        have hmPos : 0 < m := by
          dsimp only [m]
          rw [channelUnitCount_eq_card_rationalChannelUnits]
          exact Finset.card_pos.mpr ⟨_, hunit⟩
        omega
      simp [hempty]
    · have hmOne : m = 1 := by omega
      let exceptional :=
        canonicalOneUnitExceptionalComponents
          c hchoice (by simpa only [m] using hmOne)
      have hsubset :
          (exactCanonicalResidualCertificates hx hy c).image
              Subtype.val ⊆
            exceptional := by
        intro C hC
        rw [Finset.mem_image] at hC
        obtain ⟨D, hD, rfl⟩ := hC
        have hDExact :=
          mem_exactCanonicalResidualCertificates.mp hD
        exact
          canonicalResidualCertificate_mem_oneUnitExceptionalComponents_of_choice
            hx hy c hchoice
            (by simpa only [m] using hmOne) D hDExact
      calc
        (exactCanonicalResidualCertificates hx hy c).card =
            ((exactCanonicalResidualCertificates hx hy c).image
              Subtype.val).card := by
          symm
          exact Finset.card_image_of_injective _
            Subtype.val_injective
        _ ≤ exceptional.card :=
          Finset.card_le_card hsubset
        _ ≤ 2 := by
          exact
            card_canonicalOneUnitExceptionalComponents_le_two
              c hchoice (by simpa only [m] using hmOne)

/-- Canonical residual certificates whose chosen cell is not exact. -/
noncomputable def nonexactCanonicalResidualCertificates
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)) :
    Finset
      {C : (largePrimeGraph x y L).ConnectedComponent //
        C ∈ canonicalResidualComponents A x y L} := by
  classical
  exact Finset.univ.filter fun C ↦
    ¬OnChannel c.1.1 c.1.2
      (pairChannelError x y c.1.1 c.1.2)
      (canonicalResidualCertificates hx hy C).offsetCell

@[simp]
theorem mem_nonexactCanonicalResidualCertificates
    {A x y L : ℕ}
    {hx : 1 ≤ x} {hy : 1 ≤ y}
    {c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)}
    {C :
      {C : (largePrimeGraph x y L).ConnectedComponent //
        C ∈ canonicalResidualComponents A x y L}} :
    C ∈ nonexactCanonicalResidualCertificates hx hy c ↔
      ¬OnChannel c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)
        (canonicalResidualCertificates hx hy C).offsetCell := by
  simp [nonexactCanonicalResidualCertificates]

/--
Nonexact certificates inject into the primes below the explicit geometric
cutoff.
-/
theorem card_nonexactCanonicalResidualCertificates_le_primeCount
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)) :
    (nonexactCanonicalResidualCertificates hx hy c).card ≤
      PrimesUpTo.count
        (4 * Nat.max c.1.1 c.1.2 * (L + 1)) := by
  classical
  let cutoff := 4 * Nat.max c.1.1 c.1.2 * (L + 1)
  let components :=
    nonexactCanonicalResidualCertificates hx hy c
  let primeImage : Finset ℕ :=
    components.image fun C ↦
      (canonicalResidualCertificates hx hy C).prime
  have hcardImage :
      primeImage.card = components.card := by
    exact
      Finset.card_image_of_injective components
        (canonicalResidualCertificates_prime_injective hx hy)
  have hsubset :
      primeImage ⊆ DefectCounting.smallPrimesUpTo cutoff := by
    intro p hp
    dsimp only [primeImage] at hp
    rw [Finset.mem_image] at hp
    obtain ⟨C, hC, rfl⟩ := hp
    have hnonexact :
        ¬OnChannel c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2)
          (canonicalResidualCertificates hx hy C).offsetCell :=
      mem_nonexactCanonicalResidualCertificates.mp hC
    apply (DefectCounting.mem_smallPrimesUpTo).2
    refine
      ⟨(canonicalResidualCertificates_prime_large hx hy C).1,
        ?_⟩
    exact
      (canonicalResidualCertificates_prime_lt_four_mul_max_of_not_onChannel
        hx hy c C hnonexact).le
  calc
    components.card = primeImage.card := hcardImage.symm
    _ ≤ (DefectCounting.smallPrimesUpTo cutoff).card :=
      Finset.card_le_card hsubset
    _ = PrimesUpTo.count cutoff :=
      (PrimeCountBridge.count_eq_card_smallPrimesUpTo cutoff).symm

/--
Finite component-count estimate behind Proposition 7.4.  It is valid for
every selected canonical candidate, independently of its number of exact
units.
-/
theorem canonicalResidualComponentCount_le_two_add_primeCount_of_choice
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c) :
    canonicalResidualComponentCount A x y L ≤
      2 +
        PrimesUpTo.count
          (4 * Nat.max c.1.1 c.1.2 * (L + 1)) := by
  classical
  have hsplit :
      (exactCanonicalResidualCertificates
          (show 1 ≤ x by omega) (show 1 ≤ y by omega) c).card +
        (nonexactCanonicalResidualCertificates
          (show 1 ≤ x by omega) (show 1 ≤ y by omega) c).card =
        Fintype.card
          {C : (largePrimeGraph x y L).ConnectedComponent //
            C ∈ canonicalResidualComponents A x y L} := by
    simpa only [exactCanonicalResidualCertificates,
      nonexactCanonicalResidualCertificates, Finset.card_univ] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := Finset.univ)
        (fun C :
          {C : (largePrimeGraph x y L).ConnectedComponent //
            C ∈ canonicalResidualComponents A x y L} ↦
          OnChannel c.1.1 c.1.2
            (pairChannelError x y c.1.1 c.1.2)
            (canonicalResidualCertificates
              (show 1 ≤ x by omega) (show 1 ≤ y by omega) C).offsetCell))
  rw [← card_canonicalResidualCertificateIndex hx hy]
  rw [← hsplit]
  exact Nat.add_le_add
    (card_exactCanonicalResidualCertificates_le_two_of_choice
      (show 1 ≤ x by omega) (show 1 ≤ y by omega) c hchoice)
    (card_nonexactCanonicalResidualCertificates_le_primeCount
      (show 1 ≤ x by omega) (show 1 ≤ y by omega) c)

end

end SmallHeightResidualPrimeSupport
end PaperC
