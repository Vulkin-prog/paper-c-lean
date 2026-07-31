import PaperC.Arithmetic.ResidualChannelLemmaSevenTwo
import PaperC.Combinatorics.CanonicalResidualComponents

set_option maxHeartbeats 1800000

/-!
# Canonical residual certificates as residual channel cells

For an active canonical channel, Lemma 6.5 chooses in every residual
component a prime and a left--right cell.  The two selected vertex labels are
divisible by that prime, while the cell is not an exact channel cell.
Consequently the selected cell belongs to the finite family
`residualVertexPrimeCells` used in Lemma 7.2.

This is the first transport step needed to regard the pair-dependent
canonical certificate as a certificate in one fixed ambient cell family for
the selected channel.
-/

namespace PaperC
namespace CanonicalResidualComponents

open Affine
open Affine.CanonicalRationalCode
open Affine.RationalChannelCode
open LargePrimeGraph
open ResidualComponentCounts
open ResidualCertificates

noncomputable section

/--
The prime selected by a canonical residual component divides the residual
expression of its selected cell.  This algebraic fact does not require the
candidate `(a,b)` to be the canonical one: it follows from divisibility of
both complete-start vertex labels.
-/
theorem canonicalResidualCertificates_prime_dvd_residualVertexExpression
    {A x y L a b : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C :
      {C : (largePrimeGraph x y L).ConnectedComponent //
        C ∈ canonicalResidualComponents A x y L}) :
    ((canonicalResidualCertificates hx hy C).prime : ℤ) ∣
      residualVertexExpression a b (pairChannelError x y a b)
        ((canonicalResidualCertificates hx hy C).left,
          (canonicalResidualCertificates hx hy C).right) := by
  let cert := canonicalResidualCertificates hx hy C
  obtain ⟨kLeft, hkLeft⟩ :=
    canonicalResidualCertificates_prime_dvd_left hx hy C
  obtain ⟨kRight, hkRight⟩ :=
    canonicalResidualCertificates_prime_dvd_right hx hy C
  change
    (x : ℤ) + channelVertexOffset cert.left =
      (cert.prime : ℤ) * kLeft at hkLeft
  change
    (y : ℤ) + channelVertexOffset cert.right =
      (cert.prime : ℤ) * kRight at hkRight
  refine ⟨(b : ℤ) * kRight - (a : ℤ) * kLeft, ?_⟩
  calc
    residualVertexExpression a b (pairChannelError x y a b)
        (cert.left, cert.right) =
        (b : ℤ) *
            ((y : ℤ) + channelVertexOffset cert.right) -
          (a : ℤ) *
            ((x : ℤ) + channelVertexOffset cert.left) := by
      simp only [residualVertexExpression_apply, pairChannelError]
      ring
    _ =
        (b : ℤ) *
            ((cert.prime : ℤ) * kRight) -
          (a : ℤ) *
            ((cert.prime : ℤ) * kLeft) := by
      rw [hkRight, hkLeft]
    _ =
        (cert.prime : ℤ) *
          ((b : ℤ) * kRight - (a : ℤ) * kLeft) := by
      ring

/--
In the active canonical branch `m ≥ 2`, the cell selected by every residual
component belongs to the residual vertex-cell family at its selected prime.
-/
theorem canonicalResidualCertificates_mem_residualVertexPrimeCells_of_choice
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2))
    (C :
      {C : (largePrimeGraph x y L).ConnectedComponent //
        C ∈ canonicalResidualComponents A x y L}) :
    ((canonicalResidualCertificates hx hy C).left,
        (canonicalResidualCertificates hx hy C).right) ∈
      residualVertexPrimeCells
        L c.1.1 c.1.2
        (canonicalResidualCertificates hx hy C).prime
        (pairChannelError x y c.1.1 c.1.2) := by
  rw [mem_residualVertexPrimeCells]
  constructor
  · simpa only [residualVertexExpression_apply] using
      canonicalResidualCertificates_residualExpression_ne_of_choice
        hx hy c hchoice hm C
  · exact
      canonicalResidualCertificates_prime_dvd_residualVertexExpression
        (a := c.1.1) (b := c.1.2) hx hy C

/--
The prime of every active canonical residual certificate lies in the finite
dyadic range used to define `residualPrimeMass`.
-/
theorem canonicalResidualCertificates_prime_mem_residualPrimeRange_of_choice
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2))
    (C :
      {C : (largePrimeGraph x y L).ConnectedComponent //
        C ∈ canonicalResidualComponents A x y L}) :
    (canonicalResidualCertificates hx hy C).prime ∈
      ResidualChannelLemmaSevenTwo.residualPrimeRange
        L c.1.1 c.1.2 := by
  let cert := canonicalResidualCertificates hx hy C
  have hvertex :
      (cert.left, cert.right) ∈
        residualVertexPrimeCells
          L c.1.1 c.1.2 cert.prime
          (pairChannelError x y c.1.1 c.1.2) := by
    simpa only [cert] using
      canonicalResidualCertificates_mem_residualVertexPrimeCells_of_choice
        hx hy c hchoice hm C
  have hoffsets :
      cert.offsetCell ∈
        residualPrimeCells
          L c.1.1 c.1.2 cert.prime
          (pairChannelError x y c.1.1 c.1.2) := by
    simpa only [ComponentCertificate.offsetCell, cert] using
      mem_residualVertexPrimeCells_iff_offsets_mem.mp hvertex
  have hmCard :
      2 ≤
        (channelCells L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2)).card := by
    simpa only [channelUnitCount_eq_card_channelCells] using hm
  exact
    ResidualChannelLemmaSevenTwo.mem_residualPrimeRange_of_nonempty
      (candidate_fst_pos c) (candidate_snd_pos c) (candidate_coprime c)
      hmCard cert.prime_large.1 cert.prime_large.2
      ⟨cert.offsetCell, hoffsets⟩

end

end CanonicalResidualComponents
end PaperC
