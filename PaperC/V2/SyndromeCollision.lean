import PaperC.Coding.HammingBound

/-!
# Paper C v2: the elementary syndrome-collision bound

The v2 manuscript replaces two sphere-packing presentations by the direct
subset-syndrome argument. A linear syndrome map is injective on words of
weight at most `t` when its kernel has no nonzero word of weight at most
`2 * t`; consequently the number of such words is at most `2 ^ r`.

This file proves that statement directly. It does not use the Hamming-ball
bound, although it reuses the already formalized support/volume dictionary.
-/

namespace PaperC
namespace V2
namespace SyndromeCollision

open scoped BigOperators
open HammingBound

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

/-- The syndrome map on coordinate subsets induced by a binary linear map. -/
def subsetSyndrome {m r : ℕ}
    (φ : BinaryWord m →ₗ[F₂] BinaryWord r)
    (s : Finset (Fin m)) : BinaryWord r :=
  φ (wordOfSupport s)

/--
If the kernel contains no nonzero word of weight at most `2t`, then distinct
subsets of cardinality at most `t` have distinct syndromes.
-/
theorem subsetSyndrome_injectiveOn_smallSupports
    {m r t : ℕ}
    (φ : BinaryWord m →ₗ[F₂] BinaryWord r)
    (hshort : ∀ z : BinaryWord m,
      z ≠ 0 → hammingNorm z ≤ 2 * t → φ z ≠ 0) :
    Set.InjOn (subsetSyndrome φ) (smallSupports m t : Set (Finset (Fin m))) := by
  intro s hs u hu hsu
  have hsCard : s.card ≤ t := by
    simpa [smallSupports] using hs
  have huCard : u.card ≤ t := by
    simpa [smallSupports] using hu
  let x : BinaryWord m := wordOfSupport s
  let y : BinaryWord m := wordOfSupport u
  have hxNorm : hammingNorm x ≤ t := by
    rw [← card_wordSupport]
    simpa [x]
  have hyNorm : hammingNorm y ≤ t := by
    rw [← card_wordSupport]
    simpa [y]
  have hdist : hammingDist x y ≤ 2 * t := by
    calc
      hammingDist x y ≤ hammingDist x 0 + hammingDist 0 y :=
        hammingDist_triangle x 0 y
      _ = hammingNorm x + hammingNorm y := by simp
      _ ≤ 2 * t := by omega
  have hxy : x = y := by
    by_contra hxy
    let z : BinaryWord m := x - y
    have hzNe : z ≠ 0 := by
      dsimp only [z]
      exact sub_ne_zero.mpr hxy
    have hzNorm : hammingNorm z ≤ 2 * t := by
      have hnorm : hammingNorm (x - y) = hammingDist x y := by
        simpa [differenceSupport] using
          (hammingDist_eq_card_differenceSupport x y).symm
      simpa only [z, hnorm] using hdist
    have hφz : φ z = 0 := by
      dsimp only [z]
      rw [map_sub, sub_eq_zero]
      exact hsu
    exact (hshort z hzNe hzNorm) hφz
  have hsupports := congrArg wordSupport hxy
  simpa [x, y] using hsupports

/--
Numerical syndrome-collision bound:

`∑_{j≤t} choose m j ≤ 2^r`.
-/
theorem volume_le_two_pow
    {m r t : ℕ}
    (φ : BinaryWord m →ₗ[F₂] BinaryWord r)
    (hshort : ∀ z : BinaryWord m,
      z ≠ 0 → hammingNorm z ≤ 2 * t → φ z ≠ 0) :
    volume m t ≤ 2 ^ r := by
  classical
  let f : Finset (Fin m) → BinaryWord r := subsetSyndrome φ
  have hinj :
      Set.InjOn f (smallSupports m t : Set (Finset (Fin m))) := by
    simpa only [f] using
      subsetSyndrome_injectiveOn_smallSupports φ hshort
  calc
    volume m t = (smallSupports m t).card :=
      (card_smallSupports m t).symm
    _ = ((smallSupports m t).image f).card := by
      symm
      exact Finset.card_image_of_injOn hinj
    _ ≤ (Finset.univ : Finset (BinaryWord r)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ r := by
      simp [ZMod.card]

/-- Contrapositive form used when extracting a short relation. -/
theorem exists_short_kernel_word_of_two_pow_lt_volume
    {m r t : ℕ}
    (φ : BinaryWord m →ₗ[F₂] BinaryWord r)
    (hlarge : 2 ^ r < volume m t) :
    ∃ z : BinaryWord m, z ≠ 0 ∧ hammingNorm z ≤ 2 * t ∧ φ z = 0 := by
  by_contra hnone
  push Not at hnone
  have hshort : ∀ z : BinaryWord m,
      z ≠ 0 → hammingNorm z ≤ 2 * t → φ z ≠ 0 := by
    intro z hz hweight hzero
    exact hnone z hz hweight hzero
  have hbound := volume_le_two_pow φ hshort
  omega

end SyndromeCollision
end V2
end PaperC
