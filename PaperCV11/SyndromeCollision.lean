import PaperC.Coding.HammingBound

/-!
# Paper C v1.1: the elementary syndrome-collision bound

The v1.1 manuscript uses the direct subset-syndrome argument. A linear
syndrome map is injective on words of weight at most `t` when its kernel has
no nonzero word of weight at most `2 * t`; consequently the number of such
words is at most `2 ^ r`.

This file proves that statement directly. It does not use sphere packing as a
black box, although it reuses the already formalized Hamming-ball volume.
-/

namespace PaperC
namespace V11
namespace SyndromeCollision

open HammingBound

abbrev BinaryWord (n : ℕ) := Fin n → ZMod 2

/-- The syndrome map attached to a binary linear map. -/
def syndromeMap {m r : ℕ}
    (φ : BinaryWord m →ₗ[ZMod 2] BinaryWord r)
    (x : BinaryWord m) : BinaryWord r :=
  φ x

/-- Low-weight words, represented as the Hamming ball about zero. -/
def lowWeightWords (m t : ℕ) : Finset (BinaryWord m) :=
  ball (0 : BinaryWord m) t

@[simp]
theorem mem_lowWeightWords {m t : ℕ} {x : BinaryWord m} :
    x ∈ lowWeightWords m t ↔ hammingNorm x ≤ t := by
  simp [lowWeightWords]

/-- The cardinality of the low-weight words is the binary Hamming volume. -/
theorem card_lowWeightWords (m t : ℕ) :
    (lowWeightWords m t).card = volume m t := by
  simpa [lowWeightWords] using
    (card_ball (n := m) (t := t) (0 : BinaryWord m))

/--
If no nonzero kernel word has weight at most `2t`, then syndromes are
injective on the low-weight words.
-/
theorem syndrome_injective_on_lowWeight
    {m r t : ℕ}
    (φ : BinaryWord m →ₗ[ZMod 2] BinaryWord r)
    (hshort : ∀ z : BinaryWord m,
      z ≠ 0 → hammingNorm z ≤ 2 * t → φ z ≠ 0) :
    Set.InjOn φ {x | hammingNorm x ≤ t} := by
  intro x hx y hy hxy
  by_contra hne
  have hdiff_ne : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hdiff_weight : hammingNorm (x - y) ≤ 2 * t := by
    calc
      hammingNorm (x - y) = hammingDist x y := by
        simpa [differenceSupport] using
          (hammingDist_eq_card_differenceSupport x y).symm
      _ ≤ hammingDist x (0 : BinaryWord m) +
          hammingDist (0 : BinaryWord m) y :=
        hammingDist_triangle x 0 y
      _ = hammingNorm x + hammingNorm y := by simp
      _ ≤ t + t := Nat.add_le_add hx hy
      _ = 2 * t := by omega
  have hkernel : φ (x - y) = 0 := by
    simp [map_sub, hxy]
  exact (hshort (x - y) hdiff_ne hdiff_weight) hkernel

/-- The direct subset-syndrome packing inequality. -/
theorem volume_le_two_pow
    {m r t : ℕ}
    (φ : BinaryWord m →ₗ[ZMod 2] BinaryWord r)
    (hshort : ∀ z : BinaryWord m,
      z ≠ 0 → hammingNorm z ≤ 2 * t → φ z ≠ 0) :
    volume m t ≤ 2 ^ r := by
  classical
  rw [← card_lowWeightWords]
  have hinj : Set.InjOn φ (↑(lowWeightWords m t) : Set (BinaryWord m)) := by
    intro x hx y hy hxy
    exact syndrome_injective_on_lowWeight φ hshort
      (mem_lowWeightWords.mp hx) (mem_lowWeightWords.mp hy) hxy
  calc
    (lowWeightWords m t).card =
        ((lowWeightWords m t).image φ).card := by
      symm
      exact Finset.card_image_iff.mpr hinj
    _ ≤ (Finset.univ : Finset (BinaryWord r)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ r := by
      simp [ZMod.card]

/-- Contrapositive form used when extracting a short relation. -/
theorem exists_short_kernel_word_of_two_pow_lt_volume
    {m r t : ℕ}
    (φ : BinaryWord m →ₗ[ZMod 2] BinaryWord r)
    (hlarge : 2 ^ r < volume m t) :
    ∃ z : BinaryWord m, z ≠ 0 ∧ hammingNorm z ≤ 2 * t ∧ φ z = 0 := by
  by_contra hnone
  push Not at hnone
  have hshort : ∀ z : BinaryWord m,
      z ≠ 0 → hammingNorm z ≤ 2 * t → φ z ≠ 0 := by
    intro z hz hweight hzero
    exact hnone z hz hweight hzero
  exact (not_le_of_gt hlarge) (volume_le_two_pow φ hshort)

end SyndromeCollision
end V11
end PaperC
