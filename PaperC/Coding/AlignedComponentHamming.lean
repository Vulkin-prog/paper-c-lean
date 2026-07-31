import PaperC.Coding.AlignedComponentCode

/-!
# The short component selection in Section 8

This module assembles the rank, Hamming and arithmetic parts of the
component matrix `Φ`.  Under the explicit finite Hamming threshold it
produces a nonempty selection of at most `2t` components, with even left and
right vertex counts and square total label product.
-/

namespace PaperC
namespace AlignedComponentHamming

open scoped BigOperators
open AlignedComponentCode
open ComponentProductParity
open LargePrimeComponents
open LargePrimeGraph

noncomputable section

/--
Finite short-word conclusion for any enumerated family of unpinned
large-prime components.
-/
theorem exists_short_kernelWord_parity_package
    {m x y L t : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ∀ i, ¬IsPinnedComponent x y L (component i))
    (ht : 1 ≤ t)
    (hmt : 2 * t ≤ m)
    (hrows : PrimesUpTo.count (L + 1) + 2 ≤ m)
    (hlarge :
      2 * t *
          2 ^ ((PrimesUpTo.count (L + 1) + 2) / t + 1) ≤
        m) :
    ∃ word : Fin m → F₂,
      word ≠ 0 ∧
      word ∈ LinearMap.ker (componentCodeMap component) ∧
      hammingNorm word ≤ 2 * t ∧
      Even
        (∑ i ∈ HammingBound.wordSupport word,
          componentLeftCount x y L (component i)) ∧
      Even
        (∑ i ∈ HammingBound.wordSupport word,
          componentRightCount x y L (component i)) ∧
      ∃ q : ℕ,
        ∏ i ∈ HammingBound.wordSupport word,
            componentVertexProduct x y L (component i) =
          q ^ 2 := by
  obtain ⟨word, hword0, hword, hweight⟩ :=
    TwoParityColumnCode.exists_nonzero_kernel_word_hammingNorm_le
      (fun i ↦ componentSmallParityColumn x y L (component i))
      (fun i ↦ (componentLeftCount x y L (component i) : F₂))
      (fun i ↦ (componentRightCount x y L (component i) : F₂))
      ht hmt hrows hlarge
  have hpackage :=
    kernelWord_parity_package hx hy component hfree word hword
  exact
    ⟨word, hword0, hword, hweight,
      hpackage.1, hpackage.2.1, hpackage.2.2⟩

end

end AlignedComponentHamming
end PaperC
