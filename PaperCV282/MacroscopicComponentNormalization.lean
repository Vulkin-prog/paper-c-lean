import PaperCV282.MacroscopicGeometry
import PaperC.Asymptotics.BoundedRatioComponentNormalization

/-!
# Polynomial-height normalization of actual macroscopic components

The normalized squarefree coefficient is exactly `sf(d * P_I(x))`.
For a component with at most `K` vertices, all original products are at
most `M^(2K)` and the normalized coefficient is at most `M^(4K)`.
Both square parameters are at most `M^K`. These are finite consequences
of the actual component square class and the literal cutoff `M+L`.
No integral-point or Pell estimate is assumed.
-/

namespace PaperC.V282.MacroscopicComponentNormalization

open Affine PropositionSixteenOne BoundedRatioComponentNormalization
open ComponentNormalization CanonicalResidualComponents ComponentProductParity
open LargePrimeGraph LargePrimeComponents MacroscopicGeometry

noncomputable section

instance instDecidableComponentAdj (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj := Classical.decRel _

/-- The literal cylinder cutoff has polynomial height in the ambient scale. -/
theorem cutoff_pow_le_polynomial {M L : ℕ} (hM : 2 ≤ M) (hL : L ≤ M) (K : ℕ) :
    boundedRatioCutoff M L ^ K ≤ M ^ (2 * K) := by
  have hcut : boundedRatioCutoff M L ≤ M ^ 2 := by
    unfold boundedRatioCutoff
    nlinarith
  calc
    _ ≤ (M ^ 2) ^ K := Nat.pow_le_pow_left hcut K
    _ = M ^ (2 * K) := (pow_mul _ _ _).symm

/-- Canonical normalization and both square-parameter bounds follow from
a bound for the entire positive component product. -/
theorem canonical_normalization_with_polynomial_height
    {M K P Q d z : ℕ} (hP : 0 < P) (hQ : 0 < Q)
    (hd : 0 < d) (hz : 0 < z) (hdsquarefree : Squarefree d)
    (hequation : P * Q = d * z ^ 2) (hwhole : P * Q ≤ M ^ (2 * K)) :
    ∃ e v : ℕ,
      0 < e ∧ Squarefree e ∧ 0 < v ∧ Q = e * v ^ 2 ∧
      e = squarefreeKernel (d * P) ∧ e ∣ d * P ∧
      d ≤ M ^ (2 * K) ∧ P ≤ M ^ (2 * K) ∧ Q ≤ M ^ (2 * K) ∧
      e ≤ M ^ (4 * K) ∧ z ≤ M ^ K ∧ v ≤ M ^ K := by
  obtain ⟨e, v, he, hesquarefree, hv, hQeq, hecanonical, hediv, hele⟩ :=
    exists_normalized_right_factor hP hQ hd hz hdsquarefree hequation
  have hdBound : d ≤ M ^ (2 * K) := by
    calc
      d ≤ d * z ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
      _ = P * Q := hequation.symm
      _ ≤ _ := hwhole
  have hPBound : P ≤ M ^ (2 * K) := (Nat.le_mul_of_pos_right P hQ).trans hwhole
  have hQBound : Q ≤ M ^ (2 * K) := (Nat.le_mul_of_pos_left Q hP).trans hwhole
  have heBound : e ≤ M ^ (4 * K) := by
    calc
      _ ≤ d * P := hele
      _ ≤ M ^ (2 * K) * M ^ (2 * K) := Nat.mul_le_mul hdBound hPBound
      _ = M ^ (4 * K) := by rw [← pow_add]; congr 1; omega
  have hzSquare : z ^ 2 ≤ (M ^ K) ^ 2 := by
    calc
      z ^ 2 ≤ d * z ^ 2 := Nat.le_mul_of_pos_left _ hd
      _ = P * Q := hequation.symm
      _ ≤ M ^ (2 * K) := hwhole
      _ = (M ^ K) ^ 2 := by rw [← pow_mul]; congr 1; omega
  have hvSquare : v ^ 2 ≤ (M ^ K) ^ 2 := by
    calc
      v ^ 2 ≤ e * v ^ 2 := Nat.le_mul_of_pos_left _ he
      _ = Q := hQeq.symm
      _ ≤ M ^ (2 * K) := hQBound
      _ = (M ^ K) ^ 2 := by rw [← pow_mul]; congr 1; omega
  have hzBound : z ≤ M ^ K := (Nat.pow_le_pow_iff_left (by omega : 2 ≠ 0)).mp hzSquare
  have hvBound : v ≤ M ^ K := (Nat.pow_le_pow_iff_left (by omega : 2 ≠ 0)).mp hvSquare
  exact ⟨e, v, he, hesquarefree, hv, hQeq, hecanonical, hediv,
    hdBound, hPBound, hQBound, heBound, hzBound, hvBound⟩

/-- Lemma 3.15 with explicit polynomial bounds, for an actual canonical
residual component on the exact macroscopic pair domain. -/
theorem exists_macroscopic_component_normalization
    {M A L K : ℕ} {delta : ℝ} (hM : 2 ≤ M) (hdelta : 0 < delta) (hL : L ≤ M)
    (pair : SeparatedBoundedRatioPair ⌈(M : ℝ) ^ delta⌉₊ M L)
    {C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent}
    (hC : C ∈ canonicalResidualComponents A pair.1.1 pair.1.2 L)
    (hcard : Fintype.card C.supp ≤ K) :
    ∃ d z e v : ℕ,
      0 < d ∧ Squarefree d ∧ (∀ p : ℕ, p.Prime → p ∣ d → p ≤ L + 1) ∧
      0 < z ∧ 0 < e ∧ Squarefree e ∧ 0 < v ∧
      componentLeftProduct pair.1.1 pair.1.2 L C *
        componentRightProduct pair.1.1 pair.1.2 L C = d * z ^ 2 ∧
      componentRightProduct pair.1.1 pair.1.2 L C = e * v ^ 2 ∧
      e = squarefreeKernel (d * componentLeftProduct pair.1.1 pair.1.2 L C) ∧
      e ∣ d * componentLeftProduct pair.1.1 pair.1.2 L C ∧
      d ≤ M ^ (2 * K) ∧
      componentLeftProduct pair.1.1 pair.1.2 L C ≤ M ^ (2 * K) ∧
      componentRightProduct pair.1.1 pair.1.2 L C ≤ M ^ (2 * K) ∧
      e ≤ M ^ (4 * K) ∧ z ≤ M ^ K ∧ v ≤ M ^ K := by
  have hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊ := two_le_macroscopic_lowerEndpoint hM hdelta
  have hcoords := pair_coordinates_two_le hN pair
  obtain ⟨d, z, hd, hdsquarefree, hdsmooth, hz, hequation⟩ :=
    exists_component_square_class_equation hN pair hC
  have hcard' : (componentVertices pair.1.1 pair.1.2 L C).card ≤ K := by
    rwa [card_componentVertices]
  have hwhole : componentLeftProduct pair.1.1 pair.1.2 L C *
      componentRightProduct pair.1.1 pair.1.2 L C ≤ M ^ (2 * K) := by
    calc
      _ = componentVertexProduct pair.1.1 pair.1.2 L C :=
        (componentVertexProduct_eq_left_mul_right _ _ _ _).symm
      _ ≤ boundedRatioCutoff M L ^ K := componentVertexProduct_le_cutoff_pow hN pair C hcard'
      _ ≤ _ := cutoff_pow_le_polynomial hM hL K
  obtain ⟨e, v, he, hesquarefree, hv, hQeq, hecanonical, hediv,
      hdBound, hPBound, hQBound, heBound, hzBound, hvBound⟩ :=
    canonical_normalization_with_polynomial_height
      (componentLeftProduct_pos hcoords.1 C) (componentRightProduct_pos hcoords.2 C)
      hd hz hdsquarefree hequation hwhole
  exact ⟨d, z, e, v, hd, hdsquarefree, hdsmooth, hz, he, hesquarefree, hv,
    hequation, hQeq, hecanonical, hediv, hdBound, hPBound, hQBound, heBound, hzBound, hvBound⟩

end
end PaperC.V282.MacroscopicComponentNormalization
