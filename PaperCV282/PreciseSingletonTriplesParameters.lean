import PaperC.Asymptotics.BoundedRatioTwoSingletonHosts

/-! # Canonical singleton parameters for arbitrary positive integer pairs

The construction uses the equation XY=dz² directly. No graph certificate,
separation, or ratio condition on X and Y is required.
-/
namespace PaperC.V282.PreciseSingletonTriplesParameters

open SingletonProductParametrization ComponentNormalization BoundedRatioTwoSingletonHosts
open DefectivePredicate LargeOddKernel

noncomputable section

/-- The canonical four parameters attached to the actual two integers. -/
def canonicalTuple (X Y d : ℕ) : SingletonParameterTuple :=
  (canonicalDPart X d, (canonicalCommonPart X d, (canonicalFirstRoot X, canonicalSecondRoot Y)))

theorem square_root_pos {X Y d z : ℕ} (hX : 0 < X) (hY : 0 < Y)
    (heq : X*Y=d*z^2) : 0 < z := by
  by_contra h
  have hz : z=0 := by omega
  rw [hz] at heq
  have hp := Nat.mul_pos hX hY
  simp only [zero_pow (by decide : 2≠0), mul_zero] at heq
  omega

/-- The class coefficient is automatically bounded by the square of the cylinder. -/
theorem coefficient_le_square {X Y d z T : ℕ} (hX : 0 < X) (hY : 0 < Y)
    (hXT : X ≤ T) (hYT : Y ≤ T) (heq : X*Y=d*z^2) : d ≤ T^2 := by
  have hz := square_root_pos hX hY heq
  have hdone : d ≤ d*z^2 := Nat.le_mul_of_pos_right d (pow_pos hz 2)
  have hp := Nat.mul_le_mul hXT hYT
  rw [← heq] at hdone
  simpa only [pow_two] using hdone.trans hp

/-- Both integers can be reconstructed from the canonical tuple and d. -/
theorem reconstruct {X Y d z : ℕ} (hX : 0 < X) (hY : 0 < Y) (hd : 0 < d)
    (hsq : Squarefree d) (heq : X*Y=d*z^2) :
    X = (canonicalTuple X Y d).1 * (canonicalTuple X Y d).2.1 *
      (canonicalTuple X Y d).2.2.1^2 ∧
    Y = (d/(canonicalTuple X Y d).1) * (canonicalTuple X Y d).2.1 *
      (canonicalTuple X Y d).2.2.2^2 :=
  canonical_factorizations hX hY hd (square_root_pos hX hY heq) hsq heq

/-- Literal membership in the finite parameter container, uniformly in X/Y. -/
theorem canonicalTuple_mem {X Y d z T : ℕ} (hX : 0 < X) (hY : 0 < Y)
    (hXT : X ≤ T) (hYT : Y ≤ T) (hd : 0 < d) (hsq : Squarefree d)
    (heq : X*Y=d*z^2) : canonicalTuple X Y d ∈ singletonParameterTuples d T := by
  have hf := reconstruct hX hY hd hsq heq
  have hepos := canonicalDPart_pos (X := X) hd
  have hcpos := canonicalCommonPart_pos (X := X) hd
  have hup : 0 < canonicalFirstRoot X :=
    Nat.pos_of_ne_zero (canonicalSquarePart_ne_zero hX.ne')
  have hvp : 0 < canonicalSecondRoot Y :=
    Nat.pos_of_ne_zero (canonicalSquarePart_ne_zero hY.ne')
  have heT := canonicalDPart_le (X := X) hd
  have hcT := (canonicalCommonPart_le_first (d := d) hX).trans hXT
  have huT := (canonicalFirstRoot_le_sqrt hX).trans (Nat.sqrt_le_sqrt hXT)
  have hvT := (canonicalSecondRoot_le_sqrt hY).trans (Nat.sqrt_le_sqrt hYT)
  rw [singletonParameterTuples, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hepos,heT⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hcpos,hcT⟩,
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hup,huT⟩,
          Finset.mem_Icc.mpr ⟨hvp,hvT⟩⟩⟩⟩
  · exact ⟨canonicalDPart_dvd_right X d, canonicalCommonPart_coprime hd,
      hf.1.symm.le.trans hXT, hf.2.symm.le.trans hYT⟩

/-- Injectivity uses the two reconstructed values and keeps the coefficient d. -/
theorem canonicalTuple_injective {X Y X' Y' d z z' : ℕ}
    (hX : 0 < X) (hY : 0 < Y) (hX' : 0 < X') (hY' : 0 < Y')
    (hd : 0 < d) (hsq : Squarefree d) (heq : X*Y=d*z^2) (heq' : X'*Y'=d*z'^2)
    (ht : canonicalTuple X Y d = canonicalTuple X' Y' d) : X=X' ∧ Y=Y' := by
  have h := reconstruct hX hY hd hsq heq
  have h' := reconstruct hX' hY' hd hsq heq'
  rw [ht] at h
  exact ⟨h.1.trans h'.1.symm, h.2.trans h'.2.symm⟩

end
end PaperC.V282.PreciseSingletonTriplesParameters
