import PaperC.Affine.System
import Mathlib.Data.Rat.Cast.Order

/-!
# Uniform probabilities of finite affine systems

The probability model used in the paper is uniform on a finite vector space
over `𝔽₂`.  This module turns the cardinality theorem for affine fibers into an
exact rational probability formula.  It is a coordinate-free version of the
counting part of Lemma 2.1.
-/

namespace PaperC.Affine

variable {V W : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V]
variable [AddCommGroup W] [Module 𝔽₂ W]

noncomputable section

variable [Fintype V]

local instance probabilitySolutionFintype (A : V →ₗ[𝔽₂] W) (b : W) :
    Fintype (Solution A b) :=
  Fintype.ofFinite _

local instance probabilityCompatibleDecidable (A : V →ₗ[𝔽₂] W) (b : W) :
    Decidable (Compatible A b) :=
  Classical.propDecidable _

/-- Uniform probability of the affine event `A x = b`, as an exact rational
number. -/
def uniformSolutionProbability (A : V →ₗ[𝔽₂] W) (b : W) : ℚ :=
  (Fintype.card (Solution A b) : ℚ) / (Fintype.card V : ℚ)

/-- The cardinality of a finite `𝔽₂`-vector space is the corresponding power
of two. -/
theorem card_eq_two_pow_finrank :
    Fintype.card V = 2 ^ Module.finrank 𝔽₂ V := by
  calc
    Fintype.card V =
        Fintype.card 𝔽₂ ^ Module.finrank 𝔽₂ V :=
      Module.card_eq_pow_finrank (K := 𝔽₂) (V := V)
    _ = 2 ^ Module.finrank 𝔽₂ V := by rw [ZMod.card]

/-- Exact uniform probability of a finite affine system.  Incompatibility
gives probability zero; otherwise the numerator is the size of the kernel. -/
theorem uniformSolutionProbability_eq_ite
    (A : V →ₗ[𝔽₂] W) (b : W) :
    uniformSolutionProbability A b =
      if Compatible A b then
        (2 ^ Module.finrank 𝔽₂ (LinearMap.ker A) : ℚ) /
          (2 ^ Module.finrank 𝔽₂ V : ℚ)
      else
        0 := by
  classical
  unfold uniformSolutionProbability
  rw [card_solution_eq_ite, card_eq_two_pow_finrank (V := V)]
  split_ifs <;> simp_all

/-- Compatible case of the exact affine probability formula. -/
theorem uniformSolutionProbability_of_compatible
    (A : V →ₗ[𝔽₂] W) (b : W) (h : Compatible A b) :
    uniformSolutionProbability A b =
      (2 ^ Module.finrank 𝔽₂ (LinearMap.ker A) : ℚ) /
        (2 ^ Module.finrank 𝔽₂ V : ℚ) := by
  rw [uniformSolutionProbability_eq_ite, if_pos h]

/-- Incompatible affine systems have probability zero. -/
theorem uniformSolutionProbability_of_not_compatible
    (A : V →ₗ[𝔽₂] W) (b : W) (h : ¬Compatible A b) :
    uniformSolutionProbability A b = 0 := by
  rw [uniformSolutionProbability_eq_ite, if_neg h]

end

end PaperC.Affine
