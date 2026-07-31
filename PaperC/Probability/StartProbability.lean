import PaperC.Affine.Probability
import PaperC.Affine.StartSystem

/-!
# Exact probability of a run start

This module identifies the finite-cylinder definition of a start probability
with the uniform probability of the affine start system.  Combining that
identification with affine fiber counting gives the exact compatible /
incompatible power-of-two formula.
-/

namespace PaperC

open Affine

noncomputable section

/--
For positive run length, the event counted by `startProbability` is exactly
the solution fiber of the affine start system.
-/
theorem startProbability_eq_uniformSolutionProbability
    (N L x : ℕ) (hL : 0 < L) :
    startProbability N L x =
      uniformSolutionProbability
        (startSystem (dyadicCutoff N L) x L) (startRhs L) := by
  classical
  unfold startProbability uniformEventProbability uniformSolutionProbability
  congr 1
  rw [Fintype.card_subtype]
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (startSystem_eq_startRhs_iff_startAt ω hL).symm

local instance startCompatibleDecidable (N L x : ℕ) :
    Decidable
      (Compatible (startSystem (dyadicCutoff N L) x L) (startRhs L)) :=
  Classical.propDecidable _

/--
Exact finite-cylinder probability of a start.  A compatible affine system has
probability equal to the quotient of the kernel size by the ambient sample
space size; an incompatible system has probability zero.
-/
theorem startProbability_eq_ite
    (N L x : ℕ) (hL : 0 < L) :
    startProbability N L x =
      if Compatible (startSystem (dyadicCutoff N L) x L) (startRhs L) then
        (2 ^ Module.finrank 𝔽₂
            (LinearMap.ker (startSystem (dyadicCutoff N L) x L)) : ℚ) /
          (2 ^ Module.finrank 𝔽₂ (DyadicSample N L) : ℚ)
      else
        0 := by
  rw [startProbability_eq_uniformSolutionProbability N L x hL]
  exact uniformSolutionProbability_eq_ite
    (startSystem (dyadicCutoff N L) x L) (startRhs L)

end

end PaperC
