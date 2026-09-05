import PaperCV282.ProfileMonomials
import PaperCV282.ResidualSectorMass

/-!
# Arithmetic-independent assembly of the displayed sector table

The exact eight-sector mass identity is already proved. This module
records the numerical consequence if the remaining sector bounds are
supplied. Those bounds are explicit premises, not axioms or established
arithmetic conclusions. In particular this is not yet Theorem 3.1.
-/

namespace PaperC.V282.ProfileAssembly

open ProfileMonomials ResidualSectorMass PropositionSixteenOne
open MacroscopicGeometry MacroscopicRelationProfile
open scoped BigOperators

noncomputable section

/-- The eight uncapped rows in the displayed assembly table, in manuscript order. -/
def sectorEnvelope (M Q : ℝ) (i : Fin 8) : ℝ :=
  ![M ^ (3 / (2 : ℝ)) + M * Q ^ (1 / (2 : ℝ)),
    M ^ (3 / (2 : ℝ)) + M * Q ^ (1 / (2 : ℝ)) + M * Q ^ (1 / (3 : ℝ)),
    M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)),
    0,
    M * Q ^ (2 / (3 : ℝ)),
    M ^ (1 / (2 : ℝ)) * Q,
    M * Q ^ (2 / (3 : ℝ)),
    M ^ (2 / (3 : ℝ)) * Q + M ^ (3 / (4 : ℝ)) * Q ^ (2 / (3 : ℝ))] i

/-- All row envelopes are nonnegative on the positive scale domain. -/
theorem sectorEnvelope_nonneg {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 ≤ Q) (i : Fin 8) :
    0 ≤ sectorEnvelope M Q i := by
  fin_cases i <;> norm_num [sectorEnvelope] <;> positivity

/-- Exact expansion of the eight rows, with no suppressed multiplicities. -/
theorem sum_sectorEnvelope (M Q : ℝ) :
    (∑ i : Fin 8, sectorEnvelope M Q i) =
      2 * M ^ (3 / (2 : ℝ)) + 2 * M * Q ^ (1 / (2 : ℝ)) + M * Q ^ (1 / (3 : ℝ)) +
      M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) + 2 * M * Q ^ (2 / (3 : ℝ)) +
      M ^ (1 / (2 : ℝ)) * Q + M ^ (2 / (3 : ℝ)) * Q +
      M ^ (3 / (4 : ℝ)) * Q ^ (2 / (3 : ℝ)) := by
  simp [sectorEnvelope, Fin.sum_univ_succ]
  ring

/-- The rational part and all eight rows are bounded by one common raw profile. -/
theorem rational_add_sectorEnvelopes_le_eight_rawProfile
    {M Q : ℝ} (hM : 1 ≤ M) (hQ : 1 ≤ Q) :
    M * Q ^ (1 / (2 : ℝ)) + M * Q ^ (1 / (3 : ℝ)) +
      (∑ i : Fin 8, sectorEnvelope M Q i) ≤ 8 * rawProfile M Q := by
  have hMzero : 0 ≤ M := by linarith
  have hQzero : 0 ≤ Q := by linarith
  have hrational := rational_monomials_le_two_moderate hMzero hQ
  have hhalf : M * Q ^ (1 / (2 : ℝ)) ≤ M * Q ^ (2 / (3 : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)) hMzero
  have hhost := host_monomial_le_shallow hMzero hQ
  have hdefect := defects_monomial_le_terminal hM hQzero
  have hlast := exceptional_terminal_le_moderate hM hQzero
  have hfirstNonneg : 0 ≤ M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) := by positivity
  have hthirdNonneg : 0 ≤ M ^ (2 / (3 : ℝ)) * Q := by positivity
  rw [sum_sectorEnvelope]
  unfold rawProfile
  nlinarith

/-- Finite table assembly, with the actual interval sector estimates explicitly supplied. -/
theorem R2kappa_le_rawProfile_of_sector_bounds
    {N M A L : ℕ} (hN : 2 ≤ N) {E : ℝ} (hE : 0 ≤ E) (hM : 1 ≤ M)
    (hrational : systematicMass A N M L ≤
      E * ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
        (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))))
    (hsectors : ∀ i : Fin 8, sectorMass A i N M L ≤
      E * sectorEnvelope M ((2 : ℝ) ^ (L + 1)) i) :
    R2κ N M L ≤ 8 * E * rawProfile M ((2 : ℝ) ^ (L + 1)) := by
  rw [R2kappa_eq_systematic_add_sectors (A := A) hN]
  have hsum : (∑ i : Fin 8, sectorMass A i N M L) ≤
      E * ∑ i : Fin 8, sectorEnvelope M ((2 : ℝ) ^ (L + 1)) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hsectors i
  have htable := rational_add_sectorEnvelopes_le_eight_rawProfile
    (M := (M : ℝ)) (Q := (2 : ℝ) ^ (L + 1))
    (by exact_mod_cast hM) (by exact_mod_cast (Nat.one_le_pow (L + 1) 2 (by omega)))
  calc
    _ ≤ E * ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
        (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))) +
        E * ∑ i : Fin 8, sectorEnvelope M ((2 : ℝ) ^ (L + 1)) i := add_le_add hrational hsum
    _ = E * ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
        (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ)) +
        ∑ i : Fin 8, sectorEnvelope M ((2 : ℝ) ^ (L + 1)) i) := by ring
    _ ≤ E * (8 * rawProfile M ((2 : ℝ) ^ (L + 1))) := mul_le_mul_of_nonneg_left htable hE
    _ = _ := by ring

/-- The same explicit premises give the interpolated two-term profile. -/
theorem R2kappa_le_coarseProfile_of_sector_bounds
    {N M A L : ℕ} (hN : 2 ≤ N) {E : ℝ} (hE : 0 ≤ E) (hM : 1 ≤ M)
    (hrational : systematicMass A N M L ≤
      E * ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
        (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))))
    (hsectors : ∀ i : Fin 8, sectorMass A i N M L ≤
      E * sectorEnvelope M ((2 : ℝ) ^ (L + 1)) i) :
    R2κ N M L ≤ 16 * E * coarseProfile M ((2 : ℝ) ^ (L + 1)) := by
  have hraw := R2kappa_le_rawProfile_of_sector_bounds hN hE hM hrational hsectors
  have hinterp := rawProfile_le_two_coarseProfile
    (M := (M : ℝ))
    (by exact_mod_cast (show 0 < M by omega)) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  calc
    _ ≤ _ := hraw
    _ ≤ (8 * E) * (2 * coarseProfile M ((2 : ℝ) ^ (L + 1))) :=
      mul_le_mul_of_nonneg_left hinterp (by positivity)
    _ = _ := by ring

end
end PaperC.V282.ProfileAssembly
