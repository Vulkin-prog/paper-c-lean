import Mathlib.Analysis.MeanInequalities

/-!
# Numerical assembly of the three-term profile

These are inequalities between the explicit monomials, independent of
arithmetic population estimates. They record precisely the weighted
arithmetic-geometric mean step from (3.3) to (3.4), and the domination
of each row of the assembly table. They do not assert that an unproved
sector satisfies its proposed row.
-/

namespace PaperC.V282.ProfileMonomials

noncomputable section

/-- The three distinct monomials in the raw relation profile. -/
def rawProfile (M Q : ℝ) : ℝ :=
  M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) +
    M * Q ^ (2 / (3 : ℝ)) + M ^ (2 / (3 : ℝ)) * Q

/-- The two-term profile after interpolation, with the exponent 5/3 explicit. -/
def coarseProfile (M Q : ℝ) : ℝ := M ^ (5 / (3 : ℝ)) + M ^ (2 / (3 : ℝ)) * Q

/-- The capped three-term expression, keeping the common ceiling separate. -/
def cappedProfile (M Q T : ℝ) : ℝ :=
  M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) +
    M * Q ^ (2 / (3 : ℝ)) + M ^ (2 / (3 : ℝ)) * min T Q

theorem rawProfile_nonneg {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 ≤ Q) :
    0 ≤ rawProfile M Q := by unfold rawProfile; positivity

theorem coarseProfile_nonneg {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 ≤ Q) :
    0 ≤ coarseProfile M Q := by unfold coarseProfile; positivity

theorem cappedProfile_nonneg {M Q T : ℝ}
    (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hT : 0 ≤ T) : 0 ≤ cappedProfile M Q T := by
  unfold cappedProfile
  positivity

/-- The first monomial is the displayed weighted geometric mean. -/
theorem shallow_monomial_eq_geometric_mean {M Q : ℝ} (hM : 0 < M) (hQ : 0 ≤ Q) :
    M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) =
      (M ^ (5 / (3 : ℝ))) ^ (5 / (6 : ℝ)) *
        (M ^ (2 / (3 : ℝ)) * Q) ^ (1 / (6 : ℝ)) := by
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ M ^ (2 / (3 : ℝ))) hQ]
  rw [← Real.rpow_mul hM.le, ← Real.rpow_mul hM.le, ← mul_assoc, ← Real.rpow_add hM]
  norm_num

/-- The middle monomial is the other weighted geometric mean. -/
theorem moderate_monomial_eq_geometric_mean {M Q : ℝ} (hM : 0 < M) (hQ : 0 ≤ Q) :
    M * Q ^ (2 / (3 : ℝ)) =
      (M ^ (5 / (3 : ℝ))) ^ (1 / (3 : ℝ)) *
        (M ^ (2 / (3 : ℝ)) * Q) ^ (2 / (3 : ℝ)) := by
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ M ^ (2 / (3 : ℝ))) hQ]
  rw [← Real.rpow_mul hM.le, ← Real.rpow_mul hM.le, ← mul_assoc, ← Real.rpow_add hM]
  norm_num

/-- The exact coefficients in the first arithmetic-geometric mean bound. -/
theorem shallow_monomial_le_weighted_sum {M Q : ℝ} (hM : 0 < M) (hQ : 0 ≤ Q) :
    M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) ≤
      (5 / (6 : ℝ)) * M ^ (5 / (3 : ℝ)) +
        (1 / (6 : ℝ)) * (M ^ (2 / (3 : ℝ)) * Q) := by
  rw [shallow_monomial_eq_geometric_mean hM hQ]
  exact Real.geom_mean_le_arith_mean2_weighted (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by norm_num)

/-- The exact coefficients in the second arithmetic-geometric mean bound. -/
theorem moderate_monomial_le_weighted_sum {M Q : ℝ} (hM : 0 < M) (hQ : 0 ≤ Q) :
    M * Q ^ (2 / (3 : ℝ)) ≤
      (1 / (3 : ℝ)) * M ^ (5 / (3 : ℝ)) +
        (2 / (3 : ℝ)) * (M ^ (2 / (3 : ℝ)) * Q) := by
  rw [moderate_monomial_eq_geometric_mean hM hQ]
  exact Real.geom_mean_le_arith_mean2_weighted (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by norm_num)

/-- The interpolation step of Theorem 3.1, with an explicit uniform constant. -/
theorem rawProfile_le_two_coarseProfile {M Q : ℝ} (hM : 0 < M) (hQ : 0 ≤ Q) :
    rawProfile M Q ≤ 2 * coarseProfile M Q := by
  have hfirst := shallow_monomial_le_weighted_sum hM hQ
  have hsecond := moderate_monomial_le_weighted_sum hM hQ
  have hnonnegA : 0 ≤ M ^ (5 / (3 : ℝ)) := by positivity
  have hnonnegB : 0 ≤ M ^ (2 / (3 : ℝ)) * Q := by positivity
  unfold rawProfile coarseProfile
  linarith

/-- The cap acts monotonically in its ceiling. -/
theorem cappedProfile_mono_cap {M Q S T : ℝ} (hM : 0 ≤ M) (hST : S ≤ T) :
    cappedProfile M Q S ≤ cappedProfile M Q T := by
  unfold cappedProfile
  gcongr

/-- The capped expression is always bounded by the uncapped expression. -/
theorem cappedProfile_le_rawProfile {M Q T : ℝ} (hM : 0 ≤ M) :
    cappedProfile M Q T ≤ rawProfile M Q := by
  unfold cappedProfile rawProfile
  gcongr
  exact min_le_right _ _

/-- Once the ceiling reaches the word space, the two expressions agree exactly. -/
theorem cappedProfile_eq_rawProfile_of_word_le_cap {M Q T : ℝ} (hQT : Q ≤ T) :
    cappedProfile M Q T = rawProfile M Q := by simp [cappedProfile, rawProfile, min_eq_right hQT]

/-- The sparse-host correction fits into the first monomial. -/
theorem host_monomial_le_shallow {M Q : ℝ} (hM : 0 ≤ M) (hQ : 1 ≤ Q) :
    M ^ (3 / (2 : ℝ)) ≤ M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) := by
  exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hQ (by norm_num))

/-- Both rational height populations fit into the middle monomial. -/
theorem rational_monomials_le_two_moderate {M Q : ℝ} (hM : 0 ≤ M) (hQ : 1 ≤ Q) :
    M * Q ^ (1 / (2 : ℝ)) + M * Q ^ (1 / (3 : ℝ)) ≤
      2 * (M * Q ^ (2 / (3 : ℝ))) := by
  have hhalf := Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : (1 / (2 : ℝ)) ≤ 2 / 3)
  have hthird := Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : (1 / (3 : ℝ)) ≤ 2 / 3)
  nlinarith

/-- The many-defect monomial is absorbed by the terminal main term. -/
theorem defects_monomial_le_terminal {M Q : ℝ} (hM : 1 ≤ M) (hQ : 0 ≤ Q) :
    M ^ (1 / (2 : ℝ)) * Q ≤ M ^ (2 / (3 : ℝ)) * Q := by
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hM (by norm_num)) hQ

/-- The exceptional terminal stratum fits into the middle monomial. -/
theorem exceptional_terminal_le_moderate {M Q : ℝ} (hM : 1 ≤ M) (hQ : 0 ≤ Q) :
    M ^ (3 / (4 : ℝ)) * Q ^ (2 / (3 : ℝ)) ≤ M * Q ^ (2 / (3 : ℝ)) := by
  have hp : M ^ (3 / (4 : ℝ)) ≤ M := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hM (by norm_num : (3 / (4 : ℝ)) ≤ 1)
  exact mul_le_mul_of_nonneg_right hp (by positivity)

end
end PaperC.V282.ProfileMonomials
