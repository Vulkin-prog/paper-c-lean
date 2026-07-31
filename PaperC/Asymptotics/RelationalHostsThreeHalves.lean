import PaperC.Analysis.RelationalHostBound
import PaperC.Asymptotics.ExpSqrtLog
import PaperC.Asymptotics.ThreeHalvesPower
import PaperC.Probability.CriticalRunWindow

/-!
# The relational-host estimate is `N^(3/2+o(1))`

This module closes the asymptotic part of Lemma 4.2.  Its admissibility
predicate records all three hypotheses used by the finite estimate:

* `N ≥ 2`;
* `L ≤ N`;
* `L + 1 ≤ C log N`.

The explicit finite factor left after extracting `N * √N` is uniformly
subpolynomial in `N`.
-/

namespace PaperC
namespace RelationalHostsThreeHalves

/-- Admissible pairs for the relational-host estimate of Lemma 4.2. -/
def Admissible (C : ℝ) (N L : ℕ) : Prop :=
  2 ≤ N ∧ L ≤ N ∧
    ((L + 1 : ℕ) : ℝ) ≤ C * Real.log N

/--
The factor left after writing the finite estimate as
`N * √N * relationalHostResidual`.
-/
noncomputable def relationalHostResidual (_N L : ℕ) : ℝ :=
  (8 * Real.sqrt 3) *
    (((L : ℝ) + 1) *
      Real.exp (4 * Real.sqrt ((L + 1 : ℕ) : ℝ)))

/-- The residual factor in the finite relational-host bound is `N^{o(1)}`. -/
theorem relationalHostResidual_uniformSubpolynomial
    (C : ℝ) (hC : 0 ≤ C) :
    UniformSubpolynomialOn (Admissible C)
      relationalHostResidual := by
  have hlinear :
      UniformSubpolynomialOn (Admissible C)
        (fun _ L => (L + 1 : ℝ)) := by
    apply ExpSqrtLog.uniformSubpolynomialOn_linear_log_add_one
      (Admissible C) (fun _ L => L) C hC
    intro N L hNL
    have hLcast :
        (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ L
    exact hLcast.trans hNL.2.2
  have hexponential :
      UniformSubpolynomialOn (Admissible C)
        (fun _ L =>
          Real.exp
            (4 * Real.sqrt ((L + 1 : ℕ) : ℝ))) := by
    exact
      ExpSqrtLog.uniformSubpolynomialOn_exp_sqrt_of_le_log
        (Admissible C) (fun _ L => L + 1) 4 C (by norm_num) hC
        (fun N L hNL ↦ hNL.2.2)
  have hproduct :
      UniformSubpolynomialOn (Admissible C)
        (fun N L =>
          (L + 1 : ℝ) *
            Real.exp
              (4 * Real.sqrt ((L + 1 : ℕ) : ℝ))) :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      hlinear hexponential
  unfold relationalHostResidual
  exact
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      (8 * Real.sqrt 3) hproduct

/--
Quantified conclusion of Lemma 4.2:

`# relationalHosts(N,L) ≤ N^(3/2+o_C(1))`

uniformly over the explicitly admissible range.
-/
theorem card_relationalHosts_uniformThreeHalves
    (C : ℝ) (hC : 0 ≤ C) :
    UniformThreeHalvesSubpolynomialOn (Admissible C)
      (fun N L =>
        ((RelationalHosts.relationalHosts N L).card : ℝ)) := by
  apply UniformThreeHalves.of_linear_sqrt_mul_subpolynomial
    (relationalHostResidual_uniformSubpolynomial C hC)
  refine ⟨2, ?_⟩
  intro N hN L hNL
  have hfinite :=
    RelationalHostBound.card_relationalHosts_cast_le_exp_bound
      hNL.1 hNL.2.1
  have hcardNonneg :
      0 ≤ ((RelationalHosts.relationalHosts N L).card : ℝ) := by
    positivity
  rw [abs_of_nonneg hcardNonneg]
  refine hfinite.trans_eq ?_
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hresidualNonneg :
      0 ≤ relationalHostResidual N L := by
    unfold relationalHostResidual
    positivity
  rw [abs_of_nonneg hresidualNonneg]
  unfold relationalHostResidual
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  ring

/--
Literal run-length-window form of Lemma 4.2.  The constants and thresholds
are uniform for `|L - log₂ N| ≤ C`.
-/
theorem card_relationalHosts_uniformThreeHalves_inRunLengthWindow
    {C : ℝ} (hC : 0 ≤ C) :
    UniformThreeHalvesSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ((RelationalHosts.relationalHosts N L).card : ℝ)) := by
  have hupperNonneg : 0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  have hcore :=
    card_relationalHosts_uniformThreeHalves
      CriticalRunWindow.upperConstant hupperNonneg
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nlength, hlength⟩ :=
    ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually
      CriticalRunWindow.upperConstant hupperNonneg 1 (by omega)
  intro k hk
  obtain ⟨Ncore, hNcore⟩ := hcore k hk
  refine ⟨max Nwindow (max Nlength (max Ncore 2)), ?_⟩
  intro N hN L hrun
  have hNwindow : Nwindow ≤ N :=
    (le_max_left Nwindow (max Nlength (max Ncore 2))).trans hN
  have hNrest : max Nlength (max Ncore 2) ≤ N :=
    (le_max_right Nwindow (max Nlength (max Ncore 2))).trans hN
  have hNlength : Nlength ≤ N :=
    (le_max_left Nlength (max Ncore 2)).trans hNrest
  have hNcoreThreshold : Ncore ≤ N :=
    (le_max_left Ncore 2).trans
      ((le_max_right Nlength (max Ncore 2)).trans hNrest)
  have hNtwo : 2 ≤ N :=
    (le_max_right Ncore 2).trans
      ((le_max_right Nlength (max Ncore 2)).trans hNrest)
  have hfirstMoment :=
    hwindow N hNwindow L hrun
  have hcritical := hfirstMoment.1
  have hLplusTwoReal :
      (((L + 1) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    simpa using
      hlength N hNlength (L + 1) hcritical.2.2.2
  have hLleN : L ≤ N := by
    have hLplusTwo : (L + 1) + 1 ≤ N := by
      exact_mod_cast hLplusTwoReal
    omega
  exact hNcore N hNcoreThreshold L
    ⟨hNtwo, hLleN, hcritical.2.2.2⟩

end RelationalHostsThreeHalves
end PaperC
