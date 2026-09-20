import PaperCPrel8.PalmDeficit
import PaperCV282.SteinFiniteExpectation

/-! # The target-sign deficit bound for any actual finite probability law

The variance here is computed from the law of R. Identifying it with the
nonconstant Walsh coefficient energy is a separate algebraic step.
-/
namespace PaperC.Prel8.PalmTargetSignBound
open PaperC.IndependentThinning PaperC.ArratiaGoldsteinGordonInput PaperC.V282.SteinFiniteExpectation
open PaperC.Prel8.PalmDeficit
noncomputable section
variable {Ω : Type*} [Fintype Ω]

/-- Cauchy--Schwarz for a real observable, derived from its nonnegative squared deviation. -/
theorem mean_abs_le_sqrt (mu : FinitePMF Ω) (X : Ω → ℝ) :
    finitePMFExpectation mu (fun z => |X z|) ≤ Real.sqrt (finitePMFExpectation mu (fun z => (X z)^2)) := by
  let a := finitePMFExpectation mu (fun z => |X z|)
  have ha : 0 ≤ a := expectation_nonneg mu (fun z => abs_nonneg _)
  have hv := expectation_nonneg mu (f := fun z => (|X z|-a)^2) (fun z => sq_nonneg _)
  have he : finitePMFExpectation mu (fun z => (|X z|-a)^2)=
      finitePMFExpectation mu (fun z => (X z)^2)-a^2 := by
    have hpoint (z : Ω) : (|X z|-a)^2=(X z)^2-2*a*|X z|+a^2 := by rw [sub_sq,sq_abs]; ring
    simp_rw [hpoint]
    rw [expectation_add,expectation_sub,expectation_const_mul,expectation_const]
    change _-2*a*a+a^2=_
    ring
  rw [he] at hv
  exact (Real.le_sqrt ha (expectation_nonneg mu (fun z => sq_nonneg _))).mpr (by linarith)

/-- The expected centered negative part is half its mean absolute deviation. -/
theorem centered_deficit_identity (mu : FinitePMF Ω) (R : Ω → ℝ) :
    finitePMFExpectation mu (fun z => max (finitePMFExpectation mu R-R z) 0)=
      finitePMFExpectation mu (fun z => |R z-finitePMFExpectation mu R|)/2 := by
  simp_rw [positive_part_identity,div_eq_mul_inv]
  rw [expectation_mul_const,expectation_add,expectation_sub,expectation_const]
  simp only [sub_self,add_zero,abs_sub_comm]

/-- G.6's sharp factor 1/2 needs no separate smallness premise on the mean or variance. -/
theorem deficit_mean_variance_bound (mu : FinitePMF Ω) (R : Ω → ℝ) (hR : ∀ z, 0 ≤ R z) :
    finitePMFExpectation mu (fun z => max (1-R z) 0) ≤
      min 1 (max (1-finitePMFExpectation mu R) 0+
        (1/2:ℝ)*Real.sqrt (finitePMFExpectation mu (fun z => (R z-finitePMFExpectation mu R)^2))) := by
  apply le_min
  · have h := expectation_mono mu (f := fun z => max (1-R z) 0) (g := fun _ => 1)
      (fun z => max_le (by linarith [hR z]) (by norm_num))
    simpa only [expectation_const] using h
  · have h := expectation_mono mu (f := fun z => max (1-R z) 0)
      (g := fun z => max (1-finitePMFExpectation mu R) 0+max (finitePMFExpectation mu R-R z) 0)
      (fun z => max_le (by linarith [le_max_left (1-finitePMFExpectation mu R) 0, le_max_left (finitePMFExpectation mu R-R z) 0])
        (add_nonneg (le_max_right _ _) (le_max_right _ _)))
    rw [expectation_add,expectation_const,centered_deficit_identity] at h
    have hs := mean_abs_le_sqrt mu (fun z => R z-finitePMFExpectation mu R)
    linarith

end
end PaperC.Prel8.PalmTargetSignBound
