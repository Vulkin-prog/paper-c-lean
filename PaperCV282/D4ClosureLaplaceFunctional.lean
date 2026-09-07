import PaperCV282.D4ClosureLaplaceTransfer
import PaperCV282.D4ClosureIntegerLevels
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # The literal two-sided Laplace functional and compact level bands -/
namespace PaperC.V282.D4ClosureLaplaceFunctional

open MeasureTheory Filter Topology Real D4ClosureIntegerLevels D4ClosureLaplaceTransfer
open D4ClosureLaplaceSource GrowingLevelParameters SpatialMarkedParameters AllStartSoftPoisson
open scoped BigOperators

noncomputable section

def laplaceFunctional (theta : ℝ) (g : ℝ × ℤ → ℝ) : ℝ :=
  exp (-(∫ t in Set.Ico (1 : ℝ) 2,
    ∑' r : ℤ, (integerLevelRate theta r : ℝ)*(1-exp (-g (t,r)))))

def levelWindow (d E : ℕ) : Finset ℤ :=
  (Finset.range (E+1)).image (fun e : ℕ => (e : ℤ)-d)

theorem mem_levelWindow (d E : ℕ) (r : ℤ) :
    r ∈ levelWindow d E ↔ -(d : ℤ) ≤ r ∧ r ≤ (E : ℤ)-d := by
  classical
  simp only [levelWindow,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨e,he,rfl⟩
    omega
  · intro h
    refine ⟨(r+d).toNat,?_,?_⟩ <;> omega

/-- Compactness alone supplies a finite level band; no such band is an analytic premise. -/
theorem compact_support_level_band (g : ℝ × ℤ → ℝ) (hg : HasCompactSupport g) :
    ∃ d E : ℕ, (∀ t r, r < -(d : ℤ) → g (t,r) = 0) ∧
      (∀ t r, (E : ℤ)-d < r → g (t,r) = 0) := by
  classical
  let s := (hg.isCompact.image continuous_snd).finite_of_discrete.toFinset
  let d := s.sup Int.natAbs
  have hb (t : ℝ) (r : ℤ) (h : g (t,r) ≠ 0) : -(d : ℤ) ≤ r ∧ r ≤ (d : ℤ) := by
    have hmem : r ∈ s := by
      change r ∈ (hg.isCompact.image continuous_snd).finite_of_discrete.toFinset
      rw [Set.Finite.mem_toFinset]
      exact ⟨(t,r),subset_closure h,rfl⟩
    have h := Finset.le_sup (f := Int.natAbs) hmem
    change r.natAbs ≤ d at h
    omega
  refine ⟨d,2*d,?_,?_⟩
  · intro t r hr
    by_contra h
    have := (hb t r h).1
    omega
  · intro t r hr
    by_contra h
    have := (hb t r h).2
    omega

theorem level_integrand_eq_sum (theta : ℝ) (g : ℝ × ℤ → ℝ) (s : Finset ℤ)
    (hs : ∀ t r, r ∉ s → g (t,r) = 0) (t : ℝ) :
    (∑' r : ℤ, (integerLevelRate theta r : ℝ)*(1-exp (-g (t,r)))) =
      ∑ r ∈ s, (integerLevelRate theta r : ℝ)*(1-exp (-g (t,r))) := by
  apply tsum_eq_sum
  intro r hr
  simp [hs t r hr]

theorem level_window_integrand (theta : ℝ) (d E : ℕ) (g : ℝ × ℤ → ℝ)
    (hlo : ∀ t r, r < -(d : ℤ) → g (t,r) = 0)
    (hhi : ∀ t r, (E : ℤ)-d < r → g (t,r) = 0) (t : ℝ) :
    (∑' r : ℤ, (integerLevelRate theta r : ℝ)*(1-exp (-g (t,r)))) =
      (2 : ℝ)^(theta+d) * markedRetentionIntegrand E (fun t e => g (t,(e : ℤ)-d)) t := by
  classical
  rw [level_integrand_eq_sum theta g (levelWindow d E) (fun t r hr => by
    rw [mem_levelWindow] at hr
    by_cases h : r < -(d : ℤ)
    · exact hlo t r h
    · exact hhi t r (by omega))]
  unfold levelWindow
  rw [Finset.sum_image (fun a ha b hb h => by omega)]
  unfold markedRetentionIntegrand
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hrate : (integerLevelRate theta ((e : ℤ)-d) : ℝ) =
      (2 : ℝ)^(theta+d) * geometricMarkWeight e := by
    change (2 : ℝ)^(theta-(((e : ℤ)-(d : ℤ) : ℤ) : ℝ)-1) = _
    push_cast
    rw [show theta-((e : ℝ)-d)-1=theta+d-(e+1 : ℕ) by push_cast; ring,
      Real.rpow_sub (by norm_num),Real.rpow_natCast]
    unfold geometricMarkWeight
    ring
  rw [hrate]
  unfold spatialRetention
  ring

theorem laplaceFunctional_window (theta : ℝ) (d E : ℕ) (g : ℝ × ℤ → ℝ)
    (hlo : ∀ t r, r < -(d : ℤ) → g (t,r) = 0)
    (hhi : ∀ t r, (E : ℤ)-d < r → g (t,r) = 0) :
    laplaceFunctional theta g = exp (-((2 : ℝ)^(theta+d)*
      ∫ t in Set.Ico (1 : ℝ) 2, markedRetentionIntegrand E (fun t e => g (t,(e : ℤ)-d)) t)) := by
  unfold laplaceFunctional
  simp_rw [level_window_integrand theta d E g hlo hhi]
  rw [integral_const_mul]

end
end PaperC.V282.D4ClosureLaplaceFunctional
