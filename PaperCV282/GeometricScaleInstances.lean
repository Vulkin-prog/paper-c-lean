import PaperCV282.GeometricSaddleSummability

/-! # Literal geometric subsequences satisfy the proved summability hypothesis -/
namespace PaperC.V282.GeometricScaleInstances

open Filter Topology GeometricSaddleSummability

noncomputable section

/-- No upper geometric bound is necessary for the almost-sure argument. -/
theorem geometricLowerGrowth_of_geometric_lower_bound (sizes : ℕ → ℕ)
    (q D : ℝ) (hq : 1<q) (hD : 0<D)
    (hbound : ∀ᶠ k : ℕ in atTop, D*q^k ≤ (sizes k : ℝ)) : GeometricLowerGrowth sizes := by
  have hlq : 0<Real.log q := Real.log_pos hq
  have hl := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (by linarith : 0<Real.log q/2)
  refine ⟨2/Real.log q,by positivity,?_⟩
  filter_upwards [hbound,hl.eventually (eventually_ge_atTop (-Real.log D))] with k hb hk
  have hq0 : 0<q := by linarith
  have hpos : 0<D*q^k := mul_pos hD (pow_pos hq0 _)
  have hh := Real.log_le_log hpos hb
  rw [Real.log_mul (ne_of_gt hD) (ne_of_gt (pow_pos hq0 _)),Real.log_pow] at hh
  have hmul : (k : ℝ)*(Real.log q/2) ≤ Real.log (sizes k) := by nlinarith
  calc
    (k : ℝ) ≤ Real.log (sizes k)/(Real.log q/2) := (le_div_iff₀ (by linarith)).mpr hmul
    _ = (2/Real.log q)*Real.log (sizes k) := by ring

/-- Geometric lower growth forces the sizes themselves to diverge. -/
theorem sizes_tendsto_atTop {sizes : ℕ → ℕ} (hg : GeometricLowerGrowth sizes) :
    Tendsto sizes atTop atTop := by
  have hlog := log_sizes_tendsto_atTop hg
  have hreal : Tendsto (fun k => (sizes k : ℝ)) atTop atTop := by
    apply (Real.tendsto_exp_atTop.comp hlog).congr'
    filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
    have hN : (0 : ℝ)<sizes k := by
      have : (sizes k : ℝ)≠0 := by intro hz; simp [hz] at hk
      exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm this)
    exact Real.exp_log hN
  exact tendsto_natCast_atTop_iff.mp hreal

/-- The proof applies directly to every eventually bounded-below geometric scale. -/
theorem summable_nu_on_geometric_scales (sizes : ℕ → ℕ) (q D a c : ℝ)
    (hq : 1<q) (hD : 0<D) (ha : 0<a) (hc : 0<c)
    (hbound : ∀ᶠ k : ℕ in atTop, D*q^k ≤ (sizes k : ℝ)) :
    Summable (fun k => Real.exp (-c*SaddleScales.saddleNu a (Real.log (sizes k)))) :=
  summable_exp_neg_nu (geometricLowerGrowth_of_geometric_lower_bound sizes q D hq hD hbound) ha hc

end
end PaperC.V282.GeometricScaleInstances
