import PaperCPrel8.PalmVoidNormalization

/-! # Target-weighted void comparison without exponential amplification -/
namespace PaperC.Prel8.PalmVoidAverage
open PaperC.Prel8.PalmDeficit PaperC.Prel8.PalmVoidNormalization
open PaperC.V282.FiniteFieldTotalVariation
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {Ω : Type*}

def voidDeficit (q : Ω → ℝ) (regular : Ω → Prop) (R : Ω → ℝ) : ℝ :=
  ∑' z, if regular z then q z*max (1-R z) 0 else 0

theorem void_term_bounds {q R : Ω → ℝ} (hq : ∀ z, 0 ≤ q z) (hR : ∀ z, 0 ≤ R z)
    (regular : Ω → Prop) (z : Ω) :
    0 ≤ (if regular z then q z*max (1-R z) 0 else 0) ∧
      (if regular z then q z*max (1-R z) 0 else 0) ≤ q z := by
  split_ifs
  · refine ⟨mul_nonneg (hq z) (le_max_right _ _),?_⟩
    exact mul_le_of_le_one_right (hq z) (max_le (by linarith [hR z]) (by norm_num))
  · exact ⟨le_rfl,hq z⟩

theorem summable_void {q R : Ω → ℝ} (hqsum : Summable q)
    (hq : ∀ z, 0 ≤ q z) (hR : ∀ z, 0 ≤ R z) (regular : Ω → Prop) :
    Summable (fun z => if regular z then q z*max (1-R z) 0 else 0) :=
  hqsum.of_nonneg_of_le (fun z => (void_term_bounds hq hR regular z).1)
    (fun z => (void_term_bounds hq hR regular z).2)

theorem voidDeficit_nonneg {q R : Ω → ℝ} (hq : ∀ z, 0 ≤ q z)
    (hR : ∀ z, 0 ≤ R z) (regular : Ω → Prop) : 0 ≤ voidDeficit q regular R :=
  tsum_nonneg (fun z => (void_term_bounds hq hR regular z).1)

/-- A uniform log error stays unamplified after target averaging. -/
theorem averaged_normalization {q b R : Ω → ℝ} (hqsum : HasSum q 1)
    (hq : ∀ z, 0 ≤ q z) (hb : ∀ z, 0 < b z) (hR : ∀ z, 0 ≤ R z)
    (regular : Ω → Prop) {eta : ℝ} (heta : 0 ≤ eta)
    (hlog : ∀ z, regular z → |Real.log (b z)| ≤ eta) :
    |voidDeficit q regular (fun z => b z*R z)-voidDeficit q regular R| ≤ eta := by
  have hscaled := summable_void hqsum.summable hq (fun z => mul_nonneg (hb z).le (hR z)) regular
  have hplain := summable_void hqsum.summable hq hR regular
  have hpoint (z : Ω) :
      |(if regular z then q z*max (1-b z*R z) 0 else 0)-
        (if regular z then q z*max (1-R z) 0 else 0)| ≤ q z*eta := by
    by_cases hz : regular z
    · simp only [hz,ite_true,← mul_sub,abs_mul,abs_of_nonneg (hq z)]
      exact mul_le_mul_of_nonneg_left ((deficit_log_bound (hb z) (hR z)).trans (hlog z hz)) (hq z)
    · simp only [hz,ite_false,sub_self,abs_zero]
      exact mul_nonneg (hq z) heta
  unfold voidDeficit
  rw [← hscaled.tsum_sub hplain]
  calc
    _ ≤ ∑' z, |(if regular z then q z*max (1-b z*R z) 0 else 0)-
        (if regular z then q z*max (1-R z) 0 else 0)| := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hscaled.sub hplain).norm
    _ ≤ ∑' z, q z*eta := (hscaled.sub hplain).abs.tsum_le_tsum hpoint (hqsum.summable.mul_right eta)
    _ = eta := by rw [tsum_mul_right,hqsum.tsum_eq,one_mul]

/-- G.4's exact mass argument, with all model-specific hypotheses visible.
No arithmetic regularity or configuration-mass identity is assumed implicitly. -/
theorem normalized_void_deficit {p q b R : Ω → ℝ} (hpsum : HasSum p 1) (hqsum : HasSum q 1)
    (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z) (hb : ∀ z, 0 < b z) (hR : ∀ z, 0 ≤ R z)
    (regular : Ω → Prop) (hmass : ∀ z, regular z → p z=q z*(b z*R z))
    {D deletion eta : ℝ} (hprojection : 0 ≤ D-massTotalVariation p q)
    (hdeletion : D-massTotalVariation p q ≤ deletion) (heta : 0 ≤ eta)
    (hlog : ∀ z, regular z → |Real.log (b z)| ≤ eta) :
    |D-voidDeficit q regular R| ≤ deletion+exceptionalMass q regular+eta := by
  have he : deficit p q regular=voidDeficit q regular (fun z => b z*R z) := by
    apply tsum_congr
    intro z
    by_cases hz : regular z
    · simp only [hz,ite_true,hmass z hz]
      rw [mul_max_of_nonneg _ _ (hq z)]
      congr 1 <;> ring
    · simp [hz]
  have hd := deficit_restriction hpsum hqsum hp hq regular
  have hn := averaged_normalization hqsum hq hb hR regular heta hlog
  rw [← he] at hn
  have hh := abs_le.mp hn
  apply abs_le.mpr
  constructor <;> linarith

/-- The explicit normalization penalty is uniform for all regular plant sizes k<=K<=g. -/
theorem normalization_penalty {p : ℝ} {g K : ℕ} (hp : 0 ≤ p) (hp1 : p < 1)
    (k : Ω → ℕ) (hk : ∀ z, k z ≤ g) (hK : ∀ z, k z ≤ K) (z : Ω) :
    |Real.log (Real.exp ((g:ℝ)*p)*(1-p)^(g-k z))| ≤
      (K:ℝ)*p+(g:ℝ)*p^2/(1-p) := by
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity),Real.log_exp,Real.log_pow]
  apply (bernoulli_log_error hp hp1 (hk z)).trans
  have h : (k z:ℝ) ≤ K := by exact_mod_cast hK z
  gcongr

end
end PaperC.Prel8.PalmVoidAverage
