import PaperCPrel8.PalmVoidPolynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Exact logarithmic derivative of the finite tilted void polynomial -/
namespace PaperC.Prel8.TiltedVoidDerivative
open Finset ArratiaGoldsteinGordonInput IndependentThinning V282.SteinFiniteExpectation
noncomputable section
variable {Ω : Type*} [Fintype Ω]

def generating (mu : FinitePMF Ω) (N : Ω → ℕ) (t : ℝ) : ℝ :=
  finitePMFExpectation mu (fun w ↦ (1-t)^N w)

def tiltedMean (mu : FinitePMF Ω) (N : Ω → ℕ) (t : ℝ) : ℝ :=
  finitePMFExpectation mu (fun w ↦ (1-t)^N w*(N w:ℝ))/generating mu N t

def normalized (mu : FinitePMF Ω) (N : Ω → ℕ) (m : ℕ) (p t : ℝ) : ℝ :=
  generating mu N t/(1-t*p)^m

theorem positive_mass (mu : FinitePMF Ω) : ∃ w, 0<mu.prob w := by
  by_contra! hn
  have hz : ∑ w, mu.prob w=0 := sum_eq_zero (fun w _ ↦ le_antisymm (hn w) (mu.nonneg w))
  linarith [mu.sum_prob]

theorem generating_pos (mu : FinitePMF Ω) (N : Ω → ℕ) {t : ℝ} (ht : t<1) :
    0<generating mu N t := by
  obtain ⟨w,hw⟩ := positive_mass mu
  apply (mul_pos hw (pow_pos (by linarith : 0<1-t) _)).trans_le
  exact single_le_sum (fun z _ ↦ mul_nonneg (mu.nonneg z) (pow_nonneg (by linarith) _)) (mem_univ w)

theorem generating_derivative (mu : FinitePMF Ω) (N : Ω → ℕ) (t : ℝ) :
    HasDerivAt (generating mu N)
      (-finitePMFExpectation mu (fun w ↦ (N w:ℝ)*(1-t)^(N w-1))) t := by
  have hh := HasDerivAt.sum (u:=univ) (fun w _ ↦
    (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow (N w)).const_mul (mu.prob w))
  convert hh using 1
  · funext s
    simp [generating,finitePMFExpectation]
  · simp only [Pi.sub_apply,id_eq,finitePMFExpectation,one_mul,zero_sub,neg_mul,mul_neg,sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro w hw
    ring

theorem weighted_derivative (mu : FinitePMF Ω) (N : Ω → ℕ) {t : ℝ} (ht : t<1) :
    finitePMFExpectation mu (fun w ↦ (N w:ℝ)*(1-t)^(N w-1))=
      finitePMFExpectation mu (fun w ↦ (1-t)^N w*(N w:ℝ))/(1-t) := by
  have hz : 1-t≠0 := by linarith
  simp only [finitePMFExpectation,sum_div]
  apply sum_congr rfl
  intro w hw
  by_cases hN : N w=0
  · simp [hN]
  · have he : N w-1+1=N w := by omega
    have hx : (1-t)^N w=(1-t)^(N w-1)*(1-t) := by rw [← pow_succ,he]
    rw [hx]
    field_simp

/-- The normalized void has the exact tilted-mean derivative for every t<1. -/
theorem log_normalized_derivative (mu : FinitePMF Ω) (N : Ω → ℕ) (m : ℕ)
    {p t : ℝ} (hp : 0≤p) (hp1 : p<1) (ht : t<1) :
    HasDerivAt (fun s ↦ Real.log (normalized mu N m p s))
      (-tiltedMean mu N t/(1-t)+(m:ℝ)*p/(1-t*p)) t := by
  have hg := generating_pos mu N ht
  have hb : 0<1-t*p := by nlinarith
  have hd := generating_derivative mu N t
  rw [weighted_derivative mu N ht] at hd
  have hbase := ((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).mul_const p)).pow m
  have hquot := hd.div hbase (pow_ne_zero _ hb.ne')
  have hl := hquot.log (div_ne_zero hg.ne' (pow_ne_zero _ hb.ne'))
  convert hl using 1
  · rfl
  · simp only [Pi.div_apply,Pi.sub_apply,Pi.pow_apply,id_eq,zero_sub,one_mul,tiltedMean]
    by_cases hm : m=0
    · simp [hm]
      field_simp
      <;> ring
    · have he : m-1+1=m := by omega
      have hx : (1-t*p)^(m-1)*(1-t*p)=(1-t*p)^m := by rw [← pow_succ,he]
      rw [← hx]
      field_simp [hg.ne',hb.ne',show 1-t≠0 by linarith]
      <;> ring

end
end PaperC.Prel8.TiltedVoidDerivative
