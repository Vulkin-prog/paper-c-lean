import PaperCPrel8.TiltedVoidIntegral

/-! # The tilted law and occurrence count behind the Palm logarithmic identity -/
namespace PaperC.Prel8.TiltedVoidLaw
open Finset TiltedVoidDerivative TiltedVoidIntegral
open ArratiaGoldsteinGordonInput IndependentThinning V282.SteinFiniteExpectation
noncomputable section
variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def tilted (mu : FinitePMF Ω) (N : Ω → ℕ) (t : ℝ) (ht : t<1) : FinitePMF Ω where
  prob w := mu.prob w*(1-t)^N w/generating mu N t
  nonneg w := div_nonneg (mul_nonneg (mu.nonneg w) (pow_nonneg (by linarith) _)) (generating_pos mu N ht).le
  sum_prob := by
    rw [← sum_div]
    exact div_self (generating_pos mu N ht).ne'

theorem tilted_mean_eq (mu : FinitePMF Ω) (N : Ω → ℕ) {t : ℝ} (ht : t<1) :
    finitePMFExpectation (tilted mu N t ht) (fun w ↦ (N w:ℝ))=tiltedMean mu N t := by
  simp only [finitePMFExpectation,tilted,tiltedMean,sum_div]
  apply sum_congr rfl
  intro w hw
  ring

def count (S : Finset ι) (J : ι → Ω → Bool) (w : Ω) : ℕ :=
  (S.filter (fun j ↦ J j w=true)).card

theorem count_product (S : Finset ι) (J : ι → Ω → Bool) (w : Ω) (t : ℝ) :
    (∏ j∈S, (1-t*(if J j w then (1:ℝ) else 0)))=(1-t)^count S J w := by
  have hh (j : ι) : (1-t*(if J j w then (1:ℝ) else 0))=
      if J j w=true then (1-t) else 1 := by cases J j w <;> simp
  simp_rw [hh]
  rw [prod_ite]
  simp [count]

theorem normalized_avoidance (mu : FinitePMF Ω) (S : Finset ι) (J : ι → Ω → Bool) (p t : ℝ) :
    finitePMFExpectation mu (fun w ↦ ∏ j∈S, (1-t*(if J j w then (1:ℝ) else 0)))/(1-t*p)^S.card=
      normalized mu (count S J) S.card p t := by
  simp_rw [count_product]
  rfl

theorem count_zero_iff (S : Finset ι) (J : ι → Ω → Bool) (w : Ω) :
    count S J w=0 ↔ ∀ j∈S, J j w=false := by
  simp only [count,card_eq_zero,filter_eq_empty_iff]
  constructor
  · intro h j hj
    cases he : J j w
    · rfl
    · exact False.elim (h hj he)
  · intro h j hj hn
    simp [h j hj] at hn

end
end PaperC.Prel8.TiltedVoidLaw
