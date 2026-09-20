import PaperCPrel8.FiniteCumulantEnvelope
import PaperCPrel8.PalmVoidPolynomial

/-! # The finite Palm cumulant criterion, with its singleton corrections

Cumulants here are formed from moments of J-p under the actual planted law.
The singleton coefficient is E_Palm[J]-p and is never dropped.
-/
namespace PaperC.Prel8.PalmCumulantEnvelope
open Finset FiniteCumulantPartitions FiniteCumulantEnvelope PalmVoidPolynomial
open IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
noncomputable section
variable {ι Ω : Type*} [DecidableEq ι] [Fintype Ω]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem raw_exponential_bound (m : Finset ι → ℝ) (hm : m ∅=1)
    (I : Finset ι) {t : ℝ} (ht : 0≤t) :
    (∑ S∈I.powerset, t^S.card*|m S|)≤
      Real.exp (∑ B∈I.powerset.filter (fun B ↦ B.Nonempty), t^B.card*|cumulant m B|) := by
  apply (moment_product_bound m hm I ht).trans
  rw [Real.exp_sum]
  apply prod_le_prod₀ (fun B _ ↦ by positivity)
  intro B hB
  linarith [Real.add_one_le_exp (t^B.card*|cumulant m B|)]

theorem raw_nonempty_bound (m : Finset ι → ℝ) (hm : m ∅=1)
    (I : Finset ι) {t : ℝ} (ht : 0≤t) :
    (∑ S∈I.powerset.erase ∅, t^S.card*|m S|)≤
      Real.exp (∑ B∈I.powerset.filter (fun B ↦ B.Nonempty), t^B.card*|cumulant m B|)-1 := by
  have hh := raw_exponential_bound m hm I ht
  rw [← sum_erase_add _ _ (empty_mem_powerset I)] at hh
  simp only [card_empty,pow_zero,hm,abs_one,mul_one] at hh
  linarith

def referenceMoment (mu : FinitePMF Ω) (J : ι → Ω → ℝ) (p : ℝ) (S : Finset ι) : ℝ :=
  finitePMFExpectation mu (fun w ↦ ∏ j∈S, (J j w-p))

theorem singleton_correction (mu : FinitePMF Ω) (J : ι → Ω → ℝ) (p : ℝ) (j : ι) :
    cumulant (referenceMoment mu J p) {j}=finitePMFExpectation mu (J j)-p := by
  rw [cumulant_singleton]
  exact singleton_centered_moment mu J p j

/-- The exact G.6 sufficient criterion, without assuming equality of Palm and reference means. -/
theorem normalized_avoidance_bound (mu : FinitePMF Ω) (I : Finset ι)
    (J : ι → Ω → ℝ) (p : ℝ) {t : ℝ} (ht : 0≤t) (hp : 0<1-t*p) :
    |finitePMFExpectation mu (fun w ↦ ∏ j∈I, (1-t*J j w))/(1-t*p)^I.card-1|≤
      Real.exp (∑ B∈I.powerset.filter (fun B ↦ B.Nonempty),
        (t/(1-t*p))^B.card*|cumulant (referenceMoment mu J p) B|)-1 := by
  rw [normalized_expectation mu I J p t hp.ne']
  change |(∑ S∈I.powerset, (-t/(1-t*p))^S.card*referenceMoment mu J p S)-1|≤_
  have hm : referenceMoment mu J p ∅=1 := empty_centered_moment mu J p
  rw [← sum_erase_add _ _ (empty_mem_powerset I)]
  simp only [card_empty,pow_zero,hm,mul_one,add_sub_cancel_right]
  apply (abs_sum_le_sum_abs _ _).trans
  have he (S : Finset ι) : |(-t/(1-t*p))^S.card*referenceMoment mu J p S|=
      (t/(1-t*p))^S.card*|referenceMoment mu J p S| := by
    rw [abs_mul,abs_pow,abs_div,abs_neg,abs_of_nonneg ht,abs_of_pos hp]
  simp_rw [he]
  exact raw_nonempty_bound _ hm I (div_nonneg ht hp.le)

end
end PaperC.Prel8.PalmCumulantEnvelope
