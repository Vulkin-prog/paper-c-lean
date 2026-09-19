import PaperCPrel8.PoissonCloudTail
import PaperCPrel8.RoughKernelCloudBound
import PaperCV282.PoissonQuantitativeMoments

/-! # A normalized Poisson mixture of actual finite-size cloud laws -/
namespace PaperC.Prel8.PoissonCloudMixture
open Finset V282.ScalarSteinInput ArratiaGoldsteinGordonInput
open MeasureTheory ProbabilityTheory V282.PoissonQuantitativeMoments V282.PoissonPolynomialIntegrability
open scoped NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {Ω : ℕ → Type*} [∀ k, Fintype (Ω k)]

/-- Actual joint mass of the count and its finite conditional sample. -/
def mass (rate : ℝ≥0) (mu : ∀ k, FinitePMF (Ω k)) (s : Sigma Ω) : ℝ :=
  poissonMass rate s.1 * (mu s.1).prob s.2

/-- All mixture atoms are nonnegative. -/
theorem mass_nonneg (rate : ℝ≥0) (mu : ∀ k, FinitePMF (Ω k)) (s : Sigma Ω) : 0≤mass rate mu s :=
  mul_nonneg (poissonMass_nonneg rate s.1) ((mu s.1).nonneg s.2)

/-- The Poisson mixture is normalized, not merely a formal weighted expression. -/
theorem mass_hasSum (rate : ℝ≥0) (mu : ∀ k, FinitePMF (Ω k)) : HasSum (mass rate mu) 1 := by
  have hi (k : ℕ) : HasSum (fun w : Ω k ↦ mass rate mu ⟨k,w⟩) (poissonMass rate k) := by
    simpa only [mass,← mul_sum,(mu k).sum_prob,mul_one] using hasSum_fintype (fun w : Ω k ↦ mass rate mu ⟨k,w⟩)
  have hs : Summable (mass rate mu) := (summable_sigma_of_nonneg (mass_nonneg rate mu)).mpr
    ⟨fun _ ↦ (hasSum_fintype _).summable,by simpa only [(hi _).tsum_eq] using (hasSum_poissonMass rate).summable⟩
  exact (hasSum_poissonMass rate).sigma_of_hasSum hi hs

def probability (rate : ℝ≥0) (mu : ∀ k, FinitePMF (Ω k)) (P : Sigma Ω → Prop) : ℝ :=
  ∑' s, if P s then mass rate mu s else 0

/-- The event series is summable, since it is dominated by a probability law. -/
theorem event_summable (rate : ℝ≥0) (mu : ∀ k, FinitePMF (Ω k)) (P : Sigma Ω → Prop) :
    Summable (fun s ↦ if P s then mass rate mu s else 0) := by
  classical
  apply (mass_hasSum rate mu).summable.of_nonneg_of_le
  · intro s; split_ifs <;> first | exact mass_nonneg rate mu s | exact le_rfl
  · intro s; split_ifs <;> first | exact le_rfl | exact mass_nonneg rate mu s

/-- Exposing the count gives exactly the average of the genuine finite event probabilities. -/
theorem probability_eq (rate : ℝ≥0) (mu : ∀ k, FinitePMF (Ω k)) (P : Sigma Ω → Prop) :
    probability rate mu P = ∑' k, poissonMass rate k * eventProbability (mu k) (fun w ↦ P ⟨k,w⟩) := by
  classical
  rw [probability,(event_summable rate mu P).tsum_sigma' (fun _ ↦ (hasSum_fintype _).summable)]
  congr 1
  funext k
  rw [tsum_fintype,eventProbability,mul_sum]
  apply sum_congr rfl
  intro w _
  by_cases hp : P ⟨k,w⟩ <;> simp [hp,mass]

/-- Every finite conditional event has probability at most one. -/
theorem finite_probability_le_one {α : Type*} [Fintype α] (mu : FinitePMF α) (P : α → Prop) :
    eventProbability mu P ≤ 1 := by
  classical
  rw [← mu.sum_prob,eventProbability]
  apply sum_le_sum
  intro w _
  split_ifs <;> first | exact le_rfl | exact mu.nonneg w

/-- Exact first moment, in the same scalar-mass convention as the cloud mixture. -/
theorem first_moment_hasSum (rate : ℝ≥0) :
    HasSum (fun k : ℕ ↦ poissonMass rate k*(k:ℝ)) (rate:ℝ) := by
  have hi : Integrable (fun k : ℕ ↦ (k:ℝ)) (poissonMeasure rate) := by
    simpa only [pow_one] using integrable_poisson_nat_pow rate 1
  have h := hasSum_integral_poissonMeasure hi
  rw [poisson_mean] at h
  simpa only [smul_eq_mul,poissonMass,poissonMeasure_real_singleton] using h

/-- First-moment losses and a bounded regularity cost are averaged before paying the upper tail. -/
theorem probability_le_affine_cutoff (rate : ℝ≥0) (mu : ∀ k, FinitePMF (Ω k))
    (P : Sigma Ω → Prop) (K : ℕ) (a B : ℝ) (ha : 0≤a) (hB : 0≤B)
    (hb : ∀ k≤K, eventProbability (mu k) (fun w ↦ P ⟨k,w⟩) ≤ a*k+B) :
    probability rate mu P ≤ a*(rate:ℝ)+B+PoissonCloudTail.tail rate K := by
  classical
  let f := fun k ↦ poissonMass rate k * eventProbability (mu k) (fun w ↦ P ⟨k,w⟩)
  have hf : Summable f := (hasSum_poissonMass rate).summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (poissonMass_nonneg rate k) (eventProbability_nonneg _ _))
    (fun k ↦ by simpa only [mul_one] using mul_le_mul_of_nonneg_left (finite_probability_le_one _ _) (poissonMass_nonneg rate k))
  have hg := (((first_moment_hasSum rate).mul_left a).add ((hasSum_poissonMass rate).mul_left B)).summable.add
    (PoissonCloudTail.tail_summable rate K)
  have h := hf.tsum_le_tsum (g := fun k ↦ (a*(poissonMass rate k*k)+B*poissonMass rate k)+
    (if K<k then poissonMass rate k else 0)) (fun k ↦ by
      have hp := poissonMass_nonneg rate k
      by_cases hk : k≤K
      · rw [ite_eq_right (by omega)]
        have he := mul_le_mul_of_nonneg_left (hb k hk) hp
        dsimp [f]
        nlinarith only [he]
      · rw [ite_eq_left (by omega)]
        have he := mul_le_mul_of_nonneg_left (finite_probability_le_one (mu k) (fun w ↦ P ⟨k,w⟩)) hp
        have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
        dsimp [f]
        nlinarith [mul_nonneg ha (mul_nonneg hp hk0),mul_nonneg hB hp]) hg
  rw [probability_eq]
  apply h.trans_eq
  rw [Summable.tsum_add (((first_moment_hasSum rate).mul_left a).add ((hasSum_poissonMass rate).mul_left B)).summable
    (PoissonCloudTail.tail_summable rate K)]
  rw [(((first_moment_hasSum rate).mul_left a).add ((hasSum_poissonMass rate).mul_left B)).tsum_eq]
  simp only [mul_one,PoissonCloudTail.tail]

end
end PaperC.Prel8.PoissonCloudMixture
