import PaperCV282.FiniteFieldTotalVariation
import PaperCV282.ScalarSteinInput
import PaperC.Probability.PoissonVectorMass
import PaperC.Probability.SectionThirteenCouplings

/-!
# Variable-rate Poisson fields and exact linear rate perturbation

The product law is normalized on the genuine countable state space of
natural-valued finite vectors. The comparison constant is one:
half-L1 distance is bounded by the sum of absolute changes of the rates.
-/

namespace PaperC.V282.FiniteFieldPoissonCoupling

open ProbabilityTheory FiniteFieldTotalVariation PoissonVectorMass SectionThirteenCouplings ScalarSteinInput
open scoped BigOperators NNReal

noncomputable section

variable {ι : Type*} [Fintype ι]

def poissonFieldMass (rate : ι → ℝ≥0) (k : ι → ℕ) : ℝ :=
  ∏ i, poissonMass (rate i) (k i)

theorem poissonFieldMass_nonneg (rate : ι → ℝ≥0) (k : ι → ℕ) :
    0 ≤ poissonFieldMass rate k :=
  Finset.prod_nonneg (fun _ _ => poissonMass_nonneg _ _)

theorem hasSum_poissonFieldMass (rate : ι → ℝ≥0) :
    HasSum (poissonFieldMass rate) 1 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E : (ι → ℕ) ≃ (Fin (Fintype.card ι) → ℕ) := Equiv.arrowCongr e (Equiv.refl ℕ)
  rw [← E.symm.hasSum_iff]
  have h := hasSum_pi_prod (Fintype.card ι) (fun j k => poissonMass (rate (e.symm j)) k)
    (fun j k => poissonMass_nonneg _ _) (fun j => hasSum_poissonMass _)
  convert h using 1
  funext k
  change (∏ i, poissonMass (rate i) (k (e i))) =
    ∏ j, poissonMass (rate (e.symm j)) (k j)
  exact (Fintype.prod_equiv e.symm _ _ (fun j => by simp)).symm

theorem summable_poissonFieldMass (rate : ι → ℝ≥0) : Summable (poissonFieldMass rate) :=
  (hasSum_poissonFieldMass rate).summable

theorem poissonFieldMass_zero (k : ι → ℕ) :
    poissonFieldMass 0 k = if k = 0 then 1 else 0 := by
  classical
  by_cases hk : k = 0
  · subst k
    simp [poissonFieldMass, poissonMass_zero]
  · rw [if_neg hk]
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra h
      apply hk
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    unfold poissonFieldMass
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [poissonMass_zero, hi]

theorem massTotalVariation_le_one_sub_of_scaled_le {α : Type*} {p q : α → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1) (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hscale : ∀ k, c * p k ≤ q k) :
    massTotalVariation p q ≤ 1 - c := by
  have hcp : Summable (fun k => c * p k) := hp.summable.mul_left c
  have hfirst : massTotalVariation p (fun k => c * p k) = (2 : ℝ)⁻¹ * (1 - c) := by
    unfold massTotalVariation
    have hpoint (k) : |p k - c * p k| = (1 - c) * p k := by
      rw [abs_of_nonneg (by nlinarith [hp0 k])]
      ring
    simp_rw [hpoint]
    rw [tsum_mul_left, hp.tsum_eq, mul_one]
  have hsecond : massTotalVariation (fun k => c * p k) q = (2 : ℝ)⁻¹ * (1 - c) := by
    unfold massTotalVariation
    have hpoint (k) : |c * p k - q k| = q k - c * p k := by
      rw [abs_of_nonpos (sub_nonpos.2 (hscale k))]
      ring
    simp_rw [hpoint]
    rw [hq.summable.tsum_sub hcp, tsum_mul_left, hp.tsum_eq, hq.tsum_eq, mul_one]
  have h := massTotalVariation_triangle hp.summable hcp hq.summable
    hp0 (fun k => mul_nonneg hc0 (hp0 k)) hq0
  rw [hfirst, hsecond] at h
  linarith

theorem scaled_poissonMass_le_of_le {r s : ℝ≥0} (h : r ≤ s) (k : ℕ) :
    Real.exp ((r : ℝ) - (s : ℝ)) * poissonMass r k ≤ poissonMass s k := by
  simp only [poissonMass_formula]
  exact scaled_poissonPMFReal_le_of_le h k

theorem scaled_poissonFieldMass_le_of_le {rate target : ι → ℝ≥0}
    (h : ∀ i, rate i ≤ target i) (k : ι → ℕ) :
    Real.exp (∑ i, ((rate i : ℝ) - (target i : ℝ))) * poissonFieldMass rate k ≤
      poissonFieldMass target k := by
  classical
  rw [Real.exp_sum, poissonFieldMass, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod
    (fun i _ => mul_nonneg (Real.exp_pos _).le (poissonMass_nonneg _ _))
    (fun i _ => scaled_poissonMass_le_of_le (h i) (k i))

theorem massTotalVariation_poissonField_le_of_le {rate target : ι → ℝ≥0}
    (h : ∀ i, rate i ≤ target i) :
    massTotalVariation (poissonFieldMass rate) (poissonFieldMass target) ≤
      ∑ i, ((target i : ℝ) - (rate i : ℝ)) := by
  have hneg : (∑ i, ((rate i : ℝ) - (target i : ℝ))) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => sub_nonpos.2 (by exact_mod_cast h i))
  have hc := massTotalVariation_le_one_sub_of_scaled_le
    (hasSum_poissonFieldMass rate) (hasSum_poissonFieldMass target)
    (poissonFieldMass_nonneg rate) (poissonFieldMass_nonneg target)
    (Real.exp_pos _).le (Real.exp_le_one_iff.2 hneg)
    (scaled_poissonFieldMass_le_of_le h)
  have hexp := Real.add_one_le_exp (∑ i, ((rate i : ℝ) - (target i : ℝ)))
  have hsum : (∑ i, ((target i : ℝ) - (rate i : ℝ))) =
      -(∑ i, ((rate i : ℝ) - (target i : ℝ))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

theorem massTotalVariation_poissonField_le_sum_abs (rate target : ι → ℝ≥0) :
    massTotalVariation (poissonFieldMass rate) (poissonFieldMass target) ≤
      ∑ i, |(rate i : ℝ) - (target i : ℝ)| := by
  let common : ι → ℝ≥0 := fun i => min (rate i) (target i)
  have hr := massTotalVariation_poissonField_le_of_le
    (fun i => show common i ≤ rate i from min_le_left _ _)
  have hs := massTotalVariation_poissonField_le_of_le
    (fun i => show common i ≤ target i from min_le_right _ _)
  have htri := massTotalVariation_triangle
    (summable_poissonFieldMass rate) (summable_poissonFieldMass common)
    (summable_poissonFieldMass target)
    (poissonFieldMass_nonneg rate) (poissonFieldMass_nonneg common)
    (poissonFieldMass_nonneg target)
  rw [massTotalVariation_comm (poissonFieldMass rate) (poissonFieldMass common)] at htri
  have hsum : (∑ i, ((rate i : ℝ) - (common i : ℝ))) +
      (∑ i, ((target i : ℝ) - (common i : ℝ))) =
      ∑ i, |(rate i : ℝ) - (target i : ℝ)| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [common]
    rw [NNReal.coe_min]
    rcases le_total (rate i : ℝ) (target i : ℝ) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]
      ring
  linarith

def retainedRates (good : Finset ι) (rate : ι → ℝ≥0) (i : ι) : ℝ≥0 := by
  classical
  exact if i ∈ good then rate i else 0

theorem massTotalVariation_retainedRates_le (good : Finset ι) (rate : ι → ℝ≥0) :
    massTotalVariation (poissonFieldMass (retainedRates good rate)) (poissonFieldMass rate) ≤
      ∑ i ∈ badFieldSites good, (rate i : ℝ) := by
  classical
  apply (massTotalVariation_poissonField_le_of_le
    (fun i => show retainedRates good rate i ≤ rate i by
      by_cases hi : i ∈ good <;> simp [retainedRates, hi])).trans_eq
  rw [badFieldSites, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ good <;> simp [retainedRates, hi]

theorem field_comparison_via_retention {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (W : Ω → ι → ℕ) (good : Finset ι) (rate : ι → ℝ≥0)
    {error : ℝ}
    (hretained : massTotalVariation (finiteFieldLaw μ (retainedField good W))
      (poissonFieldMass (retainedRates good rate)) ≤ error) :
    massTotalVariation (finiteFieldLaw μ W) (poissonFieldMass rate) ≤
      (∑ i ∈ badFieldSites good, ArratiaGoldsteinGordonInput.eventProbability μ (fun ω => W ω i ≠ 0)) +
        error + ∑ i ∈ badFieldSites good, (rate i : ℝ) := by
  have hfirst := massTotalVariation_retainedField_le_bad_sites μ good W
  have hlast := massTotalVariation_retainedRates_le good rate
  have htri1 := massTotalVariation_triangle (summable_finiteFieldLaw μ W)
    (summable_finiteFieldLaw μ (retainedField good W)) (summable_poissonFieldMass rate)
    (finiteFieldLaw_nonneg μ W) (finiteFieldLaw_nonneg μ (retainedField good W))
    (poissonFieldMass_nonneg rate)
  have htri2 := massTotalVariation_triangle
    (summable_finiteFieldLaw μ (retainedField good W))
    (summable_poissonFieldMass (retainedRates good rate)) (summable_poissonFieldMass rate)
    (finiteFieldLaw_nonneg μ (retainedField good W))
    (poissonFieldMass_nonneg (retainedRates good rate)) (poissonFieldMass_nonneg rate)
  linarith

end

end PaperC.V282.FiniteFieldPoissonCoupling
