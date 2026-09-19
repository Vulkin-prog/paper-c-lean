import PaperCV282.SteinFiniteExpectation
import PaperC.Arithmetic.ParityVector

/-!
# Exact forcing of independent private coordinates

Finite probability-law construction behind 3PREL8 companion F.7. The law
of the nonpivot coordinates is arbitrary, including an already conditioned
law. The arithmetic identification of these coordinates with actual private
prime signs is a separate obligation in the correspondence.
-/
namespace PaperC.Prel8.PrivateForcing
open PaperC.IndependentThinning PaperC.ArratiaGoldsteinGordonInput
open PaperC.V282.SteinFiniteExpectation
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {R Ξ : Type*}

/-- Keep every nonpivot coordinate and prescribe the private coordinate block. -/
def force (target : R → Ξ) (z : R × Ξ) : R × Ξ := (z.1, target z.1)

theorem force_preserves_nonpivots (target : R → Ξ) (z : R × Ξ) :
    (force target z).1=z.1 := rfl

theorem force_hits (target : R → Ξ) (z : R × Ξ) :
    (force target z).2=target (force target z).1 := rfl

theorem force_fixes_satisfied (target : R → Ξ) (z : R × Ξ) (h : z.2=target z.1) :
    force target z=z := by
  ext <;> simp [force, h]

theorem force_idempotent (target : R → Ξ) (z : R × Ξ) :
    force target (force target z)=force target z := rfl

variable [Fintype R] [Fintype Ξ] [Nonempty Ξ]

/-- The law after forcing, tested against any real observable of the entire sample. -/
theorem forced_expectation (μ : FinitePMF R) (target : R → Ξ) (f : R × Ξ → ℝ) :
    finitePMFExpectation (productPMF μ (FinitePMF.uniform Ξ)) (fun z => f (force target z)) =
      finitePMFExpectation μ (fun r => f (r,target r)) := by
  classical
  unfold finitePMFExpectation productPMF force
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  simp [FinitePMF.uniform]
  field_simp

/-- Restricting to the forced block costs the same mass on every nonpivot fibre. -/
theorem restricted_expectation (μ : FinitePMF R) (target : R → Ξ) (f : R × Ξ → ℝ) :
    finitePMFExpectation (productPMF μ (FinitePMF.uniform Ξ))
      (fun z => if z.2=target z.1 then f z else 0) =
      (Fintype.card Ξ : ℝ)⁻¹ * finitePMFExpectation μ (fun r => f (r,target r)) := by
  classical
  unfold finitePMFExpectation productPMF
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp [FinitePMF.uniform, mul_ite, mul_comm, mul_left_comm]

/-- Full conditional-law identity, not merely the forced word's marginal. -/
theorem exact_conditional_expectation (μ : FinitePMF R) (target : R → Ξ)
    (f : R × Ξ → ℝ) :
    finitePMFExpectation (productPMF μ (FinitePMF.uniform Ξ)) (fun z => f (force target z)) =
      finitePMFExpectation (productPMF μ (FinitePMF.uniform Ξ))
        (fun z => if z.2=target z.1 then f z else 0) / (Fintype.card Ξ : ℝ)⁻¹ := by
  rw [forced_expectation, restricted_expectation]
  have hc : (Fintype.card Ξ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The conditioning event has positive, fibre-independent probability. -/
theorem forcing_event_probability (μ : FinitePMF R) (target : R → Ξ) :
    eventProbability (productPMF μ (FinitePMF.uniform Ξ)) (fun z => z.2=target z.1) =
      (Fintype.card Ξ : ℝ)⁻¹ := by
  classical
  rw [← finitePMFExpectation_indicator]
  have h := restricted_expectation μ target (fun _ => (1 : ℝ))
  simpa only [expectation_const, mul_one] using h

omit [Fintype R] in
/-- In a private affine coordinate system the prescribed pivots give exactly the word. -/
theorem affine_word_forced {ι : Type*} (offset : R → ι → F₂) (word : ι → F₂)
    (r : R) : (word-offset r)+offset r=word := sub_add_cancel _ _

end
end PaperC.Prel8.PrivateForcing
