import PaperCPrel8.MicroscopicInfiniteField

/-! # F.7 as an equality of complete conditional distributions -/
namespace PaperC.Prel8.ActualSignedConditionalLaw
open PaperC.Prel8.ActualSignedPalm PaperC.Prel8.SignedPalmForcing
open PaperC.Prel8.FiniteConditioning PaperC.Prel8.HardConditionalForcing
open PaperC.Prel8.PrimeForcing PaperC.Prel8.PalmStein
open PaperC.ConditionalStartProbability PaperC.V282.ExactMarkedModel
open PaperC.V282.SignedExactMarks PaperC.ArratiaGoldsteinGordonInput PaperC.IndependentThinning
open PaperC.V282.SteinFiniteExpectation PaperC.V282.InfiniteFieldTransfer
open PaperC.V282.FiniteFieldTotalVariation
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E : ℕ} {G : Finset ℕ}

/-- The conditional source marginal is exactly its geometric mark rate. -/
theorem mark_probability (h : GoodGeometry C Y L E G) (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) (i : Index G E) :
    eventProbability (sourceLaw A hA)
      (fun ω => SignedExactMark (valueBit ω) (i.1.val+1) L i.2.1.val i.2.2) = rate L i := by
  change eventProbability (conditional _ _ hA) _ = _
  rw [probability_conditional]
  have hb : L+i.2.1.val+2 ≤ Y := by have := h.support_le; have := i.2.1.isLt; omega
  rw [actual_signed_small_probability (h.start_pos _ i.1.property) h.length_pos
    (mark_cylinder h i) h.cutoff_pos hb (mark_good h i) i.2.2 A]
  exact mul_div_cancel_left₀ _ hA.ne'

/-- Each exact mark has positive mass after conditioning on the small-prime event. -/
theorem mark_probability_pos (h : GoodGeometry C Y L E G) (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) (i : Index G E) :
    0 < eventProbability (sourceLaw A hA)
      (fun ω => SignedExactMark (valueBit ω) (i.1.val+1) L i.2.1.val i.2.2) := by
  rw [mark_probability h A hA]
  change 0 < 1/(2:ℝ)^(L+i.2.1.val+2)
  positivity

/-- F.7: the forced whole-vector distribution is its actual mark-conditioned distribution. -/
theorem whole_field_conditional_law (h : GoodGeometry C Y L E G) (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) (i : Index G E) :
    finiteFieldLaw (sourceLaw A hA) (coupledField h i) =
      finiteFieldLaw (conditional (sourceLaw A hA)
        (fun ω => SignedExactMark (valueBit ω) (i.1.val+1) L i.2.1.val i.2.2)
        (mark_probability_pos h A hA i)) (field C L E G) := by
  funext z
  have hp := actual_palm_law h A hA i (fun v => if v=z then 1 else 0)
  have he : finitePMFExpectation (sourceLaw A hA)
      (fun ω => (field C L E G ω i : ℝ) * (if field C L E G ω=z then 1 else 0)) =
      eventProbability (sourceLaw A hA) (fun ω =>
        SignedExactMark (valueBit ω) (i.1.val+1) L i.2.1.val i.2.2 ∧ field C L E G ω=z) := by
    simp only [finitePMFExpectation, eventProbability, field, signedMarkValue]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp_all
  have hl : finitePMFExpectation (sourceLaw A hA)
      (fun ω => if coupledField h i ω = z then (1:ℝ) else 0) =
      eventProbability (sourceLaw A hA) (fun ω => coupledField h i ω = z) := by
    simp only [finitePMFExpectation, eventProbability]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hz : coupledField h i ω = z <;> simp [hz]
  rw [he, hl] at hp
  rw [finiteFieldLaw_eq_eventProbability, finiteFieldLaw_eq_eventProbability,
    probability_conditional, mark_probability h A hA]
  have hr : (rate L i : ℝ) ≠ 0 := by
    change (1/(2:ℝ)^(L+i.2.1.val+2)) ≠ 0
    positivity
  exact (eq_div_iff hr).mpr (by simpa only [mul_comm] using hp)

/-- An already satisfied marked word fixes the complete prime sample. -/
theorem force_fixes (h : GoodGeometry C Y L E G) (i : Index G E) (ω : SampleSpace C)
    (hi : SignedExactMark (valueBit ω) (i.1.val+1) L i.2.1.val i.2.2) :
    force h i ω = ω :=
  forceWord_fixes _ _ _ ω ((signedWord_iff h.length_pos i.2.2 ω).mpr hi)

/-- The complete small-prime trace is unchanged, rather than just the event used to condition. -/
theorem force_preserves_small_trace (h : GoodGeometry C Y L E G) (i : Index G E)
    (ω : SampleSpace C) : restrictSmall C Y (force h i ω) = restrictSmall C Y ω :=
  smallTrace_unchanged _ (pivots h i) (mark_good h i) _ ω

end
end PaperC.Prel8.ActualSignedConditionalLaw
