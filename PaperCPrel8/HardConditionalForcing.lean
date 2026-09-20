import PaperCPrel8.PrimeForcing

/-! # Exact forcing after conditioning on the small primes

The conditioning event is an arbitrary predicate of the actual small-prime
trace, not just a single environment. We also retain the weighted identity,
which avoids disintegrating that trace and applies to soft tilts.
-/
namespace PaperC.Prel8.HardConditionalForcing
open PaperC.Prel8.PrimeForcing PaperC.Prel8.PivotGeometry
open PaperC.ConditionalStartProbability PaperC.V282.PrescribedValues
open PaperC.IndependentThinning PaperC.ArratiaGoldsteinGordonInput
open PaperC.V282.SteinFiniteExpectation
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {M Y : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The entire small-prime environment is fixed by the arithmetic forcing map. -/
theorem smallTrace_unchanged (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hqY : ∀ a, Y < (q a).val.val) (word : ι → F₂) (ω : SampleSpace M) :
    restrictSmall M Y (forceWord v q word ω) = restrictSmall M Y ω := by
  funext p
  exact forceWord_preserves_small v q word ω Y hqY p.val p.property

/-- Exact identity for every weight depending on the actual small-prime trace. -/
theorem weighted_conditional_identity (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (hqY : ∀ a, Y < (q a).val.val) (word : ι → F₂)
    (weight : SmallSample M Y → ℝ) (f : SampleSpace M → ℝ) :
    finitePMFExpectation (FinitePMF.uniform (SampleSpace M))
      (fun ω => weight (restrictSmall M Y ω) * f (forceWord v q word ω)) =
    finitePMFExpectation (FinitePMF.uniform (SampleSpace M))
      (fun ω => if valueSystem M v ω = word then weight (restrictSmall M Y ω)*f ω else 0) /
        (Fintype.card (ι → F₂) : ℝ)⁻¹ := by
  have h := uniform_conditional_expectation v q hq word
    (fun ω => weight (restrictSmall M Y ω)*f ω)
  simpa only [smallTrace_unchanged v q hqY] using h

/-- The mass of any word is `2^-card ι`, independently of every small-prime event. -/
theorem word_small_event_probability (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (hqY : ∀ a, Y < (q a).val.val) (word : ι → F₂) (A : SmallSample M Y → Prop) :
    eventProbability (FinitePMF.uniform (SampleSpace M))
      (fun ω => A (restrictSmall M Y ω) ∧ valueSystem M v ω = word) =
      eventProbability (FinitePMF.uniform (SampleSpace M)) (fun ω => A (restrictSmall M Y ω)) *
        (Fintype.card (ι → F₂) : ℝ)⁻¹ := by
  have h := weighted_conditional_identity v q hq hqY word (fun s => if A s then 1 else 0)
    (fun _ => 1)
  simp only [mul_one] at h
  rw [← finitePMFExpectation_indicator, ← finitePMFExpectation_indicator]
  have he : (fun ω : SampleSpace M => if valueSystem M v ω = word then
      (if A (restrictSmall M Y ω) then (1 : ℝ) else 0) else 0) =
      (fun ω => if A (restrictSmall M Y ω) ∧ valueSystem M v ω = word then 1 else 0) := by
    funext ω
    split_ifs <;> simp_all
  rw [he] at h
  have hc : (Fintype.card (ι → F₂) : ℝ)⁻¹ ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  convert ((eq_div_iff hc).mp h).symm using 1
  congr!

/-- Under any positive-probability small-prime event, forcing produces the full conditional law. -/
theorem hard_conditional_expectation (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (hqY : ∀ a, Y < (q a).val.val) (word : ι → F₂) (A : SmallSample M Y → Prop)
    (_hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace M))
      (fun ω => A (restrictSmall M Y ω))) (f : SampleSpace M → ℝ) :
    finitePMFExpectation (FinitePMF.uniform (SampleSpace M))
      (fun ω => if A (restrictSmall M Y ω) then f (forceWord v q word ω) else 0) /
      eventProbability (FinitePMF.uniform (SampleSpace M)) (fun ω => A (restrictSmall M Y ω)) =
    finitePMFExpectation (FinitePMF.uniform (SampleSpace M))
      (fun ω => if A (restrictSmall M Y ω) ∧ valueSystem M v ω = word then f ω else 0) /
      eventProbability (FinitePMF.uniform (SampleSpace M))
        (fun ω => A (restrictSmall M Y ω) ∧ valueSystem M v ω = word) := by
  have h := weighted_conditional_identity v q hq hqY word (fun s => if A s then 1 else 0) f
  simp only [ite_mul, one_mul, zero_mul] at h
  have he : (fun ω : SampleSpace M => if valueSystem M v ω = word then
      (if A (restrictSmall M Y ω) then f ω else 0) else 0) =
      (fun ω => if A (restrictSmall M Y ω) ∧ valueSystem M v ω = word then f ω else 0) := by
    funext ω
    split_ifs <;> simp_all
  rw [he] at h
  rw [h, word_small_event_probability v q hq hqY word A, div_div, mul_comm]

/-- All arithmetic and small-prime hypotheses are discharged by the actual odd-prime pivots. -/
theorem actual_window_hard_conditional {j B : ℕ} (hj : 0 < j) (hM : j+B ≤ M+1)
    (hY : 1 ≤ Y) (hBY : B ≤ Y)
    (hgood : ∀ a : Fin B, Y < OddPrimePivot.largestOddPrime (j+a.val))
    (word : Fin B → F₂) (A : SmallSample M Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace M))
      (fun ω => A (restrictSmall M Y ω))) (f : SampleSpace M → ℝ) :
    let q := cylinderPivot hj hM (fun a => hY.trans_lt (hgood a))
    finitePMFExpectation (FinitePMF.uniform (SampleSpace M))
      (fun ω => if A (restrictSmall M Y ω) then
        f (forceWord (fun a : Fin B => j+a.val) q word ω) else 0) /
      eventProbability (FinitePMF.uniform (SampleSpace M)) (fun ω => A (restrictSmall M Y ω)) =
    finitePMFExpectation (FinitePMF.uniform (SampleSpace M))
      (fun ω => if A (restrictSmall M Y ω) ∧
        valueSystem M (fun a : Fin B => j+a.val) ω = word then f ω else 0) /
      eventProbability (FinitePMF.uniform (SampleSpace M))
        (fun ω => A (restrictSmall M Y ω) ∧
          valueSystem M (fun a : Fin B => j+a.val) ω = word) := by
  dsimp only
  apply hard_conditional_expectation _ _ _ _ word A hA f
  · exact cylinderPivot_basis hj hM _ (fun a => hBY.trans (hgood a).le)
  · exact hgood

end
end PaperC.Prel8.HardConditionalForcing
