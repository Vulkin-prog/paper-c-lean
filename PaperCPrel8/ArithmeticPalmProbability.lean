import PaperCPrel8.ArithmeticPalmCompletion

/-! # Actual Palm completion in mean and target-configuration probability -/
namespace PaperC.Prel8.ArithmeticPalmProbability
open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher
open ConditionalStartProbability V282.BulkMarkedTypes V282.FiniteFieldTotalVariation
open ArithmeticPalmMass ArithmeticPalmDeficit ArithmeticPalmNormalization
open PalmVoidAverage PalmDeficitProbability
noncomputable section
local instance : MeasurableSpace F₂ := ⊤
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The bounded lower relative-void defect, zero off the regular configurations. -/
def defect {C L E Y K : ℕ} (sites : Finset ℕ) (A : SmallSample C Y → Prop)
    (z : SpatialMarkedConfig sites) : ℝ :=
  if boundedRegular sites C L E Y K z then max (1-normalizedVoid sites L A z) 0 else 0

theorem defect_bounds {C L E Y K : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (z : SpatialMarkedConfig sites) :
    0≤defect (L := L) (E := E) (K := K) sites A z ∧ defect (L := L) (E := E) (K := K) sites A z≤1 := by
  unfold defect
  split_ifs
  · exact ⟨le_max_right _ _,max_le (by linarith [normalizedVoid_nonneg sites hL A z]) (by norm_num)⟩
  · norm_num

theorem mean_eq_void {C L E Y K : ℕ} (sites : Finset ℕ) (A : SmallSample C Y → Prop) :
    mean (targetMass sites L) (defect (L := L) (E := E) (K := K) sites A)=
      voidDeficit (targetMass sites L) (boundedRegular sites C L E Y K) (normalizedVoid sites L A) := by
  apply tsum_congr
  intro z
  by_cases hz : boundedRegular sites C L E Y K z <;> simp [defect,hz]

/-- G.5 for the actual arithmetic Palm ratios, on changing countable spaces.
The distance premise is the conclusion of 7.7 (or its deterministic restriction).
The normalization error has an independent literal-budget bound in PalmNormalizationRate. -/
theorem normalized_average_tendsto (sites : ℕ → Finset ℕ) (C L E Y K : ℕ → ℕ)
    (A : (M : ℕ) → SmallSample (C M) (Y M) → Prop)
    (hL : ∀ᶠ M in atTop, 1≤L M)
    (hA : ∀ᶠ M in atTop, 0 < infiniteRademacherMeasure.real
      (MicroscopicConditionalSpatial.traceEvent (C M) (Y M) (A M)))
    (hTV : Tendsto (fun M ↦ massTotalVariation (sourceMass (sites M) (L M) (A M))
      (targetMass (sites M) (L M))) atTop (𝓝 0))
    (hpen : Tendsto (fun M ↦ penalty (sites M) (L M) (K M)) atTop (𝓝 0)) :
    Tendsto (fun M ↦ voidDeficit (targetMass (sites M) (L M))
      (boundedRegular (sites M) (C M) (L M) (E M) (Y M) (K M))
      (normalizedVoid (sites M) (L M) (A M))) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa using hTV.add hpen)
  · filter_upwards [hL] with M hlen
    exact voidDeficit_nonneg (fun _ ↦ ENNReal.toReal_nonneg)
      (normalizedVoid_nonneg (sites M) hlen (A M)) _
  · filter_upwards [hL,hA] with M hlen hpos
    exact normalized_average_le (sites M) hlen (A M) hpos

/-- The same actual completion holds in target probability, with an explicit Markov bound. -/
theorem target_exceedance_bound {C L E Y K : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop)
    (hA : 0 < infiniteRademacherMeasure.real (MicroscopicConditionalSpatial.traceEvent C Y A))
    {t : ℝ} (ht : 0<t) :
    exceedance (targetMass sites L) (defect (L := L) (E := E) (K := K) sites A) t≤
      (massTotalVariation (sourceMass sites L A) (targetMass sites L)+penalty sites L K)/t := by
  have h := exceedance_le (hasSum_targetMass sites L).summable (fun _ ↦ ENNReal.toReal_nonneg)
    (defect_bounds (E := E) (K := K) sites hL A) ht
  rw [mean_eq_void] at h
  exact h.trans (div_le_div_of_nonneg_right (normalized_average_le sites hL A hA) ht.le)

/-- Vanishing in target probability follows directly under the same actual-law hypotheses. -/
theorem target_probability_tendsto (sites : ℕ → Finset ℕ) (C L E Y K : ℕ → ℕ)
    (A : (M : ℕ) → SmallSample (C M) (Y M) → Prop)
    (hL : ∀ᶠ M in atTop, 1≤L M)
    (hA : ∀ᶠ M in atTop, 0 < infiniteRademacherMeasure.real
      (MicroscopicConditionalSpatial.traceEvent (C M) (Y M) (A M)))
    (hTV : Tendsto (fun M ↦ massTotalVariation (sourceMass (sites M) (L M) (A M))
      (targetMass (sites M) (L M))) atTop (𝓝 0))
    (hpen : Tendsto (fun M ↦ penalty (sites M) (L M) (K M)) atTop (𝓝 0))
    {t : ℝ} (ht : 0<t) :
    Tendsto (fun M ↦ exceedance (targetMass (sites M) (L M))
      (defect (L := L M) (E := E M) (K := K M) (sites M) (A M)) t) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun M ↦ exceedance_nonneg (fun _ ↦ ENNReal.toReal_nonneg) t))
  · filter_upwards [hL,hA] with M hlen hpos
    exact target_exceedance_bound (sites M) hlen (A M) hpos ht
  · simpa using (hTV.add hpen).div_const t

end
end PaperC.Prel8.ArithmeticPalmProbability
