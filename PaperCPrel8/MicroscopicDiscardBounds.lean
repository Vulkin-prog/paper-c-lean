import PaperCPrel8.IndependentScalarTail
import PaperCV282.MesoscopicPrefixMass
import PaperC.Probability.MarkedDetruncation

/-! # Independent source bounds for deletion and excess truncation

The first-moment input predates the microscopic field theorem. All masks and
positive conditioning events are quantified after the common scale threshold.
The two signs are included in a single exact-length event, without a factor two.
-/
namespace PaperC.Prel8.MicroscopicDiscardBounds
open MeasureTheory Set PaperC.InfiniteRademacher
open PaperC.Prel8.IndependentScalarTail PaperC.InfiniteStartProbabilityTransfer
open PaperC.V282.MesoscopicPrefixMass PaperC.V282.LaishramUniformInput
open PaperC.V282.PostQuadraticLiterature PaperC.V282.PrimeEulerPNT
open PaperC.ExactLengthDecomposition PaperC.MixedLengthAffine
open PaperC.InfiniteExactLengthProbabilityTransfer
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Arbitrary finite start masks obey the source union bound. -/
theorem hit_probability_le_first_moment (K : ℕ) (mask : Finset ℕ) :
    infiniteRademacherMeasure.real (hitEvent K mask) ≤
      ∑ x ∈ mask, infiniteStartProbability x K := by
  have he : hitEvent K mask = ⋃ x ∈ mask, infiniteStartEvent x K := by
    ext ω
    simp [hitEvent_iff, infiniteStartEvent]
  rw [he]
  exact measureReal_biUnion_finset_le mask (fun x => infiniteStartEvent x K)

/-- Conditioning costs only the reciprocal probability, for any actual event. -/
theorem conditional_event_bound (A B : Set InfiniteSample)
    (hA : 0 < infiniteRademacherMeasure.real A) {b : ℝ}
    (hb : infiniteRademacherMeasure.real B ≤ b) :
    infiniteRademacherMeasure.real (A ∩ B) / infiniteRademacherMeasure.real A ≤
      b / infiniteRademacherMeasure.real A := by
  exact div_le_div_of_nonneg_right
    ((measureReal_mono Set.inter_subset_right (measure_ne_top _ _)).trans hb) hA.le

/-- A sharper independent masked hit bound needs no scalar Stein input. -/
theorem masked_hit_bound_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ K : ℕ,
      betaMin * Real.log M ≤ (K+1:ℝ) → (K+1:ℝ) ≤ betaMax * Real.log M →
      ∀ mask : Finset ℕ, (∀ x ∈ mask, 2 ≤ x ∧ x ≤ 2*M) →
      infiniteRademacherMeasure.real (hitEvent K mask) ≤ (mask.card:ℝ)/(2:ℝ)^K +
        2*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Mzero,h⟩ := masked_prefix_mass_eventually betaMin betaMax hbetaMin hbeta hLS hShorey hPNT hNR
  refine ⟨Mzero, ?_⟩
  intro M hM K hlo hhi mask hmask
  exact (hit_probability_le_first_moment K mask).trans (h M hM K (by simpa using hlo) (by simpa using hhi) mask hmask)

/-- Exact marks above the retained cutoff, allowing either sign and any finite mask. -/
def excessTail (L E : ℕ) (mask : Finset ℕ) : Set InfiniteSample :=
  {ω | ∃ x ∈ mask, ∃ e : ℕ, E < e ∧
    ExactLengthEvent (infiniteValueBit ω) x (excessRowCount L e)}

/-- The discarded mark event is a measurable countable union of actual cylinders. -/
theorem measurableSet_excessTail (L E : ℕ) (mask : Finset ℕ) :
    MeasurableSet (excessTail L E mask) := by
  have he : excessTail L E mask = ⋃ x ∈ mask, ⋃ e : ℕ, ⋃ (_ : E < e),
      infiniteExactLengthEvent x (excessRowCount L e) := by
    ext ω
    simp [excessTail, infiniteExactLengthEvent]
  rw [he]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun e => MeasurableSet.iUnion fun _ =>
      measurableSet_infiniteExactLengthEvent x (excessRowCount L e)

/-- A discarded excess forces an ordinary start at the shifted length. -/
theorem excessTail_subset_hit (L E : ℕ) (mask : Finset ℕ) :
    excessTail L E mask ⊆ hitEvent (L+E+1) mask := by
  rintro ω ⟨x,hx,e,he,hex⟩
  exact (hitEvent_iff _ _ _).mpr
    ⟨x,hx,exactLengthEvent_start_longer_of_excess_gt he hex⟩

/-- The true signed tail is bounded independently, uniformly before the mask and event. -/
theorem conditional_tail_bound_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L E : ℕ,
      betaMin * Real.log M ≤ (L+E+2:ℝ) → (L+E+2:ℝ) ≤ betaMax * Real.log M →
      ∀ mask : Finset ℕ, (∀ x ∈ mask, 2 ≤ x ∧ x ≤ 2*M) →
      ∀ A : Set InfiniteSample, 0 < infiniteRademacherMeasure.real A →
      infiniteRademacherMeasure.real (A ∩ excessTail L E mask) / infiniteRademacherMeasure.real A ≤
        ((mask.card:ℝ)/(2:ℝ)^(L+E+1) +
          2*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M)))) /
            infiniteRademacherMeasure.real A := by
  obtain ⟨Mzero,h⟩ := masked_hit_bound_eventually betaMin betaMax hbetaMin hbeta hLS hShorey hPNT hNR
  refine ⟨Mzero, ?_⟩
  intro M hM L E hlo hhi mask hmask A hA
  apply conditional_event_bound A _ hA
  apply (measureReal_mono (excessTail_subset_hit L E mask) (measure_ne_top _ _)).trans
  exact h M hM (L+E+1) (by push_cast; linarith) (by push_cast; linarith) mask hmask

/-- Any deleted set of starts satisfies the same uniform conditional first-moment bound. -/
theorem conditional_deleted_bound_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax * Real.log M →
      ∀ deleted : Finset ℕ, (∀ x ∈ deleted, 2 ≤ x ∧ x ≤ 2*M) →
      ∀ A : Set InfiniteSample, 0 < infiniteRademacherMeasure.real A →
      infiniteRademacherMeasure.real (A ∩ hitEvent L deleted) / infiniteRademacherMeasure.real A ≤
        ((deleted.card:ℝ)/(2:ℝ)^L +
          2*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M)))) /
            infiniteRademacherMeasure.real A := by
  obtain ⟨Mzero,h⟩ := masked_hit_bound_eventually betaMin betaMax hbetaMin hbeta hLS hShorey hPNT hNR
  exact ⟨Mzero, fun M hM L hlo hhi deleted hd A hA =>
    conditional_event_bound A _ hA (h M hM L hlo hhi deleted hd)⟩

/-- The cutoff budget gives the exponentially small conditional bulk tail directly. -/
theorem cutoff_bulk_tail_bound (L E : ℕ) {m a V : ℝ} (ha : 0 < a)
    (hcut : m / (2:ℝ)^L ≤ a * Real.exp (-V) * (2:ℝ)^(E+1)) :
    (m / (2:ℝ)^(L+E+1)) / a ≤ Real.exp (-V) := by
  apply (div_le_iff₀ ha).mpr
  apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(L+E+1))).mpr
  have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^L)).mp hcut
  convert hh using 1
  rw [show L+E+1=L+(E+1) by omega, pow_add]
  ring

end
end PaperC.Prel8.MicroscopicDiscardBounds
