import PaperCV282.CrossoverPrimeClockStable
import PaperCV282.PrimeClockMicroscopicTransfer
import PaperCV282.SpatialDiffuseMarks

/-! # Exact finite and tail laws for the actual prime clock used in the crossover -/
namespace PaperC.V282.CrossoverPrimeClockLaw

open MeasureTheory ProbabilityTheory InfiniteRademacher MicroscopicBorderEvents
open PrimeClockDistribution PrimeClockMicroscopicTransfer GeometricClusterTarget SpatialDiffuseMarks
open CrossoverPrimeClockStable CrossoverPrimeClockBase CrossoverPrimeClockCylinder

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem actualClockRecord_off_border {L K : ℕ} {omega : InfiniteSample}
    (hb : omega ∉ borderEvent L) : actualClockRecord L K omega=(false,0) := by
  simp [actualClockRecord,primeOvershoot,hb]

/-- Conditioning the real source on its border gives the geometric clock, capped at K. -/
theorem conditional_actualClockRecord (L K : ℕ) :
    (cond infiniteRademacherMeasure (borderEvent L)).map (actualClockRecord L K)=
      (geometricMeasure halfSuccess).map (fun G => (true,min G K)) := by
  rw [← conditionalPrimeClockLaw_eq_geometric L,conditionalPrimeClockLaw,
    Measure.map_map (measurable_of_countable _) (measurable_primeOvershoot L)]
  apply Measure.map_congr
  filter_upwards [ae_cond_mem (μ := infiniteRademacherMeasure) (measurableSet_borderEvent L)] with omega hb
  simp [actualClockRecord,hb]

theorem geometric_partial_mass (K : ℕ) :
    (∑ e ∈ Finset.range K, (geometricMeasure halfSuccess).real {e})=1-1/(2 : ℝ)^K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ,ih,geometric_excess_real,pow_succ]
    field_simp
    ring

theorem geometric_survival (K : ℕ) :
    (geometricMeasure halfSuccess).real {G : ℕ | K ≤ G}=1/(2 : ℝ)^K := by
  have he : {G : ℕ | K ≤ G}=(Finset.range K : Set ℕ)ᶜ := by ext G; simp
  rw [he,measureReal_compl (Finset.measurableSet _),probReal_univ,
    ← sum_measureReal_singleton,geometric_partial_mass]
  ring

theorem geometric_strict_tail (K : ℕ) :
    (geometricMeasure halfSuccess).real {G : ℕ | K < G}=1/(2 : ℝ)^(K+1) := by
  exact geometric_survival (K+1)

/-- The discarded prime-clock mass is exact, for the actual normalized source law. -/
theorem conditional_prime_clock_survival (L K : ℕ) :
    (cond infiniteRademacherMeasure (borderEvent L)).real {omega | K ≤ primeOvershoot L omega}=
      1/(2 : ℝ)^K := by
  have he := congrArg (fun mu : Measure ℕ => mu.real {G | K ≤ G})
    (conditionalPrimeClockLaw_eq_geometric L)
  rw [conditionalPrimeClockLaw,map_measureReal_apply (measurable_primeOvershoot L)
    (Set.to_countable _).measurableSet,geometric_survival] at he
  exact he

/-- This finite intersection is the input needed before rare-event normalization. -/
theorem border_prime_clock_tail (L K : ℕ) :
    infiniteRademacherMeasure.real (borderEvent L ∩ {omega | K ≤ primeOvershoot L omega})=
      infiniteRademacherMeasure.real (borderEvent L)/(2 : ℝ)^K := by
  have he := conditional_prime_clock_survival L K
  rw [SharpConditioning.cond_real_apply _ _ (measurableSet_borderEvent L)] at he
  exact (div_eq_iff (borderEvent_probability_pos L).ne').mp he |>.trans (by ring)

end
end PaperC.V282.CrossoverPrimeClockLaw
