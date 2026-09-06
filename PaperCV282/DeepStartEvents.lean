import PaperCV282.DeepStartMass

/-! # Actual probability of deep starts below a free cutoff -/
namespace PaperC.V282.DeepStartEvents

open MeasureTheory InfiniteRademacher InfiniteStartProbabilityTransfer
open DeepStartMass PostQuadraticLiterature BalasubramanianShoreyInput
open scoped BigOperators

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The ordinary union bound uses the actual infinite start events. -/
theorem probability_any_start_le_mass (s : Finset ℕ) (L : ℕ) :
    infiniteRademacherMeasure.real (⋃ x ∈ s, infiniteStartEvent x L) ≤
      ∑ x ∈ s, infiniteStartProbability x L := by
  exact measureReal_biUnion_finset_le s (fun x => infiniteStartEvent x L)

/-- Every cutoff up to twice the ambient scale is controlled at once.
The interval starts strictly above 2L² and includes the upper integer cutoff. -/
theorem integer_cutoff_bound_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ theta K : ℝ, 0 ≤ K ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℕ) →
      (L + 1 : ℕ) ≤ betaMax * Real.log M →
      ∀ T : ℕ, T ≤ 2 * M →
      infiniteRademacherMeasure.real (⋃ x ∈ Finset.Ioc (2 * L ^ 2) T, infiniteStartEvent x L) ≤
        (T : ℝ) / (2 : ℝ) ^ L +
        Real.exp (K * ((L : ℝ) / Real.log L)) * (2 : ℝ) ^ (-gap (L + 1) theta) := by
  obtain ⟨theta, K, hK, Mmass, hmass⟩ := deep_mass_bound_eventually
    betaMin betaMax hbetaMin hbeta hShorey hPNT hNR
  obtain ⟨Ma, ha⟩ := CriticalWeightedDefect.admissible_eventually hbetaMin hbeta
  obtain ⟨Mh, hh⟩ := CriticalWeightedDefect.height_tends_to_infinity
    (c₂ := betaMax) hbetaMin 5
  refine ⟨theta, K, hK, max Mmass (max Ma Mh), ?_⟩
  intro M hM L hlo hup T hT
  have hLlarge := hh M (by omega) (L + 1) (ha M (by omega) (L + 1) ⟨hbetaMin,hbeta,hlo,hup⟩)
  have hm := hmass M (by omega) L hlo hup (Finset.Ioc (2 * L ^ 2) T) (by
    intro x hx
    obtain ⟨hxl, hxu⟩ := Finset.mem_Ioc.mp hx
    have hlocal : (L + 1) ^ 2 + 2 < 2 * L ^ 2 := by nlinarith
    exact ⟨by omega, by omega⟩)
  apply (probability_any_start_le_mass _ L).trans (hm.trans _)
  refine add_le_add ?_ le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (show (Finset.Ioc (2 * L ^ 2) T).card ≤ T by simp [Nat.card_Ioc])

/-- The literal real-cutoff event in (7.8), with a stronger exceptional term.
In particular the old harmless linear number of dyadic slices is unnecessary. -/
theorem equation_seven_eight
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ theta K : ℝ, 0 ≤ K ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℕ) →
      (L + 1 : ℕ) ≤ betaMax * Real.log M →
      ∀ delta : ℝ, 0 < delta → delta < 1 →
      infiniteRademacherMeasure.real
        {omega | ∃ x : ℕ, 2 * L ^ 2 < x ∧ (x : ℝ) < (M : ℝ) ^ delta ∧
          omega ∈ infiniteStartEvent x L} ≤
        (M : ℝ) ^ delta / (2 : ℝ) ^ L +
        Real.exp (K * ((L : ℝ) / Real.log L)) * (2 : ℝ) ^ (-gap (L + 1) theta) := by
  obtain ⟨theta, K, hK, Mzero, h⟩ := integer_cutoff_bound_eventually
    betaMin betaMax hbetaMin hbeta hShorey hPNT hNR
  refine ⟨theta, K, hK, max Mzero 1, ?_⟩
  intro M hM L hlo hup delta _hdelta hdeltaOne
  have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
  have hpower : (M : ℝ) ^ delta ≤ M := by
    simpa using Real.rpow_le_rpow_of_exponent_le hMone hdeltaOne.le
  have hT : ⌊(M : ℝ) ^ delta⌋₊ ≤ M :=
    Nat.floor_le_of_le hpower
  have hprob := h M (by omega) L hlo hup ⌊(M : ℝ) ^ delta⌋₊ (by omega)
  have hsubset :
      {omega | ∃ x : ℕ, 2 * L ^ 2 < x ∧ (x : ℝ) < (M : ℝ) ^ delta ∧
        omega ∈ infiniteStartEvent x L} ⊆
      ⋃ x ∈ Finset.Ioc (2 * L ^ 2) ⌊(M : ℝ) ^ delta⌋₊, infiniteStartEvent x L := by
    intro omega homega
    obtain ⟨x, hx, hxM, hxevent⟩ := homega
    apply Set.mem_iUnion.mpr
    refine ⟨x, Set.mem_iUnion.mpr ⟨Finset.mem_Ioc.mpr ⟨hx, ?_⟩, hxevent⟩⟩
    exact (Nat.le_floor_iff (Real.rpow_nonneg (by positivity) _)).mpr hxM.le
  apply (measureReal_mono hsubset (measure_ne_top _ _)).trans (hprob.trans _)
  refine add_le_add ?_ le_rfl
  exact div_le_div_of_nonneg_right (Nat.floor_le (Real.rpow_nonneg (by positivity) _)) (by positivity)

end
end PaperC.V282.DeepStartEvents
