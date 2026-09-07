import PaperCV282.PrimeFieldEventConditioning
import PaperCV282.InfiniteSoftTransfer
import PaperCV282.DyadicPoissonDistance

/-!
# Poisson transfer after a genuine small-prime conditioning event

The denominator is exactly the positive source probability of the chosen
F_Y event. The actual conditional law is a normalized mixture of the
selected equiprobable source atoms. This does not permit arbitrary selection on the
count itself, and does not claim the later path or rare-event asymptotics.
-/

namespace PaperC.V282.RestrictedPoissonTransfer

open MeasureTheory Set
open InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open InfiniteMaskedScalarTransfer PrimeFieldEventConditioning
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound SectionThirteenCouplings
open MaskedScalarCoupling AllStartSoftPoisson ScalarSteinInput
open SoftArithmeticTransfer DyadicPoissonDistance
open scoped BigOperators NNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- The literal source conditional law of the complete count on an event. -/
def restrictedCountLaw (N L : ℕ) (E : Set InfiniteSample) (k : ℕ) : ℝ :=
  infiniteRademacherMeasure.real ({omega | infiniteMaskedCount L (dyadicBlock N) omega = k} ∩ E) /
    infiniteRademacherMeasure.real E

/-- The actual event-conditioned law is the normalized mixture of its selected fibres. -/
theorem restrictedCountLaw_eq_selected_average (N L Y : ℕ)
    (S : Finset (SmallSample (dyadicCutoff N L) Y)) (hS : S.Nonempty) :
    restrictedCountLaw N L (primeFieldEvent (dyadicCutoff N L) Y S) =
      fun k => finiteUniformAverage (fun sigma : {sigma // sigma ∈ S} =>
        conditionalMaskedLaw N L Y (dyadicBlock N) sigma.val k) := by
  classical
  funext k
  unfold restrictedCountLaw
  rw [source_event_ratio_eq_atom_average _ _ S hS _
    (measurableSet_infiniteMaskedCount_event (dyadicBlock N) (Finset.Subset.refl _) k)]
  change (∑ sigma ∈ S,
    (infiniteRademacherMeasure ({omega | infiniteMaskedCount L (dyadicBlock N) omega = k} ∩
      infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal /
      (infiniteRademacherMeasure (infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal) /
      S.card = _
  simp_rw [← conditionalMaskedLaw_eq_infinite_atom_ratio (dyadicBlock N) (Finset.Subset.refl _)]
  rw [finiteUniformAverage, Fintype.card_coe,
    ← Finset.sum_subtype S (fun _ => Iff.rfl)
      (fun sigma => conditionalMaskedLaw N L Y (dyadicBlock N) sigma k)]

/-- The conditional source mass function is a probability law, with total mass one. -/
theorem hasSum_restrictedCountLaw_selected (N L Y : ℕ)
    (S : Finset (SmallSample (dyadicCutoff N L) Y)) (hS : S.Nonempty) :
    HasSum (restrictedCountLaw N L (primeFieldEvent (dyadicCutoff N L) Y S)) 1 := by
  obtain ⟨sigma, hsigma⟩ := hS
  letI : Nonempty {sigma // sigma ∈ S} := ⟨⟨sigma,hsigma⟩⟩
  rw [restrictedCountLaw_eq_selected_average N L Y S ⟨sigma,hsigma⟩]
  exact FiniteFieldTotalVariation.hasSum_uniformMixture _ (fun _ => hasSum_finiteNatLaw _ _)

/-- Keeping a positive set of atoms costs precisely the inverse of its source probability. -/
theorem selected_average_le_average_div_probability (C Y : ℕ)
    (S : Finset (SmallSample C Y)) (hS : S.Nonempty) (f : SmallSample C Y → ℝ)
    (hf : ∀ sigma, 0 ≤ f sigma) :
    finiteUniformAverage (fun sigma : {sigma // sigma ∈ S} => f sigma.val) ≤
      finiteUniformAverage f / infiniteRademacherMeasure.real (primeFieldEvent C Y S) := by
  classical
  rw [real_primeFieldEvent, finiteUniformAverage, finiteUniformAverage, Fintype.card_coe,
    ← Finset.sum_subtype S (fun _ => Iff.rfl) f]
  have htotal : (Fintype.card (SmallSample C Y) : ℝ) ≠ 0 := by positivity
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [show ((∑ sigma, f sigma) / (Fintype.card (SmallSample C Y) : ℝ)) /
      ((S.card : ℝ) / (Fintype.card (SmallSample C Y) : ℝ)) = (∑ sigma, f sigma) / S.card by
        field_simp]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun sigma _ _ => hf sigma)) hcard.le

/-- Convexity plus the exact event mass controls the genuine conditional count law. -/
theorem selected_event_tv_le_conditionalDistance (N L Y : ℕ)
    (S : Finset (SmallSample (dyadicCutoff N L) Y)) (hS : S.Nonempty) :
    natTotalVariation (restrictedCountLaw N L (primeFieldEvent (dyadicCutoff N L) Y S))
      (poissonMass (fullRate N L)) ≤
      conditionalDistance N L Y / infiniteRademacherMeasure.real (primeFieldEvent (dyadicCutoff N L) Y S) := by
  obtain ⟨sigma, hsigma⟩ := hS
  letI : Nonempty {sigma // sigma ∈ S} := ⟨⟨sigma,hsigma⟩⟩
  rw [restrictedCountLaw_eq_selected_average N L Y S ⟨sigma,hsigma⟩]
  apply (natTotalVariation_uniformMixture_le
    (fun sigma : {sigma // sigma ∈ S} => conditionalMaskedLaw N L Y (dyadicBlock N) sigma.val)
    (poissonMass (fullRate N L)) (fun sigma =>
      summable_abs_sub_of_nonneg (summable_finiteNatLaw _ _) (hasSum_poissonMass _).summable
        (finiteNatLaw_nonneg _ _) (poissonMass_nonneg _))).trans
  exact selected_average_le_average_div_probability _ _ S ⟨sigma,hsigma⟩ _
    (fun _ => natTotalVariation_nonneg _ _)

/-- Every genuine positive F_Y event receives the same exact inverse-probability bound. -/
theorem event_tv_le_conditionalDistance {N L Y : ℕ} (hYcut : Y ≤ dyadicCutoff N L)
    (E : Set InfiniteSample)
    (hE : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] E)
    (hpos : 0 < infiniteRademacherMeasure.real E) :
    natTotalVariation (restrictedCountLaw N L E) (poissonMass (fullRate N L)) ≤
      conditionalDistance N L Y / infiniteRademacherMeasure.real E := by
  rw [← smallPrimeSigmaAlgebra_eq_primeCylinder hYcut] at hE
  obtain ⟨S,rfl⟩ := measurableSet_eq_primeFieldEvent hE
  exact selected_event_tv_le_conditionalDistance N L Y S
    ((real_primeFieldEvent_pos_iff _ _ S).mp hpos)

/-- The arbitrary positive F_Y restriction is still a genuine probability law. -/
theorem hasSum_restrictedCountLaw {N L Y : ℕ} (hYcut : Y ≤ dyadicCutoff N L)
    (E : Set InfiniteSample)
    (hE : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] E)
    (hpos : 0 < infiniteRademacherMeasure.real E) :
    HasSum (restrictedCountLaw N L E) 1 := by
  rw [← smallPrimeSigmaAlgebra_eq_primeCylinder hYcut] at hE
  obtain ⟨S,rfl⟩ := measurableSet_eq_primeFieldEvent hE
  exact hasSum_restrictedCountLaw_selected N L Y S
    ((real_primeFieldEvent_pos_iff _ _ S).mp hpos)

/-- Companion B.3's restriction applied to the true free-cutoff soft arithmetic ledger. -/
theorem event_tv_le_soft_budget (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hYcut : Y ≤ dyadicCutoff N L) (E : Set InfiniteSample)
    (hE : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] E)
    (hpos : 0 < infiniteRademacherMeasure.real E) :
    natTotalVariation (restrictedCountLaw N L E) (poissonMass (fullRate N L)) ≤
      softArithmeticBudget N L Y / infiniteRademacherMeasure.real E := by
  apply (event_tv_le_conditionalDistance hYcut E hE hpos).trans
  exact div_le_div_of_nonneg_right
    (average_conditionalMaskedLaw_soft_le hStein hN hL hLY) hpos.le

end
end PaperC.V282.RestrictedPoissonTransfer
