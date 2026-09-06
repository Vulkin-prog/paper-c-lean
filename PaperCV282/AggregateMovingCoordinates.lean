import PaperCV282.SignedAggregateHardBudget

/-!
# The actual aggregated fields in moving integer coordinates

The excess-to-level change is a bijection, including the sign coordinate.
Both conditional distances and the distance of the whole threshold path are
preserved exactly. No probabilistic independence is inferred by splitting an
unsigned law: the signed target is the image of the previously proved signed
aggregate target.
-/
namespace PaperC.V282.AggregateMovingCoordinates

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open MovingMarkedLevels GrowingLevelParameters SignedAggregateConfiguration
open SignedAggregateTruncation UnsignedAggregateComparison SignedAggregateHardBudget
open ConditionedCountableLaw InfiniteMassCoupling FiniteFieldTotalVariation MassPushforward
open AllStartSoftPoisson RareConditioningRates AggregateInformationBudget HardPoissonRates
open SaddleParameters SaddleScales DirectionalSteinInput PrimeEulerPNT
open ThresholdPathEquivalence InfiniteStartProbabilityTransfer

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

def signedLevelConfigEquiv (d : ℕ) : SignedAggregateConfig ≃ (MovingLevel d × F₂ →₀ ℕ) :=
  Finsupp.equivCongrLeft (Equiv.prodCongr (levelEquiv d) (Equiv.refl F₂))

def unsignedLevelConfigEquiv (d : ℕ) : (ℕ →₀ ℕ) ≃ (MovingLevel d →₀ ℕ) :=
  Finsupp.equivCongrLeft (levelEquiv d)

theorem signedLevelConfigEquiv_apply (d : ℕ) (k : SignedAggregateConfig) (e : ℕ) (s : F₂) :
    signedLevelConfigEquiv d k (levelEquiv d e,s)=k (e,s) := by
  simp [signedLevelConfigEquiv,Finsupp.equivCongrLeft_apply,Finsupp.equivMapDomain_apply]

theorem unsignedLevelConfigEquiv_apply (d : ℕ) (k : ℕ →₀ ℕ) (e : ℕ) :
    unsignedLevelConfigEquiv d k (levelEquiv d e)=k e := by
  simp [unsignedLevelConfigEquiv,Finsupp.equivCongrLeft_apply,Finsupp.equivMapDomain_apply]

def signedMovingAggregateSource (N d : ℕ) :=
  signedLevelConfigEquiv d ∘ signedAggregateSource N (movingLength N d)

def unsignedMovingAggregateSource (N d : ℕ) :=
  unsignedLevelConfigEquiv d ∘ unsignedAggregateSource N (movingLength N d)

theorem signedMovingAggregateSource_apply (N d e : ℕ) (s : F₂) (omega : InfiniteSample) :
    signedMovingAggregateSource N d omega (levelEquiv d e,s)=
      signedAggregateSource N (movingLength N d) omega (e,s) :=
  signedLevelConfigEquiv_apply d _ e s

theorem unsignedMovingAggregateSource_apply (N d e : ℕ) (omega : InfiniteSample) :
    unsignedMovingAggregateSource N d omega (levelEquiv d e)=
      unsignedAggregateSource N (movingLength N d) omega e :=
  unsignedLevelConfigEquiv_apply d _ e

/-- A bijective change of the observed value commutes with the actual conditional law. -/
theorem conditionalObservableLaw_equiv_eq {Ω α β : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (A : Set Ω) (f : Ω → α) (e : α ≃ β) :
    conditionalObservableLaw mu A (e ∘ f)=pushforwardMass e (conditionalObservableLaw mu A f) := by
  funext b
  rw [pushforwardMass_equiv]
  unfold conditionalObservableLaw observableLaw
  congr 1
  ext omega
  exact e.apply_eq_iff_eq_symm_apply

def signedMovingAggregateDistance (N d : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTotalVariation
    (conditionalObservableLaw infiniteRademacherMeasure A (signedMovingAggregateSource N d))
    (pushforwardMass (signedLevelConfigEquiv d) (signedAggregateTargetLaw N (movingLength N d)))

def unsignedMovingAggregateDistance (N d : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTotalVariation
    (conditionalObservableLaw infiniteRademacherMeasure A (unsignedMovingAggregateSource N d))
    (pushforwardMass (unsignedLevelConfigEquiv d) (geometricConfigurationLaw (fullRate N (movingLength N d))))

/-- Positivity is unnecessary for this identity; positive events are required by the comparison. -/
theorem signedMovingAggregateDistance_eq (N d : ℕ) (A : Set InfiniteSample) :
    signedMovingAggregateDistance N d A=
      conditionalSignedAggregateDistance N (movingLength N d) A := by
  unfold signedMovingAggregateDistance signedMovingAggregateSource
  rw [conditionalObservableLaw_equiv_eq]
  exact massTotalVariation_equiv _ _ _

theorem unsignedMovingAggregateDistance_eq (N d : ℕ) (A : Set InfiniteSample) :
    unsignedMovingAggregateDistance N d A=
      conditionalUnsignedAggregateDistance N (movingLength N d) A := by
  unfold unsignedMovingAggregateDistance unsignedMovingAggregateSource
  rw [conditionalObservableLaw_equiv_eq]
  exact massTotalVariation_equiv _ _ _

/-- The true signed category mean, now at any retained integer level r. -/
theorem signed_target_level_mean {N d : ℕ} (hN : 1≤N) (hd : d≤criticalBase N)
    (r : MovingLevel d) :
    (fullRate N (movingLength N d) : ℝ)/(2 : ℝ)^((levelEquiv d).symm r+2)=
      (2 : ℝ)^(dyadicPhase N-(r.val : ℝ)-2) := by
  simpa using signed_level_mean hN hd ((levelEquiv d).symm r)

theorem unsigned_target_level_mean {N d : ℕ} (hN : 1≤N) (hd : d≤criticalBase N)
    (r : MovingLevel d) :
    (fullRate N (movingLength N d) : ℝ)/(2 : ℝ)^((levelEquiv d).symm r+1)=
      (2 : ℝ)^(dyadicPhase N-(r.val : ℝ)-1) := by
  simpa using exact_level_mean hN hd ((levelEquiv d).symm r)

/-- Renaming the argument of an entire path is also a bijection. -/
def levelPathEquiv (d : ℕ) : (ℕ → ℕ) ≃ (MovingLevel d → ℕ) :=
  Equiv.arrowCongr (levelEquiv d) (Equiv.refl ℕ)

theorem levelPathEquiv_apply (d : ℕ) (f : ℕ → ℕ) (r : MovingLevel d) :
    levelPathEquiv d f r=f ((levelEquiv d).symm r) := rfl

/-- The literal whole path has the same distance as the true moving exact counts. -/
theorem conditional_moving_path_distance_eq {N d : ℕ} (hN : 2≤N) (A : Set InfiniteSample) :
    massTotalVariation
      (conditionalObservableLaw infiniteRademacherMeasure A
        (fun omega r => infiniteDyadicStartCount N
          (movingLength N d+(levelEquiv d).symm r) omega))
      (pushforwardMass (levelPathEquiv d)
        (pushforwardMass thresholdFunction (geometricConfigurationLaw (fullRate N (movingLength N d)))))=
      unsignedMovingAggregateDistance N d A := by
  change massTotalVariation
    (conditionalObservableLaw infiniteRademacherMeasure A
      (levelPathEquiv d ∘ (fun omega m => infiniteDyadicStartCount N (movingLength N d+m) omega))) _=_
  rw [conditionalObservableLaw_equiv_eq,massTotalVariation_equiv]
  rw [conditional_path_distance_eq hN,unsignedMovingAggregateDistance_eq]

/-- The path indexed by r is the start count at the physical length b_N+r. -/
theorem moving_threshold_length {N d : ℕ} (hd : d≤criticalBase N) (r : MovingLevel d) :
    ((movingLength N d+(levelEquiv d).symm r : ℕ) : ℤ)=
      (criticalBase N : ℤ)+r.val := by
  simpa only [Equiv.apply_symm_apply,movingLength] using
    runLength_eq (criticalBase N) d ((levelEquiv d).symm r) hd

/-- The signed aggregate conclusion of 5.9 in its literal (r,s) coordinates. -/
theorem corollary_five_nine_aggregate_sequences (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (c : ℝ) (hc : 0<c)
    (sizes depths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hdepths : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,
      aggregateLogCost (eventInformation (A n)) (fullRate (sizes n) (movingLength (sizes n) (depths n)))≤
        saddleCutoff 1 (Real.log (sizes n))-c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => signedMovingAggregateDistance (sizes n) (depths n) (A n)) atTop (𝓝 0) ∧
    Tendsto (fun n => unsignedMovingAggregateDistance (sizes n) (depths n) (A n)) atTop (𝓝 0) := by
  simpa only [signedMovingAggregateDistance_eq,unsignedMovingAggregateDistance_eq] using
    theorem_five_eight_aggregate_hard_sequences hStein hPNT c hc sizes depths hsizes hdepths A hA hpos hbudget

end
end PaperC.V282.AggregateMovingCoordinates
