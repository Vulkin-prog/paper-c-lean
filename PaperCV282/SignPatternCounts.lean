import PaperCV282.SignPatternRates
import PaperCV282.DictionaryCountTargets

/-!
# Actual counts of words up to a common sign

The statistic is the indicator of the union of the two disjoint word events.
The target mean is the mask cardinality times 2^(-L), proved by aggregation
of the two labelled Poisson coordinates, rather than assumed independence.
-/

namespace PaperC.V282.SignPatternCounts

open SignDictionary SignOverlap SignPatternRates DictionaryCountTargets
open DictionaryFieldModel DictionaryFieldInfinite InfiniteWordTransfer InfiniteRademacher
open InfiniteConditionalWords ConditionalStartProbability ConditionalAGGAverage
open SectionThirteenFiniteBound FiniteFieldTotalVariation ScalarSteinInput
open HardPoissonRates PrimeEulerPNT ProcessAGGInput Filter Topology MeasureTheory
open scoped BigOperators NNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Actual occurrences of a word up to one common sign, on the selected sites. -/
def signPatternCount {L : ℕ} (a : Fin (L+1) → F₂) (mask : Finset ℕ)
    (omega : InfiniteSample) : ℕ := by
  classical
  exact ∑ x ∈ mask, if omega ∈ infiniteWordEvent x (L+1) a ∨
    omega ∈ infiniteWordEvent x (L+1) (oppositeWord a) then 1 else 0

def signPatternRate (L : ℕ) (mask : Finset ℕ) : ℝ≥0 :=
  ⟨mask.card/(2 : ℝ)^L,by positivity⟩

/-- Total variation for the true infinite source count and its exact Poisson mean. -/
def signCountDistance {L : ℕ} (a : Fin (L+1) → F₂) (mask : Finset ℕ) : ℝ :=
  massTotalVariation
    (fun b => (infiniteRademacherMeasure {omega | signPatternCount a mask omega=b}).toReal)
    (poissonMass (signPatternRate L mask))

/-- The actual normalized conditional laws on the small-prime atoms. -/
def conditionalSignCountDistance (N L Y : ℕ) (a : Fin (L+1) → F₂) (mask : Finset ℕ) : ℝ :=
  finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
    massTotalVariation
      (fun b => (infiniteRademacherMeasure
        ({omega | signPatternCount a mask omega=b} ∩
          infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal /
        (infiniteRademacherMeasure (infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal)
      (poissonMass (signPatternRate L mask)))

/-- Summing the two labelled indicators equals the genuine union-event indicator. -/
theorem sum_sign_indicators {L : ℕ} (a : Fin (L+1) → F₂) (x : ℕ) (omega : InfiniteSample) :
    (∑ b ∈ signDictionary a, if omega ∈ infiniteWordEvent x (L+1) b then 1 else 0 : ℕ) =
      if omega ∈ infiniteWordEvent x (L+1) a ∨
        omega ∈ infiniteWordEvent x (L+1) (oppositeWord a) then 1 else 0 := by
  classical
  have hmem : a ∉ ({oppositeWord a} : Finset (Fin (L+1) → F₂)) := by
    simpa using Ne.symm (oppositeWord_ne (by omega) a)
  simp only [signDictionary,Finset.sum_insert hmem,Finset.sum_singleton]
  have hdis := Set.disjoint_left.mp (sign_events_disjoint (by omega) x a)
  by_cases ha : omega ∈ infiniteWordEvent x (L+1) a <;>
    by_cases hb : omega ∈ infiniteWordEvent x (L+1) (oppositeWord a)
  · exact False.elim (hdis ha hb)
  · simp [ha,hb]
  · simp [ha,hb]
  · simp [ha,hb]

/-- Exact identification of the selected field statistic with the source union count. -/
theorem maskedDictionaryCount_sign_eq {N L : ℕ} (a : Fin (L+1) → F₂)
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (omega : InfiniteSample) :
    maskedDictionaryCount (signDictionary a) mask
      (infiniteDictionaryField N L (signDictionary a) omega) = signPatternCount a mask omega := by
  classical
  unfold maskedDictionaryCount
  change (∑ i : {x // x ∈ dyadicBlock N} × {b // b ∈ signDictionary a},
    if i.1.val ∈ mask then
      (if omega ∈ infiniteWordEvent i.1.val (L+1) i.2.val then 1 else 0) else 0) = _
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  have hword (x : {x // x ∈ dyadicBlock N}) :
      (∑ b : {b // b ∈ signDictionary a},
        if omega ∈ infiniteWordEvent x.val (L+1) b.val then 1 else 0 : ℕ) =
        if omega ∈ infiniteWordEvent x.val (L+1) a ∨
          omega ∈ infiniteWordEvent x.val (L+1) (oppositeWord a) then 1 else 0 := by
    rw [← Finset.sum_subtype (signDictionary a) (fun _ => Iff.rfl)
      (fun b => if omega ∈ infiniteWordEvent x.val (L+1) b then (1 : ℕ) else 0)]
    exact sum_sign_indicators a x.val omega
  simp_rw [hword]
  rw [← Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl)
    (fun x => if x ∈ mask then (if omega ∈ infiniteWordEvent x (L+1) a ∨
      omega ∈ infiniteWordEvent x (L+1) (oppositeWord a) then (1 : ℕ) else 0) else 0),
    ← Finset.sum_filter]
  have hf : (dyadicBlock N).filter (fun x => x ∈ mask) = mask := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hx => ⟨hmask hx,hx⟩⟩
  rw [hf]
  rfl

theorem maskedDictionaryTargetRate_sign (L : ℕ) (a : Fin (L+1) → F₂) (mask : Finset ℕ) :
    maskedDictionaryTargetRate L (signDictionary a) mask = signPatternRate L mask := by
  apply NNReal.coe_injective
  rw [maskedDictionaryTargetRate_coe,card_signDictionary (by omega),pow_succ]
  change (mask.card : ℝ)*2/((2 : ℝ)^L*2) = mask.card/(2 : ℝ)^L
  field_simp

/-- Scalar aggregation contracts the actual infinite field distance. -/
theorem signCountDistance_le_field {N L : ℕ} (a : Fin (L+1) → F₂)
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    signCountDistance a mask ≤ dictionaryDistance N L (signDictionary a) := by
  have h := infinite_dictionary_count_distance_le (signDictionary a) mask hmask
  simp_rw [maskedDictionaryCount_sign_eq a mask hmask,maskedDictionaryTargetRate_sign] at h
  exact h

/-- The same contraction applies to averages of genuine conditional atom laws. -/
theorem conditionalSignCountDistance_le_field {N L Y : ℕ} (a : Fin (L+1) → F₂)
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    conditionalSignCountDistance N L Y a mask ≤
      dictionaryConditionalDistance N L Y (signDictionary a) := by
  have h := average_dictionary_count_distance_le (Y := Y) (signDictionary a) mask hmask
  simp_rw [maskedDictionaryCount_sign_eq a mask hmask,maskedDictionaryTargetRate_sign] at h
  exact h

/-- Equation (5.10), including every deterministic spatial mask and its exact mean. -/
theorem corollary_five_five (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C epsilon eta : ℝ)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∀ a : Fin (L+1) → F₂, ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
        signCountDistance a mask ≤
          8*signPatternCoefficient (Real.exp (C*Real.log 2))*signPatternError N a epsilon eta ∧
        conditionalSignCountDistance N L (hardCutoff N) a mask ≤
          8*signPatternCoefficient (Real.exp (C*Real.log 2))*signPatternError N a epsilon eta := by
  obtain ⟨Nzero,hzero⟩ := sign_field_rate_eventually hAGG hPNT C epsilon eta hepsilon heta
  refine ⟨Nzero,?_⟩
  intro N hN L hw a mask hmask
  obtain ⟨hc,hu⟩ := hzero N hN L hw a
  exact ⟨(signCountDistance_le_field a mask hmask).trans hu,
    (conditionalSignCountDistance_le_field a mask hmask).trans hc⟩

/-- In particular, the full dyadic target mean is N*2^(-L). -/
theorem signPatternRate_dyadic (N L : ℕ) :
    (signPatternRate L (dyadicBlock N) : ℝ) = (N : ℝ)/(2 : ℝ)^L := by
  change ((dyadicBlock N).card : ℝ)/(2 : ℝ)^L = _
  rw [TouchingPairs.card_dyadicBlock]

/-- The least compatible shift criterion also applies to arbitrary varying spatial masks. -/
theorem masked_sign_count_convergence (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C : ℝ)
    (L : ℕ → ℕ) (a : ∀ N : ℕ, Fin (L N+1) → F₂) (mask : ℕ → Finset ℕ)
    (hwindow : ∀ᶠ N : ℕ in atTop, |(L N : ℝ)-Real.log N/Real.log 2| ≤ C)
    (hmasks : ∀ᶠ N : ℕ in atTop, mask N ⊆ dyadicBlock N)
    (hshift : Tendsto (fun N => leastCompatibleShift (a N)) atTop atTop) :
    Tendsto (fun N => signCountDistance (a N) (mask N)) atTop (𝓝 0) := by
  have hfield := (sign_field_convergence hAGG hPNT C L a hwindow hshift).2
  apply squeeze_zero' _ _ hfield
  · exact Eventually.of_forall fun N => massTotalVariation_nonneg _ _
  · filter_upwards [hmasks] with N hm
    exact signCountDistance_le_field (a N) (mask N) hm

end
end PaperC.V282.SignPatternCounts
