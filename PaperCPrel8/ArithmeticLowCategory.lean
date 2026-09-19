import PaperCPrel8.CategoricalActivityWitness
import PaperCPrel8.PrimeWitnessRetention

/-! # The original arithmetic low-type categorical field in G.8 and G.9 -/
namespace PaperC.Prel8.ArithmeticLowCategory
open Finset ConditionalStartProbability V282.ExactMarkedModel
open CategoricalMomentExpansion CategoricalOccupancyEnvelope CategoricalCumulantBound
open CategoricalActivityWitness PrimeWitnessRetention ArratiaGoldsteinGordonInput IndependentThinning
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def lowCategory (C L E j : ℕ) (w : SampleSpace C) : Option (Fin (E+1)×F₂) :=
  if h : ∃ a : Fin (E+1)×F₂, SignedExactMark (valueBit w) (j+1) L a.1.val a.2
    then some (Classical.choose h) else none

theorem lowCategory_some {C L E j : ℕ} (hL : 1≤L) (w : SampleSpace C) (a : Fin (E+1)×F₂) :
    lowCategory C L E j w=some a ↔ SignedExactMark (valueBit w) (j+1) L a.1.val a.2 := by
  unfold lowCategory
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro he
      simpa only [he] using Classical.choose_spec h
    · intro ha
      obtain ⟨he,hs⟩ := signedExactMark_unique hL (Classical.choose_spec h) ha
      exact Prod.ext (Fin.ext he) hs
  · simp only [reduceCtorEq,false_iff]
    exact fun ha ↦ h ⟨a,ha⟩

def retainedCategory (C L E : ℕ) (G : Finset ℕ) : G → SampleSpace C → Option (Fin (E+1)×F₂) :=
  fun j ↦ lowCategory C L E j.val

/-- Categorical indicators are the original signed exact-mark indicators. -/
theorem indicator_eq {C L E : ℕ} (hL : 1≤L) (G : Finset ℕ)
    (a : G×(Fin (E+1)×F₂)) (w : SampleSpace C) :
    indicator (retainedCategory C L E G) a w=
      (signedMarkValue (valueBit w) (a.1.val+1) L a.2.1.val a.2.2:ℝ) := by
  unfold indicator delta retainedCategory signedMarkValue
  by_cases h : SignedExactMark (valueBit w) (a.1.val+1) L a.2.1.val a.2.2
  · simp [(lowCategory_some hL w a.2).mpr h,h]
  · simp [mt (lowCategory_some hL w a.2).mp h,h]

theorem certified_occupied {C q M E : ℕ} (hq : q.Prime) (p : PrimeUpTo C) (hp : p.val.val=q)
    (G : Finset ℕ) :
    (certifiedSites q M∩G).card≤
      occupiedCount (retainedCategory C (q-1) E G) (Pi.single p 1) := by
  let f : ↥(certifiedSites q M∩G) → {i : G // retainedCategory C (q-1) E G i (Pi.single p 1)≠none} :=
    fun j ↦ ⟨⟨j.val,(mem_inter.mp j.property).2⟩,by
      have hj := retained_mark hq p hp G j.val j.property
      have he := (lowCategory_some (E:=E) (by have := hq.two_le; omega) (Pi.single p 1)
        (⟨0,by omega⟩,(0:F₂))).mpr hj
      change lowCategory C (q-1) E j.val (Pi.single p 1)≠none
      rw [he]
      simp⟩
  have hi : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun z ↦ z.val.val) he)
  have hc := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe,Fintype.card_subtype,occupiedCount,card_filter] using hc

/-- Actual arithmetic activity is bounded below by the probability and multiplicity of the prime witness. -/
theorem arithmetic_activity_lower {C q M E : ℕ} (hq : q.Prime) (p : PrimeUpTo C) (hp : p.val.val=q)
    (G : Finset ℕ) {r : ℝ} (hr : 2*r<1)
    (hmean : ∀ i : G, finitePMFExpectation (FinitePMF.uniform (SampleSpace C))
      (occupancy (retainedCategory C (q-1) E G) i)=r) :
    (-(Nat.primeCounting C:ℝ)*Real.log 2+(G.card:ℝ)*Real.log (1-2*r)+
      (((certifiedSites q M).card-((Icc 1 M)\G).card:ℕ):ℝ)*Real.log ((3-2*r)/(1-2*r)))/2≤
        activity (FinitePMF.uniform (SampleSpace C)) (retainedCategory C (q-1) E G) := by
  have hpP : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ w=Pi.single p 1) := by
    rw [witness_probability]
    positivity
  have hh := witness_activity_lower (FinitePMF.uniform (SampleSpace C)) (retainedCategory C (q-1) E G)
    hr hmean (fun w ↦ w=Pi.single p 1) hpP
    ((certifiedSites q M).card-((Icc 1 M)\G).card) (fun w hw ↦ by
      subst w
      exact (retained_count hq.two_le G).trans (certified_occupied hq p hp G))
  rw [witness_probability,Real.log_div (by norm_num) (by positivity),Real.log_one,Real.log_pow] at hh
  simpa only [Fintype.card_coe,zero_sub,neg_mul] using hh

end
end PaperC.Prel8.ArithmeticLowCategory
