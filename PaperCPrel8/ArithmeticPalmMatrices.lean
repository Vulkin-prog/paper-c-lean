import PaperCPrel8.RegularTargetPresence
import PaperCPrel8.CenteredPalmFourier
import PaperCPrel8.ArithmeticEnvironmentLaw

/-! # Actual valuation matrices in the signed Palm Fourier formula -/
namespace PaperC.Prel8.ArithmeticPalmMatrices
open Finset ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
open _root_.PaperC.Affine V282.PrescribedValues V282.ExactMarkedModel
open RegularPlantPresence RegularTargetPresence PrimeForcing HardConditionalForcing
open AffinePalmCharacters AffinePalmEnvironment CenteredAffineBlocks CenteredPalmFourier
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E k : ℕ}

/-- The actual small-prime columns of the simultaneous raw-value equations. -/
def smallRaw (C Y L : ℕ) (j e : Fin k → ℕ) :
    SmallSample C Y →ₗ[F₂] (Raw (L := L) e → F₂) :=
  (valueSystem C (vertices (L := L) j e)).comp (extendSmall C Y)

/-- The actual large-prime columns; regularity will prove their full row rank. -/
def largeRaw (C Y L : ℕ) (j e : Fin k → ℕ) :
    LargeSample C Y →ₗ[F₂] (Raw (L := L) e → F₂) :=
  largeValueSystem C Y (vertices (L := L) j e)

def smallStart (C Y x L : ℕ) : SmallSample C Y →ₗ[F₂] (Fin L → F₂) :=
  (startSystem C x L).comp (extendSmall C Y)

/-- The private raw pivots give a right inverse entirely among the large primes. -/
theorem largeRaw_surjective (j e : Fin k → ℕ)
    (q : Raw (L := L) e → PrimeUpTo C)
    (hqY : ∀ a, Y<(q a).val.val)
    (hodd : ∀ a, parityVec (vertices (L := L) j e a) (q a).val.val=1)
    (hprivate : ∀ a b, b≠a → ¬(q a).val.val∣vertices (L := L) j e b) :
    Function.Surjective (largeRaw C Y L j e) := by
  intro b
  let w := forceWord (vertices (L := L) j e) q b 0
  have hword : valueSystem C (vertices (L := L) j e) w=b :=
    forceWord_hits _ q (private_basis _ q hodd hprivate) b 0
  have hs : restrictSmall C Y w=0 := by
    dsimp [w]
    rw [smallTrace_unchanged _ q hqY,map_zero]
  have hw : extendLarge C Y (restrictLarge C Y w)=w := by
    have hh := assemble_restrictions C Y w
    simpa only [ConditionalStartProbability.assemble,hs,map_zero,zero_add] using hh
  refine ⟨restrictLarge C Y w,?_⟩
  change valueSystem C (vertices (L := L) j e) (extendLarge C Y (restrictLarge C Y w))=b
  rw [hw,hword]

/-- Full row rank is discharged from the actual regularity predicate, not assumed. -/
theorem regular_largeRaw_surjective (j e : Fin k → ℕ)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : RoughKernelRegularity.Regular (L+E+1) Y j) :
    Function.Surjective (largeRaw C Y L j e) := by
  obtain ⟨q,hqY,hodd,hprivate⟩ := exists_private_raw j e hj he hC hr
  exact largeRaw_surjective j e q hqY hodd hprivate

/-- The planted affine equations are exactly the simultaneous arithmetic signed words. -/
theorem plant_iff_marks (hL : 1≤L) (j e : Fin k → ℕ) (s : Fin k → F₂)
    (z : SmallSample C Y × LargeSample C Y) :
    plant (smallRaw C Y L j e) (largeRaw C Y L j e) (word (L := L) e s) z ↔
      ∀ i, SignedExactMark (valueBit (assemble C Y z.1 z.2)) (j i+1) L (e i) (s i) := by
  rw [← word_iff hL j e s]
  simp only [plant,smallRaw,largeRaw,largeValueSystem,ConditionalStartProbability.assemble,map_add,LinearMap.comp_apply]
  exact eq_sub_iff_add_eq.trans (by rw [add_comm])

/-- The queried blocks are the actual arithmetic base-start indicators. -/
theorem block_eq_start (hL : 1≤L) (x : ℕ) (z : SmallSample C Y × LargeSample C Y) :
    block (smallStart C Y x L) (largeStartSystem C Y x L) (startRhs L) z=
      if startAt (assemble C Y z.1 z.2) x L then 1 else 0 := by
  have he : smallStart C Y x L z.1+largeStartSystem C Y x L z.2=
      startSystem C x L (assemble C Y z.1 z.2) := by
    simp [smallStart,largeStartSystem,ConditionalStartProbability.assemble]
  unfold block
  simp only [he,startSystem_eq_startRhs_iff_startAt _ (show 0<L by omega)]

/-- Positivity of the plant law on every already-conditioned small-prime distribution. -/
theorem regular_plant_probability_pos (mu : FinitePMF (SmallSample C Y))
    (j e : Fin k → ℕ) (s : Fin k → F₂)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : RoughKernelRegularity.Regular (L+E+1) Y j) :
    0<eventProbability (productPMF mu (FinitePMF.uniform (LargeSample C Y)))
      (plant (smallRaw C Y L j e) (largeRaw C Y L j e) (word (L := L) e s)) := by
  rw [plant_probability mu _ _ (regular_largeRaw_surjective j e hj he hC hr)]
  positivity

end
end PaperC.Prel8.ArithmeticPalmMatrices
