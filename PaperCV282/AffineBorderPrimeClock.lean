import PaperCV282.AffineBorderCylinders
import PaperCV282.PrimeClockDistribution

/-! # Future prime-clock information after an affine border condition

The tail system reads the first K primes strictly after L. Its intersection
with the already exposed row space determines the exact conditional tail;
disjointness preserves the geometric tail and implies compatibility.
-/
namespace PaperC.V282.AffineBorderPrimeClock

open Affine MeasureTheory ProbabilityTheory Set InfiniteRademacher InfiniteCylinderTransfer
open MicroscopicBorderEvents PrimeClockEvents PrimeClockDistribution
open AffineBorderLinear AffineBorderCylinders
open scoped ENNReal Classical

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def futurePrimeEmbedding {M L K : ℕ} (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤M) :
    Fin K ↪ PrimeUpTo M where
  toFun i := ⟨⟨Nat.nth Nat.Prime (Nat.primeCounting L+i.val),Nat.lt_succ_of_le
    ((Nat.nth_monotone Nat.infinite_setOf_prime (by omega : Nat.primeCounting L+i.val≤Nat.primeCounting L+K)).trans hcut)⟩,
      Nat.prime_nth_prime _⟩
  inj' i j hij := by
    have hp := congrArg (fun p : PrimeUpTo M => p.val.val) hij
    have heq := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hp
    exact Fin.ext (by omega)

def futurePrimeProjection {M L K : ℕ} (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤M) :
    SampleSpace M →ₗ[F₂] (Fin K → F₂) where
  toFun sigma i := sigma (futurePrimeEmbedding hcut i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem futurePrimeProjection_surjective {M L K : ℕ}
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤M) :
    Function.Surjective (futurePrimeProjection hcut) := by
  intro sigma
  refine ⟨Function.extend (futurePrimeEmbedding hcut) sigma 0,?_⟩
  funext p
  exact (futurePrimeEmbedding hcut).injective.extend_apply sigma 0 p

theorem futurePrimeProjection_rank {M L K : ℕ}
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤M) :
    Module.finrank F₂ (LinearMap.range (futurePrimeProjection hcut))=K := by
  rw [LinearMap.range_eq_top.mpr (futurePrimeProjection_surjective hcut),finrank_top,
    Module.finrank_fintype_fun_eq_card,Fintype.card_fin]

/-- These are precisely the unexposed prime-rank coordinates, not integer offsets. -/
theorem futurePrimeProjection_restrict_apply {M L K : ℕ}
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤M) (omega : InfiniteSample) (i : Fin K) :
    futurePrimeProjection hcut (restrictToFinite M omega) i=omega (Nat.primeCounting L+i.val) := by
  simp [futurePrimeProjection,restrictToFinite,finitePrimeCoordinate,futurePrimeEmbedding]

/-- The homogeneous future system is exactly survival past those K prime signs. -/
theorem future_zero_iff_first_index {M L K : ℕ}
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤M) {omega : InfiniteSample}
    (hex : ∃ j,omega j≠0) (hb : omega∈borderEvent L) :
    omega∈affineCylinder (futurePrimeProjection hcut) 0 ↔
      Nat.primeCounting L+K≤firstNegativeIndex omega := by
  have hi := (borderEvent_iff_first_index hex L).mp hb
  change futurePrimeProjection hcut (restrictToFinite M omega)=0 ↔ _
  simp only [funext_iff,futurePrimeProjection_restrict_apply,Pi.zero_apply]
  constructor
  · intro hall
    by_contra hn
    let i : Fin K := ⟨firstNegativeIndex omega-Nat.primeCounting L,by omega⟩
    have hz := hall i
    have heq : Nat.primeCounting L+i.val=firstNegativeIndex omega := by dsimp [i];omega
    rw [heq,coordinate_first_negative hex] at hz
    exact one_ne_zero hz
  · intro hle i
    exact coordinate_zero_before_first hex (by have := i.isLt;omega)

/-- The actual clock tail and the future zero cylinder agree on the border almost surely. -/
theorem prime_tail_inter_border_ae {M L K : ℕ}
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤M) :
    (borderEvent L ∩ {omega | K≤primeOvershoot L omega} : Set InfiniteSample)
      =ᵐ[infiniteRademacherMeasure] (borderEvent L ∩ affineCylinder (futurePrimeProjection hcut) 0 : Set InfiniteSample) := by
  filter_upwards [ae_exists_negative] with omega hex
  apply propext
  change (omega∈borderEvent L ∧ K≤primeOvershoot L omega) ↔
    (omega∈borderEvent L ∧ omega∈affineCylinder (futurePrimeProjection hcut) 0)
  by_cases hb : omega∈borderEvent L
  · have hi := (borderEvent_iff_first_index hex L).mp hb
    simp only [hb,true_and,primeOvershoot,ite_true,future_zero_iff_first_index hcut hex hb]
    omega
  · simp only [hb,false_and]

/-- Actual prime-clock tail under the affine event and the border, including incompatibility. -/
theorem affine_prime_tail_probability {M L K : ℕ} (hLM : L≤M)
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤M)
    {W : Type*} [AddCommGroup W] [Module F₂ W]
    (A : SampleSpace M →ₗ[F₂] W) (b : W) :
    (cond infiniteRademacherMeasure (affineCylinder A b ∩ borderEvent L)).real
      {omega | K≤primeOvershoot L omega} =
      if Compatible ((A.prod (borderProjection hLM)).prod (futurePrimeProjection hcut)) ((b,0),0)
      then 1/(2 : ℝ)^(K-rowOverlap (A.prod (borderProjection hLM)) (futurePrimeProjection hcut)) else 0 := by
  have heq :
      (affineCylinder A b ∩ borderEvent L ∩ {omega | K≤primeOvershoot L omega} : Set InfiniteSample)
        =ᵐ[infiniteRademacherMeasure]
      (affineCylinder A b ∩ borderEvent L ∩ affineCylinder (futurePrimeProjection hcut) 0 : Set InfiniteSample) := by
    filter_upwards [prime_tail_inter_border_ae hcut] with omega hh
    apply propext
    change (omega∈affineCylinder A b ∧ omega∈borderEvent L) ∧ K≤primeOvershoot L omega ↔
      (omega∈affineCylinder A b ∧ omega∈borderEvent L) ∧ omega∈affineCylinder (futurePrimeProjection hcut) 0
    have hiff : (omega∈borderEvent L ∧ K≤primeOvershoot L omega) ↔
      (omega∈borderEvent L ∧ omega∈affineCylinder (futurePrimeProjection hcut) 0) := Iff.of_eq hh
    tauto
  have hevent : (cond infiniteRademacherMeasure (affineCylinder A b ∩ borderEvent L)).real
      {omega | K≤primeOvershoot L omega} =
      (cond infiniteRademacherMeasure (affineCylinder A b ∩ borderEvent L)).real
        (affineCylinder (futurePrimeProjection hcut) 0) := by
    rw [Measure.real,Measure.real,cond_apply ((measurableSet_affineCylinder A b).inter (measurableSet_borderEvent L)),
      cond_apply ((measurableSet_affineCylinder A b).inter (measurableSet_borderEvent L)),measure_congr heq]
  rw [hevent,affineCylinder_inter_border hLM,conditional_affineCylinder_probability,futurePrimeProjection_rank]

/-- A zero intersection preserves the prime-clock tail; compatibility is derived. -/
theorem geometric_prime_tail_of_zero_overlap {M L K : ℕ} (hLM : L≤M)
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K)≤M)
    {W : Type*} [AddCommGroup W] [Module F₂ W]
    (A : SampleSpace M →ₗ[F₂] W) (b : W)
    (hbase : Compatible (A.prod (borderProjection hLM)) (b,0))
    (hover : rowOverlap (A.prod (borderProjection hLM)) (futurePrimeProjection hcut)=0) :
    (cond infiniteRademacherMeasure (affineCylinder A b ∩ borderEvent L)).real
      {omega | K≤primeOvershoot L omega}=1/(2 : ℝ)^K := by
  have hfuture : Compatible (futurePrimeProjection hcut) 0 := ⟨0,map_zero _⟩
  have hc := compatible_prod_of_rowOverlap_zero (A.prod (borderProjection hLM))
    (futurePrimeProjection hcut) (b,0) 0 hbase hfuture hover
  rw [affine_prime_tail_probability hLM hcut A b,if_pos hc,hover,Nat.sub_zero]

end
end PaperC.V282.AffineBorderPrimeClock
