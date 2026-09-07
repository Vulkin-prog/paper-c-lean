import PaperCV282.AffineBorderLinear
import PaperCV282.MicroscopicBorderEvents
import Mathlib.Probability.ConditionalProbability

/-! # The exact affine-conditioned border mass

The source is the same infinite prime-sign product. The border projection
reads every prime at most L, inside any cylinder M >= L. Its dual range is
the border row space; the overlap counts complete linear consequences.
-/
namespace PaperC.V282.AffineBorderCylinders

open Affine MeasureTheory ProbabilityTheory Set InfiniteRademacher InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer PrefixBoundaryProbability MicroscopicBorderEvents
open AffineBorderLinear
open scoped ENNReal Classical

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

/-- Inclusion of all border prime coordinates into an adequate cylinder. -/
def borderPrimeEmbedding {M L : ℕ} (hLM : L≤M) : PrimeUpTo L ↪ PrimeUpTo M where
  toFun p := ⟨⟨p.val.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ p.val.isLt).trans hLM)⟩,p.property⟩
  inj' p q hpq := by
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun p : PrimeUpTo M => p.val.val) hpq

/-- The exact coordinate restriction defining the border equations. -/
def borderProjection {M L : ℕ} (hLM : L≤M) : SampleSpace M →ₗ[F₂] SampleSpace L where
  toFun sigma p := sigma (borderPrimeEmbedding hLM p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem borderProjection_surjective {M L : ℕ} (hLM : L≤M) :
    Function.Surjective (borderProjection hLM) := by
  intro sigma
  refine ⟨Function.extend (borderPrimeEmbedding hLM) sigma 0,?_⟩
  funext p
  exact (borderPrimeEmbedding hLM).injective.extend_apply sigma 0 p

/-- Its rank is exactly pi(L), including an empty prime set. -/
theorem borderProjection_rank {M L : ℕ} (hLM : L≤M) :
    Module.finrank F₂ (LinearMap.range (borderProjection hLM))=Nat.primeCounting L := by
  rw [LinearMap.range_eq_top.mpr (borderProjection_surjective hLM),finrank_top]
  rw [Module.finrank_fintype_fun_eq_card,card_primeUpTo_eq_primeCounting]

theorem borderProjection_restrictToFinite {M L : ℕ} (hLM : L≤M) (omega : InfiniteSample) :
    borderProjection hLM (restrictToFinite M omega)=restrictToFinite L omega := rfl

/-- The actual infinite affine event on the finite prime cylinder. -/
def affineCylinder {M : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]
    (A : SampleSpace M →ₗ[F₂] W) (b : W) : Set InfiniteSample :=
  {omega | A (restrictToFinite M omega)=b}

theorem measurableSet_affineCylinder {M : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]
    (A : SampleSpace M →ₗ[F₂] W) (b : W) : MeasurableSet (affineCylinder A b) :=
  (measurable_restrictToFinite M) (Set.toFinite {sigma : SampleSpace M | A sigma=b} |>.measurableSet)

/-- Every finite affine mass is transported exactly to the true infinite source. -/
theorem affineCylinder_probability {M : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]
    (A : SampleSpace M →ₗ[F₂] W) (b : W) :
    infiniteRademacherMeasure.real (affineCylinder A b)=((uniformSolutionProbability A b : ℚ) : ℝ) := by
  have hevent : uniformEventProbability (fun sigma : SampleSpace M => A sigma=b)=
      uniformSolutionProbability A b := by
    unfold uniformEventProbability uniformSolutionProbability
    rw [Fintype.card_subtype]
    simp only [solutionSet,Set.mem_setOf_eq]
  change (infiniteRademacherMeasure (restrictToFinite M ⁻¹' {sigma | A sigma=b})).toReal = _
  rw [← Measure.map_apply (measurable_restrictToFinite M) (Set.toFinite _ |>.measurableSet),
    map_infiniteRademacherMeasure_restrictToFinite,
    finiteRademacherMeasure_event_eq_uniformEventProbability,hevent,ENNReal.toReal_ofReal]
  apply Rat.cast_nonneg.mpr
  unfold uniformSolutionProbability
  positivity


/-- General intersection identity on the same genuine source cylinder. -/
theorem affineCylinder_inter {M : ℕ} {W Z : Type*}
    [AddCommGroup W] [Module F₂ W] [AddCommGroup Z] [Module F₂ Z]
    (A : SampleSpace M →ₗ[F₂] W) (B : SampleSpace M →ₗ[F₂] Z) (b : W) (c : Z) :
    affineCylinder A b ∩ affineCylinder B c=affineCylinder (A.prod B) (b,c) := by
  ext omega
  simp only [affineCylinder,Set.mem_inter_iff,Set.mem_setOf_eq,
    LinearMap.prod_apply,Function.prod_apply,Prod.mk.injEq]

/-- The true conditional source mass of two affine systems, including incompatible fibers. -/
theorem conditional_affineCylinder_probability {M : ℕ} {W Z : Type*}
    [AddCommGroup W] [Module F₂ W] [AddCommGroup Z] [Module F₂ Z]
    (A : SampleSpace M →ₗ[F₂] W) (B : SampleSpace M →ₗ[F₂] Z) (b : W) (c : Z) :
    (cond infiniteRademacherMeasure (affineCylinder A b)).real (affineCylinder B c)=
      if Compatible (A.prod B) (b,c) then
        1/(2 : ℝ)^(Module.finrank F₂ (LinearMap.range B)-rowOverlap A B) else 0 := by
  rw [Measure.real,cond_apply (measurableSet_affineCylinder A b),
    ENNReal.toReal_mul,ENNReal.toReal_inv]
  change (infiniteRademacherMeasure.real (affineCylinder A b))⁻¹*
    infiniteRademacherMeasure.real (affineCylinder A b ∩ affineCylinder B c)=_
  rw [affineCylinder_inter,affineCylinder_probability,affineCylinder_probability]
  split_ifs with hc
  · have hh := congrArg (fun q : ℚ => (q : ℝ)) (conditional_affine_probability A B b c hc)
    simp only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] at hh
    simpa only [div_eq_mul_inv,mul_comm] using hh
  · rw [uniformSolutionProbability_of_not_compatible _ _ hc]
    simp

/-- The border is the zero fiber of its actual coordinate projection. -/
theorem borderEvent_eq_affineCylinder {M L : ℕ} (hLM : L≤M) :
    borderEvent L=affineCylinder (borderProjection hLM) 0 := by
  rw [borderEvent_eq_prefix,infinitePrefixBoundaryEvent_eq_preimage,
    finitePrefixBoundaryEvent_eq_singleton_zero]
  ext omega
  change restrictToFinite L omega=0 ↔ borderProjection hLM (restrictToFinite M omega)=0
  rw [borderProjection_restrictToFinite]

/-- Intersection is exactly the stacked system, including its affine right-hand side. -/
theorem affineCylinder_inter_border {M L : ℕ} (hLM : L≤M)
    {W : Type*} [AddCommGroup W] [Module F₂ W]
    (A : SampleSpace M →ₗ[F₂] W) (b : W) :
    affineCylinder A b ∩ borderEvent L = affineCylinder (A.prod (borderProjection hLM)) (b,0) := by
  rw [borderEvent_eq_affineCylinder hLM]
  ext omega
  simp only [affineCylinder,Set.mem_inter_iff,Set.mem_setOf_eq,LinearMap.prod_apply,Function.prod_apply,Prod.mk.injEq]

/-- The conditioning event itself has strictly positive source mass. -/
theorem affineCylinder_probability_pos {M : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]
    (A : SampleSpace M →ₗ[F₂] W) (b : W) (h : Compatible A b) :
    0 < infiniteRademacherMeasure.real (affineCylinder A b) := by
  rw [affineCylinder_probability,compatible_probability_inverse_rank A b h]
  positivity

/-- Exact mass in Theorem7.10: pi(L) minus the shared dual row-space dimension. -/
theorem theorem_seven_ten_exact_border_mass {M L : ℕ} (hLM : L≤M)
    {W : Type*} [AddCommGroup W] [Module F₂ W]
    (A : SampleSpace M →ₗ[F₂] W) (b : W)
    (hcompat : Compatible (A.prod (borderProjection hLM)) (b,0)) :
    (cond infiniteRademacherMeasure (affineCylinder A b)).real (borderEvent L)=
      1/(2 : ℝ)^(Nat.primeCounting L-rowOverlap A (borderProjection hLM)) := by
  rw [Measure.real,cond_apply (measurableSet_affineCylinder A b),
    ENNReal.toReal_mul,ENNReal.toReal_inv]
  change (infiniteRademacherMeasure.real (affineCylinder A b))⁻¹*
    infiniteRademacherMeasure.real (affineCylinder A b ∩ borderEvent L)=_
  rw [affineCylinder_inter_border hLM,affineCylinder_probability,affineCylinder_probability]
  have hh := conditional_affine_probability A (borderProjection hLM) b 0 hcompat
  rw [borderProjection_rank] at hh
  have hc := congrArg (fun q : ℚ => (q : ℝ)) hh
  simp only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] at hc
  simpa only [div_eq_mul_inv,mul_comm] using hc

end
end PaperC.V282.AffineBorderCylinders
