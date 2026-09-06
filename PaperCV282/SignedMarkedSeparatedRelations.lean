import PaperCV282.SignedExactMarks
import PaperCV282.DictionaryMarginalCap
import PaperCV282.ExactMarkedPairCosts
import PaperCV282.RelationProfileRestriction

/-!
# Actual mixed signed equations and the full maximal value relation space

Zero extension retains every value equation, including the prescribed sign.
The bound for separated labels holds after averaging the conditioning atoms;
it does not assert this unconditional estimate on each atom individually.
-/
namespace PaperC.V282.SignedMarkedSeparatedRelations

open Affine PrescribedValues WindowValues InfiniteWordTransfer DictionaryMarginalCap
open MixedLengthAffine ExactMarkedModel SignedExactMarks ExactMarkedDependency
open ExactMarkedPairCosts ConditionalStartProbability ConditionalAGGAverage
open ArratiaGoldsteinGordonInput SectionThirteenCouplings TwoWindowParity ConditionalAGGInstantiation SectionThirteenFiniteBound
open scoped BigOperators

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The two actual value blocks may have different lengths. -/
def mixedValueSystem (C x y q r : ℕ) :
    SampleSpace C →ₗ[F₂] (Sum (Fin q) (Fin r) → F₂) :=
  valueSystem C (Sum.elim (vertex x q) (vertex y r))

theorem mixedValueSystem_apply_embedding {C x y q r B : ℕ}
    (hq : q ≤ B) (hr : r ≤ B) (omega : SampleSpace C) (i : Sum (Fin q) (Fin r)) :
    jointValueSystem C x y B omega (mixedIndexEmbedding hq hr i) =
      mixedValueSystem C x y q r omega i := by
  cases i <;> rfl

/-- A mixed signed relation extends to a full value relation with zero coefficients. -/
theorem zeroExtend_mem_valueRelationSpace {C x y q r B : ℕ}
    (hq : q ≤ B) (hr : r ≤ B) (u : RelationSpace (mixedValueSystem C x y q r)) :
    zeroExtendMixedCoefficients hq hr (u : Sum (Fin q) (Fin r) → F₂) ∈
      RelationSpace (jointValueSystem C x y B) := by
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro omega
  rw [relationMap_apply, relationFunctional_apply, dotProduct_zeroExtendMixedCoefficients]
  simp_rw [mixedValueSystem_apply_embedding hq hr]
  have hu := DFunLike.congr_fun (LinearMap.mem_ker.mp u.2) omega
  simpa only [relationMap_apply, relationFunctional_apply, LinearMap.zero_apply] using hu

def mixedValueRelationEmbedding {C x y q r B : ℕ} (hq : q ≤ B) (hr : r ≤ B) :
    RelationSpace (mixedValueSystem C x y q r) →ₗ[F₂]
      RelationSpace (jointValueSystem C x y B) :=
  (zeroExtendMixedCoefficients hq hr).domRestrict
    (RelationSpace (mixedValueSystem C x y q r)) |>.codRestrict
      (RelationSpace (jointValueSystem C x y B)) (zeroExtend_mem_valueRelationSpace hq hr)

theorem mixedValueRelationEmbedding_injective {C x y q r B : ℕ} (hq : q ≤ B) (hr : r ≤ B) :
    Function.Injective (mixedValueRelationEmbedding (C := C) (x := x) (y := y) hq hr) := by
  intro u v huv
  apply Subtype.ext
  exact zeroExtendMixedCoefficients_injective hq hr (congrArg Subtype.val huv)

theorem mixed_value_relationRho_le_common {C x y q r B : ℕ} (hq : q ≤ B) (hr : r ≤ B) :
    relationRho (mixedValueSystem C x y q r) ≤ relationRho (jointValueSystem C x y B) := by
  unfold relationRho
  exact LinearMap.finrank_le_finrank_of_injective
    (mixedValueRelationEmbedding_injective (C := C) (x := x) (y := y) hq hr)

/-- Actual finite mixed word probability, with no independence assumption. -/
theorem mixed_word_probability_eq_affine (C x y q r : ℕ) (u : Fin q → F₂) (v : Fin r → F₂) :
    eventProbability (fullUniformPMF C) (fun omega =>
      omega ∈ finiteWordEvent C x q u ∧ omega ∈ finiteWordEvent C y r v) =
      (uniformSolutionProbability (mixedValueSystem C x y q r) (Sum.elim u v) : ℝ) := by
  rw [← eventProbability_affine_eq]
  unfold fullUniformPMF
  congr 1
  funext omega
  apply propext
  simp only [finiteWordEvent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hu, hv⟩
    funext i
    cases i with
    | inl i => exact hu i
    | inr i => exact hv i
  · intro h
    exact ⟨fun i => congrFun h (Sum.inl i), fun i => congrFun h (Sum.inr i)⟩

/-- Pointwise in the pair of signed labels; the probability is the genuine source law. -/
theorem signed_joint_probability_le_full_value_weight {C x y L E e f : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hL : 1 ≤ L) (he : e ≤ E) (hf : f ≤ E) (s t : F₂) :
    eventProbability (fullUniformPMF C) (fun omega =>
      SignedExactMark (valueBit omega) x L e s ∧ SignedExactMark (valueBit omega) y L f t) ≤
      (signedMarkRate L e : ℝ) * (signedMarkRate L f : ℝ) *
        (2 : ℝ) ^ relationRho (jointValueSystem C x y (L+E+2)) := by
  simp_rw [signedExactMark_iff_finiteWordEvent hx hL s,
    signedExactMark_iff_finiteWordEvent hy hL t]
  rw [mixed_word_probability_eq_affine]
  have hprob := affine_probability_le_relation_weight
    (mixedValueSystem C x y (L+e+2) (L+f+2))
    (Sum.elim (signedExactWord L e s) (signedExactWord L f t))
  have hrho := mixed_value_relationRho_le_common (C := C) (x := x) (y := y)
    (q := L+e+2) (r := L+f+2) (B := L+E+2) (by omega) (by omega)
  have hpow : (2 : ℝ)^relationRho (mixedValueSystem C x y (L+e+2) (L+f+2)) ≤
      (2 : ℝ)^relationRho (jointValueSystem C x y (L+E+2)) :=
    pow_le_pow_right₀ (by norm_num) hrho
  apply hprob.trans
  simp only [Fintype.card_sum, Fintype.card_fin]
  calc
    _ ≤ (2 : ℝ)^relationRho (jointValueSystem C x y (L+E+2)) /
        (2 : ℝ)^((L+e+2)+(L+f+2)) := div_le_div_of_nonneg_right hpow (by positivity)
    _ = _ := by simp only [signedMarkRate_coe, pow_add]; ring

/-- Conditioning is averaged before the full-value relation estimate is applied. -/
theorem average_signed_joint_probability_le_full_value_weight {C x y L E Y : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hL : 1 ≤ L) (a b : Fin (E+1) × F₂) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      eventProbability (largeUniformPMF C Y) (fun eta =>
        conditionedSignedAt C L E Y sigma x a eta = true ∧
        conditionedSignedAt C L E Y sigma y b eta = true)) ≤
      (signedMarkRate L a.1.val : ℝ) * (signedMarkRate L b.1.val : ℝ) *
        (2 : ℝ)^relationRho (jointValueSystem C x y (L+E+2)) := by
  simp only [conditionedSignedAt, signedAt, decide_eq_true_eq]
  rw [finiteUniformAverage_largeEventProbability_eq_full C Y (fun omega =>
    SignedExactMark (valueBit omega) x L a.1.val a.2 ∧
    SignedExactMark (valueBit omega) y L b.1.val b.2)]
  have hp := signed_joint_probability_le_full_value_weight (C := C) hx hy hL
    (e := a.1.val) (f := b.1.val) (E := E) (by omega) (by omega) a.2 b.2
  convert hp using 1
  rw [eventProbability_fullUniformPMF_eq, finiteUniformProbability_eq_uniformEventProbability]

/-- The maximal system is the existing profile system with Q+1 value vertices. -/
theorem maximal_jointValueSystem_eq_twoValueSystem {C x y L E : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    jointValueSystem C x y (L+E+2) = twoValueSystem C x y (L+E+1) :=
  jointValueSystem_eq_twoValueSystem hx hy

end

end PaperC.V282.SignedMarkedSeparatedRelations
