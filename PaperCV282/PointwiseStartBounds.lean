import PaperCV282.TwoWindowParity
import PaperC.Affine.StartDefectRank
import PaperC.Probability.InfiniteStartProbabilityTransfer

/-!
# The two pointwise bounds of Corollary 2.5

The interior defect set contains precisely the non-root vertices. The full
boundary is supported on the actual complete-window defects and has even
total parity, giving the additional dimension saving of one. Bounds hold
for every affine right-hand side and transfer to the source infinite law.
-/

namespace PaperC.V282.PointwiseStartBounds

open Affine RationalChannelCode StartDefectRank PrescribedValues WindowValues
open InfiniteRademacher InfiniteCylinderTransfer InfiniteExactLengthProbabilityTransfer
open InfiniteStartProbabilityTransfer MeasureTheory Set
open scoped BigOperators

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- A start relation is a full-value relation after taking its actual tree boundary. -/
theorem boundary_mem_value_relation {M x L : ℕ} (hx : 1 ≤ x)
    (u : RelationSpace (startSystem M x L)) :
    startCompleteBoundary L u ∈ RelationSpace (valueSystem M (vertex x (L + 1))) := by
  simp only [RelationSpace, LinearMap.mem_ker, LinearMap.ext_iff,
    relationMap_apply, relationFunctional_apply, LinearMap.zero_apply]
  intro omega
  have hrel : dotProduct (u : Fin L → F₂) (startSystem M x L omega) = 0 := by
    have h := DFunLike.congr_fun u.property omega
    simpa only [relationMap_apply, relationFunctional_apply, LinearMap.zero_apply] using h
  rw [dotProduct, sum_startSystem_eq_sum_completeBoundary] at hrel
  simpa only [dotProduct, valueSystem_apply, TwoWindowParity.start_label_eq_consecutive hx] using hrel

/-- Every nondefective complete vertex has zero relation boundary. -/
theorem boundary_zero_of_not_defective {M x L : ℕ} (hx : 2 ≤ x)
    (hcut : x + L ≤ M) (u : RelationSpace (startSystem M x L))
    (i : Fin (L + 1)) (hi : i ∉ defectIndices (L + 1) x (L + 1)) :
    startCompleteBoundary L u i = 0 := by
  classical
  have hdef : ¬ DefectivePredicate.HDefective (L + 1) (vertex x (L + 1) i) := by
    simpa [defectIndices] using hi
  obtain ⟨p, _, hp, hother⟩ := private_prime_of_not_defective hx
    (by omega : x - 1 + (L + 1) ≤ M + 1) (le_refl (L + 1)) i hdef
  exact relation_coefficient_eq_zero_of_private_coordinate
    (valueSystem M (vertex x (L + 1)))
    ⟨startCompleteBoundary L u, boundary_mem_value_relation (by omega) u⟩ i
    (Pi.single p 1) (valueSystem_prime_basis M (vertex x (L + 1)) i p hp hother)

/-- The full tree boundary restricted to the actual defective occurrences. -/
def fullDefectBoundary (M x L : ℕ) :
    RelationSpace (startSystem M x L) →ₗ[F₂]
      ((defectIndices (L + 1) x (L + 1)) → F₂) where
  toFun u i := startCompleteBoundary L u i.val
  map_add' u v := by
    funext i
    exact congrFun (map_add (startCompleteBoundary L) u.val v.val) i.val
  map_smul' c u := by
    funext i
    exact congrFun (map_smul (startCompleteBoundary L) c u.val) i.val

/-- No edge relation is lost by reading only its defective boundary. -/
theorem fullDefectBoundary_injective {M x L : ℕ} (hx : 2 ≤ x)
    (hcut : x + L ≤ M) : Function.Injective (fullDefectBoundary M x L) := by
  classical
  intro u v huv
  apply Subtype.ext
  apply startCompleteBoundary_injective L
  funext i
  by_cases hi : i ∈ defectIndices (L + 1) x (L + 1)
  · exact congrFun huv ⟨i,hi⟩
  · rw [boundary_zero_of_not_defective hx hcut u i hi,
      boundary_zero_of_not_defective hx hcut v i hi]

/-- The restricted defective boundary still has total parity zero. -/
theorem coordinateSum_fullDefectBoundary_eq_zero {M x L : ℕ} (hx : 2 ≤ x)
    (hcut : x + L ≤ M) (u : RelationSpace (startSystem M x L)) :
    coordinateSum (defectIndices (L + 1) x (L + 1)) (fullDefectBoundary M x L u) = 0 := by
  classical
  rw [coordinateSum_apply]
  change (∑ i : defectIndices (L + 1) x (L + 1), startCompleteBoundary L u i.val) = 0
  rw [Finset.sum_coe_sort]
  have heq : (∑ i ∈ defectIndices (L + 1) x (L + 1), startCompleteBoundary L u i) =
      ∑ i : Fin (L + 1), startCompleteBoundary L u i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    exact boundary_zero_of_not_defective hx hcut u i hi
  rw [heq]
  exact startVertexSum_startCompleteBoundary_eq_zero u.val

/-- The dimension saving is valid also when there are no defective vertices. -/
theorem finrank_ker_coordinateSum_finset {alpha : Type*} (D : Finset alpha) :
    Module.finrank F₂ (LinearMap.ker (coordinateSum D)) = D.card - 1 := by
  classical
  by_cases hD : D.Nonempty
  · letI : Nonempty D := ⟨⟨hD.choose,hD.choose_spec⟩⟩
    simpa using finrank_ker_coordinateSum D
  · have hcard : D.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hD)
    have hfull : Module.finrank F₂ (D → F₂) = 0 := by simp [Module.finrank_fintype_fun_eq_card,hcard]
    have h := (LinearMap.ker (coordinateSum D)).finrank_le
    rw [hfull] at h
    omega

/-- The full parity constraint saves one degree of freedom among defective vertices. -/
theorem relationRho_le_full_defects_sub_one {M x L : ℕ} (hx : 2 ≤ x)
    (hcut : x + L ≤ M) :
    relationRho (startSystem M x L) ≤ (defectIndices (L + 1) x (L + 1)).card - 1 := by
  have hrange : LinearMap.range (fullDefectBoundary M x L) ≤
      LinearMap.ker (coordinateSum (defectIndices (L + 1) x (L + 1))) := by
    intro w hw
    obtain ⟨u,rfl⟩ := hw
    exact coordinateSum_fullDefectBoundary_eq_zero hx hcut u
  have hdim := Submodule.finrank_mono hrange
  rw [LinearMap.finrank_range_of_inj (fullDefectBoundary_injective hx hcut),
    finrank_ker_coordinateSum_finset] at hdim
  exact hdim

/-- The original interior restriction gives the exact non-root defect count. -/
theorem relationRho_le_nonroot_defects {x L : ℕ} (hx : 2 ≤ x) (hL : 0 < L) :
    relationRho (startSystem (dyadicCutoff x L) x L) ≤ (startDefectIndices x L).card := by
  have hmem : x ∈ dyadicBlock x := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have h := LinearMap.finrank_le_finrank_of_injective (startDefectRestriction_injective hx hmem hL)
  simpa [relationRho, Module.finrank_fintype_fun_eq_card] using h

/-- The first pointwise inequality of (2.5), uniformly over affine right-hand sides. -/
theorem corollary_two_five_pointwise_finite {x L : ℕ} (hx : 2 ≤ x) (hL : 0 < L)
    (b : Fin L → F₂) :
    |uniformSolutionProbability (startSystem (dyadicCutoff x L) x L) b - 1 / (2 : ℚ) ^ L| ≤
      ((2 : ℚ) ^ (startDefectIndices x L).card - 1) / (2 : ℚ) ^ L := by
  simpa using abs_probability_sub_baseline_le
    (startSystem (dyadicCutoff x L) x L) b (relationRho_le_nonroot_defects hx hL)

/-- The second pointwise inequality of (2.5); natural subtraction represents max(m-1,0). -/
theorem corollary_two_five_upper_finite {M x L : ℕ} (hx : 2 ≤ x)
    (hcut : x + L ≤ M) (b : Fin L → F₂) :
    uniformSolutionProbability (startSystem M x L) b ≤
      (2 : ℚ) ^ ((defectIndices (L + 1) x (L + 1)).card - 1) / (2 : ℚ) ^ L := by
  rw [probability_eq_eta_weight]
  simp only [Fintype.card_fin]
  have heta : (relationEta (startSystem M x L) b : ℚ) ≤ 1 := by
    rcases relationEta_eq_zero_or_one (startSystem M x L) b with h | h <;> simp [h]
  have hrho := relationRho_le_full_defects_sub_one hx hcut
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ 1 * (2 : ℚ) ^ relationRho (startSystem M x L) := mul_le_mul_of_nonneg_right heta (by positivity)
    _ ≤ _ := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hrho

/-- The actual edge-bit equations on the infinite prime-sign sample. -/
def infiniteAffineStartEvent (x L : ℕ) (b : Fin L → F₂) : Set InfiniteSample :=
  {omega | ∀ i : Fin L,
    (if i.val = 0 then infiniteValueBit omega (x - 1) + infiniteValueBit omega x
      else infiniteValueBit omega x + infiniteValueBit omega (x + i.val)) = b i}

/-- The probability of an arbitrary affine right-hand side in the infinite model. -/
def infiniteAffineStartProbability (x L : ℕ) (b : Fin L → F₂) : ℝ :=
  (infiniteRademacherMeasure (infiniteAffineStartEvent x L b)).toReal

/-- Every adequate finite cylinder represents these same infinite edge equations. -/
theorem infiniteAffineStartEvent_eq_preimage {M x L : ℕ} (hcut : x + L ≤ M)
    (b : Fin L → F₂) :
    infiniteAffineStartEvent x L b = restrictToFinite M ⁻¹'
      {omega : SampleSpace M | startSystem M x L omega = b} := by
  ext omega
  simp only [infiniteAffineStartEvent, Set.mem_setOf_eq, Set.mem_preimage, funext_iff]
  apply forall_congr'
  intro i
  have hroot := valueBit_restrictToFinite_eq_infiniteValueBit omega (show x - 1 ≤ M by omega)
  have hcenter := valueBit_restrictToFinite_eq_infiniteValueBit omega (show x ≤ M by omega)
  have hleaf := valueBit_restrictToFinite_eq_infiniteValueBit omega (show x + i.val ≤ M by have := i.isLt; omega)
  simp only [startSystem_apply,hroot,hcenter,hleaf]

/-- The infinite affine event is measurable. -/
theorem measurableSet_infiniteAffineStartEvent (x L : ℕ) (b : Fin L → F₂) :
    MeasurableSet (infiniteAffineStartEvent x L b) := by
  rw [infiniteAffineStartEvent_eq_preimage (M := x + L) (le_refl _) b]
  exact (measurable_restrictToFinite _) (Set.toFinite _ |>.measurableSet)

/-- Exact finite/infinite equality for every affine right-hand side. -/
theorem infiniteAffineStartProbability_eq_uniformSolutionProbability
    {M x L : ℕ} (hcut : x + L ≤ M) (b : Fin L → F₂) :
    infiniteAffineStartProbability x L b =
      ((uniformSolutionProbability (startSystem M x L) b : ℚ) : ℝ) := by
  classical
  have hevent : uniformEventProbability (fun omega : SampleSpace M => startSystem M x L omega = b) =
      uniformSolutionProbability (startSystem M x L) b := by
    unfold uniformEventProbability uniformSolutionProbability
    rw [Fintype.card_subtype]
    simp only [solutionSet, Set.mem_setOf_eq]
  unfold infiniteAffineStartProbability
  rw [infiniteAffineStartEvent_eq_preimage hcut b,
    ← Measure.map_apply (measurable_restrictToFinite M) (Set.toFinite _ |>.measurableSet),
    map_infiniteRademacherMeasure_restrictToFinite,
    finiteRademacherMeasure_event_eq_uniformEventProbability, hevent,
    ENNReal.toReal_ofReal]
  apply Rat.cast_nonneg.mpr
  unfold uniformSolutionProbability
  positivity

/-- Infinite-model version of the first inequality in (2.5), uniform in b. -/
theorem corollary_two_five_pointwise_infinite {x L : ℕ} (hx : 2 ≤ x) (hL : 0 < L)
    (b : Fin L → F₂) :
    |infiniteAffineStartProbability x L b - 1 / (2 : ℝ) ^ L| ≤
      ((2 : ℝ) ^ (startDefectIndices x L).card - 1) / (2 : ℝ) ^ L := by
  rw [infiniteAffineStartProbability_eq_uniformSolutionProbability
    (M := dyadicCutoff x L) (by unfold dyadicCutoff; omega) b]
  have h := (Rat.cast_le (K := ℝ)).mpr (corollary_two_five_pointwise_finite hx hL b)
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using h

/-- Infinite-model upper bound with the full defective parity hyperplane. -/
theorem corollary_two_five_upper_infinite {x L : ℕ} (hx : 2 ≤ x) (b : Fin L → F₂) :
    infiniteAffineStartProbability x L b ≤
      (2 : ℝ) ^ ((defectIndices (L + 1) x (L + 1)).card - 1) / (2 : ℝ) ^ L := by
  rw [infiniteAffineStartProbability_eq_uniformSolutionProbability (M := x + L) (le_refl _) b]
  have h := (Rat.cast_le (K := ℝ)).mpr (corollary_two_five_upper_finite hx (le_refl (x + L)) b)
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using h

/-- The start right-hand side is exactly the genuine infinite start event. -/
theorem infiniteAffineStartEvent_startRhs_eq {x L : ℕ} (hL : 0 < L) :
    infiniteAffineStartEvent x L (startRhs L) = infiniteStartEvent x L := by
  rw [infiniteAffineStartEvent_eq_preimage (M := x + L) (le_refl _),
    infiniteStartEvent_eq_preimage (M := x + L) (le_refl _)]
  congr 1
  ext omega
  exact startSystem_eq_startRhs_iff_startAt omega hL

/-- Identification with the retained ordinary start probability. -/
theorem infiniteAffineStartProbability_startRhs_eq {x L : ℕ} (hL : 0 < L) :
    infiniteAffineStartProbability x L (startRhs L) = infiniteStartProbability x L := by
  unfold infiniteAffineStartProbability infiniteStartProbability
  rw [infiniteAffineStartEvent_startRhs_eq hL]

/-- The same two pointwise bounds for the ordinary start indicator. -/
theorem corollary_two_five_start_bounds {x L : ℕ} (hx : 2 ≤ x) (hL : 0 < L) :
    |infiniteStartProbability x L - 1 / (2 : ℝ) ^ L| ≤
      ((2 : ℝ) ^ (startDefectIndices x L).card - 1) / (2 : ℝ) ^ L ∧
    infiniteStartProbability x L ≤
      (2 : ℝ) ^ ((defectIndices (L + 1) x (L + 1)).card - 1) / (2 : ℝ) ^ L := by
  rw [← infiniteAffineStartProbability_startRhs_eq hL]
  exact ⟨corollary_two_five_pointwise_infinite hx hL _, corollary_two_five_upper_infinite hx _⟩

/-- Non-root defective occurrences embed into the full defective window. -/
theorem card_nonroot_defects_le_full {x L : ℕ} (hx : 1 ≤ x) :
    (startDefectIndices x L).card ≤ (defectIndices (L + 1) x (L + 1)).card := by
  classical
  apply Finset.card_le_card_of_injOn Fin.succ
  · intro i hi
    have hd : DefectivePredicate.HDefective (L + 1) (x + i.val) := by
      simpa [startDefectIndices] using hi
    have heq : vertex x (L + 1) i.succ = x + i.val := by
      unfold vertex
      simp only [Fin.val_succ]
      omega
    simpa [defectIndices,heq] using hd
  · intro i _ j _ hij
    exact Fin.succ_injective _ hij

end
end PaperC.V282.PointwiseStartBounds
