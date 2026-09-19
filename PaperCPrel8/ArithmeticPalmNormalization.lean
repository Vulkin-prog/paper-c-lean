import PaperCPrel8.ArithmeticPalmDeficit

/-! # The normalized arithmetic Palm void and its exact comparison error -/
namespace PaperC.Prel8.ArithmeticPalmNormalization
open Finset MeasureTheory ProbabilityTheory InfiniteRademacher
open V282.BulkMarkedTypes V282.BulkMarkedTarget V282.CrossoverBulkAtoms
open V282.FiniteFieldTotalVariation ConditionalStartProbability MicroscopicConditionalSpatial
open ArithmeticPalmMass ArithmeticPalmDeficit InfinitePlantMass PalmVoidAverage PalmVoidNormalization
noncomputable section
local instance : MeasurableSpace F₂ := ⊤
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def baseRate (L : ℕ) : ℝ := 1/(2:ℝ)^L

def boundedRegular (sites : Finset ℕ) (C L E Y K : ℕ) (z : SpatialMarkedConfig sites) : Prop :=
  RegularPlant sites C L E Y z ∧ totalSize sites z≤K

def normalizer (sites : Finset ℕ) (L : ℕ) (z : SpatialMarkedConfig sites) : ℝ :=
  Real.exp (totalRate sites L:ℝ)*(1-baseRate L)^(sites.card-totalSize sites z)

def normalizedVoid {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop)
    (z : SpatialMarkedConfig sites) : ℝ :=
  palmVoid sites L A z/(1-baseRate L)^(sites.card-totalSize sites z)

def penalty (sites : Finset ℕ) (L K : ℕ) : ℝ :=
  (K:ℝ)*baseRate L+(sites.card:ℝ)*(baseRate L)^2/(1-baseRate L)

theorem baseRate_bounds {L : ℕ} (hL : 1≤L) : 0<baseRate L ∧ baseRate L<1 := by
  have hh : (1:ℝ)<2^L := one_lt_pow₀ (by norm_num) (by omega)
  constructor
  · unfold baseRate; positivity
  · exact (div_lt_one (by positivity)).mpr hh

theorem enumerated_size {k : ℕ} (sites : Finset ℕ) (labels : Fin k → SpatialMarkedIndex sites) :
    totalSize sites (enumeratedConfiguration sites labels)=k := by
  unfold totalSize enumeratedConfiguration
  rw [← Finsupp.sum_finsetSum_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
  simp

theorem regular_size_le_sites {C L E Y : ℕ} (sites : Finset ℕ) (z : SpatialMarkedConfig sites)
    (hz : RegularPlant sites C L E Y z) : totalSize sites z≤sites.card := by
  obtain ⟨k,labels,rfl,hj,he,hC,hr⟩ := hz
  rw [enumerated_size]
  have hi := regular_sites_injective _ hr
  have hinj : Function.Injective (fun i ↦ (labels i).1) := by
    intro i j h
    exact hi (congrArg (fun x : sites ↦ x.val-1) h)
  simpa using Fintype.card_le_of_injective _ hinj

theorem normalizer_pos {L : ℕ} (sites : Finset ℕ) (hL : 1≤L) (z : SpatialMarkedConfig sites) :
    0<normalizer sites L z := by
  have hp := (baseRate_bounds hL).2
  unfold normalizer
  positivity

theorem normalizedVoid_nonneg {C L Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (z : SpatialMarkedConfig sites) : 0≤normalizedVoid sites L A z := by
  have hp := (baseRate_bounds hL).2
  exact div_nonneg ENNReal.toReal_nonneg (pow_nonneg (by linarith) _)

theorem normalizer_mul_void {C L Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (z : SpatialMarkedConfig sites) :
    normalizer sites L z*normalizedVoid sites L A z=
      Real.exp (totalRate sites L:ℝ)*palmVoid sites L A z := by
  have hp := (baseRate_bounds hL).2
  unfold normalizer normalizedVoid
  have hh : (1-baseRate L)^(sites.card-totalSize sites z)≠0 := by positivity
  field_simp

theorem penalty_nonneg {L : ℕ} (sites : Finset ℕ) (hL : 1≤L) (K : ℕ) : 0≤penalty sites L K := by
  have hp := baseRate_bounds hL
  have hp0 := hp.1.le
  have hp1 : 0<1-baseRate L := sub_pos.mpr hp.2
  unfold penalty
  positivity

/-- Uniform logarithmic normalization on the actual regular configurations. -/
theorem normalizer_log_bound {C L E Y K : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (z : SpatialMarkedConfig sites) (hz : boundedRegular sites C L E Y K z) :
    |Real.log (normalizer sites L z)|≤penalty sites L K := by
  have hp := baseRate_bounds hL
  have hp0 := hp.1.le
  have hp1 : 0<1-baseRate L := sub_pos.mpr hp.2
  have hsize := regular_size_le_sites sites z hz.1
  have hrate : (totalRate sites L:ℝ)=(sites.card:ℝ)*baseRate L := by
    simp [totalRate,baseRate,div_eq_mul_inv]
  unfold normalizer
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity),Real.log_exp,Real.log_pow,hrate]
  apply (bernoulli_log_error hp.1.le hp.2 hsize).trans
  unfold penalty
  have hk : (totalSize sites z:ℝ)≤K := by exact_mod_cast hz.2
  gcongr

/-- Quantitative G.4 comparison for genuine arithmetic and Poisson masses.
The ordinary full-to-retained deletion error can be inserted as D-TV. -/
theorem normalized_comparison {C L E Y K : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A))
    {D deletion : ℝ}
    (hprojection : 0≤D-massTotalVariation (sourceMass sites L A) (targetMass sites L))
    (hdeletion : D-massTotalVariation (sourceMass sites L A) (targetMass sites L)≤deletion) :
    |D-voidDeficit (targetMass sites L) (boundedRegular sites C L E Y K) (normalizedVoid sites L A)|≤
      deletion+PalmDeficit.exceptionalMass (targetMass sites L) (boundedRegular sites C L E Y K)+
        penalty sites L K := by
  apply normalized_void_deficit (hasSum_sourceMass sites L A hA) (hasSum_targetMass sites L)
    (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)
    (normalizer_pos sites hL) (normalizedVoid_nonneg sites hL A)
    (boundedRegular sites C L E Y K) _ hprojection hdeletion (penalty_nonneg sites hL K)
    (normalizer_log_bound sites hL)
  intro z hz
  rw [normalizer_mul_void sites hL A z]
  exact source_target_palm_mass sites hL A hA z hz.1

/-- For completion, the target exceptional mass is unnecessary: the one-sided
normalized deficit is at most the actual distance plus the normalization cost. -/
theorem normalized_average_le {C L E Y K : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    voidDeficit (targetMass sites L) (boundedRegular sites C L E Y K) (normalizedVoid sites L A)≤
      massTotalVariation (sourceMass sites L A) (targetMass sites L)+penalty sites L K := by
  have hn := averaged_normalization (hasSum_targetMass sites L) (fun _ ↦ ENNReal.toReal_nonneg)
    (normalizer_pos sites hL) (normalizedVoid_nonneg sites hL A)
    (boundedRegular sites C L E Y K) (penalty_nonneg sites hL K) (normalizer_log_bound sites hL)
  have he : PalmDeficit.deficit (sourceMass sites L A) (targetMass sites L)
      (boundedRegular sites C L E Y K)=voidDeficit (targetMass sites L)
        (boundedRegular sites C L E Y K) (fun z ↦ normalizer sites L z*normalizedVoid sites L A z) := by
    apply tsum_congr
    intro z
    by_cases hz : boundedRegular sites C L E Y K z
    · simp only [hz,ite_true]
      rw [normalizer_mul_void sites hL A z]
      have hm : sourceMass sites L A z=targetMass sites L z*
          (Real.exp (totalRate sites L:ℝ)*palmVoid sites L A z) :=
        source_target_palm_mass sites hL A hA z hz.1
      rw [hm]
      rw [mul_max_of_nonneg _ _ (show 0≤targetMass sites L z from ENNReal.toReal_nonneg)]
      congr 1 <;> ring
    · simp [hz]
  rw [← he] at hn
  have hd := (PalmDeficit.deficit_restriction (hasSum_sourceMass sites L A hA)
    (hasSum_targetMass sites L) (fun _ ↦ ENNReal.toReal_nonneg)
    (fun _ ↦ ENNReal.toReal_nonneg) (boundedRegular sites C L E Y K)).1
  linarith [abs_le.mp hn]

end
end PaperC.Prel8.ArithmeticPalmNormalization
