import PaperCV282.PointwiseStartBounds
import PaperCV282.MacroscopicPointwiseDefects
import PaperCV282.MacroscopicShallowSigma
import PaperCV282.WordFirstMomentAsymptotics
import PaperCV282.SizeTwoHostAsymptotics
import PaperC.Analysis.DefectGlobalBound
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Uniform masked first moments on the true macroscopic interval

The complete defective-vertex weight is summed by counting only windows
which actually contain a defect. Each positive defective integer belongs
to at most one window per offset. Its global square-root count and the
uniform pointwise defect bound give M^(1/2+epsilon), without comparing a
start to M. Integration is under the retained infinite prime-sign law.
-/

namespace PaperC.V282.MacroscopicFirstMoment

open Affine StartDefectRank WindowValues PointwiseStartBounds WordDefectCounting
open MacroscopicGeometry MacroscopicPointwiseDefects MacroscopicCanonicalCode
open SizeTwoHostAsymptotics LogarithmicWordPowers
open InfiniteRademacher InfiniteStartProbabilityTransfer MeasureTheory Set
open scoped BigOperators

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

local instance instIsProbabilityMeasureInfiniteRademacher :
    IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The complete actual window defects are included in the enclosing root interval. -/
theorem card_fullDefects_le_root_interval (x B : ℕ) :
    (defectIndices B x B).card ≤ (IntervalDefectBound.defectsInInterval B (x - 1)).card := by
  classical
  apply Finset.card_le_card_of_injOn (vertex x B)
  · intro i hi
    have hd : DefectivePredicate.HDefective B (vertex x B i) := by simpa [defectIndices] using hi
    apply DefectiveVertexIntervalBound.mem_defectsInInterval_of_hDefective hd
    · unfold vertex; omega
    · unfold vertex; have := i.isLt; omega
  · intro i _ j _ hij
    apply Fin.ext
    unfold vertex at hij
    omega

/-- The actual full defect weight is subpolynomial, uniformly before the chosen start. -/
theorem two_pow_fullDefects_le_rpow_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ x ∈ macroscopicStarts M delta,
        (2 : ℝ) ^ (defectIndices (L + 1) x (L + 1)).card ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨K,hK,Mpoint,hpoint⟩ := root_defects_log_bound_eventually
    betaMin betaMax delta hbetaMin hbeta hdelta
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hepsilon
  obtain ⟨Mexp, hexp⟩ := ExpSqrtLog.two_pow_log_div_loglog_pow_le_nat_eventually
    K hK (n + 1) (by omega)
  refine ⟨max Mpoint (max Mexp 1), ?_⟩
  intro M hM L hlower hupper x hx
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hd : ((defectIndices (L + 1) x (L + 1)).card : ℝ) ≤
      K * (Real.log M / Real.log (Real.log M)) := by
    have hfinite : ((defectIndices (L + 1) x (L + 1)).card : ℝ) ≤
        ((IntervalDefectBound.defectsInInterval (L + 1) (x - 1)).card : ℝ) := by
      exact_mod_cast card_fullDefects_le_root_interval x (L + 1)
    exact hfinite.trans (hpoint M (by omega) (L + 1) (by simpa using hlower) (by simpa using hupper) x hx)
  have hp := hexp M (by omega) (defectIndices (L + 1) x (L + 1)).card
    (by simpa only [mul_div_assoc] using hd)
  have hroot : (2 : ℝ) ^ (defectIndices (L + 1) x (L + 1)).card ≤
      (M : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (by positivity : (0 : ℝ) < n + 1)).mpr
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
    exact_mod_cast hp
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hMone hn.le)

/-- Windows with an actual defect cost at most one window length per positive defective value. -/
theorem card_active_windows_le_global_defects (B X : ℕ) (s : Finset ℕ)
    (hpos : ∀ x ∈ s, 2 ≤ x)
    (hcover : ∀ x ∈ s, ∀ i : Fin B, vertex x B i ≤ X) :
    (s.filter fun x => (defectIndices B x B).Nonempty).card ≤
      B * (WeightedDefectCounting.positiveDefectValues (DefectCounting.smallPrimesUpTo B) X).card := by
  classical
  let D := WeightedDefectCounting.positiveDefectValues (DefectCounting.smallPrimesUpTo B) X
  have hsub : (s.filter fun x => (defectIndices B x B).Nonempty) ⊆
      (Finset.univ : Finset (Fin B)).biUnion fun i => D.image (fun n => n + 1 - i.val) := by
    intro x hx
    obtain ⟨hxs,i,hi⟩ := Finset.mem_filter.mp hx
    have hxpos := hpos x hxs
    have hd : DefectivePredicate.HDefective B (vertex x B i) := by simpa [defectIndices] using hi
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ?_⟩
    exact ⟨vertex x B i,mem_positiveDefectValues_of_hDefective
      (by unfold vertex; omega) (hcover x hxs i) hd, by unfold vertex; omega⟩
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ _i : Fin B, D.card := Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
    _ = _ := by simp [D]

/-- Finite weighted aggregation pays nothing for windows without defects. -/
theorem sum_fullDefectWeight_le_global (B X : ℕ) (s : Finset ℕ) (W : ℝ)
    (hW : 0 ≤ W) (hpos : ∀ x ∈ s, 2 ≤ x)
    (hcover : ∀ x ∈ s, ∀ i : Fin B, vertex x B i ≤ X)
    (hpoint : ∀ x ∈ s, (2 : ℝ) ^ (defectIndices B x B).card ≤ W) :
    (∑ x ∈ s, ((2 : ℝ) ^ (defectIndices B x B).card - 1)) ≤
      (B : ℝ) * (WeightedDefectCounting.positiveDefectValues (DefectCounting.smallPrimesUpTo B) X).card * W := by
  classical
  have hsum : (∑ x ∈ s, ((2 : ℝ) ^ (defectIndices B x B).card - 1)) ≤
      ((s.filter fun x => (defectIndices B x B).Nonempty).card : ℝ) * W := by
    calc
      _ ≤ ∑ x ∈ s, if (defectIndices B x B).Nonempty then W else 0 := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases hd : (defectIndices B x B).Nonempty
        · simp only [if_pos hd]
          exact (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans (hpoint x hx)
        · have he : defectIndices B x B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hd
          simp [he]
      _ = _ := by simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : ((s.filter fun x => (defectIndices B x B).Nonempty).card : ℝ) ≤
      (B : ℝ) * (WeightedDefectCounting.positiveDefectValues (DefectCounting.smallPrimesUpTo B) X).card := by
    exact_mod_cast card_active_windows_le_global_defects B X s hpos hcover
  exact hsum.trans (mul_le_mul_of_nonneg_right hc hW)

/-- The full defective-window mass on every macroscopic mask has square-root order. -/
theorem sum_fullDefectWeight_le_half_power_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ s : Finset ℕ, s ⊆ macroscopicStarts M delta →
        (∑ x ∈ s, ((2 : ℝ) ^ (defectIndices (L + 1) x (L + 1)).card - 1)) ≤
          (M : ℝ) ^ (1 / (2 : ℝ) + epsilon) := by
  have heps : 0 < epsilon / 2 := by positivity
  have hbmax : 0 ≤ betaMax := (hbetaMin.trans hbeta).le
  obtain ⟨Mpoint,hpoint⟩ := two_pow_fullDefects_le_rpow_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mfactor,hfactor⟩ := polynomial_euler_le_rpow_eventually betaMax 2 (epsilon / 2) hbmax heps
  obtain ⟨Mlength,hlength⟩ := logarithmic_power_lt_rpow_eventually betaMax 1 hbmax (by norm_num) 1 (by omega)
  refine ⟨max Mpoint (max Mfactor (max Mlength 2)), ?_⟩
  intro M hM L hlower hupper s hs
  have hMtwo : 2 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlen := hlength M (by omega) (L + 1) (by simpa using hupper)
  have hL : L ≤ M := by
    simp only [pow_one,Real.rpow_one,Nat.cast_add,Nat.cast_one] at hlen
    exact_mod_cast (show (L : ℝ) ≤ M by linarith)
  have hxpos : ∀ x ∈ s, 2 ≤ x := fun x hx =>
    (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta (hs hx))).1
  have hcover : ∀ x ∈ s, ∀ i : Fin (L + 1), vertex x (L + 1) i ≤ 3 * M := by
    intro x hx i
    have hxm := (mem_macroscopicStarts M delta x).mp (hs hx)
    have hi := i.isLt
    unfold vertex
    omega
  have hfinite := sum_fullDefectWeight_le_global (L + 1) (3 * M) s ((M : ℝ) ^ (epsilon / 2))
    (by positivity) hxpos hcover (fun x hx => hpoint M (by omega) L hlower hupper x (hs hx))
  have hglobal := card_positiveHDefectValues_cast_le_sqrt_mul_exp (L + 1) (3 * M)
  have hsqrt : Real.sqrt (3 * M : ℕ) ≤ 2 * Real.sqrt M := by
    calc
      _ = Real.sqrt 3 * Real.sqrt M := by push_cast; rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num [Real.sqrt_le_iff]) (Real.sqrt_nonneg _)
  have hfac := hfactor M (by omega) L (by simpa using hupper)
  rw [abs_of_nonneg (by positivity)] at hfac
  have hB : (1 : ℝ) ≤ L + 1 := by have := Nat.cast_nonneg (α := ℝ) L; linarith
  have hpow : (L + 1 : ℝ) ≤ (L + 1 : ℝ) ^ 5 := by
    simpa using pow_le_pow_right₀ hB (by omega : 1 ≤ 5)
  have hexp : Real.exp (2 * Real.sqrt (L + 1 : ℝ)) ≤ Real.exp (4 * Real.sqrt (L + 1 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sqrt_nonneg (L + 1 : ℝ)]
  have hsmall : 2 * (L + 1 : ℝ) * Real.exp (2 * Real.sqrt (L + 1 : ℝ)) ≤ (M : ℝ) ^ (epsilon / 2) :=
    (by gcongr : 2 * (L + 1 : ℝ) * Real.exp (2 * Real.sqrt (L + 1 : ℝ)) ≤
      2 * (L + 1 : ℝ) ^ 5 * Real.exp (4 * Real.sqrt (L + 1 : ℝ))).trans hfac
  simp only [Nat.cast_add,Nat.cast_one] at hfinite hglobal
  calc
    _ ≤ _ := hfinite
    _ ≤ (L + 1 : ℝ) * (Real.sqrt (3 * M : ℕ) * Real.exp (2 * Real.sqrt (L + 1 : ℝ))) *
        (M : ℝ) ^ (epsilon / 2) := by gcongr
    _ ≤ (L + 1 : ℝ) * ((2 * Real.sqrt M) * Real.exp (2 * Real.sqrt (L + 1 : ℝ))) *
        (M : ℝ) ^ (epsilon / 2) := by gcongr
    _ = Real.sqrt M * (2 * (L + 1 : ℝ) * Real.exp (2 * Real.sqrt (L + 1 : ℝ))) *
        (M : ℝ) ^ (epsilon / 2) := by ring
    _ ≤ Real.sqrt M * (M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2) := by gcongr
    _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos]; congr 1; ring

/-- An arbitrary finite family of actual infinite affine occurrence indicators. -/
def affineOccurrenceCount (L : ℕ) (s : Finset ℕ) (b : ℕ → Fin L → F₂)
    (omega : InfiniteSample) : ℝ :=
  ∑ x ∈ s, (infiniteAffineStartEvent x L (b x)).indicator (fun _ => (1 : ℝ)) omega

/-- The ordinary finite start count in the source model, with its actual position mask. -/
def startOccurrenceCount (L : ℕ) (s : Finset ℕ) (omega : InfiniteSample) : ℝ :=
  ∑ x ∈ s, (infiniteStartEvent x L).indicator (fun _ => (1 : ℝ)) omega

/-- Every individual affine indicator is integrable. -/
theorem integrable_affineIndicator (x L : ℕ) (b : Fin L → F₂) :
    Integrable ((infiniteAffineStartEvent x L b).indicator (fun _ => (1 : ℝ))) infiniteRademacherMeasure :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_infiniteAffineStartEvent x L b)

/-- The finite family of affine occurrences is integrable. -/
theorem integrable_affineOccurrenceCount (L : ℕ) (s : Finset ℕ) (b : ℕ → Fin L → F₂) :
    Integrable (affineOccurrenceCount L s b) infiniteRademacherMeasure :=
  integrable_finsetSum s fun x _ => integrable_affineIndicator x L (b x)

/-- Integration gives the actual infinite affine probability sum. -/
theorem integral_affineOccurrenceCount (L : ℕ) (s : Finset ℕ) (b : ℕ → Fin L → F₂) :
    (∫ omega, affineOccurrenceCount L s b omega ∂infiniteRademacherMeasure) =
      ∑ x ∈ s, infiniteAffineStartProbability x L (b x) := by
  unfold affineOccurrenceCount
  rw [integral_finsetSum s (fun x _ => integrable_affineIndicator x L (b x))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_indicator_const (1 : ℝ) (measurableSet_infiniteAffineStartEvent x L (b x))]
  simp [infiniteAffineStartProbability,measureReal_def]

/-- The ordinary source count is integrable for every finite mask. -/
theorem integrable_startOccurrenceCount (L : ℕ) (s : Finset ℕ) :
    Integrable (startOccurrenceCount L s) infiniteRademacherMeasure :=
  integrable_finsetSum s fun x _ =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_infiniteStartEvent x L)

/-- Its literal expectation equals the sum of retained infinite start probabilities. -/
theorem integral_startOccurrenceCount (L : ℕ) (s : Finset ℕ) :
    (∫ omega, startOccurrenceCount L s omega ∂infiniteRademacherMeasure) =
      ∑ x ∈ s, infiniteStartProbability x L := by
  unfold startOccurrenceCount
  rw [integral_finsetSum s (fun x _ =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_infiniteStartEvent x L))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_indicator_const (1 : ℝ) (measurableSet_infiniteStartEvent x L)]
  simp [infiniteStartProbability,measureReal_def]

/-- Specializing the right-hand sides gives exactly the ordinary start count. -/
theorem affineOccurrenceCount_startRhs_eq {L : ℕ} (hL : 0 < L) (s : Finset ℕ) :
    affineOccurrenceCount L s (fun _ => startRhs L) = startOccurrenceCount L s := by
  funext omega
  unfold affineOccurrenceCount startOccurrenceCount
  apply Finset.sum_congr rfl
  intro x _
  rw [infiniteAffineStartEvent_startRhs_eq hL]

/-- Finite first-moment error, with no independence assumption among positions. -/
theorem abs_affine_expectation_sub_baseline_le (L : ℕ) (s : Finset ℕ)
    (b : ℕ → Fin L → F₂) (hL : 0 < L) (hpos : ∀ x ∈ s, 2 ≤ x) :
    |(∫ omega, affineOccurrenceCount L s b omega ∂infiniteRademacherMeasure) -
      (s.card : ℝ) / (2 : ℝ) ^ L| ≤
        (∑ x ∈ s, ((2 : ℝ) ^ (defectIndices (L + 1) x (L + 1)).card - 1)) / (2 : ℝ) ^ L := by
  rw [integral_affineOccurrenceCount]
  have hbase : (s.card : ℝ) / (2 : ℝ) ^ L = ∑ _x ∈ s, 1 / (2 : ℝ) ^ L := by
    simp [div_eq_mul_inv]
  rw [hbase,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x ∈ s, |infiniteAffineStartProbability x L (b x) - 1 / (2 : ℝ) ^ L| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ s, ((2 : ℝ) ^ (defectIndices (L + 1) x (L + 1)).card - 1) / (2 : ℝ) ^ L := by
      apply Finset.sum_le_sum
      intro x hx
      refine (corollary_two_five_pointwise_infinite (hpos x hx) hL (b x)).trans ?_
      have hcount := card_nonroot_defects_le_full (x := x) (L := L) (by have := hpos x hx; omega)
      exact div_le_div_of_nonneg_right
        (sub_le_sub_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcount) 1) (by positivity)
    _ = _ := (Finset.sum_div _ _ _).symm

/-- The macroscopic affine first moment, with the threshold before every mask and all right-hand sides. -/
theorem corollary_two_five_macroscopic_affine_expectation
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ s : Finset ℕ, s ⊆ macroscopicStarts M delta → ∀ b : ℕ → Fin L → F₂,
        |(∫ omega, affineOccurrenceCount L s b omega ∂infiniteRademacherMeasure) -
          (s.card : ℝ) / (2 : ℝ) ^ L| ≤ (M : ℝ) ^ (1 / (2 : ℝ) + epsilon) / (2 : ℝ) ^ L := by
  obtain ⟨Mmass,hmass⟩ := sum_fullDefectWeight_le_half_power_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  obtain ⟨Mlength,hlength⟩ := MacroscopicShallowSigma.length_ge_eventually_of_logarithmic_lower
    betaMin hbetaMin 2
  refine ⟨max Mmass (max Mlength 2), ?_⟩
  intro M hM L hlower hupper s hs b
  have hL : 0 < L := by
    have hh := hlength M (by omega) L (by simpa using hlower)
    have htwo : 2 ≤ L + 1 := by exact_mod_cast hh
    omega
  have hxpos : ∀ x ∈ s, 2 ≤ x := fun x hx =>
    (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc (by omega) hdelta (hs hx))).1
  exact (abs_affine_expectation_sub_baseline_le L s b hL hxpos).trans
    (div_le_div_of_nonneg_right (hmass M (by omega) L hlower hupper s hs) (by positivity))

/-- Corollary 2.5 on every mask of the exact macroscopic interval, as a true source-model integral. -/
theorem corollary_two_five_macroscopic_expectation
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ s : Finset ℕ, s ⊆ macroscopicStarts M delta →
        |(∫ omega, startOccurrenceCount L s omega ∂infiniteRademacherMeasure) -
          (s.card : ℝ) / (2 : ℝ) ^ L| ≤ (M : ℝ) ^ (1 / (2 : ℝ) + epsilon) / (2 : ℝ) ^ L := by
  obtain ⟨Maffine,haffine⟩ := corollary_two_five_macroscopic_affine_expectation
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  obtain ⟨Mlength,hlength⟩ := MacroscopicShallowSigma.length_ge_eventually_of_logarithmic_lower
    betaMin hbetaMin 2
  refine ⟨max Maffine Mlength, ?_⟩
  intro M hM L hlower hupper s hs
  have hL : 0 < L := by
    have hh := hlength M (by omega) L (by simpa using hlower)
    have htwo : 2 ≤ L + 1 := by exact_mod_cast hh
    omega
  simpa only [affineOccurrenceCount_startRhs_eq hL] using
    haffine M (by omega) L hlower hupper s hs (fun _ => startRhs L)

/-- Dyadic clause with the retained reciprocal-power representation of the subpolynomial error. -/
theorem corollary_two_five_dyadic_expectation
    {betaMin betaMax : ℝ} (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (k : ℕ) (hk : 0 < k) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ s : Finset ℕ, s ⊆ dyadicBlock N →
        |(∫ omega, startOccurrenceCount L s omega ∂infiniteRademacherMeasure) -
          (s.card : ℝ) / (2 : ℝ) ^ L| ^ (2 * k) ≤ (N : ℝ) ^ (k + 1) / ((2 : ℝ) ^ L) ^ (2 * k) := by
  obtain ⟨Nmass,hmass⟩ := WordDefectAsymptotics.wordDefectMass_uniformHalfPower_on_window hbetaMin hbeta k hk
  obtain ⟨Nlength,hlength⟩ := MacroscopicShallowSigma.length_ge_eventually_of_logarithmic_lower betaMin hbetaMin 2
  refine ⟨max Nmass (max Nlength 2), ?_⟩
  intro N hN L hlower hupper s hs
  have hNtwo : 2 ≤ N := by omega
  have hL : 0 < L := by
    have hh := hlength N (by omega) L (by simpa using hlower)
    have htwo : 2 ≤ L + 1 := by exact_mod_cast hh
    omega
  have hfinite := abs_affine_expectation_sub_baseline_le L s (fun _ => startRhs L) hL
    (fun x hx => two_le_of_mem_dyadicBlock hNtwo (hs hx))
  rw [affineOccurrenceCount_startRhs_eq hL] at hfinite
  have hsum := WordFirstMomentAsymptotics.sum_wordDefectWeight_cast_le_wordDefectMass N (L + 1) s hs
  have hbound := hfinite.trans (div_le_div_of_nonneg_right hsum (by positivity))
  have hm := hmass N (by omega) (L + 1) (by exact ⟨hbetaMin,hbeta,by simpa using hlower,by simpa using hupper⟩)
  rw [abs_of_nonneg (by positivity)] at hm
  calc
    _ ≤ ((wordDefectMass N (L + 1) : ℝ) / (2 : ℝ) ^ L) ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg _) hbound _
    _ = (wordDefectMass N (L + 1) : ℝ) ^ (2 * k) / ((2 : ℝ) ^ L) ^ (2 * k) := div_pow _ _ _
    _ ≤ _ := div_le_div_of_nonneg_right hm (by positivity)

end
end PaperC.V282.MacroscopicFirstMoment
