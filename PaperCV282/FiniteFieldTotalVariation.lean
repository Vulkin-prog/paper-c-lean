import PaperC.Probability.SectionThirteenFiniteBound

/-!
# Half-L1 variation and finite pushforwards for finite fields

The target type is arbitrary, in particular a finite vector of natural counts.
Every application to probability laws supplies exact mass one and summability.
The notation does not equip the infinite state space with a fictitious Fintype.
-/

namespace PaperC.V282.FiniteFieldTotalVariation

open ArratiaGoldsteinGordonInput
open scoped BigOperators

noncomputable section

variable {α : Type*}

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Half-`ℓ¹` total variation for two real mass functions on `α`. -/
def massTotalVariation
    (p q : α → ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑' k : α, |p k - q k|

/-- The absolute difference of two summable nonnegative mass functions is
summable. -/
theorem summable_abs_sub_of_nonneg
    {p q : α → ℝ}
    (hp : Summable p) (hq : Summable q)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) :
    Summable fun k ↦ |p k - q k| := by
  apply (hp.add hq).of_nonneg_of_le
  · intro k
    exact abs_nonneg _
  · intro k
    exact abs_sub_le_iff.mpr
      ⟨by linarith [hp0 k, hq0 k], by linarith [hp0 k, hq0 k]⟩

/-- Total variation is nonnegative whenever its defining series is summable. -/
theorem massTotalVariation_nonneg
    (p q : α → ℝ) :
    0 ≤ massTotalVariation p q := by
  unfold massTotalVariation
  exact mul_nonneg (by positivity)
    (tsum_nonneg fun _ ↦ abs_nonneg _)

/-- Symmetry of half-`ℓ¹` total variation. -/
theorem massTotalVariation_comm
    (p q : α → ℝ) :
    massTotalVariation p q = massTotalVariation q p := by
  unfold massTotalVariation
  congr 1
  apply tsum_congr
  intro k
  exact abs_sub_comm _ _

/-- Triangle inequality for discrete total variation. -/
theorem massTotalVariation_triangle
    {p q r : α → ℝ}
    (hp : Summable p) (hq : Summable q) (hr : Summable r)
    (hp0 : ∀ k, 0 ≤ p k)
    (hq0 : ∀ k, 0 ≤ q k)
    (hr0 : ∀ k, 0 ≤ r k) :
    massTotalVariation p r ≤
      massTotalVariation p q + massTotalVariation q r := by
  have hpq :
      Summable fun k ↦ |p k - q k| :=
    summable_abs_sub_of_nonneg hp hq hp0 hq0
  have hqr :
      Summable fun k ↦ |q k - r k| :=
    summable_abs_sub_of_nonneg hq hr hq0 hr0
  have hpr :
      Summable fun k ↦ |p k - r k| :=
    summable_abs_sub_of_nonneg hp hr hp0 hr0
  have hsum :
      (∑' k : α, |p k - r k|) ≤
        ∑' k : α, (|p k - q k| + |q k - r k|) := by
    exact hpr.tsum_le_tsum
      (fun k ↦ by
        calc
          |p k - r k| =
              |(p k - q k) + (q k - r k)| := by ring_nf
          _ ≤ |p k - q k| + |q k - r k| := abs_add_le _ _)
      (hpq.add hqr)
  unfold massTotalVariation
  calc
    (2 : ℝ)⁻¹ * ∑' k : α, |p k - r k| ≤
        (2 : ℝ)⁻¹ *
          ∑' k : α, (|p k - q k| + |q k - r k|) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ =
        (2 : ℝ)⁻¹ * ∑' k : α, |p k - q k| +
          (2 : ℝ)⁻¹ * ∑' k : α, |q k - r k| := by
      rw [hpq.tsum_add hqr]
      ring

/-! ## Uniform finite mixtures -/

/-- Uniform average of a finite family of real numbers. -/
def uniformAverage
    {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (∑ i, f i) / (Fintype.card ι : ℝ)

/--
Convexity of total variation under a finite uniform mixture.  The reference
mass `q` is the same in every component.
-/
theorem massTotalVariation_uniformMixture_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → α → ℝ) (q : α → ℝ)
    (hsummable :
      ∀ i, Summable fun k ↦ |p i k - q k|) :
    massTotalVariation
        (fun k ↦ uniformAverage (fun i ↦ p i k)) q ≤
      uniformAverage
        (fun i ↦ massTotalVariation (p i) q) := by
  classical
  let d : ℝ := Fintype.card ι
  have hdNat : 0 < Fintype.card ι := Fintype.card_pos
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast hdNat
  have hsumAbs :
      Summable fun k : α ↦
        ∑ i : ι, |p i k - q k| :=
    (hasSum_sum (s := Finset.univ)
      (fun i _hi ↦ (hsummable i).hasSum)).summable
  have hpoint :
      ∀ k : α,
        |uniformAverage (fun i ↦ p i k) - q k| ≤
          uniformAverage (fun i ↦ |p i k - q k|) := by
    intro k
    unfold uniformAverage
    have hsumq :
        (∑ _i : ι, q k) = (Fintype.card ι : ℝ) * q k := by
      simp
    rw [show (∑ i, p i k) / (Fintype.card ι : ℝ) - q k =
        (∑ i, (p i k - q k)) / (Fintype.card ι : ℝ) by
      rw [Finset.sum_sub_distrib, hsumq]
      field_simp]
    rw [abs_div, abs_of_pos hd]
    apply div_le_div_of_nonneg_right
    · exact Finset.abs_sum_le_sum_abs _ _
    · exact hd.le
  have hleftSummable :
      Summable fun k ↦
        |uniformAverage (fun i ↦ p i k) - q k| := by
    have hrightSummable :
        Summable fun k ↦
          uniformAverage (fun i ↦ |p i k - q k|) := by
      unfold uniformAverage
      exact hsumAbs.div_const _
    exact hrightSummable.of_nonneg_of_le
      (fun k ↦ abs_nonneg _) hpoint
  have hrightSummable :
      Summable fun k ↦
        uniformAverage (fun i ↦ |p i k - q k|) := by
    unfold uniformAverage
    exact hsumAbs.div_const _
  have htsum :
      (∑' k : α,
          |uniformAverage (fun i ↦ p i k) - q k|) ≤
        ∑' k : α,
          uniformAverage (fun i ↦ |p i k - q k|) :=
    hleftSummable.tsum_le_tsum hpoint hrightSummable
  have hinterchange :
      (∑' k : α,
          uniformAverage (fun i ↦ |p i k - q k|)) =
        uniformAverage
          (fun i ↦ ∑' k : α, |p i k - q k|) := by
    unfold uniformAverage
    rw [tsum_div_const]
    congr 1
    exact Summable.tsum_finsetSum
      (s := Finset.univ) (fun i _hi ↦ hsummable i)
  unfold massTotalVariation
  calc
    (2 : ℝ)⁻¹ *
          ∑' k : α,
            |uniformAverage (fun i ↦ p i k) - q k| ≤
        (2 : ℝ)⁻¹ *
          ∑' k : α,
            uniformAverage (fun i ↦ |p i k - q k|) :=
      mul_le_mul_of_nonneg_left htsum (by positivity)
    _ =
        (2 : ℝ)⁻¹ *
          uniformAverage
            (fun i ↦ ∑' k : α, |p i k - q k|) := by
      rw [hinterchange]
    _ =
        uniformAverage
          (fun i ↦
            (2 : ℝ)⁻¹ * ∑' k : α, |p i k - q k|) := by
      unfold uniformAverage
      rw [← Finset.mul_sum]
      ring

/-! ## Pushforward laws and the coupling inequality -/

/-- Law of an discrete-valued function on a finite probability space. -/
def finiteFieldLaw
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → α) (k : α) : ℝ := by
  classical
  exact ∑ ω, if Z ω = k then μ.prob ω else 0

/-- The pushforward law is nonnegative. -/
theorem finiteFieldLaw_nonneg
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → α) (k : α) :
    0 ≤ finiteFieldLaw μ Z k := by
  classical
  unfold finiteFieldLaw
  exact Finset.sum_nonneg fun ω _ ↦ by
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl

/-- The pushforward mass function has total mass one. -/
theorem hasSum_finiteFieldLaw
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → α) :
    HasSum (finiteFieldLaw μ Z) 1 := by
  classical
  let support : Finset α := Finset.univ.image Z
  have hout :
      ∀ k ∉ support, finiteFieldLaw μ Z k = 0 := by
    intro k hk
    unfold finiteFieldLaw
    apply Finset.sum_eq_zero
    intro ω _hω
    rw [if_neg]
    intro hZ
    apply hk
    exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, hZ⟩
  have hsum :
      ∑ k ∈ support, finiteFieldLaw μ Z k = 1 := by
    unfold finiteFieldLaw
    rw [Finset.sum_comm]
    calc
      (∑ ω, ∑ k ∈ support, if Z ω = k then μ.prob ω else 0) =
          ∑ ω, μ.prob ω := by
        apply Finset.sum_congr rfl
        intro ω _hω
        have hmem : Z ω ∈ support :=
          Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩
        simp [hmem]
      _ = 1 := μ.sum_prob
  have hfinite :
      HasSum (finiteFieldLaw μ Z)
        (∑ k ∈ support, finiteFieldLaw μ Z k) :=
    hasSum_sum_of_ne_finset_zero hout
  rw [hsum] at hfinite
  exact hfinite

/-- The pushforward mass function is summable. -/
theorem summable_finiteFieldLaw
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → α) :
    Summable (finiteFieldLaw μ Z) :=
  (hasSum_finiteFieldLaw μ Z).summable


/-- Restricting a summable nonnegative mass to an arbitrary set remains summable. -/
theorem summable_restricted_mass {p : α → ℝ} (hp : Summable p)
    (hp0 : ∀ k, 0 ≤ p k) (A : Set α) :
    Summable (fun k => if k ∈ A then p k else 0) := by
  classical
  apply hp.of_nonneg_of_le
  · intro k
    split_ifs <;> simp [hp0]
  · intro k
    split_ifs <;> simp [hp0]

/-- The positive part of the mass difference is an exact maximizing test set. -/
theorem massTotalVariation_eq_positive_set {p q : α → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) :
    massTotalVariation p q =
      (∑' k, if q k ≤ p k then p k else 0) -
        ∑' k, if q k ≤ p k then q k else 0 := by
  classical
  have hpa : Summable (fun k => if q k ≤ p k then p k else 0) := by
    apply hp.summable.of_nonneg_of_le
    · intro k; split_ifs <;> simp [hp0]
    · intro k; split_ifs <;> simp [hp0]
  have hqa : Summable (fun k => if q k ≤ p k then q k else 0) := by
    apply hq.summable.of_nonneg_of_le
    · intro k; split_ifs <;> simp [hq0]
    · intro k; split_ifs <;> simp [hq0]
  have hpoint (k : α) : |p k - q k| =
      2 * ((if q k ≤ p k then p k else 0) - (if q k ≤ p k then q k else 0)) - (p k - q k) := by
    by_cases h : q k ≤ p k
    · rw [if_pos h, if_pos h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · rw [if_neg h, if_neg h, abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]
      ring
  unfold massTotalVariation
  simp_rw [hpoint]
  rw [((hpa.sub hqa).mul_left 2).tsum_sub (hp.summable.sub hq.summable),
    tsum_mul_left, hpa.tsum_sub hqa, hp.summable.tsum_sub hq.summable,
    hp.tsum_eq, hq.tsum_eq]
  ring

/-- A uniform bound for all test-set discrepancies bounds the exact half-L1 distance. -/
theorem massTotalVariation_le_of_test_sets {p q : α → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) {r : ℝ}
    (h : ∀ A : Set α,
      |(∑' k, if k ∈ A then p k else 0) - ∑' k, if k ∈ A then q k else 0| ≤ r) :
    massTotalVariation p q ≤ r := by
  rw [massTotalVariation_eq_positive_set hp hq hp0 hq0]
  exact (le_abs_self _).trans (h {k | q k ≤ p k})

/-- A finite pushforward assigns the same mass as its original event. -/
theorem restricted_finiteFieldLaw_eq_eventProbability {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (W : Ω → α) (A : Set α) :
    (∑' k, if k ∈ A then finiteFieldLaw μ W k else 0) =
      eventProbability μ (fun ω => W ω ∈ A) := by
  classical
  let s : Finset α := Finset.univ.image W
  have hout (k : α) (hk : k ∉ s) : finiteFieldLaw μ W k = 0 := by
    unfold finiteFieldLaw
    apply Finset.sum_eq_zero
    intro ω _
    have hne : W ω ≠ k := fun h => hk (Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, h⟩)
    simp [hne]
  rw [tsum_eq_sum (s := s) (fun k hk => by simp [hout k hk])]
  unfold finiteFieldLaw eventProbability
  calc
    _ = ∑ k ∈ s, ∑ ω, if W ω = k then (if k ∈ A then μ.prob ω else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k ∈ A
      · simp only [hk, if_true]
      · simp [hk]
    _ = ∑ ω, ∑ k ∈ s, if W ω = k then (if k ∈ A then μ.prob ω else 0) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ω _
      have hmem : W ω ∈ s := Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩
      simp [hmem]


theorem massTotalVariation_le_one {p q : α → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) :
    massTotalVariation p q ≤ 1 := by
  have hsum := (summable_abs_sub_of_nonneg hp.summable hq.summable hp0 hq0).tsum_le_tsum
    (fun k => abs_sub_le_iff.2 ⟨by linarith [hp0 k, hq0 k], by linarith [hp0 k, hq0 k]⟩)
    (hp.summable.add hq.summable)
  rw [hp.summable.tsum_add hq.summable, hp.tsum_eq, hq.tsum_eq] at hsum
  unfold massTotalVariation
  linarith

theorem hasSum_uniformMixture {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → α → ℝ) (hp : ∀ i, HasSum (p i) 1) :
    HasSum (fun k => uniformAverage (fun i => p i k)) 1 := by
  have h := (hasSum_sum (s := Finset.univ) (fun i _ => hp i)).div_const (Fintype.card ι : ℝ)
  simpa [uniformAverage, Fintype.card_ne_zero] using h

theorem uniformMixture_nonneg {ι : Type*} [Fintype ι]
    (p : ι → α → ℝ) (hp : ∀ i k, 0 ≤ p i k) (k : α) :
    0 ≤ uniformAverage (fun i => p i k) := by
  unfold uniformAverage
  exact div_nonneg (Finset.sum_nonneg (fun i _ => hp i k)) (by positivity)

theorem event_discrepancy_le_disagreement {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z W : Ω → α) (A : Set α) :
    |eventProbability μ (fun ω => Z ω ∈ A) - eventProbability μ (fun ω => W ω ∈ A)| ≤
      eventProbability μ (fun ω => Z ω ≠ W ω) := by
  classical
  unfold eventProbability
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ ω, |(if Z ω ∈ A then μ.prob ω else 0) -
      (if W ω ∈ A then μ.prob ω else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases heq : Z ω = W ω
      · simp [heq]
      · by_cases hz : Z ω ∈ A <;> by_cases hw : W ω ∈ A <;>
          simp [heq, hz, hw, abs_of_nonneg (μ.nonneg ω), μ.nonneg ω]

theorem massTotalVariation_finiteFieldLaw_le_disagreement {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z W : Ω → α) :
    massTotalVariation (finiteFieldLaw μ Z) (finiteFieldLaw μ W) ≤
      eventProbability μ (fun ω => Z ω ≠ W ω) := by
  apply massTotalVariation_le_of_test_sets (hasSum_finiteFieldLaw μ Z) (hasSum_finiteFieldLaw μ W)
    (finiteFieldLaw_nonneg μ Z) (finiteFieldLaw_nonneg μ W)
  intro A
  rw [restricted_finiteFieldLaw_eq_eventProbability, restricted_finiteFieldLaw_eq_eventProbability]
  exact event_discrepancy_le_disagreement μ Z W A

theorem disagreement_le_sum_coordinate_disagreements {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] (μ : FinitePMF Ω) (Z W : Ω → ι → ℕ) :
    eventProbability μ (fun ω => Z ω ≠ W ω) ≤
      ∑ i, eventProbability μ (fun ω => Z ω i ≠ W ω i) := by
  classical
  unfold eventProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases heq : Z ω = W ω
  · simp only [heq, ne_eq, not_true_eq_false, if_false]
    positivity
  · rw [if_pos heq]
    obtain ⟨i, hi⟩ : ∃ i, Z ω i ≠ W ω i := by
      by_contra h
      apply heq
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    calc
      μ.prob ω = if Z ω i ≠ W ω i then μ.prob ω else 0 := by simp [hi]
      _ ≤ ∑ j, if Z ω j ≠ W ω j then μ.prob ω else 0 :=
        Finset.single_le_sum (f := fun j => if Z ω j ≠ W ω j then μ.prob ω else 0)
          (fun j _ => by split_ifs <;> simp [μ.nonneg ω]) (Finset.mem_univ i)
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : Z ω j ≠ W ω j <;> simp [hj]

theorem massTotalVariation_finiteFieldLaw_le_coordinate_disagreements {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] (μ : FinitePMF Ω) (Z W : Ω → ι → ℕ) :
    massTotalVariation (finiteFieldLaw μ Z) (finiteFieldLaw μ W) ≤
      ∑ i, eventProbability μ (fun ω => Z ω i ≠ W ω i) :=
  (massTotalVariation_finiteFieldLaw_le_disagreement μ Z W).trans
    (disagreement_le_sum_coordinate_disagreements μ Z W)

def retainedField {Ω ι : Type*} (good : Finset ι) (W : Ω → ι → ℕ) (ω : Ω) (i : ι) : ℕ := by
  classical
  exact if i ∈ good then W ω i else 0

def badFieldSites {ι : Type*} [Fintype ι] (good : Finset ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => i ∉ good)

theorem mem_badFieldSites {ι : Type*} [Fintype ι] (good : Finset ι) (i : ι) :
    i ∈ badFieldSites good ↔ i ∉ good := by
  classical
  simp [badFieldSites]

theorem massTotalVariation_retainedField_le_bad_sites {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] (μ : FinitePMF Ω) (good : Finset ι) (W : Ω → ι → ℕ) :
    massTotalVariation (finiteFieldLaw μ W) (finiteFieldLaw μ (retainedField good W)) ≤
      ∑ i ∈ badFieldSites good, eventProbability μ (fun ω => W ω i ≠ 0) := by
  classical
  apply (massTotalVariation_finiteFieldLaw_le_coordinate_disagreements μ W (retainedField good W)).trans_eq
  rw [badFieldSites, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ good <;> simp [retainedField, hi, eventProbability]
  all_goals
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : W ω i = 0 <;> simp [hω]

end
end PaperC.V282.FiniteFieldTotalVariation
