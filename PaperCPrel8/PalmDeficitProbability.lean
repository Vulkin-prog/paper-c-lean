import PaperCPrel8.PalmVoidAverage

/-! # Averaged bounded deficits and target-configuration probability

The state space and target law may change with the scale. All expectations
are weighted by actual normalized target masses, not counting measure.
-/
namespace PaperC.Prel8.PalmDeficitProbability
open Filter Topology
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {Z : Type*}

def mean (q f : Z → ℝ) : ℝ := ∑' z, q z*f z

def exceedance (q f : Z → ℝ) (t : ℝ) : ℝ := ∑' z, if t < f z then q z else 0

theorem summable_mean {q f : Z → ℝ} (hqsum : Summable q) (hq : ∀ z, 0 ≤ q z)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1) : Summable (fun z => q z*f z) :=
  hqsum.of_nonneg_of_le (fun z => mul_nonneg (hq z) (hf z).1)
    (fun z => mul_le_of_le_one_right (hq z) (hf z).2)

theorem summable_exceedance {q f : Z → ℝ} (hqsum : Summable q) (hq : ∀ z, 0 ≤ q z)
    (t : ℝ) : Summable (fun z => if t < f z then q z else 0) :=
  hqsum.of_nonneg_of_le (fun z => by split_ifs; exact hq z; exact le_rfl)
    (fun z => by split_ifs; exact le_rfl; exact hq z)

theorem mean_nonneg {q f : Z → ℝ} (hq : ∀ z, 0 ≤ q z) (hf : ∀ z, 0 ≤ f z) : 0 ≤ mean q f :=
  tsum_nonneg (fun z => mul_nonneg (hq z) (hf z))

theorem exceedance_nonneg {q f : Z → ℝ} (hq : ∀ z, 0 ≤ q z) (t : ℝ) : 0 ≤ exceedance q f t :=
  tsum_nonneg (fun z => by split_ifs; exact hq z; exact le_rfl)

/-- Markov bound for the actual target-weighted one-sided defect. -/
theorem exceedance_le {q f : Z → ℝ} (hqsum : Summable q) (hq : ∀ z, 0 ≤ q z)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1) {t : ℝ} (ht : 0 < t) :
    exceedance q f t ≤ mean q f/t := by
  apply (le_div_iff₀ ht).mpr
  unfold exceedance mean
  rw [← tsum_mul_right]
  apply ((summable_exceedance hqsum hq t).mul_right t).tsum_le_tsum _ (summable_mean hqsum hq hf)
  intro z
  by_cases hz : t < f z
  · simp only [hz,ite_true]; exact mul_le_mul_of_nonneg_left hz.le (hq z)
  · simp only [hz,ite_false,zero_mul]; exact mul_nonneg (hq z) (hf z).1

/-- Boundedness gives the converse control needed for convergence in probability. -/
theorem mean_le_threshold {q f : Z → ℝ} (hqsum : HasSum q 1) (hq : ∀ z, 0 ≤ q z)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    mean q f ≤ t+exceedance q f t := by
  have hsum := summable_exceedance (f := f) hqsum.summable hq t
  calc
    _ ≤ ∑' z, (q z*t+(if t < f z then q z else 0)) :=
      (summable_mean hqsum.summable hq hf).tsum_le_tsum (fun z => by
        by_cases hz : t < f z
        · simp only [hz,ite_true]
          have h := mul_le_of_le_one_right (hq z) (hf z).2
          nlinarith [mul_nonneg (hq z) ht]
        · simp only [hz,ite_false,add_zero]
          exact mul_le_mul_of_nonneg_left (le_of_not_gt hz) (hq z))
        ((hqsum.summable.mul_right t).add hsum)
    _ = _ := by rw [(hqsum.summable.mul_right t).tsum_add hsum,tsum_mul_right,hqsum.tsum_eq,one_mul]; rfl

/-- The precise bounded-defect equivalence used in G.5, on varying target spaces. -/
theorem mean_tendsto_zero_iff {Z : ℕ → Type*} (q f : (N : ℕ) → Z N → ℝ)
    (hqsum : ∀ N, HasSum (q N) 1) (hq : ∀ N z, 0 ≤ q N z)
    (hf : ∀ N z, 0 ≤ f N z ∧ f N z ≤ 1) :
    Tendsto (fun N => mean (q N) (f N)) atTop (𝓝 0) ↔
      ∀ t : ℝ, 0 < t → Tendsto (fun N => exceedance (q N) (f N) t) atTop (𝓝 0) := by
  constructor
  · intro hm t ht
    apply squeeze_zero' (Eventually.of_forall (fun N => exceedance_nonneg (hq N) t))
      (Eventually.of_forall (fun N => exceedance_le (hqsum N).summable (hq N) (hf N) ht))
    simpa only [zero_div] using hm.div_const t
  · intro he
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun N => ha.trans_le (mean_nonneg (hq N) (fun z => (hf N z).1)))
    · intro b hb
      filter_upwards [(tendsto_order.mp (he (b/2) (by linarith))).2 (b/2) (by linarith)] with N hN
      have h := mean_le_threshold (hqsum N) (hq N) (hf N) (show 0 ≤ b/2 by linarith)
      linarith

end
end PaperC.Prel8.PalmDeficitProbability
