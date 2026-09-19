import PaperCV282.PoissonFieldMeasure
import Mathlib.Probability.Moments.Variance

/-! # Overlapping-window frequencies under the actual product Poisson law

Only windows with disjoint sites are independent. Counting the remaining
ordered pairs gives the paper's sharp `(2h-1)/(4N)` variance bound.
-/
namespace PaperC.Prel8.EmpiricalWindowVariance
open MeasureTheory ProbabilityTheory
open PaperC.V282.PoissonFieldMeasure
open scoped BigOperators NNReal
noncomputable section
set_option maxHeartbeats 400000

/-- The actual sites in the length-h window starting at u, on a finite field. -/
def window (n h u : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => u ≤ i.val ∧ i.val < u+h

/-- The integer count in a window. -/
def windowCount {n : ℕ} (h u : ℕ) (x : Fin n → ℕ) : ℕ :=
  ∑ i ∈ window n h u, x i

/-- Indicator of a prescribed window count. -/
def hit {n : ℕ} (h u r : ℕ) (x : Fin n → ℕ) : ℝ :=
  if windowCount h u x = r then 1 else 0

/-- Empirical frequency across N overlapping origins. -/
def frequency {n : ℕ} (N h r : ℕ) (x : Fin n → ℕ) : ℝ :=
  (∑ u : Fin N, hit h u.val r x) / N

/-- Separated windows use disjoint coordinates, including truncated boundary windows. -/
theorem window_disjoint {n h u v : ℕ} (huv : u+h ≤ v ∨ v+h ≤ u) :
    Disjoint (window n h u) (window n h v) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [window, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  rcases huv with huv | huv <;> omega

/-- True independence of the two window indicators, from product-coordinate independence. -/
theorem hit_independent {n h u v : ℕ} (rate : Fin n → ℝ≥0) (r s : ℕ)
    (huv : u+h ≤ v ∨ v+h ≤ u) :
    IndepFun (hit (n := n) h u r) (hit h v s) (fieldMeasure rate) := by
  have hd := (independent_coordinates rate).indepFun_finset
    (window n h u) (window n h v) (window_disjoint huv)
    (fun i => measurable_pi_apply i)
  unfold hit windowCount
  simpa only [Function.comp_def, Finset.sum_coe_sort, Finset.sum_attach] using hd.comp
    (measurable_of_countable (fun y : window n h u → ℕ =>
      if (∑ i, y i) = r then (1:ℝ) else 0))
    (measurable_of_countable (fun y : window n h v → ℕ =>
      if (∑ i, y i) = s then (1:ℝ) else 0))

/-- All hit indicators are square-integrable. -/
theorem hit_memLp {n : ℕ} (rate : Fin n → ℝ≥0) (h u r : ℕ) :
    MemLp (hit (n := n) h u r) 2 (fieldMeasure rate) := by
  apply memLp_of_bounded (a := 0) (b := 1)
    (Filter.Eventually.of_forall fun x => by
      simp only [hit]; split <;> norm_num)
    (measurable_of_countable _).aestronglyMeasurable

/-- Any two [0,1]-valued random variables have covariance at most 1/4. -/
theorem covariance_le_quarter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (bX : ∀ x, X x ∈ Set.Icc (0:ℝ) 1) (bY : ∀ x, Y x ∈ Set.Icc (0:ℝ) 1) :
    covariance X Y μ ≤ 1/4 := by
  have mX := memLp_of_bounded (μ := μ) (Filter.Eventually.of_forall bX) hX.aestronglyMeasurable 2
  have mY := memLp_of_bounded (μ := μ) (Filter.Eventually.of_forall bY) hY.aestronglyMeasurable 2
  have vX := variance_le_sq_of_bounded (μ := μ) (Filter.Eventually.of_forall bX) hX.aemeasurable
  have vY := variance_le_sq_of_bounded (μ := μ) (Filter.Eventually.of_forall bY) hY.aemeasurable
  have hv := variance_nonneg (fun x => X x-Y x) μ
  rw [variance_fun_sub mX mY] at hv
  norm_num at vX vY
  linarith

/-- At most 2h-1 origins can overlap a fixed positive-length window. -/
theorem overlap_card_le (N h : ℕ) (hh : 0 < h) (u : Fin N) :
    (Finset.univ.filter (fun v : Fin N => ¬(u.val+h ≤ v.val ∨ v.val+h ≤ u.val))).card ≤
      2*h-1 := by
  let S := Finset.univ.filter (fun v : Fin N => ¬(u.val+h ≤ v.val ∨ v.val+h ≤ u.val))
  have hin : S.image Fin.val ⊆ Finset.Ico (u.val+1-h) (u.val+h) := by
    intro v hvin
    obtain ⟨v,hvmem,rfl⟩ := Finset.mem_image.mp hvin
    have hv := (Finset.mem_filter.mp hvmem).2
    push Not at hv
    simp only [Finset.mem_Ico]
    omega
  have hi : S.card = (S.image Fin.val).card :=
    (Finset.card_image_of_injective _ Fin.val_injective).symm
  change S.card ≤ _
  rw [hi]
  have hc := Finset.card_le_card hin
  rw [Nat.card_Ico] at hc
  omega

/-- The covariance sum retains only overlapping windows. -/
theorem hit_covariance_sum_le {n N h : ℕ} (rate : Fin n → ℝ≥0)
    (hh : 0 < h) (r : ℕ) (u : Fin N) :
    (∑ v : Fin N, covariance (hit (n := n) h u.val r) (hit h v.val r)
      (fieldMeasure rate)) ≤ (2*(h:ℝ)-1)/4 := by
  classical
  let S := Finset.univ.filter (fun v : Fin N => ¬(u.val+h ≤ v.val ∨ v.val+h ≤ u.val))
  have hb (v : Fin N) : covariance (hit (n := n) h u.val r) (hit h v.val r)
      (fieldMeasure rate) ≤ if v ∈ S then (1:ℝ)/4 else 0 := by
    by_cases hv : v ∈ S
    · rw [ite_eq_left hv]
      apply covariance_le_quarter _ _ _ (measurable_of_countable _) (measurable_of_countable _)
      all_goals intro x; simp only [hit]; split <;> norm_num
    · rw [ite_eq_right hv]
      have hsep : u.val+h ≤ v.val ∨ v.val+h ≤ u.val := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hv
        exact hv
      rw [(hit_independent rate r r hsep).covariance_eq_zero
        (hit_memLp rate h u.val r) (hit_memLp rate h v.val r)]
  have hs := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hb v)
  have hc : (S.card:ℝ) ≤ 2*(h:ℝ)-1 := by
    have hc := overlap_card_le N h hh u
    have he : 1 ≤ 2*h := by omega
    exact_mod_cast (by simpa only [Nat.cast_sub he, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] using (Nat.cast_le (α := ℝ)).mpr hc : (S.card:ℝ) ≤ 2*(h:ℝ)-1)
  have he : (∑ v : Fin N, if v ∈ S then (1:ℝ)/4 else 0) = S.card/4 := by
    rw [← Finset.sum_filter]
    simp [S, div_eq_mul_inv]
  rw [he] at hs
  linarith

/-- The exact moving-window variance bound; no independence between overlapping origins. -/
theorem frequency_variance_le {n N h : ℕ} (rate : Fin n → ℝ≥0)
    (hN : 0 < N) (hh : 0 < h) (r : ℕ) :
    variance (frequency (n := n) N h r) (fieldMeasure rate) ≤
      (2*(h:ℝ)-1)/(4*N) := by
  have hm : MemLp (fun x : Fin n → ℕ => ∑ u : Fin N, hit h u.val r x) 2
      (fieldMeasure rate) := memLp_finsetSum _ (fun u _ => hit_memLp rate h u.val r)
  have hc := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset (Fin N))) =>
    hit_covariance_sum_le rate hh r u)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hc
  have hv : variance (fun x : Fin n → ℕ => ∑ u : Fin N, hit h u.val r x)
      (fieldMeasure rate) ≤ N*((2*(h:ℝ)-1)/4) := by
    rw [← covariance_self hm.aemeasurable, covariance_fun_sum_fun_sum
      (fun u : Fin N => hit_memLp rate h u.val r) (fun u : Fin N => hit_memLp rate h u.val r)]
    exact hc
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  unfold frequency
  simp only [div_eq_mul_inv]
  rw [variance_mul_const]
  calc
    _ ≤ (N*((2*(h:ℝ)-1)/4))*((N:ℝ)⁻¹)^2 := mul_le_mul_of_nonneg_right hv (sq_nonneg _)
    _ = _ := by field_simp

end
end PaperC.Prel8.EmpiricalWindowVariance
