import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Atomic convergence from inverse-power transforms

For probability masses on the positive integers, convergence of all
inverse-power (Dirichlet) transforms determines every atom.  The proof is
elementary: after multiplying the transform by `m^s`, subtract the already
known atoms below `m`; the remaining tail is at most
`(m / (m + 1))^s`.
-/

open scoped BigOperators Topology
open Filter

namespace PaperC
namespace DirichletAtomConvergence

noncomputable section

/-- Inverse-power transform `∑_j p(j) j⁻ˢ`. -/
def inversePowerTransform (p : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑' j : ℕ, p j * ((j : ℝ)⁻¹) ^ s

theorem inversePowerWeight_nonneg (j s : ℕ) :
    0 ≤ ((j : ℝ)⁻¹) ^ s := by positivity

theorem inversePowerWeight_le_one (j s : ℕ) :
    ((j : ℝ)⁻¹) ^ s ≤ 1 := by
  apply pow_le_one₀ (by positivity)
  by_cases hj : j = 0
  · simp [hj]
  · have hj1 : (1 : ℝ) ≤ j := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hj)
    have hjpos : (0 : ℝ) < j := by
      exact_mod_cast Nat.pos_of_ne_zero hj
    exact (inv_le_one₀ hjpos).2 hj1

theorem summable_inversePowerTransform
    {p : ℕ → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hp : Summable p) (s : ℕ) :
    Summable (fun j ↦ p j * ((j : ℝ)⁻¹) ^ s) := by
  apply Summable.of_nonneg_of_le
  · intro j
    exact mul_nonneg (hp0 j) (inversePowerWeight_nonneg j s)
  · intro j
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left
        (inversePowerWeight_le_one j s) (hp0 j)
  · exact hp

/-- The transform scaled at the atom `m`. -/
def scaledInversePowerTerm
    (p : ℕ → ℝ) (m s j : ℕ) : ℝ :=
  p j * (((m : ℝ) / (j : ℝ)) ^ s)

theorem scaledInversePowerTransform_eq
    {p : ℕ → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hp : Summable p) (m s : ℕ) :
    (m : ℝ) ^ s * inversePowerTransform p s =
      ∑' j : ℕ, scaledInversePowerTerm p m s j := by
  unfold inversePowerTransform scaledInversePowerTerm
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [div_eq_mul_inv, mul_pow]
  ring

theorem summable_scaledInversePowerTerm
    {p : ℕ → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hp : Summable p) (m s : ℕ) :
    Summable (scaledInversePowerTerm p m s) := by
  have heq :
      scaledInversePowerTerm p m s =
        fun j ↦ (m : ℝ) ^ s *
          (p j * ((j : ℝ)⁻¹) ^ s) := by
    funext j
    unfold scaledInversePowerTerm
    rw [div_eq_mul_inv, mul_pow]
    ring
  rw [heq]
  exact (summable_inversePowerTransform hp0 hp s).mul_left _

theorem scaledInversePowerTerm_self
    {p : ℕ → ℝ} {m s : ℕ} (hm : 0 < m) :
    scaledInversePowerTerm p m s m = p m := by
  unfold scaledInversePowerTerm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [div_self hm0, one_pow, mul_one]

/--
After removing the atoms below `m` and the atom at `m`, the scaled
transform is exactly the shifted tail.
-/
theorem scaledInversePowerTransform_sub_lower_sub_eq_tail
    {p : ℕ → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hp : Summable p) {m s : ℕ} (hm : 0 < m) :
    (m : ℝ) ^ s * inversePowerTransform p s -
          ∑ j ∈ Finset.range m, scaledInversePowerTerm p m s j -
        p m =
      ∑' i : ℕ, scaledInversePowerTerm p m s (i + (m + 1)) := by
  have hsumm :=
    summable_scaledInversePowerTerm hp0 hp m s
  have hsplit := hsumm.sum_add_tsum_nat_add (m + 1)
  rw [← scaledInversePowerTransform_eq hp0 hp m s,
    Finset.sum_range_succ,
    scaledInversePowerTerm_self hm] at hsplit
  linarith

/-- The geometric ratio controlling the tail above `m`. -/
def tailRatio (m : ℕ) : ℝ :=
  (m : ℝ) / (m + 1 : ℕ)

theorem tailRatio_nonneg (m : ℕ) :
    0 ≤ tailRatio m := by
  unfold tailRatio
  positivity

theorem tailRatio_lt_one (m : ℕ) :
    tailRatio m < 1 := by
  unfold tailRatio
  have hpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  rw [div_lt_one hpos]
  norm_num

theorem shifted_mass_tsum_le_one
    {p : ℕ → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hp : HasSum p 1) (k : ℕ) :
    ∑' i : ℕ, p (i + k) ≤ 1 := by
  have hsplit := hp.summable.sum_add_tsum_nat_add k
  rw [hp.tsum_eq] at hsplit
  have hprefix :
      0 ≤ ∑ i ∈ Finset.range k, p i :=
    Finset.sum_nonneg fun i _ ↦ hp0 i
  linarith

theorem scaledInversePowerTail_nonneg
    {p : ℕ → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (m s : ℕ) :
    0 ≤ ∑' i : ℕ,
      scaledInversePowerTerm p m s (i + (m + 1)) := by
  apply tsum_nonneg
  intro i
  unfold scaledInversePowerTerm
  exact mul_nonneg (hp0 _) (pow_nonneg (by positivity) _)

theorem scaledInversePowerTail_le
    {p : ℕ → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hp : HasSum p 1) (m s : ℕ) :
    ∑' i : ℕ,
        scaledInversePowerTerm p m s (i + (m + 1)) ≤
      tailRatio m ^ s := by
  have hpSumm : Summable p := hp.summable
  have hshift :
      Summable (fun i : ℕ ↦ p (i + (m + 1))) :=
    (summable_nat_add_iff (m + 1)).mpr hpSumm
  have hratio :
      ∀ i : ℕ,
        (0 : ℝ) ≤ (m : ℝ) / (i + (m + 1) : ℕ) ∧
        (m : ℝ) / (i + (m + 1) : ℕ) ≤ tailRatio m := by
    intro i
    constructor
    · positivity
    · unfold tailRatio
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · norm_cast
        omega
  have hterm :
      ∀ i : ℕ,
        scaledInversePowerTerm p m s (i + (m + 1)) ≤
          p (i + (m + 1)) * tailRatio m ^ s := by
    intro i
    unfold scaledInversePowerTerm
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hratio i).1 (hratio i).2 s)
      (hp0 _)
  have hleft :
      Summable (fun i : ℕ ↦
        scaledInversePowerTerm p m s (i + (m + 1))) := by
    apply Summable.of_nonneg_of_le
    · intro i
      unfold scaledInversePowerTerm
      exact mul_nonneg (hp0 _) (pow_nonneg (by positivity) _)
    · exact hterm
    · exact hshift.mul_right _
  calc
    (∑' i : ℕ,
        scaledInversePowerTerm p m s (i + (m + 1))) ≤
        ∑' i : ℕ,
          p (i + (m + 1)) * tailRatio m ^ s :=
      hleft.tsum_le_tsum hterm (hshift.mul_right _)
    _ =
        (∑' i : ℕ, p (i + (m + 1))) * tailRatio m ^ s := by
      rw [tsum_mul_right]
    _ ≤ 1 * tailRatio m ^ s := by
      exact mul_le_mul_of_nonneg_right
        (shifted_mass_tsum_le_one hp0 hp (m + 1))
        (pow_nonneg (tailRatio_nonneg m) s)
    _ = tailRatio m ^ s := one_mul _

theorem abs_scaledInversePowerTail_sub_le
    {p q : ℕ → ℝ}
    (hp0 : ∀ j, 0 ≤ p j) (hp : HasSum p 1)
    (hq0 : ∀ j, 0 ≤ q j) (hq : HasSum q 1)
    (m s : ℕ) :
    |(∑' i : ℕ,
        scaledInversePowerTerm p m s (i + (m + 1))) -
      (∑' i : ℕ,
        scaledInversePowerTerm q m s (i + (m + 1)))| ≤
      tailRatio m ^ s := by
  have hpLower :=
    scaledInversePowerTail_nonneg hp0 m s
  have hpUpper :=
    scaledInversePowerTail_le hp0 hp m s
  have hqLower :=
    scaledInversePowerTail_nonneg hq0 m s
  have hqUpper :=
    scaledInversePowerTail_le hq0 hq m s
  rw [abs_le]
  constructor <;> linarith

/--
Convergence of every inverse-power transform implies pointwise convergence
of the underlying probability masses on `ℕ`, once the atom at zero is
known.  For positive-integer-valued laws the zero-atom premise is immediate.
-/
theorem tendsto_atoms_of_inversePowerTransforms
    {p : ℕ → ℕ → ℝ} {q : ℕ → ℝ}
    (hp0 : ∀ n j, 0 ≤ p n j)
    (hp : ∀ n, HasSum (p n) 1)
    (hq0 : ∀ j, 0 ≤ q j)
    (hq : HasSum q 1)
    (hzero : Tendsto (fun n ↦ p n 0) atTop (𝓝 (q 0)))
    (htransform :
      ∀ s : ℕ,
        Tendsto
          (fun n ↦ inversePowerTransform (p n) s)
          atTop
          (𝓝 (inversePowerTransform q s))) :
    ∀ m : ℕ,
      Tendsto (fun n ↦ p n m) atTop (𝓝 (q m)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm0 : m = 0
      · simpa [hm0] using hzero
      · have hm : 0 < m := Nat.pos_of_ne_zero hm0
        rw [Metric.tendsto_atTop]
        intro ε hε
        have hr :=
          tendsto_pow_atTop_nhds_zero_of_lt_one
            (tailRatio_nonneg m) (tailRatio_lt_one m)
        rw [Metric.tendsto_atTop] at hr
        obtain ⟨s, hs⟩ := hr (ε / 2) (by positivity)
        have hmain :
            Tendsto
              (fun n ↦
                (m : ℝ) ^ s *
                    inversePowerTransform (p n) s -
                  ∑ j ∈ Finset.range m,
                    scaledInversePowerTerm (p n) m s j)
              atTop
              (𝓝
                ((m : ℝ) ^ s * inversePowerTransform q s -
                  ∑ j ∈ Finset.range m,
                    scaledInversePowerTerm q m s j)) := by
          apply Filter.Tendsto.sub
          · exact (htransform s).const_mul _
          · apply tendsto_finsetSum
            intro j hj
            have hjm : j < m := Finset.mem_range.mp hj
            unfold scaledInversePowerTerm
            exact (ih j hjm).mul_const _
        rw [Metric.tendsto_atTop] at hmain
        obtain ⟨N, hN⟩ := hmain (ε / 2) (by positivity)
        refine ⟨N, ?_⟩
        intro n hn
        have hpn :=
          scaledInversePowerTransform_sub_lower_sub_eq_tail
            (hp0 n) (hp n).summable (m := m) (s := s) hm
        have hq' :=
          scaledInversePowerTransform_sub_lower_sub_eq_tail
            hq0 hq.summable (m := m) (s := s) hm
        have htail :=
          abs_scaledInversePowerTail_sub_le
            (hp0 n) (hp n) hq0 hq m s
        have hratio : tailRatio m ^ s < ε / 2 := by
          simpa only [Real.dist_eq, sub_zero,
            abs_of_nonneg (pow_nonneg (tailRatio_nonneg m) s)] using
            hs s le_rfl
        have hmainN := hN n hn
        rw [Real.dist_eq] at hmainN ⊢
        calc
          |p n m - q m| =
              |(((m : ℝ) ^ s *
                    inversePowerTransform (p n) s -
                  ∑ j ∈ Finset.range m,
                    scaledInversePowerTerm (p n) m s j) -
                ((m : ℝ) ^ s * inversePowerTransform q s -
                  ∑ j ∈ Finset.range m,
                    scaledInversePowerTerm q m s j)) -
                ((∑' i : ℕ,
                    scaledInversePowerTerm (p n) m s
                      (i + (m + 1))) -
                  (∑' i : ℕ,
                    scaledInversePowerTerm q m s
                      (i + (m + 1))))| := by
            rw [← hpn, ← hq']
            ring_nf
          _ ≤
              |((m : ℝ) ^ s *
                    inversePowerTransform (p n) s -
                  ∑ j ∈ Finset.range m,
                    scaledInversePowerTerm (p n) m s j) -
                ((m : ℝ) ^ s * inversePowerTransform q s -
                  ∑ j ∈ Finset.range m,
                    scaledInversePowerTerm q m s j)| +
                |(∑' i : ℕ,
                    scaledInversePowerTerm (p n) m s
                      (i + (m + 1))) -
                  (∑' i : ℕ,
                    scaledInversePowerTerm q m s
                      (i + (m + 1)))| :=
            abs_sub _ _
          _ < ε / 2 + ε / 2 := by
            exact add_lt_add hmainN (htail.trans_lt hratio)
          _ = ε := by ring

end

end DirichletAtomConvergence
end PaperC
