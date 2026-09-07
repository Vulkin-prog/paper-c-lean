import PaperCV11.RankinTilt
import PaperC.Diophantine.ComponentNormalization

/-!
# Rankin's finite bound for the actual defective integers

The population is defined by even valuations at every prime above Y,
with zero excluded. Its squarefree factor and positive square root are
unique. The old kernel-one count is identified exactly with this population;
no defect-count estimate is introduced as an assumption.
-/

namespace PaperC.V282.DefectiveRankinCount

open DefectivePredicate DefectCounting LargeOddKernel ComponentNormalization
open TerminalKernelCount V11.RankinTilt

noncomputable section

/-- Positive Y-defective integers at most X, defined by their actual valuations. -/
def defectiveValues (X Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter (HDefective Y)

/-- The finite Rankin Euler product, with its literal prime cutoff. -/
def rankinEulerProduct (Y : ℕ) (zeta : ℝ) : ℝ :=
  ∏ p ∈ smallPrimesUpTo Y, (1 + (p : ℝ) ^ (-1 + zeta))

theorem mem_defectiveValues {X Y n : ℕ} :
    n ∈ defectiveValues X Y ↔ 1 ≤ n ∧ n ≤ X ∧ HDefective Y n := by
  classical
  simp [defectiveValues, and_assoc]

/-- The intrinsic population is exactly the historical kernel-one population. -/
theorem defectiveValues_eq_kernel_one (X Y : ℕ) :
    defectiveValues X Y = boundedLargeKernelValues Y 1 X := by
  ext n
  rw [mem_defectiveValues, mem_boundedLargeKernelValues]
  have hkernel : largeOddKernel Y n ≤ 1 ↔ HDefective Y n := by
    rw [show largeOddKernel Y n ≤ 1 ↔ largeOddKernel Y n = 1 from
      ⟨fun h => le_antisymm h (one_le_largeOddKernel Y n), fun h => h.le⟩]
    exact largeOddKernel_eq_one_iff_hDefective Y n
  rw [hkernel]

/-- The canonical squarefree factor contains only primes at most Y. -/
theorem squarefreeKernel_smooth_of_defective {Y n : ℕ} (h : HDefective Y n) :
    ∀ p : ℕ, p.Prime → p ∣ squarefreeKernel n → p ≤ Y := by
  intro p hp hdvd
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdvd
  have hqsmall := mem_smallPrimesUpTo.mp (oddPrimeSupport_subset_smallPrimesUpTo h hq)
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqsmall.1).mp hpq
  exact heq ▸ hqsmall.2

/-- Conversely every positive square times a smooth squarefree integer is defective. -/
theorem defective_of_square_smooth {Y n s a : ℕ} (hs : 0 < s) (ha : 0 < a)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ s → p ≤ Y) (heq : n = s * a ^ 2) :
    HDefective Y n := by
  intro p hp hpY
  have hnotdvd : ¬p ∣ s := fun h => (not_le_of_gt hpY) (hsmooth p hp h)
  rw [heq, parityVec_mul hs.ne' (pow_ne_zero 2 ha.ne'), parityVec_pow_two, add_zero]
  simp [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hnotdvd]

/-- The squarefree smooth factor and the positive square root are jointly unique. -/
theorem exists_unique_square_smooth {Y n : ℕ} (hn : 0 < n) (h : HDefective Y n) :
    ∃! sa : ℕ × ℕ, 0 < sa.1 ∧ Squarefree sa.1 ∧
      (∀ p : ℕ, p.Prime → p ∣ sa.1 → p ≤ Y) ∧ 0 < sa.2 ∧ n = sa.1 * sa.2 ^ 2 := by
  obtain ⟨hs, hsf, ha, heq⟩ := canonical_squarefree_decomposition hn
  refine ⟨(squarefreeKernel n, canonicalSquarePart n),
    ⟨hs, hsf, squarefreeKernel_smooth_of_defective h, ha, heq⟩, ?_⟩
  rintro ⟨s, a⟩ ⟨hs', hsf', _, ha', heq'⟩
  obtain ⟨hsame, hsamea⟩ := squarefree_decomposition_unique hn hs' ha' hsf' heq'
  exact Prod.ext hsame hsamea

/-- Rankin's finite unnormalized bound for actual defective integers. -/
theorem card_defectiveValues_le_rankin (X Y : ℕ) {zeta : ℝ} (hzeta : zeta ≤ 1 / 2) :
    ((defectiveValues X Y).card : ℝ) ≤ (X : ℝ) ^ (1 - zeta) * rankinEulerProduct Y zeta := by
  rw [defectiveValues_eq_kernel_one]
  exact card_kernel_one_cast_le_rankin_eulerProduct Y X hzeta

/-- Equation (B.1), hence the finite counting step in Proposition 4.2.
It holds throughout the manuscript range 0<zeta<1/2, and also at the endpoint. -/
theorem normalized_defectiveValues_le_rankin {X : ℕ} (hX : 0 < X) (Y : ℕ)
    {zeta : ℝ} (hzeta : zeta ≤ 1 / 2) :
    ((defectiveValues X Y).card : ℝ) / X ≤ (X : ℝ) ^ (-zeta) * rankinEulerProduct Y zeta := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  apply (div_le_iff₀ hXpos).mpr
  have heq : (X : ℝ) ^ (1 - zeta) = (X : ℝ) ^ (-zeta) * X := by
    rw [show 1 - zeta = -zeta + 1 by ring, Real.rpow_add hXpos, Real.rpow_one]
  simpa only [heq, mul_assoc, mul_comm, mul_left_comm] using card_defectiveValues_le_rankin X Y hzeta

end
end PaperC.V282.DefectiveRankinCount
