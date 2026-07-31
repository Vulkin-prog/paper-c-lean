import PaperC.Arithmetic.LargeOddKernel
import PaperC.LinearAlgebra.PrivatePivots

/-!
# Large odd kernels along an exact rational unit

For an exact unit of a primitive channel one has factorizations

`X = b t`,  `Y = a t`,

where `a,b` lie below the large-prime cutoff.  Hence multiplication by
`a` or `b` cannot change any valuation parity above that cutoff.  This
module packages the resulting equality of large odd supports and kernels,
together with the defective/nondefective dichotomy needed by Lemma 6.3.
-/

namespace PaperC
namespace ExactUnitLargeKernel

open LargeOddKernel
open DefectivePredicate

/--
Arithmetic data carried by one exact unit: two positive primitive
coefficients below `B`, a positive common factor, and the two endpoint
factorizations.
-/
structure ExactUnitFactorization
    (B a b t X Y : ℕ) : Prop where
  a_pos : 0 < a
  b_pos : 0 < b
  t_pos : 0 < t
  coprime : a.Coprime b
  height_lt : Nat.max a b < B
  left_eq : X = b * t
  right_eq : Y = a * t

/--
Multiplication by a positive factor below `B` does not alter the parity
coordinate at a prime strictly above `B`.
-/
theorem parityVec_mul_small_eq
    {B c t p : ℕ}
    (hc : 0 < c) (ht : 0 < t) (hcB : c < B)
    (_hp : p.Prime) (hpB : B < p) :
    parityVec (c * t) p = parityVec t p := by
  have hcp : c < p := hcB.trans hpB
  have hpNotDvd : ¬p ∣ c := by
    intro hpDvd
    exact (Nat.not_le_of_gt hcp)
      (Nat.le_of_dvd hc hpDvd)
  have hcParity : parityVec c p = 0 := by
    rw [parityVec_apply,
      Nat.factorization_eq_zero_of_not_dvd hpNotDvd]
    rfl
  have hmul :=
    congrArg (fun v : ℕ →₀ F₂ => v p)
      (parityVec_mul hc.ne' ht.ne')
  simpa only [Finsupp.add_apply, hcParity, zero_add] using hmul

/--
The large-prime valuation parities of `X = bt`, `t`, and `Y = at`
coincide coordinatewise.
-/
theorem exactUnit_large_parity_eq
    {B a b t X Y p : ℕ}
    (h : ExactUnitFactorization B a b t X Y)
    (hp : p.Prime) (hpB : B < p) :
    parityVec X p = parityVec t p ∧
      parityVec t p = parityVec Y p := by
  have haB : a < B :=
    (Nat.le_max_left a b).trans_lt h.height_lt
  have hbB : b < B :=
    (Nat.le_max_right a b).trans_lt h.height_lt
  constructor
  · rw [h.left_eq]
    exact parityVec_mul_small_eq h.b_pos h.t_pos hbB hp hpB
  · rw [h.right_eq]
    exact
      (parityVec_mul_small_eq
        h.a_pos h.t_pos haB hp hpB).symm

/-- Oddness of the large-prime valuations is the same at all three terms. -/
theorem exactUnit_large_factorization_odd_iff
    {B a b t X Y p : ℕ}
    (h : ExactUnitFactorization B a b t X Y)
    (hp : p.Prime) (hpB : B < p) :
    (Odd (X.factorization p) ↔ Odd (t.factorization p)) ∧
      (Odd (t.factorization p) ↔ Odd (Y.factorization p)) := by
  obtain ⟨hXt, htY⟩ :=
    exactUnit_large_parity_eq h hp hpB
  constructor
  · rw [← ZMod.ne_zero_iff_odd, ← ZMod.ne_zero_iff_odd]
    change parityVec X p ≠ 0 ↔ parityVec t p ≠ 0
    rw [hXt]
  · rw [← ZMod.ne_zero_iff_odd, ← ZMod.ne_zero_iff_odd]
    change parityVec t p ≠ 0 ↔ parityVec Y p ≠ 0
    rw [htY]

/--
Multiplication by a positive small coefficient preserves the full large odd
prime support.
-/
theorem largeOddPrimeSupport_mul_small_eq
    {B c t : ℕ}
    (hc : 0 < c) (ht : 0 < t) (hcB : c < B) :
    largeOddPrimeSupport B (c * t) =
      largeOddPrimeSupport B t := by
  ext p
  constructor
  · intro hpMem
    have hpData :=
      prime_and_large_of_mem_largeOddPrimeSupport hpMem
    have hpParity :=
      (mem_largeOddPrimeSupport_iff.mp hpMem).2
    rw [mem_largeOddPrimeSupport_iff]
    refine ⟨hpData.2, ?_⟩
    have heq :=
      parityVec_mul_small_eq hc ht hcB hpData.1 hpData.2
    simpa only [← heq] using hpParity
  · intro hpMem
    have hpData :=
      prime_and_large_of_mem_largeOddPrimeSupport hpMem
    have hpParity :=
      (mem_largeOddPrimeSupport_iff.mp hpMem).2
    rw [mem_largeOddPrimeSupport_iff]
    refine ⟨hpData.2, ?_⟩
    have heq :=
      parityVec_mul_small_eq hc ht hcB hpData.1 hpData.2
    simpa only [heq] using hpParity

/-- The corresponding large odd kernels are equal. -/
theorem largeOddKernel_mul_small_eq
    {B c t : ℕ}
    (hc : 0 < c) (ht : 0 < t) (hcB : c < B) :
    largeOddKernel B (c * t) =
      largeOddKernel B t := by
  unfold largeOddKernel
  rw [largeOddPrimeSupport_mul_small_eq hc ht hcB]

/-- The exact unit has one common large odd prime support. -/
theorem exactUnit_largeOddPrimeSupport_eq
    {B a b t X Y : ℕ}
    (h : ExactUnitFactorization B a b t X Y) :
    largeOddPrimeSupport B X =
        largeOddPrimeSupport B t ∧
      largeOddPrimeSupport B Y =
        largeOddPrimeSupport B t := by
  have haB : a < B :=
    (Nat.le_max_left a b).trans_lt h.height_lt
  have hbB : b < B :=
    (Nat.le_max_right a b).trans_lt h.height_lt
  constructor
  · rw [h.left_eq]
    exact
      largeOddPrimeSupport_mul_small_eq
        h.b_pos h.t_pos hbB
  · rw [h.right_eq]
    exact
      largeOddPrimeSupport_mul_small_eq
        h.a_pos h.t_pos haB

/-- The exact unit has one common large odd kernel. -/
theorem exactUnit_largeOddKernel_eq
    {B a b t X Y : ℕ}
    (h : ExactUnitFactorization B a b t X Y) :
    largeOddKernel B X = largeOddKernel B t ∧
      largeOddKernel B Y = largeOddKernel B t := by
  have hs := exactUnit_largeOddPrimeSupport_eq h
  constructor <;> unfold largeOddKernel
  · rw [hs.1]
  · rw [hs.2]

/-- The common kernel divides all three terms of the exact unit. -/
theorem common_largeOddKernel_dvd
    {B a b t X Y : ℕ}
    (h : ExactUnitFactorization B a b t X Y) :
    largeOddKernel B t ∣ X ∧
      largeOddKernel B t ∣ t ∧
      largeOddKernel B t ∣ Y := by
  have hk := exactUnit_largeOddKernel_eq h
  refine ⟨?_, largeOddKernel_dvd B t, ?_⟩
  · rw [← hk.1]
    exact largeOddKernel_dvd B X
  · rw [← hk.2]
    exact largeOddKernel_dvd B Y

/-- Defectivity of the left endpoint is equivalent to defectivity of `t`. -/
theorem hDefective_left_iff
    {B a b t X Y : ℕ}
    (h : ExactUnitFactorization B a b t X Y) :
    HDefective B X ↔ HDefective B t := by
  have hk := (exactUnit_largeOddKernel_eq h).1
  rw [← largeOddKernel_eq_one_iff_hDefective,
    ← largeOddKernel_eq_one_iff_hDefective, hk]

/-- Defectivity of the right endpoint is equivalent to defectivity of `t`. -/
theorem hDefective_right_iff
    {B a b t X Y : ℕ}
    (h : ExactUnitFactorization B a b t X Y) :
    HDefective B Y ↔ HDefective B t := by
  have hk := (exactUnit_largeOddKernel_eq h).2
  rw [← largeOddKernel_eq_one_iff_hDefective,
    ← largeOddKernel_eq_one_iff_hDefective, hk]

/--
Kernel-one/kernel-nontrivial dichotomy for an exact unit.  In the first
branch every term is defective; in the second none is.
-/
theorem exactUnit_defect_dichotomy
    {B a b t X Y : ℕ}
    (h : ExactUnitFactorization B a b t X Y) :
    (largeOddKernel B t = 1 ∧
        HDefective B X ∧ HDefective B t ∧ HDefective B Y) ∨
      (1 < largeOddKernel B t ∧
        ¬HDefective B X ∧ ¬HDefective B t ∧ ¬HDefective B Y) := by
  by_cases hk : largeOddKernel B t = 1
  · left
    have htDef :
        HDefective B t :=
      (largeOddKernel_eq_one_iff_hDefective B t).mp hk
    exact
      ⟨hk, (hDefective_left_iff h).mpr htDef, htDef,
        (hDefective_right_iff h).mpr htDef⟩
  · right
    have hkgt : 1 < largeOddKernel B t := by
      have hkle := one_le_largeOddKernel B t
      omega
    have htNot : ¬HDefective B t := by
      intro htDef
      exact hk
        ((largeOddKernel_eq_one_iff_hDefective B t).mpr htDef)
    exact
      ⟨hkgt,
        fun hX ↦ htNot ((hDefective_left_iff h).mp hX),
        htNot,
        fun hY ↦ htNot ((hDefective_right_iff h).mp hY)⟩

/--
A nontrivial common kernel supplies a prime above `B` occurring oddly—and
hence dividing—all three exact-unit terms.
-/
theorem exists_common_large_odd_prime
    {B a b t X Y : ℕ}
    (h : ExactUnitFactorization B a b t X Y)
    (hk : largeOddKernel B t ≠ 1) :
    ∃ p : ℕ,
      p.Prime ∧ B < p ∧
        parityVec X p ≠ 0 ∧ parityVec t p ≠ 0 ∧
        parityVec Y p ≠ 0 ∧
        p ∣ largeOddKernel B t ∧
        p ∣ X ∧ p ∣ t ∧ p ∣ Y := by
  have hsne :
      largeOddPrimeSupport B t ≠ ∅ := by
    intro hs
    exact hk
      ((largeOddKernel_eq_one_iff_support_eq_empty B t).mpr hs)
  obtain ⟨p, hpMem⟩ :=
    Finset.nonempty_iff_ne_empty.mpr hsne
  have hpData :=
    prime_and_large_of_mem_largeOddPrimeSupport hpMem
  have hpt :=
    (mem_largeOddPrimeSupport_iff.mp hpMem).2
  have hparity :=
    exactUnit_large_parity_eq h hpData.1 hpData.2
  have hpKernel :
      p ∣ largeOddKernel B t :=
    (prime_dvd_largeOddKernel_iff hpData.1).mpr hpMem
  have hkDvd := common_largeOddKernel_dvd h
  exact
    ⟨p, hpData.1, hpData.2,
      by simpa only [hparity.1] using hpt,
      hpt,
      by simpa only [← hparity.2] using hpt,
      hpKernel,
      hpKernel.trans hkDvd.1,
      hpKernel.trans hkDvd.2.1,
      hpKernel.trans hkDvd.2.2⟩

/-! ## Uniqueness of a large prime inside one short block -/

/--
A prime strictly above the block length divides at most one number among
`x, x+1, ..., x+B-1`.
-/
theorem prime_dvd_unique_in_block
    {B p x i j : ℕ}
    (hpB : B < p) (hi : i < B) (hj : j < B)
    (hpi : p ∣ x + i) (hpj : p ∣ x + j) :
    i = j := by
  by_contra hij
  have hlabel : x + i ≠ x + j := by
    omega
  have hdist : Nat.dist (x + i) (x + j) < B := by
    rw [Nat.dist_add_add_left]
    simp only [Nat.dist]
    omega
  exact
    (PrivatePivots.not_dvd_of_dvd_and_dist_lt
      hpi hlabel hpB hdist) hpj

/--
In particular, an odd valuation at a prime above the block length can occur
at at most one position of that block.
-/
theorem parityVec_ne_zero_unique_in_block
    {B p x i j : ℕ}
    (hpB : B < p) (hi : i < B) (hj : j < B)
    (hip : parityVec (x + i) p ≠ 0)
    (hjp : parityVec (x + j) p ≠ 0) :
    i = j := by
  have hpi : p ∣ x + i := by
    by_contra hnot
    apply hip
    rw [parityVec_apply,
      Nat.factorization_eq_zero_of_not_dvd hnot]
    rfl
  have hpj : p ∣ x + j := by
    by_contra hnot
    apply hjp
    rw [parityVec_apply,
      Nat.factorization_eq_zero_of_not_dvd hnot]
    rfl
  exact prime_dvd_unique_in_block hpB hi hj hpi hpj

end ExactUnitLargeKernel
end PaperC
