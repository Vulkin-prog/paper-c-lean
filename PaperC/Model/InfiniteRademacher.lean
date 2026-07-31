import PaperC.Model.FiniteRademacher
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure

/-!
# The infinite extended-Rademacher model

This module constructs the unrestricted probability space used in Section 14
of the paper.  A sample is an infinite sequence of independent uniform
`F₂`-bits.  Coordinate `k` is assigned to the `k`-th prime; the value at an
integer is the parity pairing with its prime factorization.

The main result is the source-exact form of Lemma 14.5: almost surely no tail
of the resulting completely multiplicative function is constant.  The proof
uses only the product-measure API from mathlib:

* a cylinder fixing `N` coordinates has mass `2⁻ᴺ`;
* hence a tail on which every coordinate is zero has mass zero;
* if the multiplicative function were constant from `x` onwards, then the
  values at a sufficiently late prime `p` and at `p²` would force that
  constant to be `+1`, so every sufficiently late prime bit would be zero;
* a countable intersection of almost-everywhere statements handles all
  starting points `x`.

No literature bridge is needed.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set Filter

namespace PaperC
namespace InfiniteRademacher

/- The coordinate space is finite and is equipped with its discrete
σ-algebra.  Keeping this instance local prevents it from affecting the finite
cylinder modules, which do not use measure-theoretic structure on `F₂`. -/
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Infinite assignments of Rademacher bits, indexed by the prime number
enumeration.  Coordinate `k` belongs to `Nat.nth Nat.Prime k`. -/
abbrev InfiniteSample := ℕ → F₂

/-- The uniform law on one Rademacher bit. -/
noncomputable def coordinateMeasure : Measure F₂ :=
  (PMF.uniformOfFintype F₂).toMeasure

noncomputable instance instIsProbabilityMeasureCoordinateMeasure :
    IsProbabilityMeasure coordinateMeasure := by
  unfold coordinateMeasure
  infer_instance

/-- The unrestricted product law of the independent prime bits. -/
noncomputable def infiniteRademacherMeasure : Measure InfiniteSample :=
  Measure.infinitePi (fun _ : ℕ => coordinateMeasure)

/-- Each of the two coordinate values has probability `1 / 2`. -/
@[simp]
theorem coordinateMeasure_singleton (b : F₂) :
    coordinateMeasure ({b} : Set F₂) = (2 : ℝ≥0∞)⁻¹ := by
  rw [coordinateMeasure, PMF.toMeasure_uniformOfFintype_apply]
  · norm_num
  · change ({b} : Set F₂) ∈ (⊤ : Set (Set F₂))
    simp

/-- The cylinder on which the first `N` coordinates at or after `x` are
zero. -/
def zeroPrefix (x N : ℕ) : Set InfiniteSample :=
  Set.pi (Finset.Ico x (x + N)) (fun _ => {0})

/-- Exact mass `2⁻ᴺ` of a cylinder fixing `N` independent bits. -/
theorem measure_zeroPrefix (x N : ℕ) :
    infiniteRademacherMeasure (zeroPrefix x N) =
      ((2 : ℝ≥0∞)⁻¹) ^ N := by
  rw [infiniteRademacherMeasure, zeroPrefix, Measure.infinitePi_pi]
  · simp
  · intro i hi
    exact MeasurableSet.singleton _

/-- The event on which every coordinate at or after `x` is zero. -/
def zeroTail (x : ℕ) : Set InfiniteSample :=
  {ω | ∀ n, x ≤ n → ω n = 0}

/-- A zero tail lies in each of its finite-prefix cylinders. -/
theorem zeroTail_subset_zeroPrefix (x N : ℕ) :
    zeroTail x ⊆ zeroPrefix x N := by
  intro ω hω
  rw [zeroPrefix, Set.mem_pi]
  intro n hn
  simp only [Set.mem_singleton_iff]
  exact hω n (Finset.mem_Ico.mp hn).1

/-- An infinite prescribed tail of independent uniform bits has probability
zero. -/
theorem measure_zeroTail (x : ℕ) :
    infiniteRademacherMeasure (zeroTail x) = 0 := by
  apply le_zero_iff.mp
  apply ge_of_tendsto'
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1))
  intro N
  rw [← measure_zeroPrefix x N]
  exact measure_mono (zeroTail_subset_zeroPrefix x N)

/--
The unrestricted parity functional.  Since `Nat.primeCounting' p` is the
index of a prime `p`, pairing with `parityVec n` assigns coordinate `k` to the
`k`-th prime.
-/
noncomputable def infiniteValueBit (ω : InfiniteSample) (n : ℕ) : F₂ :=
  (parityVec n).sum fun p e => ω (Nat.primeCounting' p) * e

/-- The unrestricted extended-Rademacher value in `{−1,+1}`. -/
noncomputable def infiniteRandomValue (ω : InfiniteSample) (n : ℕ) : ℤ :=
  phase (infiniteValueBit ω n)

/-- Prime-exponent parity turns multiplication of nonzero naturals into
addition of infinite-model value bits. -/
theorem infiniteValueBit_mul (ω : InfiniteSample) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    infiniteValueBit ω (a * b) =
      infiniteValueBit ω a + infiniteValueBit ω b := by
  rw [infiniteValueBit, parityVec_mul ha hb, Finsupp.sum_add_index']
  · rfl
  · intro
    simp
  · intro
    simp [mul_add]

/-- Complete multiplicativity of the infinite extended-Rademacher function
on nonzero naturals. -/
theorem infiniteRandomValue_mul (ω : InfiniteSample) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    infiniteRandomValue ω (a * b) =
      infiniteRandomValue ω a * infiniteRandomValue ω b := by
  simp only [infiniteRandomValue, infiniteValueBit_mul ω ha hb, phase_add]

/-- At the `k`-th prime, the parity functional is exactly coordinate `k`. -/
@[simp]
theorem infiniteValueBit_nth_prime (ω : InfiniteSample) (k : ℕ) :
    infiniteValueBit ω (Nat.nth Nat.Prime k) = ω k := by
  simp [infiniteValueBit, parityVec, Nat.Prime.factorization]

/-- Squares have zero prime-exponent parity. -/
@[simp]
theorem infiniteValueBit_sq (ω : InfiniteSample) (n : ℕ) :
    infiniteValueBit ω (n ^ 2) = 0 := by
  simp [infiniteValueBit]

/-- The random value at the `k`-th prime is its assigned sign. -/
@[simp]
theorem infiniteRandomValue_nth_prime (ω : InfiniteSample) (k : ℕ) :
    infiniteRandomValue ω (Nat.nth Nat.Prime k) = phase (ω k) := by
  simp [infiniteRandomValue]

/-- The extended model is deterministically `+1` on squares. -/
@[simp]
theorem infiniteRandomValue_sq (ω : InfiniteSample) (n : ℕ) :
    infiniteRandomValue ω (n ^ 2) = 1 := by
  simp [infiniteRandomValue]

/-- A phase is `+1` exactly when its bit is zero. -/
theorem phase_eq_one_iff (z : F₂) :
    phase z = 1 ↔ z = 0 := by
  simp [phase]

/-- The exceptional event on which the multiplicative function is constant
from `x` onwards. -/
def constantTail (x : ℕ) : Set InfiniteSample :=
  {ω | ∀ n, x ≤ n →
    infiniteRandomValue ω n = infiniteRandomValue ω x}

/--
If the function is constant from `x` onwards, then every coordinate `k ≥ x`
is zero.  Indeed, for `p` the `k`-th prime, both `p` and `p²` lie beyond `x`;
the square has value `+1`, forcing the prime value, and hence its bit, to be
zero.
-/
theorem constantTail_subset_zeroTail (x : ℕ) :
    constantTail x ⊆ zeroTail x := by
  intro ω hω k hk
  let p := Nat.nth Nat.Prime k
  have hkp : k ≤ p := by
    exact le_trans (Nat.le_add_right k 2) (Nat.add_two_le_nth_prime k)
  have hxp : x ≤ p := hk.trans hkp
  have hpp : p ≤ p ^ 2 := Nat.le_pow (by norm_num)
  have hxp2 : x ≤ p ^ 2 := hxp.trans hpp
  have hp_const :
      infiniteRandomValue ω p = infiniteRandomValue ω x :=
    hω p hxp
  have hp2_const :
      infiniteRandomValue ω (p ^ 2) = infiniteRandomValue ω x :=
    hω (p ^ 2) hxp2
  have hfx : infiniteRandomValue ω x = 1 := by
    rw [← hp2_const]
    exact infiniteRandomValue_sq ω p
  apply (phase_eq_one_iff (ω k)).mp
  rw [← infiniteRandomValue_nth_prime ω k]
  exact hp_const.trans hfx

/-- For each fixed start `x`, the constant-tail event has probability zero. -/
theorem measure_constantTail (x : ℕ) :
    infiniteRademacherMeasure (constantTail x) = 0 :=
  measure_mono_null (constantTail_subset_zeroTail x) (measure_zeroTail x)

/-- Almost surely, the function is not constant from a fixed start `x`. -/
theorem ae_not_constantTail (x : ℕ) :
    ∀ᵐ ω ∂infiniteRademacherMeasure, ω ∉ constantTail x := by
  rw [ae_iff]
  simpa only [Set.mem_setOf_eq, not_not, Set.setOf_mem_eq] using
    measure_constantTail x

/--
**Lemma 14.5 (almost-sure finiteness of runs), source-exact form.**

Almost surely, for every integer `x ≥ 2`, some `n ≥ x` has value different
from the value at `x`.  Equivalently, no constant run extends indefinitely.
-/
theorem lemma_fourteen_four :
    ∀ᵐ ω ∂infiniteRademacherMeasure, ∀ x : ℕ, 2 ≤ x →
      ∃ n : ℕ, x ≤ n ∧
        infiniteRandomValue ω n ≠ infiniteRandomValue ω x := by
  filter_upwards [ae_all_iff.2 ae_not_constantTail] with ω hω
  intro x _hx
  by_contra h
  push Not at h
  exact hω x h

end InfiniteRademacher
end PaperC
