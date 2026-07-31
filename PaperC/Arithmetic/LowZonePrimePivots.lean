import PaperC.Affine.RationalChannelCode
import PaperC.Affine.StartBoundaryRange
import PaperC.Arithmetic.DyadicPrimeReciprocalSums
import PaperC.Probability.DefectFirstMoment
import Mathlib.Data.Nat.Sqrt
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option maxHeartbeats 1200000

/-!
# Intermediate-prime pivots in the low zone

This file formalizes the finite linear-algebraic core of Paper C, Lemma 15.1.
For a start window

`Vₓ = {x - 1, x, ..., x + L - 1}`

and a prime

`sqrt (x + L) < q ≤ L`,

let `A_q` be the vertices of `Vₓ` divisible by `q`.  We prove that:

* every `A_q` is nonempty;
* the `A_q` are pairwise disjoint;
* the `q`-adic valuation of every vertex in `A_q` is exactly one;
* if the window contains a square outside all `A_q`, the corresponding
  parity forms are independent on the even-boundary hyperplane;
* consequently the relation defect of the start system is at most
  `L - # {q prime | sqrt (x+L) < q ≤ L}` and the start probability is at
  most the reciprocal power of two with that exponent.

The square is constructed explicitly.  The elementary finite hypothesis

`2 * sqrt (x - 1) + 1 ≤ L`

places `(sqrt (x-1)+1)^2` in the start window.  This is the precise
finite inequality whose eventual validity in the manuscript's region
`x ≤ L^(2-ε)` belongs to the asymptotic wrapper.
-/

namespace PaperC
namespace LowZonePrimePivots

open scoped BigOperators

open Affine
open DyadicPrimeReciprocalSums

noncomputable section

/-! ## The intermediate primes and their vertex sets -/

/-- The primes in the interval `(sqrt (x+L), L]` from Lemma 15.1. -/
def intermediatePrimes (x L : ℕ) : Finset ℕ :=
  primesBetween (Nat.sqrt (x + L)) L

@[simp]
theorem mem_intermediatePrimes {x L q : ℕ} :
    q ∈ intermediatePrimes x L ↔
      q.Prime ∧ Nat.sqrt (x + L) < q ∧ q ≤ L := by
  simp [intermediatePrimes, and_assoc]

/-- The complete start vertices divisible by one intermediate prime. -/
def primeVertexSet (x L q : ℕ) : Finset (Fin (L + 1)) :=
  Finset.univ.filter fun v ↦
    q ∣ startCompleteVertexLabel x L v

@[simp]
theorem mem_primeVertexSet {x L q : ℕ} {v : Fin (L + 1)} :
    v ∈ primeVertexSet x L q ↔
      q ∣ startCompleteVertexLabel x L v := by
  simp [primeVertexSet]

/-- Every complete start label lies in the expected integer interval. -/
theorem startCompleteVertexLabel_bounds
    {x L : ℕ} (hx : 2 ≤ x) (v : Fin (L + 1)) :
    x - 1 ≤ startCompleteVertexLabel x L v ∧
      startCompleteVertexLabel x L v < x + L := by
  simp only [startCompleteVertexLabel]
  by_cases hv : v.1 = 0
  · simp [hv]
    omega
  · simp [hv]
    have hvlt := v.2
    omega

/--
Every interval `Vₓ` contains a multiple of every positive `q ≤ L`.
This is the exact nonemptiness argument for `A_q`.
-/
theorem primeVertexSet_nonempty
    {x L q : ℕ} (hx : 2 ≤ x) (hq : 0 < q) (hqL : q ≤ L) :
    (primeVertexSet x L q).Nonempty := by
  let a := x - 1
  let n := q * (a / q + 1)
  have han : a < n := by
    dsimp only [n]
    exact Nat.lt_mul_div_succ a hq
  have hna : n ≤ a + q := by
    calc
      n = a / q * q + q := by
        dsimp only [n]
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm q (a / q)]
      _ ≤ a + q :=
        Nat.add_le_add_right (Nat.div_mul_le_self a q) q
  let d := n - a
  have hdPos : 0 < d := by
    dsimp only [d]
    omega
  have hdL : d < L + 1 := by
    dsimp only [d]
    omega
  let v : Fin (L + 1) := ⟨d, hdL⟩
  refine ⟨v, mem_primeVertexSet.mpr ?_⟩
  have hlabel :
      startCompleteVertexLabel x L v = n := by
    simp only [startCompleteVertexLabel, v]
    rw [if_neg (by simpa [d] using hdPos.ne')]
    dsimp only [d, a] at han hna ⊢
    omega
  rw [hlabel]
  exact dvd_mul_right q (a / q + 1)

/-- Every intermediate-prime vertex set is nonempty. -/
theorem primeVertexSet_nonempty_of_intermediate
    {x L : ℕ} (hx : 2 ≤ x)
    (q : ↥(intermediatePrimes x L)) :
    (primeVertexSet x L q.1).Nonempty := by
  have hq := mem_intermediatePrimes.mp q.2
  exact primeVertexSet_nonempty hx hq.1.pos hq.2.2

/-- An intermediate prime has square strictly larger than the whole window. -/
theorem window_lt_prime_sq
    {x L q : ℕ} (hq : q ∈ intermediatePrimes x L) :
    x + L < q ^ 2 := by
  exact (Nat.sqrt_lt').mp (mem_intermediatePrimes.mp hq).2.1

/--
Every multiple of an intermediate prime in the start window has valuation
exactly one at that prime.
-/
theorem factorization_eq_one_of_mem_primeVertexSet
    {x L q : ℕ} (hx : 2 ≤ x)
    (hq : q ∈ intermediatePrimes x L)
    {v : Fin (L + 1)} (hv : v ∈ primeVertexSet x L q) :
    (startCompleteVertexLabel x L v).factorization q = 1 := by
  let n := startCompleteVertexLabel x L v
  have hnPos : 0 < n := by
    have hb := (startCompleteVertexLabel_bounds hx v).1
    dsimp only [n]
    omega
  have hqdvd : q ∣ n := by
    simpa only [n] using mem_primeVertexSet.mp hv
  have hfacPos :
      0 < n.factorization q :=
    (mem_intermediatePrimes.mp hq).1.factorization_pos_of_dvd
      hnPos.ne' hqdvd
  have hfacLt : n.factorization q < 2 := by
    by_contra hnot
    have htwo : 2 ≤ n.factorization q := Nat.le_of_not_gt hnot
    have hsqDvd : q ^ 2 ∣ n :=
      ((mem_intermediatePrimes.mp hq).1.pow_dvd_iff_le_factorization
        hnPos.ne').2 htwo
    have hsqLe : q ^ 2 ≤ n := Nat.le_of_dvd hnPos hsqDvd
    have hnUpper : n < x + L := by
      exact (startCompleteVertexLabel_bounds hx v).2
    exact (not_lt_of_ge hsqLe)
      (hnUpper.trans (window_lt_prime_sq hq))
  change n.factorization q = 1
  omega

/-- On `A_q`, the parity coordinate at `q` is one. -/
theorem parityVec_eq_one_of_mem_primeVertexSet
    {x L q : ℕ} (hx : 2 ≤ x)
    (hq : q ∈ intermediatePrimes x L)
    {v : Fin (L + 1)} (hv : v ∈ primeVertexSet x L q) :
    parityVec (startCompleteVertexLabel x L v) q = 1 := by
  rw [parityVec_apply,
    factorization_eq_one_of_mem_primeVertexSet hx hq hv]
  rfl

/-- Distinct intermediate primes have disjoint vertex sets. -/
theorem disjoint_primeVertexSet
    {x L q r : ℕ}
    (hx : 2 ≤ x)
    (hq : q ∈ intermediatePrimes x L)
    (hr : r ∈ intermediatePrimes x L)
    (hqr : q ≠ r) :
    Disjoint (primeVertexSet x L q) (primeVertexSet x L r) := by
  rw [Finset.disjoint_left]
  intro v hvq hvr
  have hqData := mem_intermediatePrimes.mp hq
  have hrData := mem_intermediatePrimes.mp hr
  let n := startCompleteVertexLabel x L v
  have hqdvd : q ∣ n := by
    simpa only [n] using mem_primeVertexSet.mp hvq
  have hrdvd : r ∣ n := by
    simpa only [n] using mem_primeVertexSet.mp hvr
  have hqrdvd : q * r ∣ n :=
    ((Nat.coprime_primes hqData.1 hrData.1).mpr hqr).mul_dvd_of_dvd_of_dvd
      hqdvd hrdvd
  have hnPos : 0 < n := by
    have hb := (startCompleteVertexLabel_bounds hx v).1
    dsimp only [n]
    omega
  have hqrLe : q * r ≤ n := Nat.le_of_dvd hnPos hqrdvd
  have hnUpper : n < x + L := by
    dsimp only [n]
    exact (startCompleteVertexLabel_bounds hx v).2
  have hsquare :
      x + L <
        (Nat.sqrt (x + L) + 1) *
          (Nat.sqrt (x + L) + 1) :=
    Nat.lt_succ_sqrt (x + L)
  have hqLower : Nat.sqrt (x + L) + 1 ≤ q := by omega
  have hrLower : Nat.sqrt (x + L) + 1 ≤ r := by omega
  have hwindowProduct : x + L < q * r :=
    hsquare.trans_le (Nat.mul_le_mul hqLower hrLower)
  omega

/-! ## A square outside all intermediate-prime sets -/

/-- Offset of the first square strictly above `x-1`. -/
def lowZoneSquareOffset (x : ℕ) : ℕ :=
  (Nat.sqrt (x - 1) + 1) ^ 2 - (x - 1)

/-- The first square above `x-1` lies in the window under the finite gap bound. -/
theorem lowZoneSquareOffset_pos_le
    {x L : ℕ} (_hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L) :
    0 < lowZoneSquareOffset x ∧ lowZoneSquareOffset x ≤ L := by
  have hlower :
      x - 1 < (Nat.sqrt (x - 1) + 1) ^ 2 :=
    Nat.lt_succ_sqrt' (x - 1)
  have hsqrt :
      Nat.sqrt (x - 1) ^ 2 ≤ x - 1 :=
    Nat.sqrt_le' (x - 1)
  have hsquareUpper :
      (Nat.sqrt (x - 1) + 1) ^ 2 ≤ (x - 1) + L := by
    calc
      (Nat.sqrt (x - 1) + 1) ^ 2 =
          Nat.sqrt (x - 1) ^ 2 +
            (2 * Nat.sqrt (x - 1) + 1) := by ring
      _ ≤ (x - 1) + (2 * Nat.sqrt (x - 1) + 1) :=
        Nat.add_le_add_right hsqrt _
      _ ≤ (x - 1) + L := Nat.add_le_add_left hgap _
  unfold lowZoneSquareOffset
  constructor
  · omega
  · omega

/-- The distinguished square vertex used to close the even-parity constraint. -/
def lowZoneSquareVertex
    (x L : ℕ) (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L) :
    Fin (L + 1) :=
  ⟨lowZoneSquareOffset x,
    Nat.lt_succ_of_le (lowZoneSquareOffset_pos_le hx hgap).2⟩

/-- The label of the distinguished vertex is the advertised perfect square. -/
theorem startCompleteVertexLabel_lowZoneSquareVertex
    {x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L) :
    startCompleteVertexLabel x L
        (lowZoneSquareVertex x L hx hgap) =
      (Nat.sqrt (x - 1) + 1) ^ 2 := by
  have hoff :=
    lowZoneSquareOffset_pos_le hx hgap
  simp only [startCompleteVertexLabel, lowZoneSquareVertex]
  rw [if_neg hoff.1.ne']
  unfold lowZoneSquareOffset
  have hlower :
      x - 1 < (Nat.sqrt (x - 1) + 1) ^ 2 :=
    Nat.lt_succ_sqrt' (x - 1)
  omega

/-- The distinguished square lies below the strict upper endpoint `x+L`. -/
theorem lowZoneSquareLabel_lt
    {x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L) :
    (Nat.sqrt (x - 1) + 1) ^ 2 < x + L := by
  rw [← startCompleteVertexLabel_lowZoneSquareVertex hx hgap]
  exact
    (startCompleteVertexLabel_bounds hx
      (lowZoneSquareVertex x L hx hgap)).2

/-- The distinguished square belongs to none of the sets `A_q`. -/
theorem lowZoneSquareVertex_not_mem
    {x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L)
    (q : ↥(intermediatePrimes x L)) :
    lowZoneSquareVertex x L hx hgap ∉ primeVertexSet x L q.1 := by
  intro hmem
  have hqData := mem_intermediatePrimes.mp q.2
  have hqdvdSquare :
      q.1 ∣ (Nat.sqrt (x - 1) + 1) ^ 2 := by
    rw [← startCompleteVertexLabel_lowZoneSquareVertex hx hgap]
    exact mem_primeVertexSet.mp hmem
  have hqdvd :
      q.1 ∣ Nat.sqrt (x - 1) + 1 :=
    hqData.1.dvd_of_dvd_pow hqdvdSquare
  have hsqDvd :
      q.1 ^ 2 ∣ (Nat.sqrt (x - 1) + 1) ^ 2 :=
    pow_dvd_pow_of_dvd hqdvd 2
  have hsquarePos :
      0 < (Nat.sqrt (x - 1) + 1) ^ 2 := by positivity
  have hsqLe :
      q.1 ^ 2 ≤ (Nat.sqrt (x - 1) + 1) ^ 2 :=
    Nat.le_of_dvd hsquarePos hsqDvd
  exact (not_lt_of_ge hsqLe)
    ((lowZoneSquareLabel_lt hx hgap).trans
      (window_lt_prime_sq q.2))

/-! ## Independent forms on the even-boundary hyperplane -/

/-- The `q`-parity form on complete start-boundary vectors. -/
def primeConstraintFunctional (x L q : ℕ) :
    (Fin (L + 1) → F₂) →ₗ[F₂] F₂ where
  toFun w :=
    ∑ v : Fin (L + 1),
      w v * parityVec (startCompleteVertexLabel x L v) q
  map_add' w z := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c w := by
    change
      (∑ v : Fin (L + 1),
          c * w v *
            parityVec (startCompleteVertexLabel x L v) q) =
        c * ∑ v : Fin (L + 1),
          w v * parityVec (startCompleteVertexLabel x L v) q
    simpa only [mul_assoc] using
      (Finset.mul_sum Finset.univ
        (fun v : Fin (L + 1) ↦
          w v * parityVec (startCompleteVertexLabel x L v) q) c).symm

/--
All intermediate-prime constraints, restricted to the even-boundary
hyperplane.
-/
def lowZoneConstraintMap (x L : ℕ) :
    LinearMap.ker (startVertexSum L) →ₗ[F₂]
      (↥(intermediatePrimes x L) → F₂) where
  toFun w q := primeConstraintFunctional x L q.1 w.1
  map_add' w z := by
    funext q
    exact LinearMap.map_add _ _ _
  map_smul' c w := by
    funext q
    exact LinearMap.map_smul _ _ _

/-- A chosen divisible vertex for each intermediate prime. -/
def primePivot
    (x L : ℕ) (hx : 2 ≤ x)
    (q : ↥(intermediatePrimes x L)) :
    Fin (L + 1) :=
  Classical.choose (primeVertexSet_nonempty_of_intermediate hx q)

theorem primePivot_mem
    (x L : ℕ) (hx : 2 ≤ x)
    (q : ↥(intermediatePrimes x L)) :
    primePivot x L hx q ∈ primeVertexSet x L q.1 :=
  Classical.choose_spec (primeVertexSet_nonempty_of_intermediate hx q)

/-- Outside `A_q`, the `q` parity coordinate vanishes. -/
theorem parityVec_eq_zero_of_not_mem_primeVertexSet
    {x L q : ℕ} {v : Fin (L + 1)}
    (hv : v ∉ primeVertexSet x L q) :
    parityVec (startCompleteVertexLabel x L v) q = 0 := by
  have hnot :
      ¬ q ∣ startCompleteVertexLabel x L v := by
    intro h
    exact hv (mem_primeVertexSet.mpr h)
  rw [parityVec_apply,
    Nat.factorization_eq_zero_of_not_dvd hnot]
  rfl

/-- The selected pivots form a Kronecker family for prime parity. -/
theorem parityVec_primePivot
    {x L : ℕ} (hx : 2 ≤ x)
    (q r : ↥(intermediatePrimes x L)) :
    parityVec
        (startCompleteVertexLabel x L (primePivot x L hx q)) r.1 =
      if q = r then 1 else 0 := by
  by_cases hqr : q = r
  · subst r
    rw [if_pos rfl]
    exact parityVec_eq_one_of_mem_primeVertexSet
      hx q.2 (primePivot_mem x L hx q)
  · rw [if_neg hqr]
    apply parityVec_eq_zero_of_not_mem_primeVertexSet
    intro hmem
    have hdisjoint :=
      disjoint_primeVertexSet hx q.2 r.2
        (fun h ↦ hqr (Subtype.ext h))
    exact Finset.disjoint_left.mp hdisjoint
      (primePivot_mem x L hx q) hmem

/-- The square has zero parity at every intermediate prime. -/
theorem parityVec_lowZoneSquareVertex
    {x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L)
    (q : ↥(intermediatePrimes x L)) :
    parityVec
        (startCompleteVertexLabel x L
          (lowZoneSquareVertex x L hx hgap)) q.1 =
      0 :=
  parityVec_eq_zero_of_not_mem_primeVertexSet
    (lowZoneSquareVertex_not_mem hx hgap q)

private theorem sum_single_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : ι → F₂) :
    (∑ j : ι, (Pi.single i (1 : F₂) : ι → F₂) j * f j) =
      f i := by
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hji
    simp [Pi.single_apply, hji]

/--
An even vector testing one prime constraint: one at its chosen pivot and
one at the distinguished square.
-/
def evenPrimeTestVector
    (x L : ℕ) (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L)
    (q : ↥(intermediatePrimes x L)) :
    LinearMap.ker (startVertexSum L) := by
  classical
  let w : Fin (L + 1) → F₂ :=
    Pi.single (primePivot x L hx q) (1 : F₂) +
      Pi.single (lowZoneSquareVertex x L hx hgap) (1 : F₂)
  refine ⟨w, ?_⟩
  change startVertexSum L w = 0
  change
    (∑ v : Fin (L + 1),
        ((Pi.single (primePivot x L hx q) (1 : F₂) :
              Fin (L + 1) → F₂) v +
          (Pi.single (lowZoneSquareVertex x L hx hgap) (1 : F₂) :
              Fin (L + 1) → F₂) v)) =
      0
  rw [Finset.sum_add_distrib]
  simp

/-- The test vectors give the identity matrix under the constraint map. -/
theorem lowZoneConstraintMap_evenPrimeTestVector
    {x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L)
    (q r : ↥(intermediatePrimes x L)) :
    lowZoneConstraintMap x L
        (evenPrimeTestVector x L hx hgap q) r =
      if q = r then 1 else 0 := by
  classical
  change
    (∑ v : Fin (L + 1),
        (((Pi.single (primePivot x L hx q) (1 : F₂) :
              Fin (L + 1) → F₂) v +
            (Pi.single (lowZoneSquareVertex x L hx hgap) (1 : F₂) :
              Fin (L + 1) → F₂) v) *
          parityVec (startCompleteVertexLabel x L v) r.1)) =
      if q = r then 1 else 0
  simp only [add_mul, Finset.sum_add_distrib]
  rw [sum_single_mul, sum_single_mul]
  simp [parityVec_primePivot hx q r,
    parityVec_lowZoneSquareVertex hx hgap r]

/-- Explicit right inverse of the low-zone constraint map. -/
def lowZoneConstraintRightInverse
    (x L : ℕ) (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L)
    (b : ↥(intermediatePrimes x L) → F₂) :
    LinearMap.ker (startVertexSum L) :=
  ∑ q : ↥(intermediatePrimes x L),
    b q • evenPrimeTestVector x L hx hgap q

theorem lowZoneConstraintMap_rightInverse
    {x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L)
    (b : ↥(intermediatePrimes x L) → F₂) :
    lowZoneConstraintMap x L
        (lowZoneConstraintRightInverse x L hx hgap b) =
      b := by
  classical
  funext r
  rw [lowZoneConstraintRightInverse, map_sum]
  simp only [Fintype.sum_apply, LinearMap.map_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [Fintype.sum_eq_single r]
  · rw [lowZoneConstraintMap_evenPrimeTestVector hx hgap r r,
      if_pos rfl]
    simp
  · intro q hqr
    rw [lowZoneConstraintMap_evenPrimeTestVector hx hgap q r,
      if_neg hqr]
    simp

/-- The intermediate-prime forms are independent on the even hyperplane. -/
theorem lowZoneConstraintMap_surjective
    {x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L) :
    Function.Surjective (lowZoneConstraintMap x L) := by
  intro b
  exact ⟨lowZoneConstraintRightInverse x L hx hgap b,
    lowZoneConstraintMap_rightInverse hx hgap b⟩

/-- There cannot be more independent intermediate-prime forms than rows. -/
theorem card_intermediatePrimes_le
    {x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L) :
    (intermediatePrimes x L).card ≤ L := by
  have hsourceDim :
      Module.finrank F₂ (LinearMap.ker (startVertexSum L)) = L := by
    calc
      Module.finrank F₂ (LinearMap.ker (startVertexSum L)) =
          Module.finrank F₂ (Fin L → F₂) :=
        (LinearEquiv.finrank_eq (startBoundaryEquivEven L)).symm
      _ = L := by simp [Module.finrank_pi]
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker
      (lowZoneConstraintMap x L)
  have hrange :
      LinearMap.range (lowZoneConstraintMap x L) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (lowZoneConstraintMap_surjective hx hgap)
  rw [hrange] at hnullity
  simp only [finrank_top, Module.finrank_pi,
    Fintype.card_coe] at hnullity
  rw [hsourceDim] at hnullity
  omega

/--
The finite square-gap hypothesis also puts the lower prime cutoff below
`L`.  This removes a hidden side condition from the prime-count identity.
-/
theorem sqrt_window_le_of_gap
    {x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L) :
    Nat.sqrt (x + L) ≤ L := by
  let s := Nat.sqrt (x - 1)
  have hsPos : 1 ≤ s := by
    apply (Nat.le_sqrt).2
    dsimp only [s]
    omega
  have hxUpper :
      x - 1 < (s + 1) * (s + 1) := by
    simpa only [s] using Nat.lt_succ_sqrt (x - 1)
  have hxBound :
      x ≤ (s + 1) * (s + 1) := by
    have hxSub : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
    omega
  have hxLsq : x + L ≤ L * L := by
    nlinarith [hxBound]
  by_contra hnot
  have hlt : L < Nat.sqrt (x + L) :=
    Nat.lt_of_not_ge hnot
  have hsucc : L + 1 ≤ Nat.sqrt (x + L) := hlt
  have hsuccSq :
      (L + 1) * (L + 1) ≤ x + L :=
    (Nat.le_sqrt).1 hsucc
  nlinarith

/--
The exponent used above is literally the manuscript quantity

`π(L) - π(sqrt (x+L))`.
-/
theorem card_intermediatePrimes_eq_primeCount_sub
    {x L : ℕ} (hsqrt : Nat.sqrt (x + L) ≤ L) :
    (intermediatePrimes x L).card =
      PrimesUpTo.count L - PrimesUpTo.count (Nat.sqrt (x + L)) := by
  let B := Nat.sqrt (x + L)
  have hsubset :
      DefectCounting.smallPrimesUpTo B ⊆
        DefectCounting.smallPrimesUpTo L := by
    intro p hp
    have hpData :=
      DefectCounting.mem_smallPrimesUpTo.mp hp
    exact DefectCounting.mem_smallPrimesUpTo.mpr
      ⟨hpData.1, hpData.2.trans (by simpa only [B] using hsqrt)⟩
  have hset :
      intermediatePrimes x L =
        DefectCounting.smallPrimesUpTo L \
          DefectCounting.smallPrimesUpTo B := by
    ext p
    simp only [intermediatePrimes, primesBetween,
      Finset.mem_filter, DefectCounting.mem_smallPrimesUpTo,
      Finset.mem_sdiff, B]
    constructor
    · rintro ⟨⟨hp, hpL⟩, hpLower⟩
      exact ⟨⟨hp, hpL⟩, by
        rintro ⟨_hp, hpB⟩
        omega⟩
    · rintro ⟨⟨hp, hpL⟩, hpB⟩
      exact ⟨⟨hp, hpL⟩, by
        by_contra hnot
        exact hpB ⟨hp, by omega⟩⟩
  rw [hset, Finset.card_sdiff hsubset]
  rw [← PrimeCountBridge.count_eq_card_smallPrimesUpTo,
    ← PrimeCountBridge.count_eq_card_smallPrimesUpTo]

/-- Gap-specialized form of the exact manuscript prime-count exponent. -/
theorem card_intermediatePrimes_eq_primeCount_sub_of_gap
    {x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L) :
    (intermediatePrimes x L).card =
      PrimesUpTo.count L - PrimesUpTo.count (Nat.sqrt (x + L)) :=
  card_intermediatePrimes_eq_primeCount_sub
    (sqrt_window_le_of_gap hx hgap)

/-! ## Relations and probability -/

private theorem valueBit_single
    {M n p : ℕ} (hp : p.Prime) (hpM : p ≤ M) :
    valueBit
        (M := M)
        (Pi.single
          (⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩ : PrimeUpTo M) 1)
        n =
      parityVec n p := by
  classical
  let q : PrimeUpTo M :=
    ⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩
  rw [valueBit]
  rw [Fintype.sum_eq_single q]
  · simp [q]
  · intro r hrq
    have hrq' :
        r ≠ (⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩ : PrimeUpTo M) := by
      simpa only [q] using hrq
    simp [Pi.single_apply, hrq']

/--
Every genuine row relation satisfies every intermediate-prime boundary
constraint.
-/
theorem relation_boundary_constraint_eq_zero
    {M x L : ℕ} (hM : x + L ≤ M)
    (u : RelationSpace (startSystem M x L))
    (q : ↥(intermediatePrimes x L)) :
    primeConstraintFunctional x L q.1
        (startCompleteBoundary L (u : Fin L → F₂)) =
      0 := by
  classical
  have hqData := mem_intermediatePrimes.mp q.2
  have hqM : q.1 ≤ M :=
    hqData.2.2.trans (by omega)
  let pM : PrimeUpTo M :=
    ⟨⟨q.1, Nat.lt_succ_of_le hqM⟩, hqData.1⟩
  let ω : SampleSpace M := Pi.single pM 1
  have hrel :
      relationFunctional
          (startSystem M x L) (u : Fin L → F₂) ω =
        0 := by
    have hu :
        relationMap
            (startSystem M x L) (u : Fin L → F₂) =
          0 :=
      LinearMap.mem_ker.mp u.2
    have huω := DFunLike.congr_fun hu ω
    change
      relationFunctional
          (startSystem M x L) (u : Fin L → F₂) ω =
        0 at huω
    exact huω
  rw [relationFunctional_apply] at hrel
  simp only [dotProduct] at hrel
  rw [Affine.RationalChannelCode.sum_startSystem_eq_sum_completeBoundary]
    at hrel
  dsimp only [ω, pM] at hrel
  simp_rw [valueBit_single hqData.1 hqM] at hrel
  exact hrel

/--
Finite rank conclusion of Lemma 15.1:

`rho(x) ≤ L - # {q prime | sqrt(x+L) < q ≤ L}`.
-/
theorem relationRho_startSystem_le_sub_card_intermediatePrimes
    {M x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L)
    (hM : x + L ≤ M) :
    relationRho (startSystem M x L) ≤
      L - (intermediatePrimes x L).card := by
  let boundaryMap :
      RelationSpace (startSystem M x L) →ₗ[F₂]
        LinearMap.ker (lowZoneConstraintMap x L) :=
    {
    toFun u :=
      ⟨startBoundaryEquivEven L (u : Fin L → F₂), by
        funext q
        change
          primeConstraintFunctional x L q.1
              (startCompleteBoundary L (u : Fin L → F₂)) =
            0
        exact relation_boundary_constraint_eq_zero hM u q⟩
    map_add' u v := by
      apply Subtype.ext
      exact LinearMap.map_add _ _ _
    map_smul' c u := by
      apply Subtype.ext
      exact LinearMap.map_smul _ _ _
    }
  have hboundaryInj : Function.Injective boundaryMap := by
    intro u v huv
    apply Subtype.ext
    have hcoe := congrArg
      (fun z : LinearMap.ker (lowZoneConstraintMap x L) ↦ z.1) huv
    dsimp only [boundaryMap] at hcoe
    change
        startBoundaryEquivEven L (u : Fin L → F₂) =
          startBoundaryEquivEven L (v : Fin L → F₂) at hcoe
    exact (startBoundaryEquivEven L).injective hcoe
  have hfinrank :
      relationRho (startSystem M x L) ≤
        Module.finrank F₂
          (LinearMap.ker (lowZoneConstraintMap x L)) := by
    unfold relationRho
    exact LinearMap.finrank_le_finrank_of_injective hboundaryInj
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker
      (lowZoneConstraintMap x L)
  have hrange :
      LinearMap.range (lowZoneConstraintMap x L) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (lowZoneConstraintMap_surjective hx hgap)
  rw [hrange] at hnullity
  have hsourceDim :
      Module.finrank F₂ (LinearMap.ker (startVertexSum L)) = L := by
    calc
      Module.finrank F₂ (LinearMap.ker (startVertexSum L)) =
          Module.finrank F₂ (Fin L → F₂) :=
        (LinearEquiv.finrank_eq (startBoundaryEquivEven L)).symm
      _ = L := by simp [Module.finrank_pi]
  have hcard :
      (intermediatePrimes x L).card ≤ L :=
    card_intermediatePrimes_le hx hgap
  have hker :
      Module.finrank F₂
          (LinearMap.ker (lowZoneConstraintMap x L)) =
        L - (intermediatePrimes x L).card := by
    simp only [finrank_top, Module.finrank_pi,
      Fintype.card_coe] at hnullity
    rw [hsourceDim] at hnullity
    omega
  exact hfinrank.trans_eq hker

/--
Finite probability conclusion of Lemma 15.1, in the exact cylinder:

`P(J_{x,L}=1) ≤ 2^{-r(x)}`.

The notation `startProbability x L x` uses a cutoff `2x+L`, which contains
every prime coordinate occurring in the window at the absolute start `x`.
-/
theorem startProbability_le_inv_two_pow_card_intermediatePrimes
    {x L : ℕ} (hx : 2 ≤ x)
    (hgap : 2 * Nat.sqrt (x - 1) + 1 ≤ L) :
    startProbability x L x ≤
      (1 : ℚ) / (2 : ℚ) ^ (intermediatePrimes x L).card := by
  have hL : 0 < L := by
    have := (lowZoneSquareOffset_pos_le hx hgap).2
    omega
  have hrho :=
    relationRho_startSystem_le_sub_card_intermediatePrimes
      (M := dyadicCutoff x L) hx hgap (by
        unfold dyadicCutoff
        omega)
  rw [DefectFirstMoment.startProbability_eq_eta_mul_two_pow_rho_div
    x L x hL]
  let A := startSystem (dyadicCutoff x L) x L
  let b := startRhs L
  have hcard :
      (intermediatePrimes x L).card ≤ L :=
    card_intermediatePrimes_le hx hgap
  rcases relationEta_eq_zero_or_one A b with heta | heta
  · rw [heta]
    simp
  · rw [heta]
    simp only [Nat.cast_one, one_mul]
    have hpow :
        (2 : ℚ) ^ relationRho A ≤
          (2 : ℚ) ^
            (L - (intermediatePrimes x L).card) := by
      apply pow_le_pow_right₀ (by norm_num)
      simpa only [A] using hrho
    calc
      (2 : ℚ) ^ relationRho A / (2 : ℚ) ^ L ≤
          (2 : ℚ) ^ (L - (intermediatePrimes x L).card) /
            (2 : ℚ) ^ L :=
        div_le_div_of_nonneg_right hpow (by positivity)
      _ = (1 : ℚ) /
          (2 : ℚ) ^ (intermediatePrimes x L).card := by
        have hpowNe :
            (2 : ℚ) ^ (L - (intermediatePrimes x L).card) ≠ 0 := by
          positivity
        rw [show L =
          (L - (intermediatePrimes x L).card) +
            (intermediatePrimes x L).card by omega,
          pow_add]
        field_simp

end

end LowZonePrimePivots
end PaperC
