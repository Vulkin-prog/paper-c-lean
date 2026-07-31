import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# A factorial bound for the number of distinct prime factors

The elementary inequality

`(#{p : p ∣ n})! ≤ n`

is strong enough to recover every fixed-base reciprocal-power consequence
normally deduced from the classical estimate
`ω(n) = O(log n / log log n)`.  The advantage of this formulation is that
Mathlib already proves that a factorial eventually dominates every fixed
exponential.
-/

namespace PaperC
namespace PrimeFactorsFactorialBound

open scoped BigOperators Nat

private theorem fin_strictMono_lower_bound
    {m : ℕ} (f : Fin m → ℕ)
    (hf : StrictMono f)
    (hpos : ∀ i, 0 < f i) :
    ∀ i : Fin m, i.1 + 1 ≤ f i := by
  intro i
  have aux :
      ∀ j : ℕ, ∀ hj : j < m,
        j + 1 ≤ f ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero =>
        intro hj
        exact hpos _
    | succ j ih =>
        intro hj
        have hjPrev : j < m := by omega
        have hprev := ih hjPrev
        have hstep :
            f ⟨j, hjPrev⟩ < f ⟨j + 1, hj⟩ :=
          hf (by simp)
        omega
  exact aux i.1 i.2

/--
The factorial of the cardinality of a finite set of positive naturals is at
most their product.
-/
theorem factorial_card_le_prod
    (s : Finset ℕ)
    (hpos : ∀ a ∈ s, 0 < a) :
    (s.card)! ≤ ∏ a ∈ s, a := by
  let e : Fin s.card ↪o ℕ :=
    s.orderEmbOfFin rfl
  have he :
      ∀ i : Fin s.card, i.1 + 1 ≤ e i :=
    fin_strictMono_lower_bound e e.strictMono fun i ↦
      hpos _ (s.orderEmbOfFin_mem rfl i)
  calc
    (s.card)! =
        ∏ j ∈ Finset.range s.card, (j + 1) :=
      (Finset.prod_range_add_one_eq_factorial s.card).symm
    _ = ∏ i : Fin s.card, (i.1 + 1) :=
      (Fin.prod_univ_eq_prod_range
        (fun j : ℕ ↦ j + 1) s.card).symm
    _ ≤ ∏ i : Fin s.card, e i :=
      Finset.prod_le_prod
        (fun _ _ ↦ Nat.zero_le _)
        (fun i _ ↦ he i)
    _ = ∏ a ∈ s, a := by
      calc
        (∏ i : Fin s.card, e i) =
            ∏ a ∈ Finset.map e.toEmbedding Finset.univ, a := by
          change
            (∏ i : Fin s.card, e.toEmbedding i) =
              ∏ a ∈ Finset.map e.toEmbedding Finset.univ, a
          rw [Finset.prod_map]
        _ = ∏ a ∈ s, a := by
          rw [s.map_orderEmbOfFin_univ rfl]

/--
For every positive natural `n`, the factorial of the number of its distinct
prime factors is at most `n`.
-/
theorem primeFactors_card_factorial_le
    {n : ℕ} (hn : 0 < n) :
    (n.primeFactors.card)! ≤ n := by
  calc
    (n.primeFactors.card)! ≤
        ∏ p ∈ n.primeFactors, p :=
      factorial_card_le_prod n.primeFactors fun p hp ↦
        (Nat.prime_of_mem_primeFactors hp).pos
    _ ≤ n :=
      Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/--
Fixed affine exponentials in `ω(n)` are reciprocal-power subpolynomial when
`n` has fixed polynomial height.

This is the exact quantitative consequence needed for the
Evertse--Silverman factor `a * b^(c * ω(n))`.  It is proved without an
analytic maximal-order theorem: `ω(n)! ≤ n`, while a factorial eventually
dominates every fixed exponential.
-/
theorem affinePow_primeFactorsCard_pow_le_of_polynomialHeight
    (a b c E k : ℕ) (hb : 1 ≤ b) (hE : 0 < E) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ n : ℕ,
      0 < n →
      n ≤ X ^ E →
      (a * b ^ (c * n.primeFactors.card)) ^ k ≤ X := by
  let A : ℕ := a ^ (k * E)
  let B : ℕ := b ^ (c * k * E)
  obtain ⟨T, hT⟩ :=
    (Filter.eventually_atTop.1
      (Nat.eventually_mul_pow_lt_factorial_sub A B 0))
  let X₀ : ℕ :=
    max 1 ((a * b ^ (c * T)) ^ k)
  refine ⟨X₀, ?_⟩
  intro X hX n hn hnHeight
  let m := n.primeFactors.card
  by_cases hm : m ≤ T
  · have hexponent : c * m ≤ c * T :=
      Nat.mul_le_mul_left c hm
    have hbase :
        a * b ^ (c * m) ≤
          a * b ^ (c * T) :=
      Nat.mul_le_mul_left a
        (Nat.pow_le_pow_right hb hexponent)
    calc
      (a * b ^ (c * n.primeFactors.card)) ^ k =
          (a * b ^ (c * m)) ^ k := rfl
      _ ≤ (a * b ^ (c * T)) ^ k :=
        Nat.pow_le_pow_left hbase k
      _ ≤ X₀ := le_max_right _ _
      _ ≤ X := hX
  · have hTm : T ≤ m := by omega
    have hfactorial :
        A * B ^ m < (m)! := by
      simpa only [Nat.sub_zero] using hT m hTm
    have hfactorialN :
        (m)! ≤ n :=
      primeFactors_card_factorial_le hn
    have hpowerIdentity :
        ((a * b ^ (c * m)) ^ k) ^ E =
          A * B ^ m := by
      dsimp only [A, B]
      rw [← pow_mul, mul_pow, ← pow_mul, ← pow_mul]
      congr 2
      ac_rfl
    have hstrict :
        ((a * b ^ (c * m)) ^ k) ^ E <
          X ^ E := by
      rw [hpowerIdentity]
      exact hfactorial.trans_le
        (hfactorialN.trans hnHeight)
    have hroot :
        (a * b ^ (c * m)) ^ k < X :=
      (Nat.pow_lt_pow_iff_left hE.ne').mp hstrict
    simpa only [m] using hroot.le

/--
Maximum of `ω(n)` over the finite polynomial-height box `0 ≤ n ≤ X^E`.
-/
noncomputable def polynomialHeightOmega
    (X E : ℕ) : ℕ := by
  classical
  let values :=
    (Finset.range (X ^ E + 1)).image
      (fun n : ℕ ↦ n.primeFactors.card)
  exact values.max' <| by
    refine ⟨0, ?_⟩
    exact Finset.mem_image.mpr
      ⟨0, by simp, by simp⟩

/-- Every integer in the polynomial-height box is controlled by its maximum. -/
theorem primeFactors_card_le_polynomialHeightOmega
    {X E n : ℕ} (hn : n ≤ X ^ E) :
    n.primeFactors.card ≤ polynomialHeightOmega X E := by
  classical
  let values :=
    (Finset.range (X ^ E + 1)).image
      (fun q : ℕ ↦ q.primeFactors.card)
  have hnonempty : values.Nonempty := by
    refine ⟨0, ?_⟩
    exact Finset.mem_image.mpr
      ⟨0, by simp, by simp⟩
  change n.primeFactors.card ≤ values.max' hnonempty
  apply Finset.le_max'
  exact Finset.mem_image.mpr
    ⟨n, Finset.mem_range.mpr (by omega), rfl⟩

/-- A witness realizes the polynomial-height maximum. -/
theorem exists_primeFactors_card_eq_polynomialHeightOmega
    (X E : ℕ) :
    ∃ n ≤ X ^ E,
      n.primeFactors.card = polynomialHeightOmega X E := by
  classical
  let values :=
    (Finset.range (X ^ E + 1)).image
      (fun q : ℕ ↦ q.primeFactors.card)
  have hnonempty : values.Nonempty := by
    refine ⟨0, ?_⟩
    exact Finset.mem_image.mpr
      ⟨0, by simp, by simp⟩
  have hmem :
      values.max' hnonempty ∈ values :=
    Finset.max'_mem values hnonempty
  obtain ⟨n, hn, heq⟩ :=
    Finset.mem_image.mp hmem
  refine ⟨n, ?_, ?_⟩
  · exact Nat.le_of_lt_succ
      (Finset.mem_range.mp hn)
  · change n.primeFactors.card =
      values.max' hnonempty
    exact heq

/--
The worst distinct-prime-factor count is monotone under inclusion of the
underlying polynomial-height boxes.
-/
theorem polynomialHeightOmega_mono_of_pow_le
    {X E Y F : ℕ} (hbox : X ^ E ≤ Y ^ F) :
    polynomialHeightOmega X E ≤
      polynomialHeightOmega Y F := by
  obtain ⟨n, hn, homega⟩ :=
    exists_primeFactors_card_eq_polynomialHeightOmega X E
  rw [← homega]
  exact
    primeFactors_card_le_polynomialHeightOmega
      (hn.trans hbox)

/--
The fixed affine exponential evaluated at the worst possible `ω` in a
polynomial-height box is reciprocal-power subpolynomial.
-/
theorem affinePow_polynomialHeightOmega_pow_le_eventually
    (a b c E k : ℕ) (hb : 1 ≤ b) (hE : 0 < E) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (a * b ^ (c * polynomialHeightOmega X E)) ^ k ≤ X := by
  obtain ⟨Xgeneric, hXgeneric⟩ :=
    affinePow_primeFactorsCard_pow_le_of_polynomialHeight
      a b c E k hb hE
  let X₀ :=
    max Xgeneric (a ^ k)
  refine ⟨X₀, ?_⟩
  intro X hX
  have hXgeneric' : Xgeneric ≤ X :=
    (le_max_left _ _).trans hX
  have ha : a ^ k ≤ X :=
    (le_max_right _ _).trans hX
  by_cases hmax :
      polynomialHeightOmega X E = 0
  · simpa only [hmax, mul_zero, pow_zero, mul_one] using ha
  · obtain ⟨n, hnHeight, hnOmega⟩ :=
      exists_primeFactors_card_eq_polynomialHeightOmega X E
    have hn : 0 < n := by
      by_contra hn'
      have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn'
      subst n
      simp only [Nat.primeFactors_zero, Finset.card_empty] at hnOmega
      exact hmax hnOmega.symm
    simpa only [hnOmega] using
      hXgeneric X hXgeneric' n hn hnHeight

end PrimeFactorsFactorialBound
end PaperC
