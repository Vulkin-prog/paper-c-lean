import PaperC.Model.InfiniteRademacher

/-!
# Transfer from the infinite Rademacher law to finite prime cylinders

The finite developments in this project use `SampleSpace M`, whose coordinates
are the primes at most `M`.  Section 14 uses the infinite product model, whose
coordinate `k` is assigned to the `k`-th prime.  This module identifies the two
representations:

* `restrictToFinite M` reads from an infinite sample exactly the coordinates
  belonging to `PrimeUpTo M`;
* on integers `n ≤ M`, its finite `valueBit` is the unrestricted
  `InfiniteRademacher.infiniteValueBit`;
* the image of the infinite product law is the exact finite uniform product
  law.

Thus the infinite model extends the previously audited finite-cylinder model
without changing any finite observable.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace PaperC
namespace InfiniteCylinderTransfer

open InfiniteRademacher

/- Keep the measurable structure definitionally identical to the local
structure used in `InfiniteRademacher`. -/
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- The infinite coordinate occupied by a prime in the finite cutoff. -/
def finitePrimeCoordinate (M : ℕ) (p : PrimeUpTo M) : ℕ :=
  Nat.primeCounting' p.1

/-- Distinct finite primes occupy distinct coordinates in the infinite
enumeration. -/
theorem finitePrimeCoordinate_injective (M : ℕ) :
    Function.Injective (finitePrimeCoordinate M) := by
  intro p q hpq
  apply Subtype.ext
  apply Fin.ext
  change Nat.count Nat.Prime (p.1 : ℕ) =
    Nat.count Nat.Prime (q.1 : ℕ) at hpq
  have h := congrArg (Nat.nth Nat.Prime) hpq
  rw [Nat.nth_count p.2, Nat.nth_count q.2] at h
  exact h

/-- The coordinate embedding of the finite prime cylinder into `ℕ`. -/
def finitePrimeCoordinateEmbedding (M : ℕ) : PrimeUpTo M ↪ ℕ where
  toFun := finitePrimeCoordinate M
  inj' := finitePrimeCoordinate_injective M

/-- The finite set of infinite coordinates observed below cutoff `M`. -/
noncomputable def finitePrimeCoordinates (M : ℕ) : Finset ℕ :=
  Finset.univ.map (finitePrimeCoordinateEmbedding M)

/-- A coordinate together with the fact that it belongs to the finite prime
cylinder. -/
abbrev FinitePrimeCoordinate (M : ℕ) :=
  {k : ℕ // k ∈ finitePrimeCoordinates M}

/-- Canonical equivalence between primes below `M` and the corresponding
coordinates of the infinite prime enumeration. -/
noncomputable def primeCoordinateEquiv (M : ℕ) :
    PrimeUpTo M ≃ FinitePrimeCoordinate M :=
  Equiv.ofBijective
    (fun p : PrimeUpTo M =>
      ⟨finitePrimeCoordinate M p, by
        simp [finitePrimeCoordinates, finitePrimeCoordinateEmbedding]⟩)
    ⟨by
      intro p q hpq
      exact finitePrimeCoordinate_injective M
        (congrArg Subtype.val hpq),
     by
      intro k
      rcases Finset.mem_map.mp k.2 with ⟨p, _hp, hpk⟩
      refine ⟨p, ?_⟩
      apply Subtype.ext
      exact hpk⟩

@[simp]
theorem primeCoordinateEquiv_apply_val (M : ℕ) (p : PrimeUpTo M) :
    (primeCoordinateEquiv M p : ℕ) = finitePrimeCoordinate M p :=
  rfl

/-- Restriction of an infinite assignment to the finite prime cylinder. -/
noncomputable def restrictToFinite (M : ℕ)
    (ω : InfiniteSample) : SampleSpace M :=
  fun p => ω (finitePrimeCoordinate M p)

@[simp]
theorem restrictToFinite_apply (M : ℕ) (ω : InfiniteSample)
    (p : PrimeUpTo M) :
    restrictToFinite M ω p = ω (finitePrimeCoordinate M p) :=
  rfl

/-- Every parity coordinate observed by an integer `n ≤ M` lies in the
finite cutoff. -/
theorem parityVec_support_subset_range {M n : ℕ}
    (hnM : n ≤ M) :
    (parityVec n).support ⊆ Finset.range (M + 1) := by
  intro p hp
  rw [Finset.mem_range]
  have hpFactor : p ∈ n.primeFactors :=
    Finsupp.support_mapRange hp
  exact Nat.lt_succ_of_le
    ((Nat.le_of_mem_primeFactors hpFactor).trans hnM)

/-- The finite and infinite parity functionals agree on every integer covered
by the cutoff. -/
theorem valueBit_restrictToFinite_eq_infiniteValueBit
    {M n : ℕ} (ω : InfiniteSample) (hnM : n ≤ M) :
    valueBit (restrictToFinite M ω) n =
      infiniteValueBit ω n := by
  classical
  have hprimeSum :
      (∑ q : PrimeUpTo M,
          ω (Nat.primeCounting' q.1) * parityVec n q.1) =
        ∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime,
          ω (Nat.primeCounting' p) * parityVec n p := by
    exact Finset.sum_bij
      (fun q _ => (q.1 : ℕ))
      (fun q _ => by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨q.1.2, q.2⟩)
      (fun q₁ _ q₂ _ hq => by
        apply Subtype.ext
        apply Fin.ext
        exact hq)
      (fun p hp => by
        simp only [Finset.mem_filter, Finset.mem_range] at hp
        let q : PrimeUpTo M :=
          ⟨⟨p, hp.1⟩, hp.2⟩
        exact ⟨q, Finset.mem_univ q, rfl⟩)
      (fun _ _ => rfl)
  have hfilter :
      (∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime,
          ω (Nat.primeCounting' p) * parityVec n p) =
        ∑ p ∈ Finset.range (M + 1),
          ω (Nat.primeCounting' p) * parityVec n p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime
    · simp [hprime]
    · simp [hprime, parityVec_apply,
        Nat.factorization_eq_zero_of_not_prime n hprime]
  have hinfinite :
      infiniteValueBit ω n =
        ∑ p ∈ Finset.range (M + 1),
          ω (Nat.primeCounting' p) * parityVec n p := by
    exact Finsupp.sum_of_support_subset
      (parityVec n)
      (parityVec_support_subset_range hnM)
      (fun p e => ω (Nat.primeCounting' p) * e)
      (by intro p hp; simp)
  change
    (∑ q : PrimeUpTo M,
      ω (Nat.primeCounting' q.1) * parityVec n q.1) =
        infiniteValueBit ω n
  rw [hprimeSum, hfilter]
  exact hinfinite.symm

/-- Integer-valued random multiplicative functions agree on every integer
covered by the cutoff. -/
theorem randomMultiplicativeValue_restrictToFinite_eq_infiniteRandomValue
    {M n : ℕ} (ω : InfiniteSample) (hnM : n ≤ M) :
    randomMultiplicativeValue (restrictToFinite M ω) n =
      infiniteRandomValue ω n := by
  simp only [randomMultiplicativeValue, infiniteRandomValue,
    valueBit_restrictToFinite_eq_infiniteValueBit ω hnM]

/-- Every finite start event covered by the cutoff is literally the
corresponding event in the unrestricted model. -/
theorem startAt_restrictToFinite_iff
    {M x L : ℕ} (ω : InfiniteSample) (hcut : x + L ≤ M) :
    startAt (restrictToFinite M ω) x L ↔
      StartEvent (infiniteValueBit ω) x L := by
  unfold startAt StartEvent
  constructor
  · rintro ⟨hleft, hrun⟩
    constructor
    · simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x - 1 ≤ M by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x ≤ M by omega)] using hleft
    · intro j hj
      have hjEq := hrun j hj
      simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x + j ≤ M by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x ≤ M by omega)] using hjEq
  · rintro ⟨hleft, hrun⟩
    constructor
    · simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x - 1 ≤ M by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x ≤ M by omega)] using hleft
    · intro j hj
      have hjEq := hrun j hj
      simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x + j ≤ M by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x ≤ M by omega)] using hjEq

/-- The exact finite uniform product measure on prime-sign assignments below
`M`. -/
noncomputable def finiteRademacherMeasure (M : ℕ) :
    Measure (SampleSpace M) :=
  Measure.pi (fun _ : PrimeUpTo M => coordinateMeasure)

noncomputable instance instIsProbabilityMeasureFiniteRademacherMeasure
    (M : ℕ) :
    IsProbabilityMeasure (finiteRademacherMeasure M) := by
  unfold finiteRademacherMeasure
  infer_instance

/-- Reindex a function on the selected coordinate subtype by the
corresponding finite primes. -/
noncomputable def finitePrimeReindex (M : ℕ) :
    (FinitePrimeCoordinate M → F₂) ≃ᵐ SampleSpace M :=
  MeasurableEquiv.piCongrLeft
    (fun _ : PrimeUpTo M => F₂)
    (primeCoordinateEquiv M).symm

/-- Restricting to the selected coordinate finset and then reindexing is
definitionally the direct restriction `restrictToFinite`. -/
theorem finitePrimeReindex_restrict (M : ℕ) (ω : InfiniteSample) :
    finitePrimeReindex M
        ((finitePrimeCoordinates M).restrict ω) =
      restrictToFinite M ω := by
  funext p
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (primeCoordinateEquiv M).symm
      (β := fun _ : PrimeUpTo M => F₂)
      ((finitePrimeCoordinates M).restrict ω)
      (primeCoordinateEquiv M p)
  simpa [finitePrimeReindex, restrictToFinite, Finset.restrict,
    primeCoordinateEquiv_apply_val] using h

/-- The image of the infinite Rademacher law on the primes at most `M` is
exactly the finite uniform product law. -/
theorem map_infiniteRademacherMeasure_restrictToFinite (M : ℕ) :
    Measure.map (restrictToFinite M) infiniteRademacherMeasure =
      finiteRademacherMeasure M := by
  let reindex := finitePrimeReindex M
  have hcomposition :
      (restrictToFinite M) =
        reindex ∘ (finitePrimeCoordinates M).restrict := by
    funext ω
    exact (finitePrimeReindex_restrict M ω).symm
  have hrestrictMeasurable :
      Measurable
        ((finitePrimeCoordinates M).restrict :
          InfiniteSample → (FinitePrimeCoordinate M → F₂)) :=
    Finset.measurable_restrict (finitePrimeCoordinates M)
  rw [hcomposition, ← Measure.map_map reindex.measurable
    hrestrictMeasurable]
  rw [infiniteRademacherMeasure,
    Measure.infinitePi_map_restrict]
  exact Measure.pi_map_piCongrLeft
    (primeCoordinateEquiv M).symm
    (fun _ : PrimeUpTo M => coordinateMeasure)

/-- Point masses of the finite image law are all equal.  This is the literal
uniform-law characterization on the finite sample space. -/
theorem finiteRademacherMeasure_singleton
    (M : ℕ) (σ : SampleSpace M) :
    finiteRademacherMeasure M ({σ} : Set (SampleSpace M)) =
      ((2 : ℝ≥0∞)⁻¹) ^ Fintype.card (PrimeUpTo M) := by
  have hsingleton :
      ({σ} : Set (SampleSpace M)) =
        Set.pi Set.univ (fun p : PrimeUpTo M => {σ p}) := by
    ext τ
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ,
      Set.mem_singleton_iff, forall_const]
    exact ⟨fun h => by simp [h],
      fun h => funext h⟩
  rw [finiteRademacherMeasure, hsingleton,
    Measure.pi_pi]
  simp only [coordinateMeasure_singleton, Finset.prod_const,
    Finset.card_univ]

end InfiniteCylinderTransfer
end PaperC
