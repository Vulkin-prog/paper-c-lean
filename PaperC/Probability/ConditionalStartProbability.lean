import PaperC.Affine.Normalization
import PaperC.Affine.Probability
import PaperC.Affine.StartDefectRank
import PaperC.Probability.BadStartCount

set_option maxHeartbeats 800000

/-!
# Exact start probability after fixing the small-prime coordinates

Section 13 conditions on all Rademacher coordinates at primes `p ≤ Y`.
This file realizes that conditioning inside the finite-cylinder model.

The prime coordinates represented up to `M` split into two disjoint finite
types: those at most `Y`, and those strictly above `Y`.  A fixed assignment
on the first type contributes an affine translate to the start system; the
second type is still sampled uniformly.

If every non-root vertex `x+j`, `0 ≤ j < L`, has an odd prime divisor
strictly larger than `Y`, and `L+1 ≤ Y`, those large coordinates give private
pivots for the start rows.  The resulting map from the remaining coordinates
onto the `L` start equations is surjective.  Consequently every affine fiber,
for every fixed small-prime assignment, has exact uniform probability

`2⁻ᴸ`.

The terminal good-start theorem specializes this finite statement to
`x ∉ D_Y`.  No measure-theoretic conditional-probability API is used: the
conditional law is represented exactly as the uniform law on the remaining
finite coordinate space.
-/

namespace PaperC
namespace ConditionalStartProbability

open scoped BigOperators

open Affine
open BadStartCount
open DefectivePredicate
open LargeOddKernel

noncomputable section

/-! ## Splitting the finite prime cylinder at `Y` -/

/-- Prime coordinates represented by the cylinder and lying at most `Y`. -/
def SmallPrimeCoordinate (M Y : ℕ) :=
  {p : PrimeUpTo M // p.1.1 ≤ Y}

/-- Prime coordinates represented by the cylinder and lying strictly above `Y`. -/
def LargePrimeCoordinate (M Y : ℕ) :=
  {p : PrimeUpTo M // Y < p.1.1}

instance (M Y : ℕ) : Fintype (SmallPrimeCoordinate M Y) :=
  Subtype.fintype _

instance (M Y : ℕ) : Fintype (LargePrimeCoordinate M Y) :=
  Subtype.fintype _

noncomputable instance (M Y : ℕ) :
    DecidableEq (SmallPrimeCoordinate M Y) :=
  Classical.decEq _

noncomputable instance (M Y : ℕ) :
    DecidableEq (LargePrimeCoordinate M Y) :=
  Classical.decEq _

/-- Assignments on the prime coordinates at most `Y`. -/
abbrev SmallSample (M Y : ℕ) :=
  SmallPrimeCoordinate M Y → F₂

/-- Assignments on the represented prime coordinates strictly above `Y`. -/
abbrev LargeSample (M Y : ℕ) :=
  LargePrimeCoordinate M Y → F₂

/-- Extend a small-prime assignment by zero on all coordinates above `Y`. -/
def extendSmall (M Y : ℕ) :
    SmallSample M Y →ₗ[F₂] SampleSpace M where
  toFun σ p :=
    if hp : p.1.1 ≤ Y then σ ⟨p, hp⟩ else 0
  map_add' σ τ := by
    funext p
    by_cases hp : p.1.1 ≤ Y <;> simp [hp]
  map_smul' c σ := by
    funext p
    by_cases hp : p.1.1 ≤ Y <;> simp [hp]

/-- Extend a large-prime assignment by zero on all coordinates at most `Y`. -/
def extendLarge (M Y : ℕ) :
    LargeSample M Y →ₗ[F₂] SampleSpace M where
  toFun η p :=
    if hp : Y < p.1.1 then η ⟨p, hp⟩ else 0
  map_add' η θ := by
    funext p
    by_cases hp : Y < p.1.1 <;> simp [hp]
  map_smul' c η := by
    funext p
    by_cases hp : Y < p.1.1 <;> simp [hp]

/-- Restrict a full cylinder assignment to the small coordinates. -/
def restrictSmall (M Y : ℕ) :
    SampleSpace M →ₗ[F₂] SmallSample M Y where
  toFun ω p := ω p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restrict a full cylinder assignment to the large coordinates. -/
def restrictLarge (M Y : ℕ) :
    SampleSpace M →ₗ[F₂] LargeSample M Y where
  toFun ω p := ω p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reassemble a full assignment from its two disjoint coordinate pieces. -/
def assemble (M Y : ℕ)
    (σ : SmallSample M Y) (η : LargeSample M Y) :
    SampleSpace M :=
  extendSmall M Y σ + extendLarge M Y η

@[simp]
theorem restrictSmall_extendSmall
    (M Y : ℕ) (σ : SmallSample M Y) :
    restrictSmall M Y (extendSmall M Y σ) = σ := by
  funext p
  simp [restrictSmall, extendSmall, p.2]

@[simp]
theorem restrictSmall_extendLarge
    (M Y : ℕ) (η : LargeSample M Y) :
    restrictSmall M Y (extendLarge M Y η) = 0 := by
  funext p
  simp [restrictSmall, extendLarge, Nat.not_lt.mpr p.2]

@[simp]
theorem restrictLarge_extendSmall
    (M Y : ℕ) (σ : SmallSample M Y) :
    restrictLarge M Y (extendSmall M Y σ) = 0 := by
  funext p
  simp [restrictLarge, extendSmall, Nat.not_le.mpr p.2]

@[simp]
theorem restrictLarge_extendLarge
    (M Y : ℕ) (η : LargeSample M Y) :
    restrictLarge M Y (extendLarge M Y η) = η := by
  funext p
  simp [restrictLarge, extendLarge, p.2]

@[simp]
theorem restrictSmall_assemble
    (M Y : ℕ) (σ : SmallSample M Y) (η : LargeSample M Y) :
    restrictSmall M Y (assemble M Y σ η) = σ := by
  simp [assemble]

@[simp]
theorem restrictLarge_assemble
    (M Y : ℕ) (σ : SmallSample M Y) (η : LargeSample M Y) :
    restrictLarge M Y (assemble M Y σ η) = η := by
  simp [assemble]

/-- The two restrictions reconstruct every full cylinder assignment. -/
theorem assemble_restrictions
    (M Y : ℕ) (ω : SampleSpace M) :
    assemble M Y (restrictSmall M Y ω) (restrictLarge M Y ω) = ω := by
  funext p
  by_cases hp : p.1.1 ≤ Y
  · simp [assemble, extendSmall, extendLarge, restrictSmall, restrictLarge,
      hp, Nat.not_lt.mpr hp]
  · have hp' : Y < p.1.1 := Nat.lt_of_not_ge hp
    simp [assemble, extendSmall, extendLarge, restrictSmall, restrictLarge,
      hp, hp']

/--
The full assignments extending a fixed small assignment are in bijection
with assignments on the large coordinates.
-/
def completionEquiv
    (M Y : ℕ) (σ : SmallSample M Y) :
    LargeSample M Y ≃
      {ω : SampleSpace M // restrictSmall M Y ω = σ} where
  toFun η := ⟨assemble M Y σ η, restrictSmall_assemble M Y σ η⟩
  invFun ω := restrictLarge M Y ω.1
  left_inv η := restrictLarge_assemble M Y σ η
  right_inv ω := by
    apply Subtype.ext
    rw [← assemble_restrictions M Y ω.1]
    simp [ω.2]

/-! ## The affine system on the unfixed large coordinates -/

/-- Linear part of the start equations after the small coordinates are fixed. -/
def largeStartSystem (M Y x L : ℕ) :
    LargeSample M Y →ₗ[F₂] (Fin L → F₂) :=
  (startSystem M x L).comp (extendLarge M Y)

/-- The translated right-hand side determined by a fixed small assignment. -/
def conditionedStartRhs
    (M Y x L : ℕ) (σ : SmallSample M Y) :
    Fin L → F₂ :=
  startRhs L - startSystem M x L (extendSmall M Y σ)

/--
After fixing the small coordinates, a full assignment solves the start
system exactly when its large-coordinate part solves the translated system.
-/
theorem assemble_solves_start_iff
    (M Y x L : ℕ) (σ : SmallSample M Y) (η : LargeSample M Y) :
    startSystem M x L (assemble M Y σ η) = startRhs L ↔
      largeStartSystem M Y x L η = conditionedStartRhs M Y x L σ := by
  simp only [assemble, map_add, largeStartSystem, LinearMap.comp_apply,
    conditionedStartRhs]
  constructor <;> intro h
  · rw [← h]
    simp
  · rw [h]
    simp

/-- Event-level form of `assemble_solves_start_iff`. -/
theorem assemble_startAt_iff
    (M Y x L : ℕ) (hL : 0 < L)
    (σ : SmallSample M Y) (η : LargeSample M Y) :
    startAt (assemble M Y σ η) x L ↔
      largeStartSystem M Y x L η = conditionedStartRhs M Y x L σ := by
  rw [← startSystem_eq_startRhs_iff_startAt
    (assemble M Y σ η) hL]
  exact assemble_solves_start_iff M Y x L σ η

/-! ## Private large-prime pivots -/

private theorem valueBit_extendLarge_single
    {M Y n p : ℕ} (hp : p.Prime) (hpM : p ≤ M) (hpY : Y < p) :
    valueBit
        (extendLarge M Y
          (Pi.single
            (⟨
              (⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩ : PrimeUpTo M),
              hpY⟩ : LargePrimeCoordinate M Y)
            1))
        n =
      parityVec n p := by
  classical
  let q : PrimeUpTo M :=
    ⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩
  let qLarge : LargePrimeCoordinate M Y := ⟨q, hpY⟩
  rw [valueBit]
  rw [Fintype.sum_eq_single q]
  · simp [extendLarge, q, qLarge, hpY]
  · intro r hrq
    have hrq' : r ≠ q := hrq
    by_cases hrY : Y < r.1.1
    · have hlarge :
          (⟨r, hrY⟩ : LargePrimeCoordinate M Y) ≠ qLarge := by
        intro h
        apply hrq'
        exact congrArg Subtype.val h
      simp [extendLarge, hrY, Pi.single_apply, hlarge, q, qLarge]
    · simp [extendLarge, hrY]

private theorem large_relation_prime_equation
    {M Y x L p : ℕ}
    (u : RelationSpace (largeStartSystem M Y x L))
    (hp : p.Prime) (hpM : p ≤ M) (hpY : Y < p) :
    ∑ i : Fin L, (u : Fin L → F₂) i *
        (if i.1 = 0 then
          parityVec (x - 1) p + parityVec x p
        else
          parityVec x p + parityVec (x + i.1) p) =
      0 := by
  classical
  let q : PrimeUpTo M :=
    ⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩
  let qLarge : LargePrimeCoordinate M Y := ⟨q, hpY⟩
  let η : LargeSample M Y := Pi.single qLarge 1
  have hrel :
      relationFunctional
          (largeStartSystem M Y x L) (u : Fin L → F₂) η = 0 := by
    have hu :
        relationMap
            (largeStartSystem M Y x L) (u : Fin L → F₂) = 0 :=
      LinearMap.mem_ker.mp u.2
    have huη := DFunLike.congr_fun hu η
    change
      relationFunctional
          (largeStartSystem M Y x L) (u : Fin L → F₂) η =
        0 at huη
    exact huη
  rw [relationFunctional_apply] at hrel
  simp only [dotProduct, largeStartSystem, LinearMap.comp_apply,
    startSystem_apply] at hrel
  dsimp only [η, qLarge, q] at hrel
  simp_rw [valueBit_extendLarge_single hp hpM hpY] at hrel
  exact hrel

private theorem exists_large_prime_coordinate_of_not_hDefective
    {Y n : ℕ} (h : ¬HDefective Y n) :
    ∃ p : ℕ, p.Prime ∧ Y < p ∧ parityVec n p ≠ 0 := by
  simp only [HDefective] at h
  push_neg at h
  exact h

private theorem parityVec_eq_zero_of_private
    {a b p Y : ℕ}
    (hpa : parityVec a p ≠ 0) (hab : a ≠ b)
    (hpY : Y < p) (hdist : Nat.dist a b < Y) :
    parityVec b p = 0 := by
  have hpFactor : a.factorization p ≠ 0 := by
    intro hz
    apply hpa
    rw [parityVec_apply, hz]
    rfl
  have hpdvd : p ∣ a := by
    by_contra hnot
    exact hpFactor (Nat.factorization_eq_zero_of_not_dvd hnot)
  have hpnot : ¬p ∣ b :=
    PrivatePivots.not_dvd_of_dvd_and_dist_lt
      hpdvd hab hpY hdist
  rw [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hpnot]
  rfl

private theorem private_prime_on_start_vertices
    {x L p Y : ℕ}
    (hx : 2 ≤ x) (hLY : L + 1 ≤ Y)
    {j : Fin L} (hpY : Y < p)
    (hjp : parityVec (x + j.1) p ≠ 0) :
    parityVec (x - 1) p = 0 ∧
      ∀ k : Fin L, k ≠ j → parityVec (x + k.1) p = 0 := by
  constructor
  · exact parityVec_eq_zero_of_private
      (Y := Y) hjp (by omega) hpY (by
        have : Nat.dist (x + j.1) (x - 1) < L + 1 := by
          simp only [Nat.dist]
          omega
        omega)
  · intro k hkj
    exact parityVec_eq_zero_of_private
      (Y := Y) hjp (by
        intro h
        apply hkj
        apply Fin.ext
        omega) hpY (by
          rw [Nat.dist_add_add_left]
          have : Nat.dist j.1 k.1 < L + 1 := by
            simp only [Nat.dist]
            omega
          omega)

/--
If every non-root start vertex has a large odd prime above `Y`, then the
restricted large-coordinate start map has no row relations.
-/
theorem relationSpace_largeStartSystem_eq_bot
    {M Y x L : ℕ}
    (hx : 2 ≤ x) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hvertices : ∀ j : Fin L, x + j.1 ≤ M)
    (hgood : ∀ j : Fin L, ¬HDefective Y (x + j.1)) :
    RelationSpace (largeStartSystem M Y x L) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  let ur : RelationSpace (largeStartSystem M Y x L) := ⟨u, hu⟩
  have hnonzero :
      ∀ j : Fin L, j.1 ≠ 0 → u j = 0 := by
    intro j hj0
    obtain ⟨p, hp, hpY, hjp⟩ :=
      exists_large_prime_coordinate_of_not_hDefective (hgood j)
    have hpDvd : p ∣ x + j.1 := by
      have hpFactor : (x + j.1).factorization p ≠ 0 := by
        intro hz
        apply hjp
        rw [parityVec_apply, hz]
        rfl
      by_contra hnot
      exact hpFactor (Nat.factorization_eq_zero_of_not_dvd hnot)
    have hpM : p ≤ M :=
      (Nat.le_of_dvd (by omega) hpDvd).trans (hvertices j)
    have hprivate :=
      private_prime_on_start_vertices hx hLY hpY hjp
    have hcenter : parityVec x p = 0 := by
      let z : Fin L := ⟨0, hL⟩
      have hzj : z ≠ j := by
        intro h
        apply hj0
        simpa [z] using congrArg Fin.val h.symm
      simpa [z] using hprivate.2 z hzj
    have heq := large_relation_prime_equation ur hp hpM hpY
    have heq' :
        u j * parityVec (x + j.1) p = 0 := by
      calc
        u j * parityVec (x + j.1) p =
            ∑ i : Fin L, u i *
              (if i = j then parityVec (x + j.1) p else 0) := by
              symm
              simp
        _ = ∑ i : Fin L, u i *
              (if i.1 = 0 then
                parityVec (x - 1) p + parityVec x p
              else
                parityVec x p + parityVec (x + i.1) p) := by
              apply Finset.sum_congr rfl
              intro i _hi
              by_cases hij : i = j
              · subst i
                simp [hj0, hcenter]
              · by_cases hi0 : i.1 = 0
                · simp [hi0, hprivate.1, hcenter, hij]
                · simp [hi0, hcenter, hij, hprivate.2 i hij]
        _ = 0 := heq
    exact (mul_eq_zero.mp heq').resolve_right hjp
  let z : Fin L := ⟨0, hL⟩
  obtain ⟨p, hp, hpY, hzp⟩ :=
    exists_large_prime_coordinate_of_not_hDefective (hgood z)
  have hpDvd : p ∣ x + z.1 := by
    have hpFactor : (x + z.1).factorization p ≠ 0 := by
      intro hz
      apply hzp
      rw [parityVec_apply, hz]
      rfl
    by_contra hnot
    exact hpFactor
      (Nat.factorization_eq_zero_of_not_dvd
        (show ¬p ∣ x + z.1 from hnot))
  have hpM : p ≤ M :=
    (Nat.le_of_dvd (by omega) hpDvd).trans (hvertices z)
  have hprivate :=
    private_prime_on_start_vertices hx hLY hpY hzp
  have heq := large_relation_prime_equation ur hp hpM hpY
  have hsum :
      (∑ i : Fin L, u i) * parityVec x p = 0 := by
    calc
      (∑ i : Fin L, u i) * parityVec x p =
          ∑ i : Fin L, u i * parityVec x p := by
            rw [Finset.sum_mul]
      _ = ∑ i : Fin L, u i *
            (if i.1 = 0 then
              parityVec (x - 1) p + parityVec x p
            else
              parityVec x p + parityVec (x + i.1) p) := by
            apply Finset.sum_congr rfl
            intro i _hi
            by_cases hi0 : i.1 = 0
            · simp [hi0, hprivate.1]
            · have hiz : i ≠ z := by
                intro h
                apply hi0
                simpa [z] using congrArg Fin.val h
              simp [hi0, hprivate.2 i hiz]
      _ = 0 := heq
  have hsumZero :
      ∑ i : Fin L, u i = 0 :=
    (mul_eq_zero.mp hsum).resolve_right (by simpa [z] using hzp)
  have huz : u z = 0 := by
    calc
      u z =
          ∑ i : Fin L, u i := by
            symm
            apply Finset.sum_eq_single z
            · intro i _hi hiz
              apply hnonzero i
              intro hi0
              apply hiz
              apply Fin.ext
              simpa [z] using hi0
            · simp
      _ = 0 := hsumZero
  funext j
  by_cases hj0 : j.1 = 0
  · have hjz : j = z := by
      apply Fin.ext
      simpa [z] using hj0
    simpa [hjz] using huz
  · exact hnonzero j hj0

/-- The large-coordinate start map is surjective under the private-pivot hypothesis. -/
theorem largeStartSystem_surjective
    {M Y x L : ℕ}
    (hx : 2 ≤ x) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hvertices : ∀ j : Fin L, x + j.1 ≤ M)
    (hgood : ∀ j : Fin L, ¬HDefective Y (x + j.1)) :
    Function.Surjective (largeStartSystem M Y x L) := by
  intro b
  have hrelations :
      RelationSpace (largeStartSystem M Y x L) = ⊥ :=
    relationSpace_largeStartSystem_eq_bot
      hx hL hLY hvertices hgood
  have hcharacter :
      relationCharacter (largeStartSystem M Y x L) b = 0 := by
    apply LinearMap.ext
    intro u
    have hu : u = 0 := by
      apply Subtype.ext
      have humem :
          (u : Fin L → F₂) ∈
            (⊥ : Submodule F₂ (Fin L → F₂)) := by
        rw [← hrelations]
        exact u.2
      exact (Submodule.mem_bot F₂).mp humem
    simp [hu]
  have hcompat :
      Compatible (largeStartSystem M Y x L) b :=
    compatible_of_relationCharacter_eq_zero
      (largeStartSystem M Y x L) b hcharacter
  exact LinearMap.mem_range.mp hcompat

/-! ## Uniform cardinality of every conditioned fiber -/

/-- Large-coordinate assignments satisfying the translated start equations. -/
def conditionedStartSolutions
    (M Y x L : ℕ) (σ : SmallSample M Y) :
    Finset (LargeSample M Y) := by
  classical
  exact Finset.univ.filter fun η ↦
    largeStartSystem M Y x L η =
      conditionedStartRhs M Y x L σ

/--
Exact fiber-cardinality identity after fixing the small coordinates:

`#solutions · 2^L = #large assignments`.

This division-free equality expresses that every translated fiber occupies
exactly the fraction `2⁻ᴸ` of the remaining finite cylinder.
-/
theorem card_conditionedStartSolutions_mul_two_pow
    {M Y x L : ℕ}
    (hx : 2 ≤ x) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hvertices : ∀ j : Fin L, x + j.1 ≤ M)
    (hgood : ∀ j : Fin L, ¬HDefective Y (x + j.1))
    (σ : SmallSample M Y) :
    (conditionedStartSolutions M Y x L σ).card * 2 ^ L =
      Fintype.card (LargeSample M Y) := by
  classical
  let A := largeStartSystem M Y x L
  let b := conditionedStartRhs M Y x L σ
  have hsurj : Function.Surjective A := by
    dsimp only [A]
    exact largeStartSystem_surjective
      hx hL hLY hvertices hgood
  have hcompat : Compatible A b :=
    LinearMap.mem_range.mpr (hsurj b)
  have heta : relationEta A b = 1 :=
    (relationEta_eq_one_iff_compatible A b).mpr hcompat
  have hrelations : RelationSpace A = ⊥ := by
    dsimp only [A]
    exact relationSpace_largeStartSystem_eq_bot
      hx hL hLY hvertices hgood
  have hrho : relationRho A = 0 := by
    rw [relationRho, hrelations]
    simp
  have hfourier :=
    affineFiber_normalized_card_identity A b
  have hfilter :
      (Finset.univ.filter fun η : LargeSample M Y => A η = b).card =
        (conditionedStartSolutions M Y x L σ).card := by
    rfl
  rw [hfilter, heta, hrho] at hfourier
  simp only [Fintype.card_fin, Nat.cast_one, one_mul, pow_zero,
    mul_one] at hfourier
  norm_cast at hfourier
  simpa [Fintype.card_fun, ZMod.card, mul_comm] using hfourier

/-!
The exact conditional statement is most transparently proved by the finite
Fourier identity.  Surjectivity makes the relation space trivial, so every
fiber has relative mass `1 / 2^L`.
-/

/--
For every fixed assignment of the coordinates at most `Y`, the uniform
probability over the remaining coordinates that the start equations hold is
exactly `2⁻ᴸ`.
-/
theorem conditionedStartProbability_eq_baseline
    {M Y x L : ℕ}
    (hx : 2 ≤ x) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hvertices : ∀ j : Fin L, x + j.1 ≤ M)
    (hgood : ∀ j : Fin L, ¬HDefective Y (x + j.1))
    (σ : SmallSample M Y) :
    uniformSolutionProbability
        (largeStartSystem M Y x L)
        (conditionedStartRhs M Y x L σ) =
      (1 : ℚ) / (2 : ℚ) ^ L := by
  let A := largeStartSystem M Y x L
  let b := conditionedStartRhs M Y x L σ
  have hsurj : Function.Surjective A := by
    dsimp only [A]
    exact largeStartSystem_surjective
      hx hL hLY hvertices hgood
  have hcompat : Compatible A b :=
    LinearMap.mem_range.mpr (hsurj b)
  rw [uniformSolutionProbability_of_compatible A b hcompat]
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker A
  have hrange : LinearMap.range A = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [hrange] at hnullity
  simp only [finrank_top, Module.finrank_pi,
    Fintype.card_fin] at hnullity
  have hsource :
      Module.finrank F₂ (LargeSample M Y) =
        Fintype.card (LargePrimeCoordinate M Y) :=
    Module.finrank_pi F₂
  have hdim :
      Module.finrank F₂ (LargeSample M Y) =
        Module.finrank F₂ (LinearMap.ker A) + L := by
    rw [hsource]
    omega
  rw [hdim, pow_add]
  field_simp

/--
Terminal good-start specialization: outside `D_Y`, fixing every represented
prime coordinate at most `Y` leaves exact start probability `2⁻ᴸ`.
-/
theorem conditionedStartProbability_eq_baseline_of_not_terminalBad
    {N Y x L : ℕ}
    (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hgood : x ∉ terminalBadStarts N L Y)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    uniformSolutionProbability
        (largeStartSystem (dyadicCutoff N L) Y x L)
        (conditionedStartRhs (dyadicCutoff N L) Y x L σ) =
      (1 : ℚ) / (2 : ℚ) ^ L := by
  apply conditionedStartProbability_eq_baseline
    (two_le_of_mem_dyadicBlock hN hx) hL hLY
  · intro j
    exact startWindow_le_dyadicCutoff hx j.2
  · intro j hjDef
    apply hgood
    rw [mem_terminalBadStarts]
    refine ⟨hx, j.1, j.2, ?_⟩
    exact (largeOddKernel_eq_one_iff_hDefective Y (x + j.1)).mpr hjDef

end

end ConditionalStartProbability
end PaperC
