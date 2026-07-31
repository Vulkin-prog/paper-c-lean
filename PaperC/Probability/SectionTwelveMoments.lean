import PaperC.Affine.Normalization
import PaperC.Affine.Probability
import PaperC.Affine.RelationBoundaryIff
import PaperC.Affine.TwoStartSystem
import PaperC.Analysis.CriticalTouchingPairs
import PaperC.Arithmetic.RationalMassFinite
import PaperC.Asymptotics.CriticalRationalMassEnvelopes
import PaperC.Asymptotics.PropositionElevenTwo
import PaperC.Asymptotics.RationalPowerLittleO
import PaperC.Combinatorics.TouchingPairs
import PaperC.Probability.FiniteExpectation
import PaperC.Probability.CriticalRunWindow
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring

set_option maxHeartbeats 1800000

/-!
# Section 12: deduction of the first two moments

This module carries out the finite probability algebra in Section 12 of
Paper C.  The ordered square of the dyadic block is partitioned into four
literal populations:

* the diagonal;
* distinct starts at distance `< L` (strict overlap);
* starts at distance `L` (touching);
* starts at distance `> L` (separated).

The second factorial moment removes the diagonal, strict overlaps contribute
zero by the deterministic local-exclusion lemma, and the remaining two
populations are controlled by their affine defects `2^ρ-1`.

The variance identity

`Var Z = E[(Z)_2] + E Z - (E Z)^2`

is proved over the exact rational finite-cylinder expectation, independently
of any asymptotic input.
-/

namespace PaperC
namespace SectionTwelveMoments

open scoped BigOperators
open Affine
open RationalMassFinite

noncomputable section

local instance startAtDecidable
    {M : ℕ} (ω : SampleSpace M) (x L : ℕ) :
    Decidable (startAt ω x L) :=
  Classical.propDecidable _

/-! ## Uniform-expectation algebra -/

/-- Uniform expectation commutes with a finite sum. -/
theorem uniformExpectation_finset_sum
    {M : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → SampleSpace M → ℚ) :
    uniformExpectation (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, uniformExpectation (f i) := by
  classical
  unfold uniformExpectation
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

/-- Additivity of exact uniform expectation. -/
theorem uniformExpectation_add
    {M : ℕ} (f g : SampleSpace M → ℚ) :
    uniformExpectation (fun ω => f ω + g ω) =
      uniformExpectation f + uniformExpectation g := by
  classical
  unfold uniformExpectation
  rw [Finset.sum_add_distrib]
  ring

/-- Subtractivity of exact uniform expectation. -/
theorem uniformExpectation_sub
    {M : ℕ} (f g : SampleSpace M → ℚ) :
    uniformExpectation (fun ω => f ω - g ω) =
      uniformExpectation f - uniformExpectation g := by
  classical
  unfold uniformExpectation
  rw [Finset.sum_sub_distrib]
  ring

/-- Constants have their expected value under the nonempty uniform law. -/
theorem uniformExpectation_const
    {M : ℕ} (c : ℚ) :
    uniformExpectation (fun _ω : SampleSpace M => c) = c := by
  classical
  unfold uniformExpectation
  have hcard :
      (Fintype.card (SampleSpace M) : ℚ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_ne_zero : Fintype.card (SampleSpace M) ≠ 0)
  simp [hcard]

/-- A constant scalar can be pulled out of exact uniform expectation. -/
theorem uniformExpectation_const_mul
    {M : ℕ} (c : ℚ) (f : SampleSpace M → ℚ) :
    uniformExpectation (fun ω => c * f ω) =
      c * uniformExpectation f := by
  classical
  unfold uniformExpectation
  rw [← Finset.mul_sum]
  ring

/-- Exact variance on a finite Rademacher cylinder. -/
noncomputable def uniformVariance
    {M : ℕ} (f : SampleSpace M → ℚ) : ℚ :=
  uniformExpectation
    (fun ω => (f ω - uniformExpectation f) ^ 2)

/-- The usual centered-square identity for exact finite variance. -/
theorem uniformVariance_eq_expectation_sq_sub_sq
    {M : ℕ} (f : SampleSpace M → ℚ) :
    uniformVariance f =
      uniformExpectation (fun ω => f ω * f ω) -
        (uniformExpectation f) ^ 2 := by
  let m := uniformExpectation f
  calc
    uniformVariance f =
        uniformExpectation
          (fun ω => f ω * f ω - 2 * m * f ω + m * m) := by
      unfold uniformVariance
      apply congrArg uniformExpectation
      funext ω
      dsimp only [m]
      ring
    _ =
        uniformExpectation (fun ω => f ω * f ω) -
          uniformExpectation (fun ω => 2 * m * f ω) +
            uniformExpectation (fun _ω : SampleSpace M => m * m) := by
      rw [uniformExpectation_add, uniformExpectation_sub]
    _ =
        uniformExpectation (fun ω => f ω * f ω) -
          2 * m * uniformExpectation f + m * m := by
      rw [uniformExpectation_const_mul, uniformExpectation_const]
    _ =
        uniformExpectation (fun ω => f ω * f ω) -
          (uniformExpectation f) ^ 2 := by
      dsimp only [m]
      ring

/--
Factorial-moment form of the finite variance identity, valid for every
rational-valued random variable.
-/
theorem uniformVariance_eq_factorial_add_mean_sub_sq
    {M : ℕ} (f : SampleSpace M → ℚ) :
    uniformVariance f =
      uniformExpectation (fun ω => f ω * (f ω - 1)) +
        uniformExpectation f - (uniformExpectation f) ^ 2 := by
  rw [uniformVariance_eq_expectation_sq_sub_sq]
  have hsquare :
      uniformExpectation (fun ω => f ω * f ω) =
        uniformExpectation (fun ω => f ω * (f ω - 1)) +
          uniformExpectation f := by
    calc
      uniformExpectation (fun ω => f ω * f ω) =
          uniformExpectation
            (fun ω => f ω * (f ω - 1) + f ω) := by
        apply congrArg uniformExpectation
        funext ω
        ring
      _ = uniformExpectation (fun ω => f ω * (f ω - 1)) +
          uniformExpectation f :=
        uniformExpectation_add _ _
  rw [hsquare]

/-! ## The four exact pair populations -/

/-- Distinct pairs whose two run windows overlap strictly. -/
def overlappingPairs (N L : ℕ) : Finset (ℕ × ℕ) :=
  (dyadicBlock N).offDiag.filter
    (fun pair => Nat.dist pair.1 pair.2 < L)

/-- Off-diagonal pairs at exactly the touching distance. -/
def touchingOffDiagPairs (N L : ℕ) : Finset (ℕ × ℕ) :=
  (dyadicBlock N).offDiag.filter
    (fun pair => Nat.dist pair.1 pair.2 = L)

/-- Off-diagonal pairs beyond the touching distance. -/
def separatedOffDiagPairs (N L : ℕ) : Finset (ℕ × ℕ) :=
  (dyadicBlock N).offDiag.filter
    (fun pair => L < Nat.dist pair.1 pair.2)

@[simp]
theorem mem_overlappingPairs {N L : ℕ} {pair : ℕ × ℕ} :
    pair ∈ overlappingPairs N L ↔
      pair.1 ∈ dyadicBlock N ∧ pair.2 ∈ dyadicBlock N ∧
        pair.1 ≠ pair.2 ∧ Nat.dist pair.1 pair.2 < L := by
  simp [overlappingPairs, and_assoc]

@[simp]
theorem mem_touchingOffDiagPairs {N L : ℕ} {pair : ℕ × ℕ} :
    pair ∈ touchingOffDiagPairs N L ↔
      pair.1 ∈ dyadicBlock N ∧ pair.2 ∈ dyadicBlock N ∧
        pair.1 ≠ pair.2 ∧ Nat.dist pair.1 pair.2 = L := by
  simp [touchingOffDiagPairs, and_assoc]

@[simp]
theorem mem_separatedOffDiagPairs {N L : ℕ} {pair : ℕ × ℕ} :
    pair ∈ separatedOffDiagPairs N L ↔
      pair.1 ∈ dyadicBlock N ∧ pair.2 ∈ dyadicBlock N ∧
        pair.1 ≠ pair.2 ∧ L < Nat.dist pair.1 pair.2 := by
  simp [separatedOffDiagPairs, and_assoc]

/-- The local touching population agrees with the one used in Lemma 3.4. -/
theorem touchingOffDiagPairs_eq_touchingPairs
    (N L : ℕ) (hL : 0 < L) :
    touchingOffDiagPairs N L =
      TouchingPairs.touchingPairs N L := by
  ext pair
  rcases pair with ⟨x, y⟩
  simp only [mem_touchingOffDiagPairs, TouchingPairs.mem_touchingPairs]
  constructor
  · rintro ⟨hx, hy, _hne, hdist⟩
    exact ⟨hx, hy, hdist⟩
  · rintro ⟨hx, hy, hdist⟩
    refine ⟨hx, hy, ?_, hdist⟩
    intro heq
    subst y
    simp only [Nat.dist_self] at hdist
    omega

/-- The local separated population is the manuscript's literal population. -/
theorem separatedOffDiagPairs_eq_separatedDyadicPairs
    (N L : ℕ) :
    separatedOffDiagPairs N L =
      separatedDyadicPairs N L := by
  ext pair
  rcases pair with ⟨x, y⟩
  simp only [mem_separatedOffDiagPairs, mem_separatedDyadicPairs]
  constructor
  · rintro ⟨hx, hy, _hne, hdist⟩
    exact ⟨hx, hy, hdist⟩
  · rintro ⟨hx, hy, hdist⟩
    refine ⟨hx, hy, ?_, hdist⟩
    intro heq
    subst y
    simp only [Nat.dist_self] at hdist
    omega

/--
The three off-diagonal distance populations are an exact, disjoint
partition.  The union form makes all later finite sums independent of
informal case splits.
-/
theorem offDiag_eq_three_distance_populations
    (N L : ℕ) :
    (dyadicBlock N).offDiag =
      overlappingPairs N L ∪
        (touchingOffDiagPairs N L ∪ separatedOffDiagPairs N L) := by
  ext pair
  simp only [Finset.mem_offDiag, Finset.mem_union,
    mem_overlappingPairs, mem_touchingOffDiagPairs,
    mem_separatedOffDiagPairs]
  constructor
  · rintro ⟨hx, hy, hne⟩
    rcases lt_trichotomy (Nat.dist pair.1 pair.2) L with hlt | heq | hgt
    · exact Or.inl ⟨hx, hy, hne, hlt⟩
    · exact Or.inr (Or.inl ⟨hx, hy, hne, heq⟩)
    · exact Or.inr (Or.inr ⟨hx, hy, hne, hgt⟩)
  · rintro (hover | htouch | hsep)
    · exact ⟨hover.1, hover.2.1, hover.2.2.1⟩
    · exact ⟨htouch.1, htouch.2.1, htouch.2.2.1⟩
    · exact ⟨hsep.1, hsep.2.1, hsep.2.2.1⟩

theorem disjoint_overlapping_touching
    (N L : ℕ) :
    Disjoint (overlappingPairs N L) (touchingOffDiagPairs N L) := by
  rw [Finset.disjoint_left]
  intro pair hover htouch
  have ho := (mem_overlappingPairs.mp hover).2.2.2
  have ht := (mem_touchingOffDiagPairs.mp htouch).2.2.2
  omega

theorem disjoint_overlapping_separated
    (N L : ℕ) :
    Disjoint (overlappingPairs N L) (separatedOffDiagPairs N L) := by
  rw [Finset.disjoint_left]
  intro pair hover hsep
  have ho := (mem_overlappingPairs.mp hover).2.2.2
  have hs := (mem_separatedOffDiagPairs.mp hsep).2.2.2
  omega

theorem disjoint_touching_separated
    (N L : ℕ) :
    Disjoint (touchingOffDiagPairs N L)
      (separatedOffDiagPairs N L) := by
  rw [Finset.disjoint_left]
  intro pair htouch hsep
  have ht := (mem_touchingOffDiagPairs.mp htouch).2.2.2
  have hs := (mem_separatedOffDiagPairs.mp hsep).2.2.2
  omega

/-! ## The elementary `O(NL)` strict-overlap count -/

/-- Positive offsets strictly smaller than `L`. -/
def overlapOffsets (L : ℕ) : Finset ℕ :=
  Finset.Ico 1 L

/-- Forward-oriented candidates `(x,x+d)` for `0<d<L`. -/
def forwardOverlapCandidates (N L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ overlapOffsets L).image
    (fun z => (z.1, z.1 + z.2))

/-- Backward-oriented candidates `(x+d,x)` for `0<d<L`. -/
def backwardOverlapCandidates (N L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ overlapOffsets L).image
    (fun z => (z.1 + z.2, z.1))

/-- Every strictly overlapping ordered pair has one of the two orientations. -/
theorem overlappingPairs_subset_candidates
    (N L : ℕ) :
    overlappingPairs N L ⊆
      forwardOverlapCandidates N L ∪
        backwardOverlapCandidates N L := by
  intro pair hpair
  obtain ⟨hx, hy, hne, hdistLt⟩ :=
    mem_overlappingPairs.mp hpair
  let d := Nat.dist pair.1 pair.2
  have hdPos : 0 < d :=
    Nat.dist_pos_of_ne hne
  have hdMem : d ∈ overlapOffsets L := by
    simpa [overlapOffsets, d] using ⟨hdPos, hdistLt⟩
  rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq
      (L := d) (by rfl) with hforward | hbackward
  · apply Finset.mem_union_left
    rw [forwardOverlapCandidates, Finset.mem_image]
    exact ⟨(pair.1, d), by simp [hx, hdMem], by
      apply Prod.ext
      · rfl
      · exact hforward.symm⟩
  · apply Finset.mem_union_right
    rw [backwardOverlapCandidates, Finset.mem_image]
    exact ⟨(pair.2, d), by simp [hy, hdMem], by
      apply Prod.ext
      · exact hbackward.symm
      · rfl⟩

theorem card_overlapOffsets_le (L : ℕ) :
    (overlapOffsets L).card ≤ L := by
  simp [overlapOffsets]

theorem card_forwardOverlapCandidates_le
    (N L : ℕ) :
    (forwardOverlapCandidates N L).card ≤ N * L := by
  calc
    (forwardOverlapCandidates N L).card ≤
        ((dyadicBlock N) ×ˢ overlapOffsets L).card :=
      Finset.card_image_le
    _ = (dyadicBlock N).card * (overlapOffsets L).card := by
      rw [Finset.card_product]
    _ ≤ N * L := by
      rw [TouchingPairs.card_dyadicBlock]
      exact Nat.mul_le_mul_left N (card_overlapOffsets_le L)

theorem card_backwardOverlapCandidates_le
    (N L : ℕ) :
    (backwardOverlapCandidates N L).card ≤ N * L := by
  calc
    (backwardOverlapCandidates N L).card ≤
        ((dyadicBlock N) ×ˢ overlapOffsets L).card :=
      Finset.card_image_le
    _ = (dyadicBlock N).card * (overlapOffsets L).card := by
      rw [Finset.card_product]
    _ ≤ N * L := by
      rw [TouchingPairs.card_dyadicBlock]
      exact Nat.mul_le_mul_left N (card_overlapOffsets_le L)

/-- Literal `O(NL)` estimate used for the local-exclusion correction. -/
theorem card_overlappingPairs_le_two_mul
    (N L : ℕ) :
    (overlappingPairs N L).card ≤ 2 * N * L := by
  calc
    (overlappingPairs N L).card ≤
        (forwardOverlapCandidates N L ∪
          backwardOverlapCandidates N L).card :=
      Finset.card_le_card (overlappingPairs_subset_candidates N L)
    _ ≤ (forwardOverlapCandidates N L).card +
        (backwardOverlapCandidates N L).card :=
      Finset.card_union_le _ _
    _ ≤ N * L + N * L :=
      Nat.add_le_add
        (card_forwardOverlapCandidates_le N L)
        (card_backwardOverlapCandidates_le N L)
    _ = 2 * N * L := by ring

/-! ## Exact joint probabilities and finite moments -/

/-- Joint probability of two starts in the same canonical dyadic cylinder. -/
noncomputable def jointStartProbability
    (N L x y : ℕ) : ℚ := by
  classical
  exact uniformEventProbability (M := dyadicCutoff N L)
    (fun ω => startAt ω x L ∧ startAt ω y L)

/-- Joint mass carried by an arbitrary finite population of ordered pairs. -/
noncomputable def jointPairMass
    (N L : ℕ) (pairs : Finset (ℕ × ℕ)) : ℚ :=
  ∑ pair ∈ pairs,
    jointStartProbability N L pair.1 pair.2

/-- Exact second factorial moment of the dyadic start count. -/
noncomputable def dyadicSecondFactorialMoment
    (N L : ℕ) : ℚ :=
  uniformExpectation
    (fun ω : DyadicSample N L =>
      (dyadicCount N L ω : ℚ) *
        ((dyadicCount N L ω : ℚ) - 1))

/-- Exact finite variance of the dyadic start count. -/
noncomputable def dyadicVariance (N L : ℕ) : ℚ :=
  uniformVariance
    (fun ω : DyadicSample N L => (dyadicCount N L ω : ℚ))

/-- Pointwise factorial identity for the dyadic indicator count. -/
theorem dyadicCount_factorial_eq_sum_offDiag
    (N L : ℕ) (ω : DyadicSample N L) :
    (dyadicCount N L ω : ℚ) *
        ((dyadicCount N L ω : ℚ) - 1) =
      ∑ pair ∈ (dyadicBlock N).offDiag,
        if startAt ω pair.1 L ∧ startAt ω pair.2 L then
          (1 : ℚ)
        else 0 := by
  classical
  have hcount :
      (dyadicCount N L ω : ℚ) =
        ∑ x ∈ dyadicBlock N,
          if startAt ω x L then (1 : ℚ) else 0 := by
    simp [dyadicCount]
  rw [hcount]
  exact ratIndicator_factorialMoment
    (dyadicBlock N) (fun x => startAt ω x L)

/-- The exact factorial moment is the off-diagonal joint-probability sum. -/
theorem dyadicSecondFactorialMoment_eq_offDiag
    (N L : ℕ) :
    dyadicSecondFactorialMoment N L =
      jointPairMass N L (dyadicBlock N).offDiag := by
  classical
  unfold dyadicSecondFactorialMoment jointPairMass
  calc
    uniformExpectation
        (fun ω : DyadicSample N L =>
          (dyadicCount N L ω : ℚ) *
            ((dyadicCount N L ω : ℚ) - 1)) =
      uniformExpectation
        (fun ω : DyadicSample N L =>
          ∑ pair ∈ (dyadicBlock N).offDiag,
            if startAt ω pair.1 L ∧ startAt ω pair.2 L then
              (1 : ℚ)
            else 0) := by
      apply congrArg uniformExpectation
      funext ω
      exact dyadicCount_factorial_eq_sum_offDiag N L ω
    _ =
      ∑ pair ∈ (dyadicBlock N).offDiag,
        uniformExpectation
          (fun ω : DyadicSample N L =>
            if startAt ω pair.1 L ∧ startAt ω pair.2 L then
              (1 : ℚ)
            else 0) :=
      uniformExpectation_finset_sum _ _
    _ =
      ∑ pair ∈ (dyadicBlock N).offDiag,
        jointStartProbability N L pair.1 pair.2 := by
      apply Finset.sum_congr rfl
      intro pair _hpair
      exact uniformExpectation_indicator
        (fun ω : DyadicSample N L =>
          startAt ω pair.1 L ∧ startAt ω pair.2 L)

/-- Joint mass is additive over disjoint finite populations. -/
theorem jointPairMass_union
    {N L : ℕ} {s t : Finset (ℕ × ℕ)}
    (hdisj : Disjoint s t) :
    jointPairMass N L (s ∪ t) =
      jointPairMass N L s + jointPairMass N L t := by
  unfold jointPairMass
  rw [Finset.sum_union hdisj]

/--
Exact four-sector decomposition.  The diagonal is displayed as the
first-moment term removed by the factorial power; the remaining terms are
strict overlap, touching, and separated pairs.
-/
theorem dyadicSecondFactorialMoment_eq_overlap_touching_separated
    (N L : ℕ) :
    dyadicSecondFactorialMoment N L =
      jointPairMass N L (overlappingPairs N L) +
        jointPairMass N L (touchingOffDiagPairs N L) +
          jointPairMass N L (separatedOffDiagPairs N L) := by
  rw [dyadicSecondFactorialMoment_eq_offDiag,
    offDiag_eq_three_distance_populations]
  have hdisj :
      Disjoint (overlappingPairs N L)
        (touchingOffDiagPairs N L ∪ separatedOffDiagPairs N L) :=
    Finset.disjoint_union_right.mpr
      ⟨disjoint_overlapping_touching N L,
        disjoint_overlapping_separated N L⟩
  rw [jointPairMass_union hdisj]
  rw [jointPairMass_union (disjoint_touching_separated N L)]
  ring

/-- Strictly overlapping distinct starts have zero joint probability. -/
theorem jointStartProbability_eq_zero_of_overlap
    {N L x y : ℕ} (hxy : x ≠ y)
    (hdist : Nat.dist x y < L) :
    jointStartProbability N L x y = 0 := by
  classical
  unfold jointStartProbability uniformEventProbability
  have hempty :
      Finset.univ.filter
          (fun ω : DyadicSample N L =>
            startAt ω x L ∧ startAt ω y L) =
        ∅ := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    exact startEvents_disjoint_of_dist_lt hxy hdist
  rw [hempty]
  simp

/-- The full strict-overlap contribution vanishes exactly. -/
theorem jointPairMass_overlappingPairs_eq_zero
    (N L : ℕ) :
    jointPairMass N L (overlappingPairs N L) = 0 := by
  classical
  unfold jointPairMass
  apply Finset.sum_eq_zero
  intro pair hpair
  exact jointStartProbability_eq_zero_of_overlap
    (mem_overlappingPairs.mp hpair).2.2.1
    (mem_overlappingPairs.mp hpair).2.2.2

/-! ## Affine normalization of the two surviving populations -/

/--
Generic `η 2^ρ / 2^m` form of the uniform probability of a finite affine
system with `m` binary equations.
-/
theorem uniformSolutionProbability_eq_eta_mul_two_pow_rho_div
    {V β : Type*}
    [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]
    [Fintype β] [DecidableEq β]
    (A : V →ₗ[F₂] (β → F₂)) (b : β → F₂) :
    uniformSolutionProbability A b =
      ((relationEta A b : ℚ) *
          (2 : ℚ) ^ relationRho A) /
        (2 : ℚ) ^ Fintype.card β := by
  classical
  unfold uniformSolutionProbability
  rw [Fintype.card_subtype]
  have hnormalized :=
    affineFiber_normalized_card_identity A b
  have hnormalizedQ :
      (2 : ℚ) ^ Fintype.card β *
          ((Finset.univ.filter fun x : V => A x = b).card : ℚ) =
        (Fintype.card V : ℚ) *
          ((relationEta A b : ℚ) *
            (2 : ℚ) ^ relationRho A) := by
    exact_mod_cast hnormalized
  have hcard :
      (Fintype.card V : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card V ≠ 0)
  have hpow :
      (2 : ℚ) ^ Fintype.card β ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  apply (div_eq_div_iff hcard hpow).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using hnormalizedQ

/-- The joint start event is exactly the affine two-start solution fiber. -/
theorem jointStartProbability_eq_uniformSolutionProbability
    (N L x y : ℕ) (hL : 0 < L) :
    jointStartProbability N L x y =
      uniformSolutionProbability
        (twoStartSystem (dyadicCutoff N L) x y L)
        (twoStartRhs L) := by
  classical
  unfold jointStartProbability uniformEventProbability
    uniformSolutionProbability
  congr 1
  rw [Fintype.card_subtype]
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (twoStartSystem_eq_twoStartRhs_iff ω hL).symm

/-- Exact affine normalization of any ordered pair of starts. -/
theorem jointStartProbability_eq_eta_mul_two_pow_rho_div
    (N L x y : ℕ) (hL : 0 < L) :
    jointStartProbability N L x y =
      ((relationEta
          (twoStartSystem (dyadicCutoff N L) x y L)
          (twoStartRhs L) : ℚ) *
        (2 : ℚ) ^
          relationRho
            (twoStartSystem (dyadicCutoff N L) x y L)) /
        (2 : ℚ) ^ (2 * L) := by
  rw [jointStartProbability_eq_uniformSolutionProbability
    N L x y hL,
    uniformSolutionProbability_eq_eta_mul_two_pow_rho_div]
  congr 1
  simp [Fintype.card_sum, two_mul]

/-- Relation defect of the canonical two-start system for an ordered pair. -/
noncomputable def jointRho
    (N L : ℕ) (pair : ℕ × ℕ) : ℕ :=
  relationRho
    (twoStartSystem
      (dyadicCutoff N L) pair.1 pair.2 L)

/-- Natural affine defect weight `2^ρ-1` for an ordered pair. -/
noncomputable def jointDefectWeight
    (N L : ℕ) (pair : ℕ × ℕ) : ℕ :=
  2 ^ jointRho N L pair - 1

/-- Sum of affine defect weights over a finite ordered-pair population. -/
noncomputable def jointDefectMass
    (N L : ℕ) (pairs : Finset (ℕ × ℕ)) : ℕ :=
  ∑ pair ∈ pairs, jointDefectWeight N L pair

/--
Pointwise form of (2.1): the deviation of one joint probability from the
independent baseline is at most `(2^ρ-1)/2^(2L)`.
-/
theorem abs_jointStartProbability_sub_baseline_le
    (N L x y : ℕ) (hL : 0 < L) :
    |jointStartProbability N L x y -
        (1 : ℚ) / (2 : ℚ) ^ (2 * L)| ≤
      (jointDefectWeight N L (x, y) : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  rw [jointStartProbability_eq_eta_mul_two_pow_rho_div
    N L x y hL]
  let A := twoStartSystem (dyadicCutoff N L) x y L
  let b := twoStartRhs L
  have habsZ :=
    abs_eta_mul_two_pow_rho_sub_one_le A b
  have habsQ :
      |(relationEta A b : ℚ) *
          (2 : ℚ) ^ relationRho A - 1| ≤
        (2 : ℚ) ^ relationRho A - 1 := by
    exact_mod_cast habsZ
  have hdenom :
      0 < (2 : ℚ) ^ (2 * L) :=
    pow_pos (by norm_num) (2 * L)
  have hnat :
      ((2 ^ relationRho A - 1 : ℕ) : ℚ) =
        (2 : ℚ) ^ relationRho A - 1 := by
    rw [Nat.cast_sub]
    · norm_num
    · exact Nat.one_le_two_pow
  dsimp only [A, b] at habsQ hnat ⊢
  rw [← sub_div, abs_div, abs_of_pos hdenom]
  rw [jointDefectWeight, jointRho, hnat]
  exact div_le_div_of_nonneg_right habsQ hdenom.le

/--
Summed finite form of (2.1) on an arbitrary pair population.
-/
theorem abs_jointPairMass_sub_baseline_le
    (N L : ℕ) (hL : 0 < L)
    (pairs : Finset (ℕ × ℕ)) :
    |jointPairMass N L pairs -
        (pairs.card : ℚ) / (2 : ℚ) ^ (2 * L)| ≤
      (jointDefectMass N L pairs : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  classical
  have hbaseline :
      (pairs.card : ℚ) / (2 : ℚ) ^ (2 * L) =
        ∑ _pair ∈ pairs,
          (1 : ℚ) / (2 : ℚ) ^ (2 * L) := by
    simp [div_eq_mul_inv]
  rw [jointPairMass, hbaseline, ← Finset.sum_sub_distrib]
  calc
    |∑ pair ∈ pairs,
          (jointStartProbability N L pair.1 pair.2 -
            (1 : ℚ) / (2 : ℚ) ^ (2 * L))| ≤
        ∑ pair ∈ pairs,
          |jointStartProbability N L pair.1 pair.2 -
            (1 : ℚ) / (2 : ℚ) ^ (2 * L)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ pair ∈ pairs,
          (jointDefectWeight N L pair : ℚ) /
            (2 : ℚ) ^ (2 * L) := by
      exact Finset.sum_le_sum fun pair hpair =>
        abs_jointStartProbability_sub_baseline_le
          N L pair.1 pair.2 hL
    _ =
        (jointDefectMass N L pairs : ℚ) /
          (2 : ℚ) ^ (2 * L) := by
      rw [jointDefectMass, Nat.cast_sum, Finset.sum_div]

/-! ## Alignment with the touching-mass module -/

/-- Every complete vertex label is positive when both starts are at least two. -/
theorem twoStartCompleteVertexLabel_pos
    {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (v : Sum (Fin (L + 1)) (Fin (L + 1))) :
    0 < twoStartCompleteVertexLabel x y L v := by
  cases v with
  | inl v =>
      simp only [twoStartCompleteVertexLabel]
      unfold startCompleteVertexLabel
      split <;> omega
  | inr v =>
      simp only [twoStartCompleteVertexLabel]
      unfold startCompleteVertexLabel
      split <;> omega

/-- The canonical dyadic cutoff contains every complete label of two starts. -/
theorem twoStartCompleteVertexLabel_le_dyadicCutoff
    {N L x y : ℕ}
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N)
    (v : Sum (Fin (L + 1)) (Fin (L + 1))) :
    twoStartCompleteVertexLabel x y L v ≤ dyadicCutoff N L := by
  have hxBounds :=
    Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)
  have hyBounds :=
    Finset.mem_Ico.mp (by simpa [dyadicBlock] using hy)
  unfold dyadicCutoff
  cases v with
  | inl v =>
      simp only [twoStartCompleteVertexLabel]
      unfold startCompleteVertexLabel
      split <;> omega
  | inr v =>
      simp only [twoStartCompleteVertexLabel]
      unfold startCompleteVertexLabel
      split <;> omega

/--
Once a prime cylinder contains every complete boundary label, enlarging its
cutoff does not change the relation space of a two-start system.
-/
theorem relationRho_twoStartSystem_cutoff_invariant
    {M M' x y L : ℕ}
    (hMM' : M ≤ M') (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hlabel :
      ∀ v : Sum (Fin (L + 1)) (Fin (L + 1)),
        twoStartCompleteVertexLabel x y L v ≤ M) :
    relationRho (twoStartSystem M x y L) =
      relationRho (twoStartSystem M' x y L) := by
  classical
  have hmem :
      ∀ u : Sum (Fin L) (Fin L) → F₂,
        u ∈ RelationSpace (twoStartSystem M x y L) ↔
          u ∈ RelationSpace (twoStartSystem M' x y L) := by
    intro u
    rw [mem_relationSpace_twoStartSystem_iff_boundary_prime_equations,
      mem_relationSpace_twoStartSystem_iff_boundary_prime_equations]
    constructor
    · intro hsmall p
      by_cases hpM : p.1.1 ≤ M
      · let q : PrimeUpTo M :=
          ⟨⟨p.1.1, Nat.lt_succ_of_le hpM⟩, p.2⟩
        exact hsmall q
      · apply Finset.sum_eq_zero
        intro v _hv
        have hparity :
            parityVec (twoStartCompleteVertexLabel x y L v) p.1 = 0 := by
          by_contra hne
          have hdvd :=
            RelationalPrimeAssignment.dvd_of_parityVec_ne_zero hne
          have hpLe :
              p.1.1 ≤ twoStartCompleteVertexLabel x y L v :=
            Nat.le_of_dvd
              (twoStartCompleteVertexLabel_pos hx hy v) hdvd
          exact hpM (hpLe.trans (hlabel v))
        rw [hparity, mul_zero]
    · intro hlarge p
      let q : PrimeUpTo M' :=
        ⟨⟨p.1.1, Nat.lt_succ_of_le
          ((Nat.le_of_lt_succ p.1.2).trans hMM')⟩, p.2⟩
      exact hlarge q
  let e :
      RelationSpace (twoStartSystem M x y L) ≃ₗ[F₂]
        RelationSpace (twoStartSystem M' x y L) := {
    toFun u := ⟨u.1, (hmem u.1).mp u.2⟩
    invFun u := ⟨u.1, (hmem u.1).mpr u.2⟩
    left_inv u := by
      apply Subtype.ext
      rfl
    right_inv u := by
      apply Subtype.ext
      rfl
    map_add' u v := by
      apply Subtype.ext
      rfl
    map_smul' c u := by
      apply Subtype.ext
      rfl
  }
  unfold relationRho
  exact LinearEquiv.finrank_eq e

/-- The two presentations of the canonically oriented touching system agree. -/
theorem touchingSystem_eq_twoStartSystem
    (M x L : ℕ) :
    touchingSystem M x L =
      twoStartSystem M x (x + L) L := by
  rfl

/-- The upper endpoint of a touching pair is `lower+L` and remains in `I_N`. -/
theorem touchingLower_add_mem_dyadicBlock
    {N L : ℕ} {pair : ℕ × ℕ}
    (hpair : pair ∈ TouchingPairs.touchingPairs N L) :
    TouchingMass.touchingLower pair + L ∈ dyadicBlock N := by
  obtain ⟨hx, hy, hdist⟩ :=
    TouchingPairs.mem_touchingPairs.mp hpair
  rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq hdist with
    hforward | hbackward
  · have hle : pair.1 ≤ pair.2 := by omega
    simpa [TouchingMass.touchingLower, min_eq_left hle,
      hforward] using hy
  · have hle : pair.2 ≤ pair.1 := by omega
    simpa [TouchingMass.touchingLower, min_eq_right hle,
      hbackward] using hx

/--
The relation defect used by the exact dyadic factorial moment agrees with
the larger-cutoff touching defect from Lemma 3.4.
-/
theorem touching_relationRho_small_eq_large
    {N L : ℕ} {pair : ℕ × ℕ}
    (hN : 2 ≤ N)
    (hpair : pair ∈ TouchingPairs.touchingPairs N L) :
    relationRho
        (touchingSystem (dyadicCutoff N L)
          (TouchingMass.touchingLower pair) L) =
      TouchingMass.touchingRho N L pair := by
  have hlowerMem :=
    TouchingMass.touchingLower_mem_dyadicBlock hpair
  have hupperMem :=
    touchingLower_add_mem_dyadicBlock hpair
  have hlower :
      2 ≤ TouchingMass.touchingLower pair :=
    two_le_of_mem_dyadicBlock hN hlowerMem
  have hupper :
      2 ≤ TouchingMass.touchingLower pair + L :=
    two_le_of_mem_dyadicBlock hN hupperMem
  rw [TouchingMass.touchingRho,
    touchingSystem_eq_twoStartSystem,
    touchingSystem_eq_twoStartSystem]
  apply relationRho_twoStartSystem_cutoff_invariant
  · unfold dyadicCutoff
    omega
  · exact hlower
  · exact hupper
  · intro v
    exact twoStartCompleteVertexLabel_le_dyadicCutoff
      hlowerMem hupperMem v

/-- Joint start probability is symmetric in its two start positions. -/
theorem jointStartProbability_comm
    (N L x y : ℕ) :
    jointStartProbability N L x y =
      jointStartProbability N L y x := by
  classical
  unfold jointStartProbability uniformEventProbability
  have hfilter :
      Finset.univ.filter
          (fun ω : DyadicSample N L =>
            startAt ω x L ∧ startAt ω y L) =
        Finset.univ.filter
          (fun ω : DyadicSample N L =>
            startAt ω y L ∧ startAt ω x L) := by
    ext ω
    simp [and_comm]
  rw [hfilter]

/-- Every touching joint event can be oriented by its lower endpoint. -/
theorem jointStartProbability_eq_touchingLower
    {N L : ℕ} {pair : ℕ × ℕ}
    (hpair : pair ∈ TouchingPairs.touchingPairs N L) :
    jointStartProbability N L pair.1 pair.2 =
      jointStartProbability N L
        (TouchingMass.touchingLower pair)
        (TouchingMass.touchingLower pair + L) := by
  have hdist :=
    (TouchingPairs.mem_touchingPairs.mp hpair).2.2
  rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq hdist with
    hforward | hbackward
  · have hle : pair.1 ≤ pair.2 := by omega
    simp only [TouchingMass.touchingLower, min_eq_left hle]
    rw [hforward]
  · have hle : pair.2 ≤ pair.1 := by omega
    simp only [TouchingMass.touchingLower, min_eq_right hle]
    rw [hbackward, jointStartProbability_comm]

/--
Pointwise touching deviation, now expressed with the exact weight already
summed by `TouchingMass.touchingMass`.
-/
theorem abs_jointStartProbability_touching_sub_baseline_le
    {N L : ℕ} {pair : ℕ × ℕ}
    (hN : 2 ≤ N) (hL : 0 < L)
    (hpair : pair ∈ TouchingPairs.touchingPairs N L) :
    |jointStartProbability N L pair.1 pair.2 -
        (1 : ℚ) / (2 : ℚ) ^ (2 * L)| ≤
      (TouchingMass.touchingWeight N L pair : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  rw [jointStartProbability_eq_touchingLower hpair]
  have hbound :=
    abs_jointStartProbability_sub_baseline_le
      N L (TouchingMass.touchingLower pair)
        (TouchingMass.touchingLower pair + L) hL
  have hrho :
      relationRho
          (twoStartSystem (dyadicCutoff N L)
            (TouchingMass.touchingLower pair)
            (TouchingMass.touchingLower pair + L) L) =
        TouchingMass.touchingRho N L pair := by
    rw [← touchingSystem_eq_twoStartSystem]
    exact touching_relationRho_small_eq_large hN hpair
  simpa only [jointDefectWeight, jointRho,
    TouchingMass.touchingWeight, hrho] using hbound

/-- Summed touching deviation controlled by the established touching mass. -/
theorem abs_touchingPairMass_sub_baseline_le
    {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    |jointPairMass N L (touchingOffDiagPairs N L) -
        ((touchingOffDiagPairs N L).card : ℚ) /
          (2 : ℚ) ^ (2 * L)| ≤
      (TouchingMass.touchingMass N L : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  classical
  rw [touchingOffDiagPairs_eq_touchingPairs N L hL]
  have hbaseline :
      ((TouchingPairs.touchingPairs N L).card : ℚ) /
          (2 : ℚ) ^ (2 * L) =
        ∑ _pair ∈ TouchingPairs.touchingPairs N L,
          (1 : ℚ) / (2 : ℚ) ^ (2 * L) := by
    simp [div_eq_mul_inv]
  rw [jointPairMass, hbaseline, ← Finset.sum_sub_distrib]
  calc
    |∑ pair ∈ TouchingPairs.touchingPairs N L,
          (jointStartProbability N L pair.1 pair.2 -
            (1 : ℚ) / (2 : ℚ) ^ (2 * L))| ≤
        ∑ pair ∈ TouchingPairs.touchingPairs N L,
          |jointStartProbability N L pair.1 pair.2 -
            (1 : ℚ) / (2 : ℚ) ^ (2 * L)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ pair ∈ TouchingPairs.touchingPairs N L,
          (TouchingMass.touchingWeight N L pair : ℚ) /
            (2 : ℚ) ^ (2 * L) := by
      exact Finset.sum_le_sum fun pair hpair =>
        abs_jointStartProbability_touching_sub_baseline_le
          hN hL hpair
    _ =
        (TouchingMass.touchingMass N L : ℚ) /
          (2 : ℚ) ^ (2 * L) := by
      rw [TouchingMass.touchingMass, Nat.cast_sum, Finset.sum_div]

/-- Reduced exact Section 12 decomposition after local exclusion. -/
theorem dyadicSecondFactorialMoment_eq_touching_add_separated
    (N L : ℕ) :
    dyadicSecondFactorialMoment N L =
      jointPairMass N L (touchingOffDiagPairs N L) +
        jointPairMass N L (separatedOffDiagPairs N L) := by
  rw [dyadicSecondFactorialMoment_eq_overlap_touching_separated,
    jointPairMass_overlappingPairs_eq_zero]
  ring

/-! ## Complete finite error estimate -/

/-- Cardinal form of the exact three-sector off-diagonal partition. -/
theorem card_offDiag_eq_overlap_add_touching_add_separated
    (N L : ℕ) :
    ((dyadicBlock N).offDiag).card =
      (overlappingPairs N L).card +
        (touchingOffDiagPairs N L).card +
          (separatedOffDiagPairs N L).card := by
  rw [offDiag_eq_three_distance_populations]
  rw [Finset.card_union_of_disjoint
    (Finset.disjoint_union_right.mpr
      ⟨disjoint_overlapping_touching N L,
        disjoint_overlapping_separated N L⟩)]
  rw [Finset.card_union_of_disjoint
    (disjoint_touching_separated N L)]
  omega

/-- Independent off-diagonal baseline `(N)_2 2^(-2L)`. -/
noncomputable def factorialBaseline (N L : ℕ) : ℚ :=
  (((dyadicBlock N).offDiag).card : ℚ) /
    (2 : ℚ) ^ (2 * L)

/-- The baseline has the manuscript's literal falling-factorial numerator. -/
theorem factorialBaseline_eq
    (N L : ℕ) :
    factorialBaseline N L =
      (N * (N - 1) : ℕ) / (2 : ℚ) ^ (2 * L) := by
  unfold factorialBaseline
  rw [Finset.offDiag_card, TouchingPairs.card_dyadicBlock]
  have hnat : N * N - N = N * (N - 1) := by
    rw [Nat.mul_sub_left_distrib]
    simp
  rw [hnat]

/--
Finite quantitative core of Section 12.  The factorial-moment error is
bounded by the number of forbidden overlaps plus the touching and separated
affine defect masses.
-/
theorem abs_dyadicSecondFactorialMoment_sub_baseline_le
    {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    |dyadicSecondFactorialMoment N L - factorialBaseline N L| ≤
      (((overlappingPairs N L).card +
          TouchingMass.touchingMass N L +
          jointDefectMass N L (separatedOffDiagPairs N L) : ℕ) : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  let d : ℚ := (2 : ℚ) ^ (2 * L)
  let overlapBase : ℚ := ((overlappingPairs N L).card : ℚ) / d
  let touchingBase : ℚ :=
    ((touchingOffDiagPairs N L).card : ℚ) / d
  let separatedBase : ℚ :=
    ((separatedOffDiagPairs N L).card : ℚ) / d
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  have hbaseline :
      factorialBaseline N L =
        overlapBase + touchingBase + separatedBase := by
    unfold factorialBaseline overlapBase touchingBase separatedBase
    rw [card_offDiag_eq_overlap_add_touching_add_separated]
    push_cast
    ring
  have htouch :=
    abs_touchingPairMass_sub_baseline_le hN hL
  have hsep :=
    abs_jointPairMass_sub_baseline_le
      N L hL (separatedOffDiagPairs N L)
  rw [dyadicSecondFactorialMoment_eq_touching_add_separated,
    hbaseline]
  change
    |jointPairMass N L (touchingOffDiagPairs N L) +
        jointPairMass N L (separatedOffDiagPairs N L) -
          (overlapBase + touchingBase + separatedBase)| ≤ _
  have hrearrange :
      jointPairMass N L (touchingOffDiagPairs N L) +
            jointPairMass N L (separatedOffDiagPairs N L) -
          (overlapBase + touchingBase + separatedBase) =
        -overlapBase +
          (jointPairMass N L (touchingOffDiagPairs N L) -
            touchingBase) +
          (jointPairMass N L (separatedOffDiagPairs N L) -
            separatedBase) := by
    ring
  rw [hrearrange]
  calc
    |-overlapBase +
          (jointPairMass N L (touchingOffDiagPairs N L) -
            touchingBase) +
          (jointPairMass N L (separatedOffDiagPairs N L) -
            separatedBase)| ≤
        |-overlapBase| +
          |jointPairMass N L (touchingOffDiagPairs N L) -
            touchingBase| +
          |jointPairMass N L (separatedOffDiagPairs N L) -
            separatedBase| := by
      let a : ℚ := -overlapBase
      let b : ℚ :=
        jointPairMass N L (touchingOffDiagPairs N L) - touchingBase
      let c : ℚ :=
        jointPairMass N L (separatedOffDiagPairs N L) - separatedBase
      change |a + b + c| ≤ |a| + |b| + |c|
      calc
        |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
        _ ≤ (|a| + |b|) + |c| :=
          add_le_add_left (abs_add_le _ _) _
    _ ≤
        ((overlappingPairs N L).card : ℚ) / d +
          (TouchingMass.touchingMass N L : ℚ) / d +
          (jointDefectMass N L
            (separatedOffDiagPairs N L) : ℚ) / d := by
      have hoverlap :
          |-overlapBase| =
            ((overlappingPairs N L).card : ℚ) / d := by
        rw [abs_neg,
          abs_of_nonneg (div_nonneg (by positivity) hd.le)]
      rw [hoverlap]
      exact add_le_add
        (add_le_add_right
          (by
            simpa only [touchingBase, d] using htouch)
          (((overlappingPairs N L).card : ℚ) / d))
        (by
          simpa only [separatedBase, d] using hsep)
    _ =
        (((overlappingPairs N L).card +
            TouchingMass.touchingMass N L +
            jointDefectMass N L
              (separatedOffDiagPairs N L) : ℕ) : ℚ) /
          (2 : ℚ) ^ (2 * L) := by
      dsimp only [d]
      push_cast
      ring

/-! ## Diagonal and variance -/

/-- Repeating one event in a conjunction does not change its probability. -/
theorem jointStartProbability_self
    (N L x : ℕ) :
    jointStartProbability N L x x = startProbability N L x := by
  classical
  unfold jointStartProbability startProbability
  unfold uniformEventProbability
  have hfilter :
      Finset.univ.filter
          (fun ω : DyadicSample N L =>
            startAt ω x L ∧ startAt ω x L) =
        Finset.univ.filter
          (fun ω : DyadicSample N L => startAt ω x L) := by
    ext ω
    simp
  rw [hfilter]

/-- The diagonal joint mass is exactly the first moment. -/
theorem jointPairMass_diag_eq_dyadicExpectation
    (N L : ℕ) :
    jointPairMass N L (dyadicBlock N).diag =
      dyadicExpectation N L := by
  unfold jointPairMass dyadicExpectation
  rw [Finset.sum_diag]
  apply Finset.sum_congr rfl
  intro x _hx
  exact jointStartProbability_self N L x

/--
The raw second moment is the sum of the diagonal and the three
off-diagonal distance sectors.
-/
theorem uniformExpectation_dyadicCount_sq_eq_four_sectors
    (N L : ℕ) :
    uniformExpectation
        (fun ω : DyadicSample N L =>
          (dyadicCount N L ω : ℚ) ^ 2) =
      dyadicExpectation N L +
        jointPairMass N L (overlappingPairs N L) +
          jointPairMass N L (touchingOffDiagPairs N L) +
            jointPairMass N L (separatedOffDiagPairs N L) := by
  have hpoint :
      (fun ω : DyadicSample N L =>
          (dyadicCount N L ω : ℚ) ^ 2) =
        (fun ω =>
          (dyadicCount N L ω : ℚ) *
              ((dyadicCount N L ω : ℚ) - 1) +
            (dyadicCount N L ω : ℚ)) := by
    funext ω
    ring
  rw [hpoint, uniformExpectation_add,
    ← dyadicSecondFactorialMoment,
    uniformExpectation_dyadicCount,
    dyadicSecondFactorialMoment_eq_overlap_touching_separated]
  ring

/-- Exact variance formula used at the end of the proof of Theorem 1.4. -/
theorem dyadicVariance_eq_factorial_add_expectation_sub_sq
    (N L : ℕ) :
    dyadicVariance N L =
      dyadicSecondFactorialMoment N L +
        dyadicExpectation N L - (dyadicExpectation N L) ^ 2 := by
  unfold dyadicVariance dyadicSecondFactorialMoment
  rw [uniformVariance_eq_factorial_add_mean_sub_sq,
    uniformExpectation_dyadicCount]

/-! ## Conditional asymptotic closure of Theorem 1.4 -/

/-- The separated defect sum is literally Proposition 11.2's finite mass. -/
theorem jointDefectMass_separated_eq_homogeneousMassNat
    {N L : ℕ} (hN : 2 ≤ N) :
    jointDefectMass N L (separatedOffDiagPairs N L) =
      PropositionElevenTwo.homogeneousMassNat (L := L) hN := by
  classical
  rw [separatedOffDiagPairs_eq_separatedDyadicPairs]
  unfold jointDefectMass jointDefectWeight jointRho
    PropositionElevenTwo.homogeneousMassNat
    PropositionElevenTwo.homogeneousWeight
    ResidualMasses.pairRho
  exact
    (Finset.sum_subtype
      (separatedDyadicPairs N L) (fun _pair => Iff.rfl)
      (fun pair =>
        2 ^ relationRho
          (twoStartSystem (dyadicCutoff N L)
            pair.1 pair.2 L) - 1))

/-- Real, proof-independent form of the same identification. -/
theorem jointDefectMass_separated_cast_eq_homogeneousMass
    {A N L : ℕ} (hN : 2 ≤ N) :
    (jointDefectMass N L (separatedOffDiagPairs N L) : ℝ) =
      PropositionElevenTwo.homogeneousMass A N L := by
  rw [PropositionElevenTwo.homogeneousMass, dif_pos hN]
  exact_mod_cast jointDefectMass_separated_eq_homogeneousMassNat hN

/--
An `N^(1+o(1))` bound is little-oh of `N²` in the repository's quantified
reciprocal-power conventions.
-/
theorem uniformLittleOQuadratic_of_uniformLinear
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hf : UniformLinearSubpolynomialOn admissible f) :
    UniformLittleOOn admissible f
      (fun N _ => (N : ℝ) ^ 2) := by
  have hrat :
      UniformRationalPowerSubpolynomialOn 1 1 admissible f := by
    intro k hk
    simpa using hf k hk
  exact
    UniformRationalPower.littleO_natPower_of_lt
      (p := 1) (q := 1) (r := 2) (by omega) hrat

/-- The `O(NL)` overlap population is `N^(1+o_C(1))`. -/
theorem overlappingPairs_uniformLinearSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLinearSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L => ((overlappingPairs N L).card : ℝ)) := by
  have hlength :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial hC
  have hfactor :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun _ L => (2 : ℝ) * ((L + 1 : ℕ) : ℝ)) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul 2 hlength
  apply UniformLinear.of_linear_mul_subpolynomial hfactor
  refine ⟨0, ?_⟩
  intro N _hN L _hwindow
  have hcardNat := card_overlappingPairs_le_two_mul N L
  have hcard :
      ((overlappingPairs N L).card : ℝ) ≤
        (2 * N * L : ℕ) := by
    exact_mod_cast hcardNat
  have hnonneg :
      0 ≤ ((overlappingPairs N L).card : ℝ) := by
    positivity
  have hfactorNonneg :
      0 ≤ (2 : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    positivity
  rw [abs_of_nonneg hnonneg, abs_of_nonneg hfactorNonneg]
  calc
    ((overlappingPairs N L).card : ℝ) ≤
        (2 * N * L : ℕ) := hcard
    _ ≤ (N : ℝ) * (2 * ((L + 1 : ℕ) : ℝ)) := by
      push_cast
      nlinarith

/-- The strict-overlap correction is uniformly little-oh of `N²`. -/
theorem overlappingPairs_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L => ((overlappingPairs N L).card : ℝ))
      (fun N _ => (N : ℝ) ^ 2) :=
  uniformLittleOQuadratic_of_uniformLinear
    (overlappingPairs_uniformLinearSubpolynomial hC)

/-- The already proved touching mass is uniformly little-oh of `N²`. -/
theorem touchingMass_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L => (TouchingMass.touchingMass N L : ℝ))
      (fun N _ => (N : ℝ) ^ 2) :=
  uniformLittleOQuadratic_of_uniformLinear
    (CriticalTouchingPairs.touchingMass_uniformLinearSubpolynomial hC)

/-- Proposition 11.2 transports to the exact separated defect mass of §12. -/
private theorem separatedDefectMass_uniformLittleOQuadratic
    {C : ℝ} {A : ℕ}
    (h11 :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass A)
        (fun N _ => (N : ℝ) ^ 2)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (jointDefectMass N L
          (separatedOffDiagPairs N L) : ℝ))
      (fun N _ => (N : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨N11, hN11⟩ := h11 ε hε
  refine ⟨max 2 N11, ?_⟩
  intro N hN L hwindow
  have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
  change
    |(jointDefectMass N L
        (separatedOffDiagPairs N L) : ℝ)| ≤
      ε * |(N : ℝ) ^ 2|
  rw [jointDefectMass_separated_cast_eq_homogeneousMass
    (A := A) hNtwo]
  exact hN11 N ((le_max_right _ _).trans hN) L hwindow

/-- Real numerator in the complete finite error estimate. -/
noncomputable def factorialErrorNumerator
    (N L : ℕ) : ℝ :=
  ((overlappingPairs N L).card : ℝ) +
    (TouchingMass.touchingMass N L : ℝ) +
    (jointDefectMass N L (separatedOffDiagPairs N L) : ℝ)

/-- All three finite error sources together are `o_C(N²)`. -/
private theorem factorialErrorNumerator_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) {A : ℕ}
    (h11 :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass A)
        (fun N _ => (N : ℝ) ^ 2)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      factorialErrorNumerator
      (fun N _ => (N : ℝ) ^ 2) := by
  have hoverlap := overlappingPairs_uniformLittleOQuadratic hC
  have htouch := touchingMass_uniformLittleOQuadratic hC
  have hsep :=
    separatedDefectMass_uniformLittleOQuadratic h11
  have hfirst :=
    PropositionElevenTwo.uniformLittleOOn_add hoverlap htouch
  have hall :=
    PropositionElevenTwo.uniformLittleOOn_add hfirst hsep
  change
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ((overlappingPairs N L).card : ℝ) +
          (TouchingMass.touchingMass N L : ℝ) +
          (jointDefectMass N L
            (separatedOffDiagPairs N L) : ℝ))
      (fun N _ => (N : ℝ) ^ 2)
  simpa only [add_assoc] using hall

/-- Real error of the second factorial moment from its exact baseline. -/
noncomputable def factorialMomentError (N L : ℕ) : ℝ :=
  (dyadicSecondFactorialMoment N L : ℝ) -
    (factorialBaseline N L : ℝ)

/-- Real cast of the complete finite error estimate. -/
theorem abs_factorialMomentError_le
    {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    |factorialMomentError N L| ≤
      factorialErrorNumerator N L /
        (2 : ℝ) ^ (2 * L) := by
  have hq :=
    abs_dyadicSecondFactorialMoment_sub_baseline_le hN hL
  calc
    |factorialMomentError N L| =
        ((|dyadicSecondFactorialMoment N L -
          factorialBaseline N L| : ℚ) : ℝ) := by
      simp only [factorialMomentError, Rat.cast_abs, Rat.cast_sub]
    _ ≤
        (((((overlappingPairs N L).card +
              TouchingMass.touchingMass N L +
              jointDefectMass N L
                (separatedOffDiagPairs N L) : ℕ) : ℚ) /
            (2 : ℚ) ^ (2 * L) : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).2 hq
    _ =
        factorialErrorNumerator N L /
          (2 : ℝ) ^ (2 * L) := by
      simp only [Rat.cast_div, Rat.cast_natCast, map_pow,
        Rat.cast_ofNat, factorialErrorNumerator]
      norm_num

/--
Conditional second-factorial-moment conclusion of Theorem 1.4:

`E[(Z_{N,L})₂] - (N)₂ 2^(-2L) = o_C(1)`.

The private assembly lemma consumes the conclusion of Proposition 11.2.
-/
private theorem factorialMomentError_uniformLittleOOne_of_propositionElevenTwo
    {C : ℝ} (hC : 0 ≤ C) {A : ℕ}
    (h11 :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass A)
        (fun N _ => (N : ℝ) ^ 2)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      factorialMomentError
      (fun _ _ => 1) := by
  have hnum :=
    factorialErrorNumerator_uniformLittleOQuadratic hC h11
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let B := CriticalRunWindow.balanceConstant C
  have hBpos : 0 < B := by
    unfold B CriticalRunWindow.balanceConstant
    positivity
  intro ε hε
  let δ : ℝ := ε / B ^ 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  obtain ⟨Nnum, hNnum⟩ := hnum δ hδ
  refine ⟨max 2 (max Nwindow Nnum), ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail : max Nwindow Nnum ≤ N :=
    (le_max_right _ _).trans hN
  have hwin :=
    hNwindow N ((le_max_left _ _).trans hNtail) L hrun
  have hLpos : 0 < L := hwin.2.1
  have hbalance :
      (N : ℝ) / (2 : ℝ) ^ L ≤ B := by
    simpa only [B] using hwin.2.2
  have hfinite :=
    abs_factorialMomentError_le hNtwo hLpos
  have hnumBound :=
    hNnum N ((le_max_right _ _).trans hNtail) L hrun
  have hnumNonneg :
      0 ≤ factorialErrorNumerator N L := by
    unfold factorialErrorNumerator
    positivity
  have hnumLe :
      factorialErrorNumerator N L ≤
        δ * (N : ℝ) ^ 2 := by
    simpa only [abs_of_nonneg hnumNonneg,
      abs_of_nonneg (sq_nonneg (N : ℝ))] using hnumBound
  have hratioNonneg :
      0 ≤ (N : ℝ) / (2 : ℝ) ^ L := by
    positivity
  have hbalanceSq :
      ((N : ℝ) / (2 : ℝ) ^ L) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hratioNonneg hbalance 2
  simp only [abs_one, mul_one]
  calc
    |factorialMomentError N L| ≤
        factorialErrorNumerator N L /
          (2 : ℝ) ^ (2 * L) :=
      hfinite
    _ ≤
        (δ * (N : ℝ) ^ 2) /
          (2 : ℝ) ^ (2 * L) :=
      div_le_div_of_nonneg_right hnumLe (by positivity)
    _ =
        δ * ((N : ℝ) / (2 : ℝ) ^ L) ^ 2 := by
      rw [show 2 * L = L * 2 by omega, pow_mul]
      ring
    _ ≤ δ * B ^ 2 :=
      mul_le_mul_of_nonneg_left hbalanceSq hδ.le
    _ = ε := by
      dsimp only [δ]
      field_simp [ne_of_gt hBpos]

/-! ## The Poisson-scale moment and variance conclusions -/

/-- The critical-window Poisson parameter `λ = N / 2^L`. -/
noncomputable def criticalMean (N L : ℕ) : ℝ :=
  (N : ℝ) / (2 : ℝ) ^ L

/--
The harmless difference between the falling-factorial baseline and `λ²`.
-/
noncomputable def factorialBaselinePoissonError
    (N L : ℕ) : ℝ :=
  (factorialBaseline N L : ℝ) - (criticalMean N L) ^ 2

/-- Exact formula for the baseline correction. -/
theorem factorialBaselinePoissonError_eq
    {N L : ℕ} (hN : 1 ≤ N) :
    factorialBaselinePoissonError N L =
      -(N : ℝ) / (2 : ℝ) ^ (2 * L) := by
  rw [factorialBaselinePoissonError, factorialBaseline_eq]
  unfold criticalMean
  push_cast
  rw [Nat.cast_sub hN]
  rw [show 2 * L = L * 2 by omega, pow_mul]
  field_simp
  ring

/-- The falling-factorial baseline differs from `λ²` by `o_C(1)`. -/
theorem factorialBaselinePoissonError_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      factorialBaselinePoissonError
      (fun _ _ => 1) := by
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let B := CriticalRunWindow.balanceConstant C
  have hBnonneg : 0 ≤ B := by
    dsimp only [B]
    exact CriticalRunWindow.balanceConstant_nonneg C
  intro ε hε
  obtain ⟨K : ℕ, hK⟩ := exists_nat_gt (B ^ 2 / ε)
  refine ⟨max 1 (max Nwindow K), ?_⟩
  intro N hN L hrun
  have hNone : 1 ≤ N := (le_max_left _ _).trans hN
  have hNtail : max Nwindow K ≤ N :=
    (le_max_right _ _).trans hN
  have hwindow :=
    hNwindow N ((le_max_left _ _).trans hNtail) L hrun
  have hbalance : criticalMean N L ≤ B := by
    simpa only [criticalMean, B] using hwindow.2.2
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hNone)
  have hKle : K ≤ N := (le_max_right _ _).trans hNtail
  have hlarge : B ^ 2 / ε < (N : ℝ) :=
    hK.trans_le (by exact_mod_cast hKle)
  have hBsqLe : B ^ 2 ≤ ε * (N : ℝ) := by
    simpa only [mul_comm] using ((div_lt_iff₀ hε).mp hlarge).le
  have hmeanNonneg : 0 ≤ criticalMean N L := by
    unfold criticalMean
    positivity
  have hmeanSq :
      (criticalMean N L) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hmeanNonneg hbalance 2
  have hidentity :
      (N : ℝ) / (2 : ℝ) ^ (2 * L) =
        (criticalMean N L) ^ 2 / (N : ℝ) := by
    unfold criticalMean
    rw [show 2 * L = L * 2 by omega, pow_mul]
    field_simp
  rw [factorialBaselinePoissonError_eq hNone, abs_div, abs_neg,
    abs_of_nonneg hNpos.le, abs_of_pos (pow_pos (by norm_num) (2 * L))]
  simp only [abs_one, mul_one]
  rw [hidentity]
  calc
    (criticalMean N L) ^ 2 / (N : ℝ) ≤
        B ^ 2 / (N : ℝ) :=
      div_le_div_of_nonneg_right hmeanSq hNpos.le
    _ ≤ ε := (div_le_iff₀ hNpos).2 hBsqLe

/--
Any `N^(-1/2+o(1))` family is uniformly `o(1)`.  This is the precise
conversion needed for the first-moment error.
-/
private theorem uniformLittleOOne_of_uniformNegativeHalfPower
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hf : UniformNegativeHalfPowerSubpolynomialOn admissible f) :
    UniformLittleOOn admissible f (fun _ _ => 1) := by
  have hrat :
      UniformRationalPowerSubpolynomialOn 1 2 admissible
        (fun N L => (N : ℝ) * f N L) := by
    intro k hk
    simpa using hf k hk
  have hscaled :
      UniformLittleOOn admissible
        (fun N L => (N : ℝ) * f N L)
        (fun N _ => (N : ℝ)) := by
    simpa only [pow_one] using
      (UniformRationalPower.littleO_natPower_of_lt
        (p := 1) (q := 2) (r := 1) (by omega) hrat)
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hscaled ε hε
  refine ⟨max 1 N₀, ?_⟩
  intro N hN L hNL
  have hNone : 1 ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hNone)
  have hbound :=
    hN₀ N ((le_max_right _ _).trans hN) L hNL
  simp only [abs_mul, abs_of_nonneg hNpos.le, abs_one, mul_one] at hbound ⊢
  apply (mul_le_mul_iff_right₀ hNpos).mp
  simpa only [mul_comm] using hbound

/-- Real first-moment error from the critical Poisson parameter. -/
noncomputable def dyadicFirstMomentPoissonError
    (N L : ℕ) : ℝ :=
  (dyadicExpectation N L : ℝ) - criticalMean N L

/-- Corollary 3.3 implies the first-moment error is uniformly `o_C(1)`. -/
theorem dyadicFirstMomentPoissonError_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      dyadicFirstMomentPoissonError
      (fun _ _ => 1) := by
  apply uniformLittleOOne_of_uniformNegativeHalfPower
  change
    UniformNegativeHalfPowerSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (dyadicExpectation N L : ℝ) -
          (N : ℝ) / (2 : ℝ) ^ L)
  exact CriticalRunWindow.firstMoment_error_uniformNegativeHalfPower hC

/-- Real second-factorial-moment error from `λ²`. -/
noncomputable def dyadicSecondFactorialPoissonError
    (N L : ℕ) : ℝ :=
  (dyadicSecondFactorialMoment N L : ℝ) -
    (criticalMean N L) ^ 2

/-- Exact split into the finite pair error and the baseline correction. -/
theorem dyadicSecondFactorialPoissonError_eq
    (N L : ℕ) :
    dyadicSecondFactorialPoissonError N L =
      factorialMomentError N L +
        factorialBaselinePoissonError N L := by
  unfold dyadicSecondFactorialPoissonError factorialMomentError
    factorialBaselinePoissonError
  ring

/-- Real variance error from the critical Poisson parameter. -/
noncomputable def dyadicVariancePoissonError
    (N L : ℕ) : ℝ :=
  (dyadicVariance N L : ℝ) - criticalMean N L

/--
Exact error identity used for the variance closure.  The final term is the
difference of squares between the exact first moment and `λ`.
-/
theorem dyadicVariancePoissonError_eq
    (N L : ℕ) :
    dyadicVariancePoissonError N L =
      dyadicSecondFactorialPoissonError N L +
        dyadicFirstMomentPoissonError N L -
          ((dyadicExpectation N L : ℝ) ^ 2 -
            (criticalMean N L) ^ 2) := by
  have hvariance :
      (dyadicVariance N L : ℝ) =
        (dyadicSecondFactorialMoment N L : ℝ) +
          (dyadicExpectation N L : ℝ) -
            (dyadicExpectation N L : ℝ) ^ 2 := by
    exact_mod_cast
      dyadicVariance_eq_factorial_add_expectation_sub_sq N L
  rw [dyadicVariancePoissonError, hvariance]
  unfold dyadicSecondFactorialPoissonError
    dyadicFirstMomentPoissonError
  ring

end

end SectionTwelveMoments
end PaperC
