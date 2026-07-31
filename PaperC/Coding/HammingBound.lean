import PaperC.Arithmetic.ParityVector
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.FieldTheory.Finiteness
import Mathlib.InformationTheory.Hamming

/-!
# The binary Hamming bound

This file isolates the sphere-packing argument used in equations (3.5) and in
Section 8 of Paper C.  A binary word of length `n` is a function
`Fin n → F₂`.  If distinct codewords have Hamming distance greater than
`2 * t`, their radius-`t` balls are disjoint.  Counting these balls gives

`|C| * ∑ j ∈ range (t + 1), n.choose j ≤ 2 ^ n`.

All cardinalities are finite natural-number cardinalities.
-/

namespace PaperC
namespace HammingBound

open Finset

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

/-- Binary words of length `n`. -/
abbrev BinaryWord (n : ℕ) := Fin n → F₂

/-- The support of a binary word. -/
def wordSupport {n : ℕ} (x : BinaryWord n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i ≠ 0

@[simp]
theorem card_wordSupport {n : ℕ} (x : BinaryWord n) :
    (wordSupport x).card = hammingNorm x :=
  rfl

/-- Over `F₂`, every nonzero scalar is one. -/
theorem eq_one_of_ne_zero (a : F₂) (ha : a ≠ 0) : a = 1 := by
  apply (ZMod.val_eq_one (by omega) a).mp
  have hpos : 0 < a.val := ZMod.val_pos.mpr ha
  have hlt : a.val < 2 := ZMod.val_lt a
  omega

/-- The binary word whose support is exactly `s`. -/
def wordOfSupport {n : ℕ} (s : Finset (Fin n)) : BinaryWord n :=
  fun i ↦ if i ∈ s then 1 else 0

@[simp]
theorem wordSupport_wordOfSupport {n : ℕ} (s : Finset (Fin n)) :
    wordSupport (wordOfSupport s) = s := by
  ext i
  by_cases hi : i ∈ s <;> simp [wordSupport, wordOfSupport, hi]

@[simp]
theorem wordOfSupport_wordSupport {n : ℕ} (x : BinaryWord n) :
    wordOfSupport (wordSupport x) = x := by
  funext i
  by_cases hi : x i = 0
  · simp [wordOfSupport, wordSupport, hi]
  · have hone : x i = 1 := eq_one_of_ne_zero (x i) hi
    simp [wordOfSupport, wordSupport, hi, hone]

/-- Binary words are canonically equivalent to subsets of their coordinates. -/
def supportEquiv (n : ℕ) : BinaryWord n ≃ Finset (Fin n) where
  toFun := wordSupport
  invFun := wordOfSupport
  left_inv := wordOfSupport_wordSupport
  right_inv := wordSupport_wordOfSupport

/-- The set of coordinates on which two binary words differ. -/
def differenceSupport {n : ℕ} (x y : BinaryWord n) : Finset (Fin n) :=
  wordSupport (x - y)

theorem hammingDist_eq_card_differenceSupport {n : ℕ} (x y : BinaryWord n) :
    hammingDist x y = (differenceSupport x y).card := by
  rw [hammingDist_eq_hammingNorm]
  change hammingNorm (-x + y) = hammingNorm (x - y)
  congr 1
  funext i
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply,
    ZMod.neg_eq_self_mod_two, sub_eq_add_neg]

/-- For fixed `x`, taking the difference support is a bijection from words to
coordinate subsets. -/
def differenceSupportEquiv {n : ℕ} (x : BinaryWord n) :
    BinaryWord n ≃ Finset (Fin n) :=
  (Equiv.subLeft x).trans (supportEquiv n)

@[simp]
theorem differenceSupportEquiv_apply {n : ℕ} (x y : BinaryWord n) :
    differenceSupportEquiv x y = differenceSupport x y :=
  rfl

/-- The closed Hamming ball of radius `t` around `x`. -/
def ball {n : ℕ} (x : BinaryWord n) (t : ℕ) : Finset (BinaryWord n) :=
  Finset.univ.filter fun y ↦ hammingDist x y ≤ t

@[simp]
theorem mem_ball {n t : ℕ} {x y : BinaryWord n} :
    y ∈ ball x t ↔ hammingDist x y ≤ t := by
  simp [ball]

/-- Subsets of the `n` coordinates having cardinality at most `t`. -/
def smallSupports (n t : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter fun s ↦ s.card ≤ t

/-- The volume of a binary Hamming ball of radius `t`. -/
def volume (n t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (t + 1), n.choose j

theorem card_ball_eq_card_smallSupports {n t : ℕ} (x : BinaryWord n) :
    (ball x t).card = (smallSupports n t).card := by
  classical
  refine Finset.card_bij
    (fun y _ ↦ differenceSupportEquiv x y) ?_ ?_ ?_
  · intro y hy
    simpa [smallSupports, hammingDist_eq_card_differenceSupport] using hy
  · intro y₁ _ y₂ _ h
    exact (differenceSupportEquiv x).injective h
  · intro s hs
    refine ⟨(differenceSupportEquiv x).symm s, ?_, ?_⟩
    · have hsle : s.card ≤ t := by
        simpa [smallSupports] using hs
      rw [mem_ball, hammingDist_eq_card_differenceSupport,
        ← differenceSupportEquiv_apply]
      simpa using hsle
    · simp

theorem card_smallSupports (n t : ℕ) :
    (smallSupports n t).card = volume n t := by
  classical
  let p : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powerset
  have hfilter :
      (smallSupports n t).card =
        (p.filter fun s ↦ s.card ∈ Finset.range (t + 1)).card := by
    congr 1
    ext s
    simp [smallSupports, p, Nat.lt_succ_iff]
  rw [hfilter, volume]
  rw [← Finset.sum_card_fiberwise_eq_card_filter p (Finset.range (t + 1)) Finset.card]
  apply Finset.sum_congr rfl
  intro j hj
  change
    ((Finset.univ : Finset (Fin n)).powerset.filter fun s ↦ s.card = j).card =
      n.choose j
  rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
  simp

/-- Every binary Hamming ball of radius `t` has the expected binomial volume. -/
theorem card_ball {n t : ℕ} (x : BinaryWord n) :
    (ball x t).card = volume n t :=
  (card_ball_eq_card_smallSupports x).trans (card_smallSupports n t)

/-- Radius-`t` balls around two words at distance greater than `2t` are
disjoint. -/
theorem disjoint_balls_of_two_mul_lt_distance {n t : ℕ} {x y : BinaryWord n}
    (hxy : 2 * t < hammingDist x y) :
    Disjoint (ball x t) (ball y t) := by
  rw [Finset.disjoint_left]
  intro z hzx hzy
  have hxz : hammingDist x z ≤ t := mem_ball.mp hzx
  have hzy' : hammingDist z y ≤ t := by
    rw [hammingDist_comm]
    exact mem_ball.mp hzy
  have htriangle : hammingDist x y ≤ hammingDist x z + hammingDist z y :=
    hammingDist_triangle x z y
  omega

/-- A convenient predicate saying that the minimum distance of `C` is
strictly greater than `d`. -/
def MinDistanceAbove {n : ℕ} (C : Finset (BinaryWord n)) (d : ℕ) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → d < hammingDist x y

/-- The radius-`t` balls around codewords are pairwise disjoint when the
minimum distance is greater than `2t`. -/
theorem pairwiseDisjoint_balls {n t : ℕ} {C : Finset (BinaryWord n)}
    (hmin : MinDistanceAbove C (2 * t)) :
    (C : Set (BinaryWord n)).PairwiseDisjoint fun x ↦ ball x t := by
  intro x hx y hy hxy
  exact disjoint_balls_of_two_mul_lt_distance (hmin hx hy hxy)

/-- The finite binary Hamming (sphere-packing) bound. -/
theorem hamming_bound {n t : ℕ} {C : Finset (BinaryWord n)}
    (hmin : MinDistanceAbove C (2 * t)) :
    C.card * volume n t ≤ 2 ^ n := by
  classical
  have hpairwise := pairwiseDisjoint_balls hmin
  calc
    C.card * volume n t = ∑ x ∈ C, (ball x t).card := by
      simp [card_ball]
    _ = (C.biUnion fun x ↦ ball x t).card :=
      (Finset.card_biUnion hpairwise).symm
    _ ≤ (Finset.univ : Finset (BinaryWord n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ n := by
      simp [Fintype.card_fun, ZMod.card]

/-- Equation (3.5), written without the abbreviation `volume`. -/
theorem hamming_bound_sum_choose {n t : ℕ} {C : Finset (BinaryWord n)}
    (hmin : MinDistanceAbove C (2 * t)) :
    C.card * (∑ j ∈ Finset.range (t + 1), n.choose j) ≤ 2 ^ n := by
  simpa [volume] using hamming_bound hmin

/-- Codimension form of the Hamming bound once the code cardinality is
identified as `2^(n-r)`.  This is the exact numerical form used in (3.5) and
Section 8. -/
theorem hamming_bound_codimension {n t r : ℕ} {C : Finset (BinaryWord n)}
    (hmin : MinDistanceAbove C (2 * t))
    (hcard : C.card = 2 ^ (n - r)) :
    2 ^ (n - r) * (∑ j ∈ Finset.range (t + 1), n.choose j) ≤ 2 ^ n := by
  rw [← hcard]
  exact hamming_bound_sum_choose hmin

/-- The words belonging to a binary linear code, regarded as a finset of the
ambient Hamming space. -/
noncomputable def submoduleCodewords {n : ℕ} (C : Submodule F₂ (BinaryWord n)) :
    Finset (BinaryWord n) := by
  classical
  exact (Finset.univ : Finset (BinaryWord n)).filter fun x ↦ x ∈ C

@[simp]
theorem mem_submoduleCodewords {n : ℕ} {C : Submodule F₂ (BinaryWord n)}
    {x : BinaryWord n} :
    x ∈ submoduleCodewords C ↔ x ∈ C := by
  classical
  simp [submoduleCodewords]

/-- A binary linear code has `2^dim(C)` codewords. -/
theorem card_submoduleCodewords {n : ℕ} (C : Submodule F₂ (BinaryWord n)) :
    (submoduleCodewords C).card = 2 ^ Module.finrank F₂ C := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  calc
    (submoduleCodewords C).card = (Finset.univ : Finset C).card := by
      refine Finset.card_bij (fun x hx ↦ ⟨x, mem_submoduleCodewords.mp hx⟩) ?_ ?_ ?_
      · intro x hx
        exact Finset.mem_univ _
      · intro x₁ _ x₂ _ h
        exact congrArg Subtype.val h
      · intro c hc
        exact ⟨c, mem_submoduleCodewords.mpr c.property, Subtype.ext rfl⟩
    _ = Fintype.card C := Finset.card_univ
    _ = 2 ^ Module.finrank F₂ C := by
      simpa only [ZMod.card] using
        (Module.card_eq_pow_finrank (K := F₂) (V := C))

/-- Minimum-weight formulation for a binary linear code. -/
def MinWeightAbove {n : ℕ} (C : Submodule F₂ (BinaryWord n)) (d : ℕ) : Prop :=
  ∀ c : C, c ≠ 0 → d < hammingNorm (c : BinaryWord n)

/-- For a linear code, a lower bound on nonzero weights gives the same lower
bound on pairwise distances. -/
theorem minDistanceAbove_submoduleCodewords {n d : ℕ}
    {C : Submodule F₂ (BinaryWord n)}
    (hweight : MinWeightAbove C d) :
    MinDistanceAbove (submoduleCodewords C) d := by
  classical
  intro x hx y hy hxy
  have hxC : x ∈ C := mem_submoduleCodewords.mp hx
  have hyC : y ∈ C := mem_submoduleCodewords.mp hy
  let c : C := ⟨x - y, C.sub_mem hxC hyC⟩
  have hcne : c ≠ 0 := by
    intro hc
    apply hxy
    apply sub_eq_zero.mp
    have hcval := congrArg Subtype.val hc
    simpa [c] using hcval
  have hc := hweight c hcne
  rw [hammingDist_eq_hammingNorm]
  simpa only [show -x + y = x - y by
    funext i
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply,
      ZMod.neg_eq_self_mod_two, sub_eq_add_neg]] using hc

/-- Sphere-packing bound for a binary linear code, in dimension form. -/
theorem hamming_bound_submodule {n t : ℕ}
    {C : Submodule F₂ (BinaryWord n)}
    (hweight : MinWeightAbove C (2 * t)) :
    2 ^ Module.finrank F₂ C *
        (∑ j ∈ Finset.range (t + 1), n.choose j) ≤
      2 ^ n := by
  have h := hamming_bound_sum_choose
    (minDistanceAbove_submoduleCodewords hweight)
  rwa [card_submoduleCodewords] at h

/-- The exact codimension form used in equations (3.5) and Section 8. -/
theorem hamming_bound_submodule_codimension {n t r : ℕ}
    {C : Submodule F₂ (BinaryWord n)}
    (hweight : MinWeightAbove C (2 * t))
    (hcodim : Module.finrank F₂ C = n - r) :
    2 ^ (n - r) * (∑ j ∈ Finset.range (t + 1), n.choose j) ≤ 2 ^ n := by
  rw [← hcodim]
  exact hamming_bound_submodule hweight

/--
The form of the first inequality in (3.5) needed in the paper: it is enough
that the code have dimension *at least* `n - r`, equivalently codimension at
most `r` when `r ≤ n`.
-/
theorem hamming_bound_submodule_of_finrank_ge {n t r : ℕ}
    {C : Submodule F₂ (BinaryWord n)}
    (hweight : MinWeightAbove C (2 * t))
    (hfinrank : n - r ≤ Module.finrank F₂ C) :
    2 ^ (n - r) * (∑ j ∈ Finset.range (t + 1), n.choose j) ≤ 2 ^ n := by
  calc
    2 ^ (n - r) * (∑ j ∈ Finset.range (t + 1), n.choose j) ≤
        2 ^ Module.finrank F₂ C *
          (∑ j ∈ Finset.range (t + 1), n.choose j) := by
      exact Nat.mul_le_mul_right _
        (pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hfinrank)
    _ ≤ 2 ^ n := hamming_bound_submodule hweight

/--
The second inequality in (3.5).  If `r ≤ n`, the factor
`2 ^ (n - r)` can be cancelled from the first inequality, giving the
binomial-volume bound by `2 ^ r`.
-/
theorem sum_choose_le_pow_of_finrank_ge {n t r : ℕ}
    {C : Submodule F₂ (BinaryWord n)}
    (hweight : MinWeightAbove C (2 * t))
    (hfinrank : n - r ≤ Module.finrank F₂ C)
    (hrn : r ≤ n) :
    (∑ j ∈ Finset.range (t + 1), n.choose j) ≤ 2 ^ r := by
  have hpacking := hamming_bound_submodule_of_finrank_ge hweight hfinrank
  have hcancel :
      2 ^ (n - r) * (∑ j ∈ Finset.range (t + 1), n.choose j) ≤
        2 ^ (n - r) * 2 ^ r := by
    calc
      2 ^ (n - r) * (∑ j ∈ Finset.range (t + 1), n.choose j) ≤
          2 ^ n := hpacking
      _ = 2 ^ (n - r) * 2 ^ r := by
        rw [← pow_add, Nat.sub_add_cancel hrn]
  exact Nat.le_of_mul_le_mul_left hcancel (by positivity)

end HammingBound
end PaperC
