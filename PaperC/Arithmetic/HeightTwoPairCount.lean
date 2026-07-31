import PaperC.Arithmetic.SeparatedSmallChannels
import PaperC.Model.FiniteRademacher
import Mathlib.Data.Finset.Card

/-!
# Counting the frontal channels of height two

There are only two positive primitive directions of height two.  For
`(a,b) = (2,1)`, condition (5.1) reads `|y - 2x| < 3B`; inside
`[N,2N)²` this confines `x` to the first `3B` positions and `y` to the
last `3B` positions.  The direction `(1,2)` gives the transposed rectangle.
Consequently the union has cardinality `O(B²)`, uniformly in `N`.
-/

namespace PaperC

open Finset

/-- Dyadic pairs satisfying (5.1) in the orientation `(a,b) = (2,1)`. -/
def heightTwoForwardPairs (N B : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun pair ↦
    SatisfiesChannelInequality pair.1 pair.2 B 2 1

/-- Dyadic pairs satisfying (5.1) in the orientation `(a,b) = (1,2)`. -/
def heightTwoBackwardPairs (N B : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun pair ↦
    SatisfiesChannelInequality pair.1 pair.2 B 1 2

/-- The union of the two primitive height-two orientations. -/
def heightTwoBoundaryPairs (N B : ℕ) : Finset (ℕ × ℕ) :=
  heightTwoForwardPairs N B ∪ heightTwoBackwardPairs N B

@[simp]
theorem mem_heightTwoForwardPairs
    {N B x y : ℕ} :
    (x, y) ∈ heightTwoForwardPairs N B ↔
      x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧
        SatisfiesChannelInequality x y B 2 1 := by
  simp [heightTwoForwardPairs, and_assoc]

@[simp]
theorem mem_heightTwoBackwardPairs
    {N B x y : ℕ} :
    (x, y) ∈ heightTwoBackwardPairs N B ↔
      x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧
        SatisfiesChannelInequality x y B 1 2 := by
  simp [heightTwoBackwardPairs, and_assoc]

@[simp]
theorem mem_heightTwoBoundaryPairs
    {N B x y : ℕ} :
    (x, y) ∈ heightTwoBoundaryPairs N B ↔
      (x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧
        SatisfiesChannelInequality x y B 2 1) ∨
      (x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧
        SatisfiesChannelInequality x y B 1 2) := by
  simp [heightTwoBoundaryPairs]

/--
The `(2,1)` inequality confines a dyadic pair to the lower-left/upper-right
corner rectangle.
-/
theorem heightTwoForwardPairs_confinement
    {N B x y : ℕ}
    (hpair : (x, y) ∈ heightTwoForwardPairs N B) :
    x ∈ Ico N (N + 3 * B) ∧
      y ∈ Ico (2 * N - 3 * B) (2 * N) := by
  obtain ⟨hx, hy, hclose⟩ :=
    mem_heightTwoForwardPairs.mp hpair
  have hxBounds :
      N ≤ x ∧ x < 2 * N :=
    Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)
  have hyBounds :
      N ≤ y ∧ y < 2 * N :=
    Finset.mem_Ico.mp (by simpa [dyadicBlock] using hy)
  have hclose' :
      -(((3 * B : ℕ) : ℤ)) <
          (y : ℤ) - 2 * (x : ℤ) ∧
        (y : ℤ) - 2 * (x : ℤ) <
          ((3 * B : ℕ) : ℤ) := by
    simpa [SatisfiesChannelInequality, pairChannelError, abs_lt]
      using hclose
  constructor
  · rw [Finset.mem_Ico]
    constructor
    · exact hxBounds.1
    · omega
  · rw [Finset.mem_Ico]
    constructor <;> omega

/--
The `(1,2)` inequality gives the transposed corner confinement.
-/
theorem heightTwoBackwardPairs_confinement
    {N B x y : ℕ}
    (hpair : (x, y) ∈ heightTwoBackwardPairs N B) :
    x ∈ Ico (2 * N - 3 * B) (2 * N) ∧
      y ∈ Ico N (N + 3 * B) := by
  obtain ⟨hx, hy, hclose⟩ :=
    mem_heightTwoBackwardPairs.mp hpair
  have hxBounds :
      N ≤ x ∧ x < 2 * N :=
    Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)
  have hyBounds :
      N ≤ y ∧ y < 2 * N :=
    Finset.mem_Ico.mp (by simpa [dyadicBlock] using hy)
  have hclose' :
      -(((3 * B : ℕ) : ℤ)) <
          2 * (y : ℤ) - (x : ℤ) ∧
        2 * (y : ℤ) - (x : ℤ) <
          ((3 * B : ℕ) : ℤ) := by
    simpa [SatisfiesChannelInequality, pairChannelError, abs_lt]
      using hclose
  constructor
  · rw [Finset.mem_Ico]
    constructor <;> omega
  · rw [Finset.mem_Ico]
    constructor
    · exact hyBounds.1
    · omega

/-- Rectangle containment for the `(2,1)` orientation. -/
theorem heightTwoForwardPairs_subset_rectangle (N B : ℕ) :
    heightTwoForwardPairs N B ⊆
      Ico N (N + 3 * B) ×ˢ Ico (2 * N - 3 * B) (2 * N) := by
  intro pair hpair
  rcases pair with ⟨x, y⟩
  exact Finset.mem_product.mpr
    (heightTwoForwardPairs_confinement hpair)

/-- Rectangle containment for the `(1,2)` orientation. -/
theorem heightTwoBackwardPairs_subset_rectangle (N B : ℕ) :
    heightTwoBackwardPairs N B ⊆
      Ico (2 * N - 3 * B) (2 * N) ×ˢ Ico N (N + 3 * B) := by
  intro pair hpair
  rcases pair with ⟨x, y⟩
  exact Finset.mem_product.mpr
    (heightTwoBackwardPairs_confinement hpair)

/-- Each oriented height-two family contains at most `(3B)²` pairs. -/
theorem card_heightTwoForwardPairs_le (N B : ℕ) :
    (heightTwoForwardPairs N B).card ≤ (3 * B) ^ 2 := by
  have hsubset :=
    Finset.card_le_card (heightTwoForwardPairs_subset_rectangle N B)
  have hlast :
      (Ico (2 * N - 3 * B) (2 * N)).card ≤ 3 * B := by
    simp only [Nat.card_Ico]
    omega
  calc
    (heightTwoForwardPairs N B).card ≤
        (Ico N (N + 3 * B) ×ˢ
          Ico (2 * N - 3 * B) (2 * N)).card :=
      hsubset
    _ = (3 * B) *
        (Ico (2 * N - 3 * B) (2 * N)).card := by
      rw [Finset.card_product]
      simp
    _ ≤ (3 * B) * (3 * B) :=
      Nat.mul_le_mul_left (3 * B) hlast
    _ = (3 * B) ^ 2 := by ring

/-- The transposed orientation satisfies the same `(3B)²` bound. -/
theorem card_heightTwoBackwardPairs_le (N B : ℕ) :
    (heightTwoBackwardPairs N B).card ≤ (3 * B) ^ 2 := by
  have hsubset :=
    Finset.card_le_card (heightTwoBackwardPairs_subset_rectangle N B)
  have hlast :
      (Ico (2 * N - 3 * B) (2 * N)).card ≤ 3 * B := by
    simp only [Nat.card_Ico]
    omega
  calc
    (heightTwoBackwardPairs N B).card ≤
        (Ico (2 * N - 3 * B) (2 * N) ×ˢ
          Ico N (N + 3 * B)).card :=
      hsubset
    _ = (Ico (2 * N - 3 * B) (2 * N)).card *
        (3 * B) := by
      rw [Finset.card_product]
      simp
    _ ≤ (3 * B) * (3 * B) :=
      Nat.mul_le_mul_right (3 * B) hlast
    _ = (3 * B) ^ 2 := by ring

/--
Uniform `O(B²)` bound for both primitive height-two orientations.
The displayed constant is deliberately compatible with the coarse
`2(6B+1)²` envelope used downstream.
-/
theorem card_heightTwoBoundaryPairs_le (N B : ℕ) :
    (heightTwoBoundaryPairs N B).card ≤
      2 * (6 * B + 1) ^ 2 := by
  have hunion :
      (heightTwoBoundaryPairs N B).card ≤
        (heightTwoForwardPairs N B).card +
          (heightTwoBackwardPairs N B).card := by
    exact Finset.card_union_le _ _
  have horiented :
      (heightTwoForwardPairs N B).card +
          (heightTwoBackwardPairs N B).card ≤
        2 * (3 * B) ^ 2 := by
    have hforward := card_heightTwoForwardPairs_le N B
    have hbackward := card_heightTwoBackwardPairs_le N B
    omega
  have hbase : 3 * B ≤ 6 * B + 1 := by
    omega
  have hsquare :
      (3 * B) ^ 2 ≤ (6 * B + 1) ^ 2 :=
    Nat.pow_le_pow_left hbase 2
  exact hunion.trans <| horiented.trans <|
    Nat.mul_le_mul_left 2 hsquare

end PaperC
