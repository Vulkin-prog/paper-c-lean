import PaperC.Asymptotics.BoundedRatioSteinChen

set_option maxHeartbeats 1800000

/-!
# Vanishing first Stein--Chen term on retained intervals

This file supplies the asymptotic consequences of the exact bounded-interval
`b₁` identity proved in `BoundedRatioSteinChen`.

There are two versions:

* a genuinely uniform statement for `2N ≤ M ≤ κ₀N`;
* the specialization to the literal retained interval
  `[M / 2^j, M)` for fixed `j`.

The small-prime assignment is universally quantified *after* the common
asymptotic threshold.  Thus the result is uniform in that assignment, rather
than merely holding for one preselected family of assignments.

The final section records the exact rounding error in
`M - M / 2^j`.  Its error lies in `[0,1)`, and after critical normalization
by `2^L` it is uniformly `o_C(1)`.  A generic closure theorem then makes the
result directly usable once the normalized bad-start correction has been
supplied.
-/

namespace PaperC
namespace BoundedRatioSteinChenRates

open scoped BigOperators NNReal

open ArratiaGoldsteinGordonInput
open BoundedRatioSteinChen
open ConditionalStartProbability
open PropositionSixteenOne
open SectionThirteenFiniteBound
open TerminalPrimeCutoff

noncomputable section

/-! ## The terminal first Stein--Chen term -/

/-- Small-prime assignments at the literal terminal cutoff. -/
abbrev TerminalSmallSample (M L : ℕ) :=
  SmallSample (boundedRatioCutoff M L)
    (terminalPrimeCutoff (L + 1))

/-- The conditional first Stein--Chen term at the literal terminal cutoff. -/
noncomputable def terminalBOne
    (N M L : ℕ) (σ : TerminalSmallSample M L) : ℝ :=
  bOne
    (boundedLargeUniformPMF M L
      (terminalPrimeCutoff (L + 1)))
    (boundedConditionedGoodIndicator N M L
      (terminalPrimeCutoff (L + 1)) σ)
    (boundedLargePrimeDependencyGraph N M L
      (terminalPrimeCutoff (L + 1)))

/-- The exact nonnegative numerator occurring in `terminalBOne`. -/
noncomputable def terminalBOneNumerator
    (N M L : ℕ) : ℝ :=
  ((boundedGoodStarts N M L
      (terminalPrimeCutoff (L + 1))).card : ℝ) +
    ((boundedOrderedDependencyEdges N M L
      (terminalPrimeCutoff (L + 1))).card : ℝ)

theorem terminalBOneNumerator_nonneg
    (N M L : ℕ) :
    0 ≤ terminalBOneNumerator N M L := by
  unfold terminalBOneNumerator
  positivity

/-- The bounded-interval identity, specialized to the terminal cutoff. -/
theorem terminalBOne_eq_terminalBOneNumerator_div
    {N M L : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L)
    (σ : TerminalSmallSample M L) :
    terminalBOne N M L σ =
      terminalBOneNumerator N M L /
        (2 : ℝ) ^ (2 * L) := by
  have hLY :
      L + 1 ≤ terminalPrimeCutoff (L + 1) :=
    window_succ_le_terminalPrimeCutoff hL le_rfl
  simpa only [terminalBOne, terminalBOneNumerator,
      Nat.cast_add] using
    (bOne_boundedConditionedGoodIndicator_eq_card_div
      hN hL hLY σ)

/-! ## Uniform bounded-ratio estimate -/

/--
The number of good starts is uniformly `o(N²)` in every bounded-ratio
window.  Only the elementary bound `#good ≤ M ≤ κ₀N` is used.
-/
theorem
    boundedGoodStarts_terminalCutoff_card_uniformLittleOInBoundedRatioWindow
    {C : ℝ} (κ₀ : ℕ) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (fun N M L =>
        ((boundedGoodStarts N M L
          (terminalPrimeCutoff (L + 1))).card : ℝ)) := by
  intro ε hε
  obtain ⟨Nsize, hNsize⟩ :=
    exists_nat_gt ((κ₀ : ℝ) / ε)
  refine ⟨max 1 Nsize, ?_⟩
  intro N hN M L hNM hMκ _hrun
  have hNposNat : 0 < N :=
    (le_max_left 1 Nsize).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hNposNat
  have hNleM : N ≤ M := by omega
  have hcardNat :
      (boundedGoodStarts N M L
        (terminalPrimeCutoff (L + 1))).card ≤ M := by
    have hpartition :=
      card_boundedGood_add_card_boundedBad
        (L := L) (Y := terminalPrimeCutoff (L + 1)) hNleM
    omega
  have hcard :
      ((boundedGoodStarts N M L
        (terminalPrimeCutoff (L + 1))).card : ℝ) ≤
          (M : ℝ) := by
    exact_mod_cast hcardNat
  have hMκR :
      (M : ℝ) ≤ (κ₀ : ℝ) * (N : ℝ) := by
    exact_mod_cast hMκ
  have hNsizeR :
      (κ₀ : ℝ) / ε < (N : ℝ) :=
    hNsize.trans_le (by exact_mod_cast
      (le_max_right 1 Nsize).trans hN)
  have hκlt :
      (κ₀ : ℝ) < ε * (N : ℝ) := by
    have hcross := (div_lt_iff₀ hε).mp hNsizeR
    simpa only [mul_comm] using hcross
  have hscale :
      (κ₀ : ℝ) * (N : ℝ) ≤
        ε * (N : ℝ) ^ 2 := by
    nlinarith
  rw [abs_of_nonneg (by positivity :
    0 ≤ ((boundedGoodStarts N M L
      (terminalPrimeCutoff (L + 1))).card : ℝ))]
  rw [abs_of_nonneg (sq_nonneg (N : ℝ))]
  exact hcard.trans (hMκR.trans hscale)

/-- The complete terminal `b₁` numerator is uniformly `o(N²)`. -/
theorem terminalBOneNumerator_uniformLittleOInBoundedRatioWindow
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformLittleOInBoundedRatioWindow C κ₀
      terminalBOneNumerator := by
  have hgood :=
    boundedGoodStarts_terminalCutoff_card_uniformLittleOInBoundedRatioWindow
      (C := C) κ₀
  have hedge :=
    boundedOrderedDependencyEdges_terminalCutoff_uniformLittleOInBoundedRatioWindow
      hC κ₀
  change UniformLittleOInBoundedRatioWindow C κ₀
    (fun N M L =>
      ((boundedGoodStarts N M L
        (terminalPrimeCutoff (L + 1))).card : ℝ) +
      ((boundedOrderedDependencyEdges N M L
        (terminalPrimeCutoff (L + 1))).card : ℝ))
  exact uniformLittleOInBoundedRatioWindow_add hgood hedge

/--
Uniform `o(1)` for a terminal `b₁`, with the sample assignment quantified
after the common threshold.
-/
def TerminalBOneUniformLittleOOne
    (C : ℝ) (κ₀ : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ σ : TerminalSmallSample M L,
        |terminalBOne N M L σ| ≤ ε

/--
At the terminal cutoff, `b₁ = o_{C,κ₀}(1)` uniformly in
`2N ≤ M ≤ κ₀N` and uniformly in the conditioned small-prime assignment.
-/
theorem terminalBOne_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    TerminalBOneUniformLittleOOne C κ₀ := by
  obtain ⟨Nwindow, hwindow⟩ :=
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
  obtain ⟨Nnum, hNnum⟩ :=
    (terminalBOneNumerator_uniformLittleOInBoundedRatioWindow
      hC κ₀) δ hδ
  refine ⟨max 2 (max Nwindow Nnum), ?_⟩
  intro N hN M L hNM hMκ hrun σ
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nwindow Nnum)).trans hN
  have htail : max Nwindow Nnum ≤ N :=
    (le_max_right 2 (max Nwindow Nnum)).trans hN
  have hw :=
    hwindow N ((le_max_left _ _).trans htail) L hrun
  have hnumBound :=
    hNnum N ((le_max_right _ _).trans htail)
      M L hNM hMκ hrun
  have hnumLe :
      terminalBOneNumerator N M L ≤
        δ * (N : ℝ) ^ 2 := by
    simpa only [
      abs_of_nonneg (terminalBOneNumerator_nonneg N M L),
      abs_of_nonneg (sq_nonneg (N : ℝ))] using hnumBound
  have hratioNonneg :
      0 ≤ (N : ℝ) / (2 : ℝ) ^ L := by positivity
  have hbalance :
      (N : ℝ) / (2 : ℝ) ^ L ≤ B := by
    simpa only [B] using hw.2.2
  have hbalanceSq :
      ((N : ℝ) / (2 : ℝ) ^ L) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hratioNonneg hbalance 2
  rw [terminalBOne_eq_terminalBOneNumerator_div
    hNtwo hw.2.1 σ]
  simp only [abs_div,
    abs_of_nonneg (terminalBOneNumerator_nonneg N M L),
    abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) (2 * L))]
  calc
    terminalBOneNumerator N M L / (2 : ℝ) ^ (2 * L) ≤
        (δ * (N : ℝ) ^ 2) / (2 : ℝ) ^ (2 * L) :=
      div_le_div_of_nonneg_right hnumLe (by positivity)
    _ = δ * ((N : ℝ) / (2 : ℝ) ^ L) ^ 2 := by
      rw [show 2 * L = L * 2 by omega, pow_mul]
      ring
    _ ≤ δ * B ^ 2 :=
      mul_le_mul_of_nonneg_left hbalanceSq hδ.le
    _ = ε := by
      dsimp only [δ]
      field_simp [ne_of_gt hBpos]

/-! ## The fixed-ratio retained interval -/

/--
For fixed `j`, the good-start contribution on `[M/2^j,M)` is `o(M²)`.
-/
theorem retainedGoodStarts_terminalCutoff_card_uniformLittleOQuadratic
    {C : ℝ} (j : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L =>
        ((boundedGoodStarts (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1))).card : ℝ))
      (fun M _ => (M : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨Msize, hMsize⟩ :=
    exists_nat_gt (1 / ε)
  refine ⟨max 1 Msize, ?_⟩
  intro M hM L _hrun
  have hMposNat : 0 < M :=
    (le_max_left 1 Msize).trans hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hMposNat
  have hbaseM : M / 2 ^ j ≤ M :=
    Nat.div_le_self M _
  have hcardNat :
      (boundedGoodStarts (M / 2 ^ j) M L
        (terminalPrimeCutoff (L + 1))).card ≤ M := by
    have hpartition :=
      card_boundedGood_add_card_boundedBad
        (L := L) (Y := terminalPrimeCutoff (L + 1)) hbaseM
    calc
      (boundedGoodStarts (M / 2 ^ j) M L
          (terminalPrimeCutoff (L + 1))).card ≤
          (boundedGoodStarts (M / 2 ^ j) M L
              (terminalPrimeCutoff (L + 1))).card +
            (boundedTerminalBadStarts (M / 2 ^ j) M L
              (terminalPrimeCutoff (L + 1))).card :=
        Nat.le_add_right _ _
      _ = M - M / 2 ^ j := hpartition
      _ ≤ M := Nat.sub_le _ _
  have hcard :
      ((boundedGoodStarts (M / 2 ^ j) M L
        (terminalPrimeCutoff (L + 1))).card : ℝ) ≤
          (M : ℝ) := by
    exact_mod_cast hcardNat
  have hMsizeR :
      1 / ε < (M : ℝ) :=
    hMsize.trans_le (by exact_mod_cast
      (le_max_right 1 Msize).trans hM)
  have honeLt :
      (1 : ℝ) < ε * (M : ℝ) := by
    have hcross := (div_lt_iff₀ hε).mp hMsizeR
    simpa only [one_mul, mul_comm] using hcross
  have hscale :
      (M : ℝ) ≤ ε * (M : ℝ) ^ 2 := by
    nlinarith
  rw [abs_of_nonneg (by positivity :
    0 ≤ ((boundedGoodStarts (M / 2 ^ j) M L
      (terminalPrimeCutoff (L + 1))).card : ℝ))]
  rw [abs_of_nonneg (sq_nonneg (M : ℝ))]
  exact hcard.trans hscale

/-- The fixed-`j` complete terminal numerator is uniformly `o(M²)`. -/
theorem retainedTerminalBOneNumerator_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L => terminalBOneNumerator (M / 2 ^ j) M L)
      (fun M _ => (M : ℝ) ^ 2) := by
  have hgood :=
    retainedGoodStarts_terminalCutoff_card_uniformLittleOQuadratic
      (C := C) j
  have hedge :=
    retainedOrderedDependencyEdges_terminalCutoff_uniformLittleOQuadratic
      hC j
  simpa only [terminalBOneNumerator] using
    PropositionElevenTwo.uniformLittleOOn_add hgood hedge

/--
Uniform `o(1)` for the first Stein--Chen term on `[M/2^j,M)`, with the
small-prime assignment quantified after the common threshold.
-/
def FixedJTerminalBOneUniformLittleOOne
    (C : ℝ) (j : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C M L →
      ∀ σ : TerminalSmallSample M L,
        |terminalBOne (M / 2 ^ j) M L σ| ≤ ε

/--
Fixed-`j` specialization: the first Stein--Chen term on
`[M/2^j,M)` is uniformly `o_C(1)`.
-/
theorem retainedTerminalBOne_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    FixedJTerminalBOneUniformLittleOOne C j := by
  obtain ⟨Mwindow, hwindow⟩ :=
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
  obtain ⟨Mnum, hMnum⟩ :=
    (retainedTerminalBOneNumerator_uniformLittleOQuadratic
      hC j) δ hδ
  refine
    ⟨max (2 ^ (j + 1)) (max Mwindow Mnum), ?_⟩
  intro M hM L hrun σ
  have hbase : 2 ≤ M / 2 ^ j := by
    rw [Nat.le_div_iff_mul_le (pow_pos (by norm_num) j)]
    calc
      2 * 2 ^ j = 2 ^ (j + 1) := by
        rw [pow_succ]
        ring
      _ ≤ M := (le_max_left _ _).trans hM
  have htail : max Mwindow Mnum ≤ M :=
    (le_max_right (2 ^ (j + 1)) (max Mwindow Mnum)).trans hM
  have hw :=
    hwindow M ((le_max_left _ _).trans htail) L hrun
  have hnumBound :=
    hMnum M ((le_max_right _ _).trans htail) L hrun
  have hnumLe :
      terminalBOneNumerator (M / 2 ^ j) M L ≤
        δ * (M : ℝ) ^ 2 := by
    simpa only [
      abs_of_nonneg
        (terminalBOneNumerator_nonneg (M / 2 ^ j) M L),
      abs_of_nonneg (sq_nonneg (M : ℝ))] using hnumBound
  have hratioNonneg :
      0 ≤ (M : ℝ) / (2 : ℝ) ^ L := by positivity
  have hbalance :
      (M : ℝ) / (2 : ℝ) ^ L ≤ B := by
    simpa only [B] using hw.2.2
  have hbalanceSq :
      ((M : ℝ) / (2 : ℝ) ^ L) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hratioNonneg hbalance 2
  rw [terminalBOne_eq_terminalBOneNumerator_div
    hbase hw.2.1 σ]
  simp only [abs_div,
    abs_of_nonneg
      (terminalBOneNumerator_nonneg (M / 2 ^ j) M L),
    abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) (2 * L))]
  calc
    terminalBOneNumerator (M / 2 ^ j) M L /
          (2 : ℝ) ^ (2 * L) ≤
        (δ * (M : ℝ) ^ 2) / (2 : ℝ) ^ (2 * L) :=
      div_le_div_of_nonneg_right hnumLe (by positivity)
    _ = δ * ((M : ℝ) / (2 : ℝ) ^ L) ^ 2 := by
      rw [show 2 * L = L * 2 by omega, pow_mul]
      ring
    _ ≤ δ * B ^ 2 :=
      mul_le_mul_of_nonneg_left hbalanceSq hδ.le
    _ = ε := by
      dsimp only [δ]
      field_simp [ne_of_gt hBpos]

/-! ## Exact fixed-ratio interval arithmetic -/

/--
The rounding error in the identity

`M - floor(M/2^j) = (1 - 2^{-j}) M + error`.

Writing it as a normalized remainder makes both its exact identity and its
sharp bound transparent.
-/
noncomputable def retainedLengthRoundingError
    (M j : ℕ) : ℝ :=
  ((M % 2 ^ j : ℕ) : ℝ) / (2 : ℝ) ^ j

theorem retainedLengthRoundingError_nonneg
    (M j : ℕ) :
    0 ≤ retainedLengthRoundingError M j := by
  unfold retainedLengthRoundingError
  positivity

theorem retainedLengthRoundingError_lt_one
    (M j : ℕ) :
    retainedLengthRoundingError M j < 1 := by
  have hpowNat : 0 < 2 ^ j := pow_pos (by norm_num) j
  have hmodNat : M % 2 ^ j < 2 ^ j :=
    Nat.mod_lt M hpowNat
  have hmodReal :
      ((M % 2 ^ j : ℕ) : ℝ) < (2 : ℝ) ^ j := by
    exact_mod_cast hmodNat
  unfold retainedLengthRoundingError
  exact (div_lt_one (by positivity)).2 hmodReal

theorem abs_retainedLengthRoundingError_le_one
    (M j : ℕ) :
    |retainedLengthRoundingError M j| ≤ 1 := by
  rw [abs_of_nonneg (retainedLengthRoundingError_nonneg M j)]
  exact (retainedLengthRoundingError_lt_one M j).le

/-- Exact retained-interval cardinal, with an explicit error in `[0,1)`. -/
theorem retainedLength_eq_main_add_roundingError
    (M j : ℕ) :
    ((M - M / 2 ^ j : ℕ) : ℝ) =
      (1 - (1 / 2 : ℝ) ^ j) * (M : ℝ) +
        retainedLengthRoundingError M j := by
  have hpowNat : 0 < 2 ^ j := pow_pos (by norm_num) j
  have hqle : M / 2 ^ j ≤ M :=
    Nat.div_le_self M _
  have hdecompNat :
      M / 2 ^ j * 2 ^ j + M % 2 ^ j = M :=
    by
      simpa only [Nat.mul_comm] using
        (Nat.div_add_mod M (2 ^ j))
  have hdecompReal :
      ((M / 2 ^ j : ℕ) : ℝ) * (2 : ℝ) ^ j +
          ((M % 2 ^ j : ℕ) : ℝ) =
        (M : ℝ) := by
    exact_mod_cast hdecompNat
  have hpowReal : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  rw [Nat.cast_sub hqle]
  unfold retainedLengthRoundingError
  rw [show (1 / 2 : ℝ) ^ j = 1 / (2 : ℝ) ^ j by
    rw [one_div_pow]]
  field_simp [ne_of_gt hpowReal]
  nlinarith

/-- Normalized form of the exact rounding identity. -/
theorem retainedLength_normalized_sub_main_eq_roundingError
    (M L j : ℕ) :
    ((M - M / 2 ^ j : ℕ) : ℝ) / (2 : ℝ) ^ L -
        (1 - (1 / 2 : ℝ) ^ j) *
          (M : ℝ) / (2 : ℝ) ^ L =
      retainedLengthRoundingError M j / (2 : ℝ) ^ L := by
  rw [retainedLength_eq_main_add_roundingError]
  ring

/--
The `O(1)` floor error becomes uniformly `o_C(1)` after critical
normalization.
-/
theorem
    retainedLengthRoundingError_div_twoPow_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L =>
        retainedLengthRoundingError M j / (2 : ℝ) ^ L)
      (fun _ _ => 1) := by
  obtain ⟨Mwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let B := CriticalRunWindow.balanceConstant C
  intro ε hε
  obtain ⟨Msize, hMsize⟩ :=
    exists_nat_gt (B / ε)
  refine ⟨max 1 (max Mwindow Msize), ?_⟩
  intro M hM L hrun
  have hMposNat : 0 < M :=
    (le_max_left 1 (max Mwindow Msize)).trans hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hMposNat
  have htail : max Mwindow Msize ≤ M :=
    (le_max_right 1 (max Mwindow Msize)).trans hM
  have hw :=
    hwindow M ((le_max_left _ _).trans htail) L hrun
  have hbalance :
      (M : ℝ) / (2 : ℝ) ^ L ≤ B := by
    simpa only [B] using hw.2.2
  have hMsizeR :
      B / ε < (M : ℝ) :=
    hMsize.trans_le (by exact_mod_cast
      (le_max_right Mwindow Msize).trans htail)
  have hBdivM :
      B / (M : ℝ) < ε := by
    apply (div_lt_iff₀ hMpos).2
    have hcross := (div_lt_iff₀ hε).mp hMsizeR
    simpa only [mul_comm] using hcross
  have hroundLe :
      retainedLengthRoundingError M j ≤ 1 :=
    (retainedLengthRoundingError_lt_one M j).le
  have hpowL : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  simp only [abs_div,
    abs_of_nonneg (retainedLengthRoundingError_nonneg M j),
    abs_of_pos hpowL, abs_one, mul_one]
  calc
    retainedLengthRoundingError M j / (2 : ℝ) ^ L ≤
        1 / (2 : ℝ) ^ L :=
      div_le_div_of_nonneg_right hroundLe hpowL.le
    _ = ((M : ℝ) / (2 : ℝ) ^ L) / (M : ℝ) := by
      field_simp [ne_of_gt hMpos]
    _ ≤ B / (M : ℝ) :=
      div_le_div_of_nonneg_right hbalance hMpos.le
    _ ≤ ε := hBdivM.le

/--
The normalized retained length differs from
`(1 - 2^{-j}) M / 2^L` by uniformly `o_C(1)`.
-/
theorem retainedLength_mainTerm_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L =>
        ((M - M / 2 ^ j : ℕ) : ℝ) / (2 : ℝ) ^ L -
          (1 - (1 / 2 : ℝ) ^ j) *
            (M : ℝ) / (2 : ℝ) ^ L)
      (fun _ _ => 1) := by
  simpa only [
    retainedLength_normalized_sub_main_eq_roundingError] using
    (retainedLengthRoundingError_div_twoPow_uniformLittleOOne
      hC j)

/-- Uniform little-oh is stable under pointwise negation. -/
theorem uniformLittleOOn_neg
    {admissible : ℕ → ℕ → Prop}
    {f scale : ℕ → ℕ → ℝ}
    (hf : UniformLittleOOn admissible f scale) :
    UniformLittleOOn admissible
      (fun M L => -f M L) scale := by
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hf ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L hML
  simpa only [abs_neg] using hM₀ M hM L hML

/--
Closure form for the retained conditional mean.  If `badCorrection` is the
normalized bad-start contribution and is uniformly `o_C(1)`, then subtracting
it from the exact retained length preserves the main term
`(1 - 2^{-j}) M / 2^L`.
-/
theorem retainedMeanMainTerm_of_badCorrection
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ)
    (badCorrection : ℕ → ℕ → ℝ)
    (hbad :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        badCorrection (fun _ _ => 1)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L =>
        ((M - M / 2 ^ j : ℕ) : ℝ) / (2 : ℝ) ^ L -
          badCorrection M L -
          (1 - (1 / 2 : ℝ) ^ j) *
            (M : ℝ) / (2 : ℝ) ^ L)
      (fun _ _ => 1) := by
  have hround := retainedLength_mainTerm_uniformLittleOOne hC j
  have hsum :=
    PropositionElevenTwo.uniformLittleOOn_add
      hround (uniformLittleOOn_neg hbad)
  convert hsum using 1
  funext M L
  ring

end

end BoundedRatioSteinChenRates
end PaperC
