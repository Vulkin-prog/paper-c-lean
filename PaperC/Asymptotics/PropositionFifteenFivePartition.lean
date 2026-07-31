import PaperC.Asymptotics.PropositionFifteenFiveClosure
import PaperC.Asymptotics.CriticalChannelPowers
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 1600000

/-!
# Proposition 15.5: the literal finite dyadic partition

This module closes the finite bookkeeping gap between the literal interval
`[2, M / 2^j₀)` and the block estimates proved in
`PropositionFifteenFive`.  Above `2 L²` we use the adjacent blocks

`[(2L²+1)2^k, (2L²+1)2^(k+1))`.

The use of the base `2L²+1` makes the low and high pieces disjoint and
avoids every endpoint ambiguity caused by natural-number division.
-/

namespace PaperC
namespace PropositionFifteenFivePartition

open scoped BigOperators Topology
open Filter

noncomputable section

/-- First integer strictly above the low-height range `x ≤ 2L²`. -/
def highDyadicBase (L : ℕ) : ℕ :=
  2 * L ^ 2 + 1

/-- The `k`-th adjacent block above the low-height range. -/
def highDyadicBlock (L k : ℕ) : Finset ℕ :=
  Finset.Ico
    (highDyadicBase L * 2 ^ k)
    (highDyadicBase L * 2 ^ (k + 1))

/-- Blocks which begin below the literal truncation endpoint. -/
def activeDyadicIndices (M L j₀ J : ℕ) : Finset ℕ :=
  (Finset.range J).filter
    (fun k ↦ highDyadicBase L * 2 ^ k < M / 2 ^ j₀)

theorem highDyadicBase_pos (L : ℕ) :
    0 < highDyadicBase L := by
  unfold highDyadicBase
  omega

theorem highDyadicBlock_eq_manuscriptBlock (L k : ℕ) :
    highDyadicBlock L k =
      Finset.Ico
        (highDyadicBase L * 2 ^ k)
        (2 * (highDyadicBase L * 2 ^ k)) := by
  unfold highDyadicBlock
  congr 1
  rw [pow_succ]
  ring

/-- The adjacent high blocks are pairwise disjoint. -/
theorem highDyadicBlocks_pairwiseDisjoint (L : ℕ) :
    Pairwise
      (fun k l : ℕ ↦ Disjoint (highDyadicBlock L k)
        (highDyadicBlock L l)) := by
  intro k l hkl
  have hforward :
      ∀ {a b : ℕ}, a < b →
        Disjoint (highDyadicBlock L a)
          (highDyadicBlock L b) := by
    intro a b hab
    apply Finset.disjoint_left.2
    intro x hxa hxb
    have hxa' := Finset.mem_Ico.mp hxa
    have hxb' := Finset.mem_Ico.mp hxb
    have hpow :
        highDyadicBase L * 2 ^ (a + 1) ≤
          highDyadicBase L * 2 ^ b := by
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact (hxa'.2.trans_le hpow).not_le hxb'.1
  rcases lt_or_gt_of_ne hkl with horder | horder
  · exact hforward horder
  · exact (hforward horder).symm

/--
Every integer between the high base and the cutoff belongs to a unique
adjacent dyadic block.  This is the endpoint-safe finite partition lemma.
-/
theorem mem_activeDyadicBlock_of_mem_highRange
    {M L j₀ J x : ℕ}
    (hcutoff :
      M / 2 ^ j₀ ≤ highDyadicBase L * 2 ^ J)
    (hxLower : highDyadicBase L ≤ x)
    (hxUpper : x < M / 2 ^ j₀) :
    ∃ k ∈ activeDyadicIndices M L j₀ J,
      x ∈ highDyadicBlock L k := by
  let q := x / highDyadicBase L
  let k := Nat.log 2 q
  have hbasePos : 0 < highDyadicBase L :=
    highDyadicBase_pos L
  have hqPos : 0 < q := by
    dsimp only [q]
    exact (Nat.one_le_div_iff hbasePos).2 hxLower
  have hxEndpoint :
      x < 2 ^ J * highDyadicBase L := by
    calc
      x < M / 2 ^ j₀ := hxUpper
      _ ≤ highDyadicBase L * 2 ^ J := hcutoff
      _ = 2 ^ J * highDyadicBase L := by
        rw [Nat.mul_comm]
  have hqJ : q < 2 ^ J := by
    exact (Nat.div_lt_iff_lt_mul hbasePos).2 hxEndpoint
  have hkJ : k < J := by
    dsimp only [k]
    exact Nat.log_lt_of_lt_pow hqPos.ne' hqJ
  have hpowLower : 2 ^ k ≤ q := by
    dsimp only [k]
    exact Nat.pow_log_le_self 2 hqPos.ne'
  have hblockLower :
      highDyadicBase L * 2 ^ k ≤ x := by
    calc
      highDyadicBase L * 2 ^ k ≤
          highDyadicBase L * q :=
        Nat.mul_le_mul_left _ hpowLower
      _ = q * highDyadicBase L := by
        rw [Nat.mul_comm]
      _ ≤ x := Nat.div_mul_le_self _ _
  have hpowUpper : q < 2 ^ (k + 1) := by
    dsimp only [k]
    simpa only [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
  have hblockUpper :
      x < highDyadicBase L * 2 ^ (k + 1) := by
    have :=
      (Nat.div_lt_iff_lt_mul hbasePos).1 hpowUpper
    simpa only [Nat.mul_comm] using this
  have hactive :
      k ∈ activeDyadicIndices M L j₀ J := by
    rw [activeDyadicIndices, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨hkJ, hblockLower.trans_lt hxUpper⟩
  refine ⟨k, hactive, ?_⟩
  exact Finset.mem_Ico.mpr ⟨hblockLower, hblockUpper⟩

/--
The sum of the left endpoints of all active blocks is at most twice the
literal cutoff.  This is the geometric-series estimate in a form that is
immune to floors.
-/
theorem sum_activeDyadicBases_le_cutoff
    (M L j₀ J : ℕ) :
    (∑ k ∈ activeDyadicIndices M L j₀ J,
        highDyadicBase L * 2 ^ k) ≤
      2 * (M / 2 ^ j₀) := by
  classical
  let active := activeDyadicIndices M L j₀ J
  let blocks := fun k : ℕ ↦ highDyadicBlock L k
  have hpairwise :
      (active : Set ℕ).PairwiseDisjoint blocks := by
    intro k hk l hl hkl
    exact highDyadicBlocks_pairwiseDisjoint L hkl
  have hcardBlock (k : ℕ) :
      (blocks k).card = highDyadicBase L * 2 ^ k := by
    dsimp only [blocks]
    rw [highDyadicBlock_eq_manuscriptBlock, Nat.card_Ico]
    omega
  have hunionSubset :
      active.biUnion blocks ⊆
        Finset.range (2 * (M / 2 ^ j₀)) := by
    intro x hx
    obtain ⟨k, hkActive, hxBlock⟩ :=
      Finset.mem_biUnion.mp hx
    have hkCutoff :
        highDyadicBase L * 2 ^ k < M / 2 ^ j₀ := by
      change k ∈ activeDyadicIndices M L j₀ J at hkActive
      exact (Finset.mem_filter.mp hkActive).2
    have hxUpper :=
      (Finset.mem_Ico.mp
        (by simpa only [blocks] using hxBlock)).2
    rw [Finset.mem_range]
    calc
      x < highDyadicBase L * 2 ^ (k + 1) := hxUpper
      _ = 2 * (highDyadicBase L * 2 ^ k) := by
        rw [pow_succ]
        ring
      _ ≤ 2 * (M / 2 ^ j₀) :=
        Nat.mul_le_mul_left 2 hkCutoff.le
  calc
    (∑ k ∈ activeDyadicIndices M L j₀ J,
        highDyadicBase L * 2 ^ k) =
        ∑ k ∈ active, (blocks k).card := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcardBlock]
    _ = (active.biUnion blocks).card := by
      exact (Finset.card_biUnion hpairwise).symm
    _ ≤ (Finset.range (2 * (M / 2 ^ j₀))).card :=
      Finset.card_le_card hunionSubset
    _ = 2 * (M / 2 ^ j₀) := Finset.card_range _

/--
Literal finite partition of the probability mass.

No asymptotics enter here: if the final adjacent block reaches the cutoff,
the low interval plus the active blocks cover every start in the exact
`Finset.Ico` defining `deepStartProbabilityMass`.
-/
theorem deepStartProbabilityMass_le_low_add_blocks
    {M L j₀ J : ℕ}
    (hcutoff :
      M / 2 ^ j₀ ≤ highDyadicBase L * 2 ^ J) :
    PropositionFifteenFiveClosure.deepStartProbabilityMass M L j₀ ≤
      PropositionFifteenFiveClosure.lowHeightProbabilityMass L +
        ∑ k ∈ activeDyadicIndices M L j₀ J,
          PropositionFifteenFive.highBlockProbabilityMass
            (highDyadicBase L * 2 ^ k) L := by
  classical
  let target := Finset.Ico 2 (M / 2 ^ j₀)
  let low := Finset.Icc 2 (2 * L ^ 2)
  let active := activeDyadicIndices M L j₀ J
  let blocks := fun k : ℕ ↦ highDyadicBlock L k
  let probability :=
    fun x : ℕ ↦ PropositionFifteenFive.globalStartProbability L x
  have hpairwise :
      (active : Set ℕ).PairwiseDisjoint blocks := by
    intro k hk l hl hkl
    exact highDyadicBlocks_pairwiseDisjoint L hkl
  have hcover : target ⊆ low ∪ active.biUnion blocks := by
    intro x hx
    have hxTarget : 2 ≤ x ∧ x < M / 2 ^ j₀ := by
      simpa only [target, Finset.mem_Ico] using hx
    by_cases hxLow : x ≤ 2 * L ^ 2
    · apply Finset.mem_union_left
      simpa only [low, Finset.mem_Icc] using
        ⟨hxTarget.1, hxLow⟩
    · apply Finset.mem_union_right
      have hxBase : highDyadicBase L ≤ x := by
        unfold highDyadicBase
        omega
      obtain ⟨k, hkActive, hxBlock⟩ :=
        mem_activeDyadicBlock_of_mem_highRange
          hcutoff hxBase hxTarget.2
      exact Finset.mem_biUnion.mpr
        ⟨k, by simpa only [active] using hkActive,
          by simpa only [blocks] using hxBlock⟩
  have hnonneg (x : ℕ) : 0 ≤ probability x :=
    PropositionFifteenFive.globalStartProbability_nonneg L x
  have htarget :
      (∑ x ∈ target, probability x) ≤
        ∑ x ∈ low ∪ active.biUnion blocks, probability x :=
    Finset.sum_le_sum_of_subset_of_nonneg hcover
      (fun x _ _ ↦ hnonneg x)
  have hunion :
      (∑ x ∈ low ∪ active.biUnion blocks, probability x) ≤
        (∑ x ∈ low, probability x) +
          ∑ x ∈ active.biUnion blocks, probability x := by
    rw [show low ∪ active.biUnion blocks =
        low ∪ (active.biUnion blocks \ low) by
      ext x
      simp]
    rw [Finset.sum_union Finset.disjoint_sdiff]
    exact add_le_add_left
      (Finset.sum_le_sum_of_subset_of_nonneg
        Finset.sdiff_subset (fun x _ _ ↦ hnonneg x)) _
  have hblocks :
      (∑ x ∈ active.biUnion blocks, probability x) =
        ∑ k ∈ active,
          PropositionFifteenFive.highBlockProbabilityMass
            (highDyadicBase L * 2 ^ k) L := by
    rw [Finset.sum_biUnion hpairwise]
    apply Finset.sum_congr rfl
    intro k hk
    unfold PropositionFifteenFive.highBlockProbabilityMass
    rw [← highDyadicBlock_eq_manuscriptBlock]
  unfold PropositionFifteenFiveClosure.deepStartProbabilityMass
  unfold PropositionFifteenFiveClosure.lowHeightProbabilityMass
  change (∑ x ∈ target, probability x) ≤ _
  calc
    (∑ x ∈ target, probability x) ≤
        ∑ x ∈ low ∪ active.biUnion blocks, probability x := htarget
    _ ≤
        (∑ x ∈ low, probability x) +
          ∑ x ∈ active.biUnion blocks, probability x := hunion
    _ =
        (∑ x ∈ low, probability x) +
          ∑ k ∈ active,
            PropositionFifteenFive.highBlockProbabilityMass
              (highDyadicBase L * 2 ^ k) L := by
      rw [hblocks]
    _ = _ := by rfl

/--
Deterministic assembly of uniform block bounds.  The baseline terms sum to
at most `4 floor(M/2^j₀) / 2^L`, while at most `J` exceptional envelopes
are paid.
-/
theorem deepStartProbabilityMass_le_low_add_baseline_add_exceptional
    {M L j₀ J : ℕ} {E : ℝ}
    (hcutoff :
      M / 2 ^ j₀ ≤ highDyadicBase L * 2 ^ J)
    (hE : 0 ≤ E)
    (hblock :
      ∀ k ∈ activeDyadicIndices M L j₀ J,
        PropositionFifteenFive.highBlockProbabilityMass
            (highDyadicBase L * 2 ^ k) L ≤
          ((highDyadicBase L * 2 ^ k : ℕ) : ℝ) *
              (2 / (2 : ℝ) ^ L) + E) :
    PropositionFifteenFiveClosure.deepStartProbabilityMass M L j₀ ≤
      PropositionFifteenFiveClosure.lowHeightProbabilityMass L +
        4 * ((M / 2 ^ j₀ : ℕ) : ℝ) / (2 : ℝ) ^ L +
        (J : ℝ) * E := by
  have hpartition :=
    deepStartProbabilityMass_le_low_add_blocks hcutoff
  have hsum :
      (∑ k ∈ activeDyadicIndices M L j₀ J,
          PropositionFifteenFive.highBlockProbabilityMass
            (highDyadicBase L * 2 ^ k) L) ≤
        4 * ((M / 2 ^ j₀ : ℕ) : ℝ) / (2 : ℝ) ^ L +
          (J : ℝ) * E := by
    calc
      (∑ k ∈ activeDyadicIndices M L j₀ J,
          PropositionFifteenFive.highBlockProbabilityMass
            (highDyadicBase L * 2 ^ k) L) ≤
          ∑ k ∈ activeDyadicIndices M L j₀ J,
            (((highDyadicBase L * 2 ^ k : ℕ) : ℝ) *
                (2 / (2 : ℝ) ^ L) + E) :=
        Finset.sum_le_sum hblock
      _ =
          ((∑ k ∈ activeDyadicIndices M L j₀ J,
              highDyadicBase L * 2 ^ k : ℕ) : ℝ) *
              (2 / (2 : ℝ) ^ L) +
            ((activeDyadicIndices M L j₀ J).card : ℝ) * E := by
        push_cast
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        simp
      _ ≤
          ((2 * (M / 2 ^ j₀) : ℕ) : ℝ) *
              (2 / (2 : ℝ) ^ L) +
            (J : ℝ) * E := by
        gcongr
        · exact_mod_cast sum_activeDyadicBases_le_cutoff M L j₀ J
        · have hcard :
              (activeDyadicIndices M L j₀ J).card ≤ J := by
            calc
              (activeDyadicIndices M L j₀ J).card ≤
                  (Finset.range J).card :=
                Finset.card_le_card (by
                  unfold activeDyadicIndices
                  exact Finset.filter_subset _ _)
              _ = J := Finset.card_range J
          exact_mod_cast hcard
      _ =
          4 * ((M / 2 ^ j₀ : ℕ) : ℝ) / (2 : ℝ) ^ L +
            (J : ℝ) * E := by
        push_cast
        ring
  linarith

/-- The exceptional summand in the block estimate is exactly the envelope
used in `PropositionFifteenFiveDecay`. -/
theorem exceptionalBlockTerm_eq
    (K θ : ℝ) (L : ℕ) :
    Real.exp (K * ((L : ℝ) / Real.log (L : ℝ))) *
          ((2 : ℝ) ^
              (((L + 1 : ℕ) : ℝ) -
                BalasubramanianShoreyInput.gap (L + 1) θ) /
            (2 : ℝ) ^ L) =
      Real.exp (K * ((L : ℝ) / Real.log (L : ℝ))) *
        (2 : ℝ) ^
          (1 - BalasubramanianShoreyInput.gap (L + 1) θ) := by
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

/--
The literal floor in the cutoff costs no constant: after division by
`2^L`, it is bounded by the critical balance times `2⁻ʲ⁰`.
-/
theorem four_cutoff_div_pow_le_criticalTail
    {C : ℝ} {M L j₀ : ℕ}
    (hbalance :
      (M : ℝ) / (2 : ℝ) ^ L ≤
        CriticalRunWindow.balanceConstant C) :
    4 * ((M / 2 ^ j₀ : ℕ) : ℝ) / (2 : ℝ) ^ L ≤
      (4 * CriticalRunWindow.balanceConstant C) *
        (1 / 2 : ℝ) ^ j₀ := by
  have hpowj : (0 : ℝ) < (2 : ℝ) ^ j₀ := by positivity
  have hpowL : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hfloor :
      ((M / 2 ^ j₀ : ℕ) : ℝ) ≤
        (M : ℝ) / (2 : ℝ) ^ j₀ := by
    rw [le_div_iff₀ hpowj]
    norm_cast
    exact Nat.div_mul_le_self M (2 ^ j₀)
  calc
    4 * ((M / 2 ^ j₀ : ℕ) : ℝ) / (2 : ℝ) ^ L ≤
        4 * ((M : ℝ) / (2 : ℝ) ^ j₀) /
          (2 : ℝ) ^ L := by
      gcongr
    _ =
        4 * ((M : ℝ) / (2 : ℝ) ^ L) *
          (1 / 2 : ℝ) ^ j₀ := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      simp only [div_eq_mul_inv, one_div, inv_pow]
      ring
    _ ≤
        4 * CriticalRunWindow.balanceConstant C *
          (1 / 2 : ℝ) ^ j₀ := by
      gcongr
    _ =
        (4 * CriticalRunWindow.balanceConstant C) *
          (1 / 2 : ℝ) ^ j₀ := by ring

/--
Eventually `2L` adjacent blocks reach past `M`.  This is the precise use of
the critical-window balance in the finite partition.
-/
theorem two_mul_runLength_blocks_cover_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C M L →
      M ≤ highDyadicBase L * 2 ^ (2 * L) := by
  obtain ⟨Mbalance, hbalance⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  have hpowers :
      Tendsto (fun L : ℕ ↦ (2 : ℝ) ^ L) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨Lpower, hLpower⟩ :=
    eventually_atTop.mp
      (hpowers.eventually
        (eventually_ge_atTop
          (CriticalRunWindow.balanceConstant C)))
  obtain ⟨Mlength, hlength⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC (Lpower + 1)
  refine ⟨max 1 (max Mbalance Mlength), ?_⟩
  intro M hM L hrun
  have hMpos : 0 < M := by
    exact (le_trans (le_max_left 1 (max Mbalance Mlength)) hM)
  have hMbalance : Mbalance ≤ M :=
    (le_trans (le_max_left Mbalance Mlength)
      (le_max_right 1 (max Mbalance Mlength))).trans hM
  have hMlength : Mlength ≤ M :=
    (le_trans (le_max_right Mbalance Mlength)
      (le_max_right 1 (max Mbalance Mlength))).trans hM
  have hLthreshold : Lpower ≤ L := by
    have := hlength M hMlength L hrun
    omega
  have hbalanceML :
      (M : ℝ) / (2 : ℝ) ^ L ≤
        CriticalRunWindow.balanceConstant C :=
    (hbalance M hMbalance L hrun).2.2
  have hconstant :
      CriticalRunWindow.balanceConstant C ≤ (2 : ℝ) ^ L :=
    hLpower L hLthreshold
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hMreal :
      (M : ℝ) ≤ (2 : ℝ) ^ (2 * L) := by
    calc
      (M : ℝ) =
          ((M : ℝ) / (2 : ℝ) ^ L) * (2 : ℝ) ^ L := by
        field_simp
      _ ≤
          CriticalRunWindow.balanceConstant C *
            (2 : ℝ) ^ L :=
        mul_le_mul_of_nonneg_right hbalanceML hpowPos.le
      _ ≤ (2 : ℝ) ^ L * (2 : ℝ) ^ L :=
        mul_le_mul_of_nonneg_right hconstant hpowPos.le
      _ = (2 : ℝ) ^ (2 * L) := by
        rw [← pow_add]
        congr 1
        omega
  have hMnat : M ≤ 2 ^ (2 * L) := by
    exact_mod_cast hMreal
  calc
    M ≤ 2 ^ (2 * L) := hMnat
    _ ≤ highDyadicBase L * 2 ^ (2 * L) := by
      exact Nat.le_mul_of_pos_left _
        (highDyadicBase_pos L)

/-- Multiplying the high-zone envelope by the harmless constant two
preserves its uniform little-oh estimate. -/
theorem twice_highZoneExceptionalEnvelope_uniformLittleOOne
    {C θ K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L ↦
        2 *
          ((L : ℝ) *
            Real.exp
              (K * (L : ℝ) / Real.log (L : ℝ)) *
            (2 : ℝ) ^
              (1 -
                BalasubramanianShoreyInput.gap (L + 1) θ)))
      (fun _ _ ↦ 1) := by
  intro ε hε
  obtain ⟨M₀, hM₀⟩ :=
    PropositionFifteenFiveClosure.highZoneExceptionalEnvelope_uniformLittleOOne
      (θ := θ) hC hK (ε / 2) (by positivity)
  refine ⟨M₀, ?_⟩
  intro M hM L hrun
  have hbound := hM₀ M hM L hrun
  simp only [abs_one, mul_one] at hbound ⊢
  rw [abs_mul]
  norm_num
  linarith

/-- The sum of the low and high remainders is still uniform little-oh. -/
theorem completeRemainder_uniformLittleOOne
    {C θ K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hLS : LaishramShoreyInput.LaishramShoreyStatement)
    (hpnt : PrimeNumberTheoremInput.PrimeNumberTheoremStatement) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L ↦
        PropositionFifteenFiveClosure.lowPolynomialRemainder L +
          2 *
            ((L : ℝ) *
              Real.exp
                (K * (L : ℝ) / Real.log (L : ℝ)) *
              (2 : ℝ) ^
                (1 -
                  BalasubramanianShoreyInput.gap (L + 1) θ)))
      (fun _ _ ↦ 1) := by
  have hlow :=
    PropositionFifteenFiveClosure.lowPolynomialRemainder_uniformLittleOOne
      hC hLS hpnt
  have hhigh :=
    twice_highZoneExceptionalEnvelope_uniformLittleOOne
      (θ := θ) hC hK
  intro ε hε
  obtain ⟨Mlow, hMlow⟩ :=
    hlow (ε / 2) (by positivity)
  obtain ⟨Mhigh, hMhigh⟩ :=
    hhigh (ε / 2) (by positivity)
  refine ⟨max Mlow Mhigh, ?_⟩
  intro M hM L hrun
  have hlowBound :=
    hMlow M ((le_max_left Mlow Mhigh).trans hM) L hrun
  have hhighBound :=
    hMhigh M ((le_max_right Mlow Mhigh).trans hM) L hrun
  simp only [abs_one, mul_one] at hlowBound hhighBound ⊢
  calc
    |PropositionFifteenFiveClosure.lowPolynomialRemainder L +
        2 *
          ((L : ℝ) *
            Real.exp
              (K * (L : ℝ) / Real.log (L : ℝ)) *
            (2 : ℝ) ^
              (1 -
                BalasubramanianShoreyInput.gap (L + 1) θ))| ≤
        |PropositionFifteenFiveClosure.lowPolynomialRemainder L| +
          |2 *
            ((L : ℝ) *
              Real.exp
                (K * (L : ℝ) / Real.log (L : ℝ)) *
              (2 : ℝ) ^
                (1 -
                  BalasubramanianShoreyInput.gap (L + 1) θ))| :=
      abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 :=
      add_le_add hlowBound hhighBound
    _ = ε := by ring

/--
Proposition 15.5, with exactly the four manuscript inputs used by its proof.

The conclusion concerns the literal finite-cylinder probabilities and the
ordered double limit from the paper.  The finite interval is partitioned
inside Lean, so no additional decomposition hypothesis or audit bridge is
present.
-/
theorem proposition_fifteen_five
    {C : ℝ} (hC : 0 ≤ C)
    (hpnt : PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS : LaishramShoreyInput.LaishramShoreyStatement)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (hBS :
      BalasubramanianShoreyInput.BalasubramanianShoreyStatement) :
    PropositionFifteenFiveClosure.PropositionFifteenFiveStatement C := by
  obtain ⟨K, hK, θ, Mhigh, hhigh⟩ :=
    PropositionFifteenFive.highBlockProbabilityMass_le_uniform_height_range
      hC hpnt hPell hBS
  obtain ⟨Mcover, hcover⟩ :=
    two_mul_runLength_blocks_cover_eventually hC
  obtain ⟨Mbalance, hbalance⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Mlength, hlength⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity hC 4
  let envelope : ℕ → ℝ :=
    fun L ↦
      (L : ℝ) *
        Real.exp
          (K * (L : ℝ) / Real.log (L : ℝ)) *
        (2 : ℝ) ^
          (1 -
            BalasubramanianShoreyInput.gap (L + 1) θ)
  let remainder : ℕ → ℕ → ℝ :=
    fun _ L ↦
      PropositionFifteenFiveClosure.lowPolynomialRemainder L +
        2 * envelope L
  let D : ℝ := 4 * CriticalRunWindow.balanceConstant C
  apply PropositionFifteenFiveClosure.proposition_fifteen_five_of_eventual_uniformLittleO_remainder
      (C := C) (D := D) (remainder := remainder)
  · dsimp only [D]
    exact mul_nonneg (by norm_num)
      (CriticalRunWindow.balanceConstant_nonneg C)
  · refine ⟨max Mhigh (max Mcover (max Mbalance Mlength)), ?_⟩
    intro M hM L j₀ hrun
    have hMhigh : Mhigh ≤ M :=
      (le_max_left Mhigh
        (max Mcover (max Mbalance Mlength))).trans hM
    have hMcover : Mcover ≤ M :=
      (le_trans
        (le_max_left Mcover (max Mbalance Mlength))
        (le_max_right Mhigh
          (max Mcover (max Mbalance Mlength)))).trans hM
    have hMbalance : Mbalance ≤ M :=
      (le_trans
        (le_trans
          (le_max_left Mbalance Mlength)
          (le_max_right Mcover (max Mbalance Mlength)))
        (le_max_right Mhigh
          (max Mcover (max Mbalance Mlength)))).trans hM
    have hMlength : Mlength ≤ M :=
      (le_trans
        (le_trans
          (le_max_right Mbalance Mlength)
          (le_max_right Mcover (max Mbalance Mlength)))
        (le_max_right Mhigh
          (max Mcover (max Mbalance Mlength)))).trans hM
    have hLthree : 3 ≤ L := by
      have := hlength M hMlength L hrun
      omega
    have hcoverM :
        M ≤ highDyadicBase L * 2 ^ (2 * L) :=
      hcover M hMcover L hrun
    have hcutoff :
        M / 2 ^ j₀ ≤ highDyadicBase L * 2 ^ (2 * L) :=
      (Nat.div_le_self M _).trans hcoverM
    let E : ℝ :=
      Real.exp (K * ((L : ℝ) / Real.log (L : ℝ))) *
        ((2 : ℝ) ^
            (((L + 1 : ℕ) : ℝ) -
              BalasubramanianShoreyInput.gap (L + 1) θ) /
          (2 : ℝ) ^ L)
    have hE : 0 ≤ E := by
      dsimp only [E]
      positivity
    have hassembly :=
      deepStartProbabilityMass_le_low_add_baseline_add_exceptional
        (M := M) (L := L) (j₀ := j₀) (J := 2 * L)
        (E := E) hcutoff hE
        (by
          intro k hk
          have hkCutoff :
              highDyadicBase L * 2 ^ k < M / 2 ^ j₀ :=
            (Finset.mem_filter.mp hk).2
          have hNlower :
              2 * L ^ 2 ≤ highDyadicBase L * 2 ^ k := by
            calc
              2 * L ^ 2 ≤ highDyadicBase L := by
                unfold highDyadicBase
                omega
              _ ≤ highDyadicBase L * 2 ^ k := by
                exact Nat.le_mul_of_pos_right _
                  (pow_pos (by norm_num) k)
          have hNupper :
              highDyadicBase L * 2 ^ k ≤ M :=
            hkCutoff.le.trans
              ((Nat.div_le_self M _).trans (le_refl M))
          exact hhigh M hMhigh L hrun
            (highDyadicBase L * 2 ^ k) hNlower hNupper)
    have hlow :
        PropositionFifteenFiveClosure.lowHeightProbabilityMass L ≤
          PropositionFifteenFiveClosure.lowPolynomialRemainder L :=
      PropositionFifteenFiveClosure.lowHeightProbabilityMass_le_lowPolynomialRemainder
        hLthree
    have hbalanceML :
        (M : ℝ) / (2 : ℝ) ^ L ≤
          CriticalRunWindow.balanceConstant C :=
      (hbalance M hMbalance L hrun).2.2
    have hbaseline :
        4 * ((M / 2 ^ j₀ : ℕ) : ℝ) / (2 : ℝ) ^ L ≤
          D * (1 / 2 : ℝ) ^ j₀ := by
      exact four_cutoff_div_pow_le_criticalTail hbalanceML
    have hexceptional :
        ((2 * L : ℕ) : ℝ) * E = 2 * envelope L := by
      dsimp only [E, envelope]
      rw [exceptionalBlockTerm_eq]
      push_cast
      ring
    dsimp only [remainder]
    rw [hexceptional] at hassembly
    linarith
  · dsimp only [remainder, envelope]
    exact completeRemainder_uniformLittleOOne hC hK hLS hpnt

end

end PropositionFifteenFivePartition
end PaperC
