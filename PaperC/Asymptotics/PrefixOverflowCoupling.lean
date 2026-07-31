import PaperC.Asymptotics.CorollaryPrefixLaw
import PaperC.Asymptotics.MaskedFirstMomentCritical
import PaperC.Asymptotics.PrefixBoundaryProbability

/-!
# Coupling the finite-prefix count to the global interior count

The prefix observable stops admitting starts at `M - L + 1`, whereas the
global count of Theorem 16.2 keeps every start `x < M`.  This file isolates
that deterministic comparison on their common finite prime cylinder.  The
only possible discrepancies are the special left-boundary indicator and a
start in the overflowing mask `[M-L+2,M)`.
-/

namespace PaperC
namespace PrefixOverflowCoupling

open scoped BigOperators

open CorollaryPrefixLaw
open ConditionalAGGAverage
open ArratiaGoldsteinGordonInput
open FiniteCylinderCountTransport
open MaskedFirstMoment
open SectionThirteenCouplings
open SectionThirteenFiniteBound
open TheoremSixteenTwo

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Starts counted globally whose length-`L` window overflows the prefix. -/
def prefixOverflowStartIndices (M L : ℕ) : Finset ℕ :=
  Finset.Ico (M - L + 2) M

/-- The prefix count evaluated on the same cylinder as the global count. -/
def finitePrefixStartCount
    (M L : ℕ)
    (ω : SampleSpace (globalCylinderCutoff M L)) : ℕ :=
  prefixStartCount (valueBit ω) M L

/-- Probability of the special left-boundary event on the global cylinder. -/
def finitePrefixBoundaryProbability (M L : ℕ) : ℝ :=
  eventProbability (globalUniformPMF M L)
    (fun ω ↦ prefixBoundaryEvent (valueBit ω) L)

/-- First-moment mass of all overflowing starts on the global cylinder. -/
def prefixOverflowStartProbabilityMass (M L : ℕ) : ℝ :=
  ∑ x ∈ prefixOverflowStartIndices M L,
    commonCylinderStartProbability M L x

theorem prefixOverflowStartProbabilityMass_nonneg (M L : ℕ) :
    0 ≤ prefixOverflowStartProbabilityMass M L := by
  unfold prefixOverflowStartProbabilityMass commonCylinderStartProbability
  exact Finset.sum_nonneg fun x _hx ↦ eventProbability_nonneg _ _

theorem prefixInteriorStartIndices_subset_globalStartIndices
    {M L : ℕ} (hL : 2 ≤ L) :
    prefixInteriorStartIndices M L ⊆ globalStartIndices M := by
  intro x hx
  simp only [prefixInteriorStartIndices, globalStartIndices,
    Finset.mem_Ico] at hx ⊢
  omega

/-- If neither exceptional event occurs, the two coupled counts coincide. -/
theorem finitePrefixStartCount_eq_globalStartCount_of_no_exceptions
    {M L : ℕ} (hL : 2 ≤ L)
    (ω : SampleSpace (globalCylinderCutoff M L))
    (hboundary : ¬ prefixBoundaryEvent (valueBit ω) L)
    (hoverflow :
      ∀ x ∈ prefixOverflowStartIndices M L,
        ¬ startAt ω x L) :
    finitePrefixStartCount M L ω = globalStartCount M L ω := by
  classical
  unfold finitePrefixStartCount prefixStartCount globalStartCount
  rw [if_neg hboundary, zero_add]
  apply Finset.sum_subset
    (prefixInteriorStartIndices_subset_globalStartIndices hL)
  intro x hxGlobal hxNotPrefix
  have hxOverflow : x ∈ prefixOverflowStartIndices M L := by
    simp only [prefixOverflowStartIndices, globalStartIndices,
      prefixInteriorStartIndices, Finset.mem_Ico] at hxGlobal hxNotPrefix ⊢
    omega
  rw [if_neg (by
    simpa only [startAt] using hoverflow x hxOverflow)]

/-- A pointwise disagreement has one of the two advertised witnesses. -/
theorem boundary_or_overflow_start_of_finitePrefix_ne_global
    {M L : ℕ} (hL : 2 ≤ L)
    {ω : SampleSpace (globalCylinderCutoff M L)}
    (hne : finitePrefixStartCount M L ω ≠ globalStartCount M L ω) :
    prefixBoundaryEvent (valueBit ω) L ∨
      ∃ x ∈ prefixOverflowStartIndices M L, startAt ω x L := by
  classical
  by_contra h
  push Not at h
  exact hne
    (finitePrefixStartCount_eq_globalStartCount_of_no_exceptions
      hL ω h.1 h.2)

/-- Union bound for the finite-cylinder coupling error. -/
theorem disagreementProbability_finitePrefix_global_le
    {M L : ℕ} (hL : 2 ≤ L) :
    disagreementProbability
        (globalUniformPMF M L)
        (finitePrefixStartCount M L)
        (globalStartCount M L) ≤
      finitePrefixBoundaryProbability M L +
        prefixOverflowStartProbabilityMass M L := by
  classical
  have hpoint :
      ∀ ω : SampleSpace (globalCylinderCutoff M L),
        (if finitePrefixStartCount M L ω ≠ globalStartCount M L ω then
            (globalUniformPMF M L).prob ω
          else 0) ≤
          (if prefixBoundaryEvent (valueBit ω) L then
              (globalUniformPMF M L).prob ω
            else 0) +
          ∑ x ∈ prefixOverflowStartIndices M L,
            if startAt ω x L then
              (globalUniformPMF M L).prob ω
            else 0 := by
    intro ω
    by_cases hne :
        finitePrefixStartCount M L ω ≠ globalStartCount M L ω
    · rw [if_pos hne]
      rcases boundary_or_overflow_start_of_finitePrefix_ne_global hL hne with
        hboundary | ⟨x, hxOverflow, hxStart⟩
      · rw [if_pos hboundary]
        exact le_add_of_nonneg_right
          (Finset.sum_nonneg fun y _hy ↦ by
            split_ifs
            · exact (globalUniformPMF M L).nonneg ω
            · exact le_rfl)
      · have hsingle :
            (globalUniformPMF M L).prob ω ≤
              ∑ y ∈ prefixOverflowStartIndices M L,
                if startAt ω y L then
                  (globalUniformPMF M L).prob ω
                else 0 := by
          calc
            (globalUniformPMF M L).prob ω =
                (if startAt ω x L then
                  (globalUniformPMF M L).prob ω
                else 0) := by rw [if_pos hxStart]
            _ ≤
                ∑ y ∈ prefixOverflowStartIndices M L,
                  if startAt ω y L then
                    (globalUniformPMF M L).prob ω
                  else 0 := by
              apply Finset.single_le_sum
                (s := prefixOverflowStartIndices M L)
                (f := fun y ↦
                  if startAt ω y L then
                    (globalUniformPMF M L).prob ω
                  else 0)
              · intro y _hy
                split_ifs
                · exact (globalUniformPMF M L).nonneg ω
                · exact le_rfl
              · exact hxOverflow
        exact hsingle.trans (le_add_of_nonneg_left
          (by
            split_ifs
            · exact (globalUniformPMF M L).nonneg ω
            · exact le_rfl))
    · rw [if_neg hne]
      exact add_nonneg
        (by
          split_ifs
          · exact (globalUniformPMF M L).nonneg ω
          · exact le_rfl)
        (Finset.sum_nonneg fun x _hx ↦ by
          split_ifs
          · exact (globalUniformPMF M L).nonneg ω
          · exact le_rfl)
  unfold disagreementProbability finitePrefixBoundaryProbability
    prefixOverflowStartProbabilityMass commonCylinderStartProbability
    eventProbability
  calc
    (∑ ω,
      if finitePrefixStartCount M L ω ≠ globalStartCount M L ω then
        (globalUniformPMF M L).prob ω else 0) ≤
        ∑ ω,
          ((if prefixBoundaryEvent (valueBit ω) L then
              (globalUniformPMF M L).prob ω else 0) +
            ∑ x ∈ prefixOverflowStartIndices M L,
              if startAt ω x L then
                (globalUniformPMF M L).prob ω else 0) :=
      Finset.sum_le_sum fun ω _hω ↦ hpoint ω
    _ =
        (∑ ω,
          if prefixBoundaryEvent (valueBit ω) L then
            (globalUniformPMF M L).prob ω else 0) +
          ∑ x ∈ prefixOverflowStartIndices M L,
            ∑ ω,
              if startAt ω x L then
                (globalUniformPMF M L).prob ω else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]

/-- Total-variation form of the same coupling. -/
theorem natTotalVariation_finitePrefix_global_le
    {M L : ℕ} (hL : 2 ≤ L) :
    natTotalVariation
        (finiteNatLaw (globalUniformPMF M L)
          (finitePrefixStartCount M L))
        (globalStartLaw M L) ≤
      finitePrefixBoundaryProbability M L +
        prefixOverflowStartProbabilityMass M L := by
  exact
    (natTotalVariation_finiteNatLaw_le_disagreement
      (globalUniformPMF M L)
      (finitePrefixStartCount M L)
      (globalStartCount M L)).trans
        (disagreementProbability_finitePrefix_global_le hL)

/-! ## Identification with the masked first moment -/

/-- Once `2(L+1) ≤ M`, the overflowing mask is contained in the dyadic
block based at `M-L+2`. -/
theorem prefixOverflowStartIndices_subset_dyadicBlock
    {M L : ℕ} (htwo : 2 * (L + 1) ≤ M) :
    prefixOverflowStartIndices M L ⊆ dyadicBlock (M - L + 2) := by
  intro x hx
  simp only [prefixOverflowStartIndices, dyadicBlock, Finset.mem_Ico]
    at hx ⊢
  constructor
  · exact hx.1
  · omega

/-- A one-start marginal on the global cylinder is the same marginal used
by Proposition 14.1 at the shifted base `M-L+2`. -/
theorem commonCylinderStartProbability_eq_shiftedStartProbability
    {M L x : ℕ} (hL : 2 ≤ L) (htwo : 2 * (L + 1) ≤ M)
    (hxBlock : x ∈ dyadicBlock (M - L + 2)) :
    commonCylinderStartProbability M L x =
      ((startProbability (M - L + 2) L x : ℚ) : ℝ) := by
  have hbase : M - L + 2 ≤ M := by omega
  have hcutoff :
      dyadicCutoff (M - L + 2) L ≤ globalCylinderCutoff M L := by
    unfold globalCylinderCutoff dyadicCutoff
    omega
  have hxBounds : M - L + 2 ≤ x ∧ x < 2 * (M - L + 2) := by
    simpa only [dyadicBlock, Finset.mem_Ico] using hxBlock
  have hxTwo : 2 ≤ x := by omega
  have hwindow : x + L ≤ dyadicCutoff (M - L + 2) L := by
    unfold dyadicCutoff
    omega
  unfold commonCylinderStartProbability globalUniformPMF startProbability
  rw [eventProbability_fullUniformPMF_eq,
    finiteUniformProbability_eq_uniformEventProbability]
  norm_cast
  exact
    FiniteCylinderCountTransport.uniformEventProbability_startAt_cutoff_invariant
      hcutoff hxTwo hwindow

/-- The overflowing first-moment mass is exactly the masked expectation at
the shifted dyadic base. -/
theorem prefixOverflowStartProbabilityMass_eq_maskedDyadicExpectation
    {M L : ℕ} (hL : 2 ≤ L) (htwo : 2 * (L + 1) ≤ M) :
    prefixOverflowStartProbabilityMass M L =
      ((maskedDyadicExpectation (M - L + 2) L
        (prefixOverflowStartIndices M L) : ℚ) : ℝ) := by
  classical
  unfold prefixOverflowStartProbabilityMass maskedDyadicExpectation
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  exact
    commonCylinderStartProbability_eq_shiftedStartProbability hL htwo
      (prefixOverflowStartIndices_subset_dyadicBlock htwo hx)

/-! ## Transport of the critical window -/

/-- Replacing `M` by `M-L+2` changes the logarithmic centre by at most one
once `2(L+1) ≤ M`. -/
theorem shiftedPrefixBase_inRunLengthWindow
    {C : ℝ} {M L : ℕ} (hL : 2 ≤ L)
    (htwo : 2 * (L + 1) ≤ M)
    (hrun : CriticalRunWindow.InRunLengthWindow C M L) :
    CriticalRunWindow.InRunLengthWindow (C + 1) (M - L + 2) L := by
  let N := M - L + 2
  have hN : 1 ≤ N := by
    dsimp only [N]
    omega
  have hNM : N ≤ M := by
    dsimp only [N]
    omega
  have hMN : M ≤ 2 * N := by
    dsimp only [N]
    omega
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast hN.trans hNM
  have hlogNM : Real.log (N : ℝ) ≤ Real.log (M : ℝ) := by
    apply Real.log_le_log hNpos
    exact_mod_cast hNM
  have hlogUpper :
      Real.log (M : ℝ) ≤ Real.log 2 + Real.log (N : ℝ) := by
    calc
      Real.log (M : ℝ) ≤ Real.log (((2 * N : ℕ) : ℝ)) := by
        apply Real.log_le_log hMpos
        exact_mod_cast hMN
      _ = Real.log 2 + Real.log (N : ℝ) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNpos.ne']
  have hlogDifferenceNonneg :
      0 ≤ Real.log (M : ℝ) / Real.log 2 -
        Real.log (N : ℝ) / Real.log 2 := by
    exact sub_nonneg.mpr
      (div_le_div_of_nonneg_right hlogNM hlogTwo.le)
  have hlogDifferenceLe :
      Real.log (M : ℝ) / Real.log 2 -
          Real.log (N : ℝ) / Real.log 2 ≤ 1 := by
    rw [show
      Real.log (M : ℝ) / Real.log 2 -
          Real.log (N : ℝ) / Real.log 2 =
        (Real.log (M : ℝ) - Real.log (N : ℝ)) /
          Real.log 2 by ring]
    apply (div_le_iff₀ hlogTwo).2
    linarith
  have hlogDifferenceAbs :
      |Real.log (M : ℝ) / Real.log 2 -
          Real.log (N : ℝ) / Real.log 2| ≤ 1 := by
    rw [abs_of_nonneg hlogDifferenceNonneg]
    exact hlogDifferenceLe
  unfold CriticalRunWindow.InRunLengthWindow at hrun ⊢
  dsimp only [N] at *
  rw [show
    (L : ℝ) - Real.log (M - L + 2 : ℕ) / Real.log 2 =
      ((L : ℝ) - Real.log (M : ℕ) / Real.log 2) +
        (Real.log (M : ℕ) / Real.log 2 -
          Real.log (M - L + 2 : ℕ) / Real.log 2) by ring]
  calc
    |((L : ℝ) - Real.log (M : ℕ) / Real.log 2) +
        (Real.log (M : ℕ) / Real.log 2 -
          Real.log (M - L + 2 : ℕ) / Real.log 2)| ≤
        |(L : ℝ) - Real.log (M : ℕ) / Real.log 2| +
          |Real.log (M : ℕ) / Real.log 2 -
            Real.log (M - L + 2 : ℕ) / Real.log 2| :=
      abs_add_le _ _
    _ ≤ C + 1 := add_le_add hrun hlogDifferenceAbs

/-! ## Vanishing of the overflow baseline -/

/-- Geometric main term associated with the overflowing mask. -/
def prefixOverflowBaseline (M L : ℕ) : ℝ :=
  ((prefixOverflowStartIndices M L).card : ℝ) / (2 : ℝ) ^ L

theorem prefixOverflowStartIndices_card_le (M L : ℕ) :
    (prefixOverflowStartIndices M L).card ≤ L := by
  unfold prefixOverflowStartIndices
  rw [Nat.card_Ico]
  omega

theorem prefixOverflowBaseline_nonneg (M L : ℕ) :
    0 ≤ prefixOverflowBaseline M L := by
  unfold prefixOverflowBaseline
  positivity

/-- A convenient explicit majorant: the overflow baseline is at most a
fixed constant times `M⁻¹/²` in the critical window. -/
theorem prefixOverflowBaseline_le_invSqrt
    {C : ℝ} {M L : ℕ} (hM : 0 < M)
    (hwindow :
      CriticalFirstMoment.FirstMomentWindow
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant
        (CriticalRunWindow.balanceConstant C) M L) :
    prefixOverflowBaseline M L ≤
      2 * CriticalRunWindow.upperConstant *
        CriticalRunWindow.balanceConstant C / Real.sqrt M := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogMnonneg : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg hMone
  have hupperPos : 0 < CriticalRunWindow.upperConstant :=
    CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hcard :
      ((prefixOverflowStartIndices M L).card : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast prefixOverflowStartIndices_card_le M L
  have hLupper :
      (L : ℝ) ≤ CriticalRunWindow.upperConstant * Real.log M := by
    have hcriticalUpper := hwindow.1.2.2.2
    norm_num only [Nat.cast_add, Nat.cast_one] at hcriticalUpper
    linarith
  have hlogSqrt :
      Real.log (M : ℝ) ≤ 2 * Real.sqrt M := by
    have h := Real.log_le_rpow_div (Nat.cast_nonneg M)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    norm_num at h ⊢
    linarith
  have hsqrtPos : 0 < Real.sqrt (M : ℝ) :=
    Real.sqrt_pos.2 hMreal
  calc
    prefixOverflowBaseline M L ≤ (L : ℝ) / (2 : ℝ) ^ L := by
      unfold prefixOverflowBaseline
      exact div_le_div_of_nonneg_right hcard hpowPos.le
    _ = ((L : ℝ) / (M : ℝ)) *
        ((M : ℝ) / (2 : ℝ) ^ L) := by
      field_simp
    _ ≤
        (CriticalRunWindow.upperConstant * Real.log M / (M : ℝ)) *
          CriticalRunWindow.balanceConstant C := by
      exact mul_le_mul
        (div_le_div_of_nonneg_right hLupper hMreal.le)
        hwindow.2.2
        (div_nonneg (Nat.cast_nonneg M) hpowPos.le)
        (div_nonneg (mul_nonneg hupperPos.le hlogMnonneg) hMreal.le)
    _ ≤
        (CriticalRunWindow.upperConstant * (2 * Real.sqrt M) /
            (M : ℝ)) *
          CriticalRunWindow.balanceConstant C := by
      apply mul_le_mul_of_nonneg_right _
        (CriticalRunWindow.balanceConstant_nonneg C)
      apply div_le_div_of_nonneg_right _ hMreal.le
      exact mul_le_mul_of_nonneg_left hlogSqrt hupperPos.le
    _ =
        2 * CriticalRunWindow.upperConstant *
          CriticalRunWindow.balanceConstant C / Real.sqrt M := by
      field_simp [hsqrtPos.ne', hMreal.ne']
      rw [Real.sq_sqrt hMreal.le]

/-- A fixed nonnegative constant divided by `sqrt M` tends uniformly to
zero; the auxiliary parameter is irrelevant. -/
theorem const_div_sqrt_uniformLittleOOne
    {admissible : ℕ → ℕ → Prop} {D : ℝ} (hD : 0 ≤ D) :
    UniformLittleOOn admissible
      (fun M _L ↦ D / Real.sqrt M) (fun _ _ ↦ 1) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((D / ε) ^ 2)
  refine ⟨N₀, ?_⟩
  intro M hM L _hrun
  have hthreshold : (D / ε) ^ 2 < (M : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hM)
  have hquotNonneg : 0 ≤ D / ε := div_nonneg hD hε.le
  have hsqrtLower : D / ε < Real.sqrt (M : ℝ) :=
    (Real.lt_sqrt hquotNonneg).2 hthreshold
  have hMpos : (0 : ℝ) < M := by
    have : (0 : ℝ) < (M : ℝ) :=
      (sq_nonneg (D / ε)).trans_lt hthreshold
    exact this
  have hsqrtPos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 hMpos
  have hsmall : D / Real.sqrt (M : ℝ) < ε := by
    apply (div_lt_iff₀ hsqrtPos).2
    simpa only [mul_comm] using (div_lt_iff₀ hε).1 hsqrtLower
  simpa only [abs_of_nonneg (div_nonneg hD hsqrtPos.le), abs_one,
    mul_one] using hsmall.le

/-- The geometric baseline of the overflowing mask is uniformly `o(1)` in
the literal critical run-length window. -/
theorem prefixOverflowBaseline_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      prefixOverflowBaseline (fun _ _ ↦ 1) := by
  let D : ℝ :=
    2 * CriticalRunWindow.upperConstant *
      CriticalRunWindow.balanceConstant C
  have hD : 0 ≤ D := by
    dsimp only [D]
    have hupperNonneg : 0 ≤ CriticalRunWindow.upperConstant :=
      (CriticalRunWindow.lowerConstant_pos.trans
        CriticalRunWindow.lowerConstant_lt_upperConstant).le
    exact mul_nonneg
      (mul_nonneg (by norm_num) hupperNonneg)
      (CriticalRunWindow.balanceConstant_nonneg C)
  have hmajor :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun M _L ↦ D / Real.sqrt M) (fun _ _ ↦ 1) :=
    const_div_sqrt_uniformLittleOOne hD
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Nmajor, hmajorBound⟩ := hmajor ε hε
  refine ⟨max 1 (max Nwindow Nmajor), ?_⟩
  intro M hM L hrun
  have hMpos : 0 < M := (le_max_left 1 (max Nwindow Nmajor)).trans hM
  have hw := hwindow M
    ((le_max_left Nwindow Nmajor).trans
      ((le_max_right 1 (max Nwindow Nmajor)).trans hM)) L hrun
  have hbound : prefixOverflowBaseline M L ≤ D / Real.sqrt M := by
    simpa only [D] using
      prefixOverflowBaseline_le_invSqrt (C := C) hMpos hw
  have hsmall := hmajorBound M
    ((le_max_right Nwindow Nmajor).trans
      ((le_max_right 1 (max Nwindow Nmajor)).trans hM)) L hrun
  have hbaseNonneg := prefixOverflowBaseline_nonneg M L
  have hmajorNonneg : 0 ≤ D / Real.sqrt (M : ℝ) := by
    exact div_nonneg hD (Real.sqrt_nonneg _)
  simpa only [abs_of_nonneg hbaseNonneg, abs_one, mul_one] using
    hbound.trans (by
      simpa only [abs_of_nonneg hmajorNonneg, abs_one, mul_one] using hsmall)

/-! ## Uniform vanishing of the full overflow mass -/

/-- The overflowing starts have total probability `o_C(1)`.  Proposition
14.1 controls the masked first-moment error at `N' = M-L+2`, while the
preceding lemma controls its `O(L 2⁻ᴸ)` baseline. -/
theorem prefixOverflowStartProbabilityMass_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      prefixOverflowStartProbabilityMass (fun _ _ ↦ 1) := by
  have hCshift : 0 ≤ C + 1 := by positivity
  have hmasked :=
    MaskedFirstMomentCritical.maskedFirstMomentError_uniformLittleOOne
      hCshift
  have hbaseline := prefixOverflowBaseline_uniformLittleOOne hC
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nheight, hheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      CriticalRunWindow.lowerConstant_pos 3
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Nerror, herror⟩ := hmasked (ε / 2) hhalf
  obtain ⟨Nbase, hbase⟩ := hbaseline (ε / 2) hhalf
  let N₀ : ℕ :=
    max Nwindow
      (max Nadm (max Nheight (max Nbase (2 * Nerror))))
  refine ⟨N₀, ?_⟩
  intro M hM L hrun
  have hMwindow : Nwindow ≤ M := by
    dsimp only [N₀] at hM
    omega
  have hMadm : Nadm ≤ M := by
    dsimp only [N₀] at hM
    omega
  have hMheight : Nheight ≤ M := by
    dsimp only [N₀] at hM
    omega
  have hMbase : Nbase ≤ M := by
    dsimp only [N₀] at hM
    omega
  have hMerror : 2 * Nerror ≤ M := by
    dsimp only [N₀] at hM
    omega
  have hw := hwindow M hMwindow L hrun
  have hAdm := hadm M hMadm (L + 1) hw.1
  have hLtwo : 2 ≤ L := by
    have hthree : 3 ≤ L + 1 := hheight M hMheight (L + 1) hAdm
    omega
  have htwo : 2 * (L + 1) ≤ M :=
    CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
      hAdm.1 hAdm.2.2.2.1
  have hshiftWindow :
      CriticalRunWindow.InRunLengthWindow (C + 1) (M - L + 2) L :=
    shiftedPrefixBase_inRunLengthWindow hLtwo htwo hrun
  have hshiftError : Nerror ≤ M - L + 2 := by omega
  have hmask :
      prefixOverflowStartIndices M L ⊆ dyadicBlock (M - L + 2) :=
    prefixOverflowStartIndices_subset_dyadicBlock htwo
  have herr := herror (M - L + 2) hshiftError L hshiftWindow
    (prefixOverflowStartIndices M L) hmask
  have herrCast :
      |((maskedDyadicExpectation (M - L + 2) L
            (prefixOverflowStartIndices M L) : ℚ) : ℝ) -
          ((prefixOverflowStartIndices M L).card : ℝ) /
            (2 : ℝ) ^ L| ≤ ε / 2 := by
    simpa only [MaskedFirstMomentCritical.maskedFirstMomentErrorReal,
      Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_ofNat] using herr
  have hmassUpper :
      prefixOverflowStartProbabilityMass M L ≤
        prefixOverflowBaseline M L + ε / 2 := by
    rw [prefixOverflowStartProbabilityMass_eq_maskedDyadicExpectation
      hLtwo htwo]
    unfold prefixOverflowBaseline
    linarith [le_abs_self
      (((maskedDyadicExpectation (M - L + 2) L
          (prefixOverflowStartIndices M L) : ℚ) : ℝ) -
        ((prefixOverflowStartIndices M L).card : ℝ) /
          (2 : ℝ) ^ L)]
  have hbaseSmall := hbase M hMbase L hrun
  have hbaseNonneg := prefixOverflowBaseline_nonneg M L
  have hbaseUpper : prefixOverflowBaseline M L ≤ ε / 2 := by
    simpa only [abs_of_nonneg hbaseNonneg, abs_one, mul_one] using hbaseSmall
  have hmassNonneg := prefixOverflowStartProbabilityMass_nonneg M L
  simpa only [abs_of_nonneg hmassNonneg, abs_one, mul_one] using
    hmassUpper.trans (by linarith)

/-! ## Complete prefix/global coupling cost -/

/-- The finite-cylinder boundary probability is exactly the source-model
probability computed in `PrefixBoundaryProbability`. -/
theorem finitePrefixBoundaryProbability_eq_infinitePrefixBoundaryProbability
    (M L : ℕ) :
    finitePrefixBoundaryProbability M L =
      PrefixBoundaryProbability.infinitePrefixBoundaryProbability L := by
  change CorollaryPrefixLaw.prefixBoundaryProbability M L =
    PrefixBoundaryProbability.infinitePrefixBoundaryProbability L
  rw [CorollaryPrefixLaw.prefixBoundaryProbability_eq_measure]
  rfl

theorem finitePrefixBoundaryProbability_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      finitePrefixBoundaryProbability (fun _ _ ↦ 1) := by
  have heq :
      finitePrefixBoundaryProbability =
        (fun M L ↦
          PrefixBoundaryProbability.infinitePrefixBoundaryProbability L) := by
    funext M L
    exact finitePrefixBoundaryProbability_eq_infinitePrefixBoundaryProbability M L
  rw [heq]
  exact
    PrefixBoundaryProbability.infinitePrefixBoundaryProbability_uniformLittleOOne
      hC

/-- Sum of the two exceptional probabilities in the prefix/global coupling. -/
def prefixGlobalCouplingCost (M L : ℕ) : ℝ :=
  finitePrefixBoundaryProbability M L +
    prefixOverflowStartProbabilityMass M L

theorem prefixGlobalCouplingCost_nonneg (M L : ℕ) :
    0 ≤ prefixGlobalCouplingCost M L := by
  unfold prefixGlobalCouplingCost
  exact add_nonneg
    (by
      unfold finitePrefixBoundaryProbability
      exact eventProbability_nonneg _ _)
    (prefixOverflowStartProbabilityMass_nonneg M L)

/-- Both boundary corrections vanish uniformly. -/
theorem prefixGlobalCouplingCost_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      prefixGlobalCouplingCost (fun _ _ ↦ 1) := by
  change UniformLittleOOn
    (CriticalRunWindow.InRunLengthWindow C)
    (fun M L ↦ finitePrefixBoundaryProbability M L +
      prefixOverflowStartProbabilityMass M L)
    (fun _ _ ↦ 1)
  exact PropositionElevenTwo.uniformLittleOOn_add
    (finitePrefixBoundaryProbability_uniformLittleOOne hC)
    (prefixOverflowStartProbabilityMass_uniformLittleOOne hC)

/-- The total-variation cost of replacing the prefix count by the global
interior count is uniformly `o_C(1)`. -/
theorem natTotalVariation_finitePrefix_global_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (finiteNatLaw (globalUniformPMF M L)
            (finitePrefixStartCount M L))
          (globalStartLaw M L))
      (fun _ _ ↦ 1) := by
  have hcost := prefixGlobalCouplingCost_uniformLittleOOne hC
  obtain ⟨Nlength, hlength⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity hC 3
  intro ε hε
  obtain ⟨Ncost, hcostBound⟩ := hcost ε hε
  refine ⟨max Nlength Ncost, ?_⟩
  intro M hM L hrun
  have hLthree : 3 ≤ L + 1 :=
    hlength M ((le_max_left _ _).trans hM) L hrun
  have hLtwo : 2 ≤ L := by omega
  have htv := natTotalVariation_finitePrefix_global_le
    (M := M) (L := L) hLtwo
  have hsmall := hcostBound M ((le_max_right _ _).trans hM) L hrun
  have hcostNonneg := prefixGlobalCouplingCost_nonneg M L
  have hsumNonneg :
      0 ≤ finitePrefixBoundaryProbability M L +
        prefixOverflowStartProbabilityMass M L := by
    simpa only [prefixGlobalCouplingCost] using hcostNonneg
  have hsmall' :
      finitePrefixBoundaryProbability M L +
          prefixOverflowStartProbabilityMass M L ≤ ε := by
    simpa only [prefixGlobalCouplingCost, abs_of_nonneg hsumNonneg,
      abs_one, mul_one] using hsmall
  have htvNonneg := natTotalVariation_nonneg
    (finiteNatLaw (globalUniformPMF M L) (finitePrefixStartCount M L))
    (globalStartLaw M L)
  simpa only [abs_of_nonneg htvNonneg, abs_one, mul_one] using
    htv.trans hsmall'

/-- The same result in the notation exported by `CorollaryPrefixLaw`. -/
theorem natTotalVariation_prefixStartLaw_global_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (CorollaryPrefixLaw.prefixStartLaw M L)
          (globalStartLaw M L))
      (fun _ _ ↦ 1) := by
  have heq :
      (fun M L ↦
        natTotalVariation
          (finiteNatLaw (globalUniformPMF M L)
            (finitePrefixStartCount M L))
          (globalStartLaw M L)) =
      (fun M L ↦
        natTotalVariation
          (CorollaryPrefixLaw.prefixStartLaw M L)
          (globalStartLaw M L)) := by
    funext M L
    rfl
  rw [← heq]
  exact natTotalVariation_finitePrefix_global_uniformLittleOOne hC

end

end PrefixOverflowCoupling
end PaperC
