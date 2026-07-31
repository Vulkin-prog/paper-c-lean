import PaperC.Asymptotics.TheoremSixteenTwo
import PaperC.Probability.FiniteCylinderCountTransport

set_option maxHeartbeats 1200000

/-!
# Exact transport from bounded-ratio counts to retained counts

The bounded-ratio construction uses the local cylinder with cutoff `M+L`,
whereas Theorem 16.2 realizes the same starts on its common cylinder with
cutoff `2M+L`.  This module identifies the two constructions when the
bounded-ratio left endpoint is `M / 2^j`.

The comparison is exact.  It uses the finite-cylinder cutoff invariance from
`FiniteCylinderCountTransport`; no bridge hypothesis is introduced.
-/

namespace PaperC
namespace BoundedRatioRetainedTransport

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The bounded-ratio block at `N = M / 2^j` is the retained population. -/
theorem boundedRatioBlock_div_eq_retainedStartIndices
    (M j : ℕ) :
    PropositionSixteenOne.boundedRatioBlock (M / 2 ^ j) M =
      TheoremSixteenTwo.retainedStartIndices M j := by
  ext x
  simp only [PropositionSixteenOne.mem_boundedRatioBlock,
    TheoremSixteenTwo.retainedStartIndices, Finset.mem_Ico]

/-- The local bounded-ratio cutoff is contained in the common global one. -/
theorem boundedRatioCutoff_le_globalCylinderCutoff
    (M L : ℕ) :
    PropositionSixteenOne.boundedRatioCutoff M L ≤
      TheoremSixteenTwo.globalCylinderCutoff M L := by
  unfold PropositionSixteenOne.boundedRatioCutoff
    TheoremSixteenTwo.globalCylinderCutoff dyadicCutoff
  omega

/-- Under the natural support hypothesis, every retained start is interior. -/
theorem two_le_of_mem_retainedStartIndices
    {M j x : ℕ} (hcut : 2 ≤ M / 2 ^ j)
    (hx : x ∈ TheoremSixteenTwo.retainedStartIndices M j) :
    2 ≤ x := by
  have hx' :
      M / 2 ^ j ≤ x ∧ x < M := by
    simpa only [TheoremSixteenTwo.retainedStartIndices,
      Finset.mem_Ico] using hx
  exact hcut.trans hx'.1

/-- Every retained window is supported on the local cutoff `M+L`. -/
theorem retained_window_le_boundedRatioCutoff
    {M L j x : ℕ}
    (hx : x ∈ TheoremSixteenTwo.retainedStartIndices M j) :
    x + L ≤ PropositionSixteenOne.boundedRatioCutoff M L := by
  have hx' :
      M / 2 ^ j ≤ x ∧ x < M := by
    simpa only [TheoremSixteenTwo.retainedStartIndices,
      Finset.mem_Ico] using hx
  unfold PropositionSixteenOne.boundedRatioCutoff
  omega

/--
Count-level transport under the canonical product decomposition of the
common cylinder into the local cylinder and its unused prime coordinates.
-/
theorem retainedStartCount_eq_boundedFullStartCount_transport
    {M L j : ℕ} (hcut : 2 ≤ M / 2 ^ j)
    (ω :
      SampleSpace (TheoremSixteenTwo.globalCylinderCutoff M L)) :
    TheoremSixteenTwo.retainedStartCount M L j ω =
      FiniteCylinderCountTransport.boundedFullStartCount
        (M / 2 ^ j) M L
        ((FiniteCylinderCountTransport.sampleSpaceEquivLocalProd
          (boundedRatioCutoff_le_globalCylinderCutoff M L) ω).1) := by
  have htransport :=
    FiniteCylinderCountTransport.startCountOn_sampleSpaceEquivLocalProd
      (boundedRatioCutoff_le_globalCylinderCutoff M L)
      (TheoremSixteenTwo.retainedStartIndices M j)
      (fun x hx ↦ two_le_of_mem_retainedStartIndices hcut hx)
      (fun x hx ↦ retained_window_le_boundedRatioCutoff hx)
      ω
  simpa only [TheoremSixteenTwo.retainedStartCount,
    FiniteCylinderCountTransport.boundedFullStartCount,
    FiniteCylinderCountTransport.startCountOn,
    boundedRatioBlock_div_eq_retainedStartIndices] using htransport

/--
The local full bounded-ratio law is exactly the retained law used in
Theorem 16.2.
-/
theorem boundedFullStartLaw_eq_retainedStartLaw
    {M L j : ℕ} (hcut : 2 ≤ M / 2 ^ j) :
    FiniteCylinderCountTransport.boundedFullStartLaw
        (M / 2 ^ j) M L =
      TheoremSixteenTwo.retainedStartLaw M L j := by
  have htransport :=
    FiniteCylinderCountTransport.finiteNatLaw_startCountOn_cutoff_invariant
      (boundedRatioCutoff_le_globalCylinderCutoff M L)
      (TheoremSixteenTwo.retainedStartIndices M j)
      (fun x hx ↦ two_le_of_mem_retainedStartIndices hcut hx)
      (fun x hx ↦ retained_window_le_boundedRatioCutoff hx)
  change
    SectionThirteenFiniteBound.finiteNatLaw
        (SectionThirteenCouplings.fullUniformPMF
          (PropositionSixteenOne.boundedRatioCutoff M L))
        (FiniteCylinderCountTransport.startCountOn
          (TheoremSixteenTwo.retainedStartIndices M j) L
          (PropositionSixteenOne.boundedRatioCutoff M L)) =
      SectionThirteenFiniteBound.finiteNatLaw
        (SectionThirteenCouplings.fullUniformPMF
          (TheoremSixteenTwo.globalCylinderCutoff M L))
        (FiniteCylinderCountTransport.startCountOn
          (TheoremSixteenTwo.retainedStartIndices M j) L
          (TheoremSixteenTwo.globalCylinderCutoff M L))
  exact htransport.symm

/--
The exact local first moment is the retained first moment on the common
cylinder.
-/
theorem boundedFullStartMean_eq_retainedStartMean
    {M L j : ℕ} (hcut : 2 ≤ M / 2 ^ j) :
    FiniteCylinderCountTransport.boundedFullStartMean
        (M / 2 ^ j) M L =
      TheoremSixteenTwo.retainedStartMean M L j := by
  classical
  unfold FiniteCylinderCountTransport.boundedFullStartMean
    TheoremSixteenTwo.retainedStartMean
  rw [boundedRatioBlock_div_eq_retainedStartIndices]
  apply Finset.sum_congr rfl
  intro x hx
  have hxBlock :
      x ∈
        PropositionSixteenOne.boundedRatioBlock
          (M / 2 ^ j) M := by
    rw [boundedRatioBlock_div_eq_retainedStartIndices]
    exact hx
  have hxGlobal :
      x ∈ TheoremSixteenTwo.globalStartIndices M := by
    have hxRetained :
        M / 2 ^ j ≤ x ∧ x < M := by
      simpa only [TheoremSixteenTwo.retainedStartIndices,
        Finset.mem_Ico] using hx
    simp only [TheoremSixteenTwo.globalStartIndices,
      Finset.mem_Ico]
    exact ⟨hcut.trans hxRetained.1, hxRetained.2⟩
  rw [FiniteCylinderCountTransport.boundedStartProbability_eq_selfStartProbability
      hcut hxBlock,
    TheoremSixteenTwo.commonCylinderStartProbability_eq_globalStartProbability
      hxGlobal]
  rfl

end

end BoundedRatioRetainedTransport
end PaperC
