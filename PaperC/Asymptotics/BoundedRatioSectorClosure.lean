import PaperC.Asymptotics.BoundedRatioRelationalHostsCritical
import PaperC.Combinatorics.BoundedRatioResidualMasses

set_option maxHeartbeats 1800000

/-!
# Common closure lemmas for bounded-ratio residual sectors

This module contains the two pieces shared by all three elementary
Section 17 sectors.

* An active residual pair has `τ > 0`, hence `ρ = σ + τ > 0`; after
  forgetting its subtype proof it is therefore a member of the exact
  bounded-interval relational-host population.
* An endpoint-independent two-variable envelope may be proved negligible
  with the existing uniform asymptotic calculus and then transferred to the
  three-variable bounded-ratio predicate.

Neither statement depends on the definition of a particular sector.
-/

namespace PaperC
namespace BoundedRatioSectorClosure

open BoundedRatioRelationalHosts
open BoundedRatioResidualMasses
open PropositionSixteenOne

noncomputable section

/-! ## Active residual pairs are relational hosts -/

/-- Every active pair in any Section 17 sector has positive full rank. -/
theorem pairRho_pos_of_mem_activeSectorPairs
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {sector : SectionElevenPartition.ResidualSector}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs N M A L hN terminal sector) :
    0 < pairRho pair := by
  have hactive := mem_activeSectorPairs.mp hpair
  rw [pairRho_eq_pairSigma_add_pairTau (A := A) hN pair]
  omega

/-- Forgetting the subtype sends every active sector pair to a bounded
relational host at the same exact cutoff `M+L`. -/
theorem pairValue_mem_boundedRelationalHosts_of_mem_activeSectorPairs
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {sector : SectionElevenPartition.ResidualSector}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs N M A L hN terminal sector) :
    pair.1 ∈ boundedRelationalHosts N M L := by
  have hp :=
    PropositionSixteenOne.mem_separatedBoundedRatioPairs.mp pair.2
  apply mem_boundedRelationalHosts.mpr
  refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
  change 0 < pairRho pair
  exact pairRho_pos_of_mem_activeSectorPairs hpair

/-- The unbundled active sector population is contained in the exact
bounded relational-host population. -/
theorem activeSectorPairValues_subset_boundedRelationalHosts
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : SectionElevenPartition.ResidualSector) :
    activeSectorPairValues N M A L hN terminal sector ⊆
      boundedRelationalHosts N M L := by
  intro pair hpair
  rw [activeSectorPairValues, populationPairValues,
    Finset.mem_image] at hpair
  obtain ⟨bundledPair, hbundledPair, rfl⟩ := hpair
  exact
    pairValue_mem_boundedRelationalHosts_of_mem_activeSectorPairs
      hbundledPair

/-- Cardinality form of the preceding injection. -/
theorem card_activeSectorPairs_le_boundedRelationalHosts
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : SectionElevenPartition.ResidualSector) :
    (activeSectorPairs N M A L hN terminal sector).card ≤
      (boundedRelationalHosts N M L).card := by
  rw [← card_activeSectorPairValues N M A L hN terminal sector]
  exact Finset.card_le_card
    (activeSectorPairValues_subset_boundedRelationalHosts
      hN terminal sector)

/--
Cauchy--Schwarz with the active population cardinality already replaced by
the common bounded relational-host count.
-/
theorem sectorResidualMassNat_cast_le_host_sqrt_mul_quadratic_sqrt
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : SectionElevenPartition.ResidualSector) :
    (sectorResidualMassNat
        (M := M) (L := L) A hN terminal sector : ℝ) ≤
      Real.sqrt ((boundedRelationalHosts N M L).card : ℝ) *
        Real.sqrt
          (activeSectorQuadraticResidualMass
            (M := M) (L := L) A hN terminal sector : ℝ) := by
  have hinterp :=
    sectorResidualMassNat_cast_le_sqrt_active_card_mul_sqrt_quadratic
      (M := M) (A := A) (L := L) hN terminal sector
  have hcard :
      ((activeSectorPairs N M A L hN terminal sector).card : ℝ) ≤
        ((boundedRelationalHosts N M L).card : ℝ) := by
    exact_mod_cast
      card_activeSectorPairs_le_boundedRelationalHosts
        hN terminal sector
  exact hinterp.trans
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt hcard)
      (Real.sqrt_nonneg _))

/-! ## Endpoint-independent asymptotic envelopes -/

/--
Transfer an ordinary two-variable rational-power envelope to the literal
bounded-ratio predicate, provided it eventually dominates every endpoint
choice.
-/
theorem uniformRationalPowerInBoundedRatioWindow_of_envelope
    {p q : ℕ} {C : ℝ} {κ₀ : ℕ}
    {f : ℕ → ℕ → ℕ → ℝ}
    {envelope : ℕ → ℕ → ℝ}
    (henvelope :
      UniformRationalPowerSubpolynomialOn
        p q
        (CriticalRunWindow.InRunLengthWindow C)
        envelope)
    (hdom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        |f N M L| ≤ |envelope N L|) :
    UniformRationalPowerInBoundedRatioWindow
      p q C κ₀ f := by
  intro k hk
  obtain ⟨Nenv, hNenv⟩ := henvelope k hk
  obtain ⟨Ndom, hNdom⟩ := hdom
  refine ⟨max Nenv Ndom, ?_⟩
  intro N hN M L hNM hMκ hrun
  exact
    (pow_le_pow_left₀
      (abs_nonneg (f N M L))
      (hNdom N ((le_max_right _ _).trans hN)
        M L hNM hMκ hrun)
      (q * k)).trans
      (hNenv N ((le_max_left _ _).trans hN) L hrun)

/--
Nonnegative specialization of
`uniformRationalPowerInBoundedRatioWindow_of_envelope`.
-/
theorem uniformRationalPowerInBoundedRatioWindow_of_nonnegative_envelope
    {p q : ℕ} {C : ℝ} {κ₀ : ℕ}
    {f : ℕ → ℕ → ℕ → ℝ}
    {envelope : ℕ → ℕ → ℝ}
    (henvelope :
      UniformRationalPowerSubpolynomialOn
        p q
        (CriticalRunWindow.InRunLengthWindow C)
        envelope)
    (hf : ∀ N M L, 0 ≤ f N M L)
    (henv : ∀ N L, 0 ≤ envelope N L)
    (hdom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        f N M L ≤ envelope N L) :
    UniformRationalPowerInBoundedRatioWindow
      p q C κ₀ f := by
  apply uniformRationalPowerInBoundedRatioWindow_of_envelope henvelope
  obtain ⟨N₁, hN₁⟩ := hdom
  refine ⟨N₁, ?_⟩
  intro N hN M L hNM hMκ hrun
  rw [abs_of_nonneg (hf N M L), abs_of_nonneg (henv N L)]
  exact hN₁ N hN M L hNM hMκ hrun

/--
Transfer an ordinary two-variable little-oh envelope to the literal
bounded-ratio predicate, provided it eventually dominates every endpoint
choice.  The domination hypothesis deliberately includes the same geometric
side conditions as the target predicate.
-/
theorem uniformLittleOInBoundedRatioWindow_of_envelope
    {C : ℝ} {κ₀ : ℕ}
    {f : ℕ → ℕ → ℕ → ℝ}
    {envelope : ℕ → ℕ → ℝ}
    (henvelope :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        envelope
        (fun N _ ↦ (N : ℝ) ^ 2))
    (hdom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        |f N M L| ≤ |envelope N L|) :
    UniformLittleOInBoundedRatioWindow C κ₀ f := by
  intro ε hε
  obtain ⟨Nenv, hNenv⟩ := henvelope ε hε
  obtain ⟨Ndom, hNdom⟩ := hdom
  refine ⟨max Nenv Ndom, ?_⟩
  intro N hN M L hNM hMκ hrun
  exact
    (hNdom N ((le_max_right _ _).trans hN)
      M L hNM hMκ hrun).trans
      (hNenv N ((le_max_left _ _).trans hN) L hrun)

/--
Nonnegative specialization convenient for natural-valued sector masses and
explicit nonnegative envelopes.
-/
theorem uniformLittleOInBoundedRatioWindow_of_nonnegative_envelope
    {C : ℝ} {κ₀ : ℕ}
    {f : ℕ → ℕ → ℕ → ℝ}
    {envelope : ℕ → ℕ → ℝ}
    (henvelope :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        envelope
        (fun N _ ↦ (N : ℝ) ^ 2))
    (hf : ∀ N M L, 0 ≤ f N M L)
    (henv : ∀ N L, 0 ≤ envelope N L)
    (hdom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        f N M L ≤ envelope N L) :
    UniformLittleOInBoundedRatioWindow C κ₀ f := by
  apply uniformLittleOInBoundedRatioWindow_of_envelope henvelope
  obtain ⟨N₁, hN₁⟩ := hdom
  refine ⟨N₁, ?_⟩
  intro N hN M L hNM hMκ hrun
  rw [abs_of_nonneg (hf N M L), abs_of_nonneg (henv N L)]
  exact hN₁ N hN M L hNM hMκ hrun

end

end BoundedRatioSectorClosure
end PaperC
