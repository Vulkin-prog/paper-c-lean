import PaperC.Asymptotics.BoundedRatioNonterminalMobileAssembly
import PaperC.Asymptotics.BoundedRatioTwoSingletonCritical

set_option maxHeartbeats 3600000

/-!
# Final assembly of the bounded-ratio nonterminal sector

`BoundedRatioNonterminalMobileAssembly` constructs the moderate-density
size-ten host envelope from Evertse--Silverman, generalized Pell, and a
separate bound for the two-singleton shapes.  The density-split theorem in
`BoundedRatioNonterminalCardinality` already turns such a linear host
envelope, together with the direct size-two high-density estimate, into the
required little-oh bound.

This file is the final glue between those two interfaces.  It introduces no
new arithmetic statement or bridge.
-/

namespace PaperC
namespace BoundedRatioNonterminalAssembly

open BoundedRatioComponentHosts
open BoundedRatioCanonicalTerminalPopulation
open BoundedRatioNonterminalCardinality
open BoundedRatioNonterminalMobileAssembly
open BoundedRatioNonterminalHostCounts
open BoundedRatioTwoSingletonCritical
open EvertseSilvermanInput
open PropositionSixteenOne

noncomputable section

/--
Direct source-faithful closure of the sixth residual sector.

The only inputs besides Evertse--Silverman and generalized Pell are the two
finite host estimates used in the manuscript's density split:

* a linear-subpolynomial fixed-shape envelope for two singletons;
* the direct size-two envelope in the high-density branch.
-/
theorem intrinsicNonterminalSector_uniformLittleO_of_arithmeticEnvelopes
    {C Cterm K : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (hES : EvertseSilvermanAbscissaStatement)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (Q₂ : ℕ → ℕ → ℝ)
    (hQ₂Rate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) Q₂)
    (hQ₂Nonneg : ∀ N L, 0 ≤ Q₂ N L)
    (hQ₂Dom :
      ∃ N₂ : ℕ, ∀ N ≥ N₂, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ∀ shape ∈ boundedOffsetShapes L 10,
          shape.1.card + shape.2.card = 2 →
          ((boundedComponentHostsOfShape
            N M A L 10 shape).card : ℝ) ≤
            Q₂ N L)
    (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2)
    (hhostsTwo :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedComponentHosts
          N M A L 2).card : ℝ) ≤
            sizeTwoComponentHostEnvelope Cterm N L) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K)
        .nonterminal) := by
  obtain
      ⟨hostEnvelope, hhostRate,
        hhostNonneg, hhostsTen⟩ :=
    evertseSilverman_generalizedPell_imply_exists_moderateNonterminalHostEnvelope
      hC κ₀ A hES hPell Q₂
        hQ₂Rate hQ₂Nonneg hQ₂Dom
  exact
    intrinsicNonterminalSector_uniformLittleO_of_densitySplit
      hC hCterm hthreshold
      hostEnvelope hhostRate hhostNonneg
      hhostsTen hhostsTwo

/--
Registered-interface wrapper for the same arithmetic assembly.

The Evertse--Silverman and generalized-Pell hypotheses are exposed exactly
where `NonterminalSectorStabilityStatement` requires them.
-/
theorem nonterminalSectorStability_of_arithmeticEnvelopes
    {C Cterm K : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (Q₂ : ℕ → ℕ → ℝ)
    (hQ₂Rate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) Q₂)
    (hQ₂Nonneg : ∀ N L, 0 ≤ Q₂ N L)
    (hQ₂Dom :
      ∃ N₂ : ℕ, ∀ N ≥ N₂, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ∀ shape ∈ boundedOffsetShapes L 10,
          shape.1.card + shape.2.card = 2 →
          ((boundedComponentHostsOfShape
            N M A L 10 shape).card : ℝ) ≤
            Q₂ N L)
    (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2)
    (hhostsTwo :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedComponentHosts
          N M A L 2).card : ℝ) ≤
            sizeTwoComponentHostEnvelope Cterm N L) :
    NonterminalSectorStabilityStatement C κ₀ A
      (boundedIntrinsicTerminalPredicate A K) := by
  intro hES hPell
  exact
    intrinsicNonterminalSector_uniformLittleO_of_arithmeticEnvelopes
      hC κ₀ A hES hPell Q₂
        hQ₂Rate hQ₂Nonneg hQ₂Dom
        hCterm hthreshold hhostsTwo

/--
Complete registered form of Lemma 17.28.

Both finite host inputs are now constructed internally: the fixed-shape
two-singleton envelope supplies the moderate-density input, while the
complete size-two estimate supplies the high-density input.  The terminal
constant is absorbed by choosing a nonnegative threshold `K` with
`2 * Cterm < K * log 2`.  No additional bridge is introduced.
-/
theorem exists_nonterminalSectorStability
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      NonterminalSectorStabilityStatement C κ₀ A
        (boundedIntrinsicTerminalPredicate A K) := by
  obtain ⟨Q₂, hQ₂Rate, hQ₂Nonneg, hQ₂Dom⟩ :=
    exists_twoSingletonShapeFiberEnvelope hC κ₀ A
  obtain ⟨Cterm, hCterm, hhostsTwo⟩ :=
    exists_sizeTwoComponentHostEnvelope hC κ₀ A
  have hlogTwo :
      0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  let K : ℝ :=
    (2 * Cterm + 1) / Real.log 2
  have hK :
      0 ≤ K := by
    dsimp [K]
    exact div_nonneg (by linarith) hlogTwo.le
  have hthreshold :
      2 * Cterm < K * Real.log 2 := by
    dsimp [K]
    rw [div_mul_cancel₀ _ hlogTwo.ne']
    linarith
  refine ⟨K, hK, ?_⟩
  exact
    nonterminalSectorStability_of_arithmeticEnvelopes
      hC κ₀ A Q₂ hQ₂Rate hQ₂Nonneg hQ₂Dom
        hCterm hthreshold hhostsTwo

end

end BoundedRatioNonterminalAssembly
end PaperC
