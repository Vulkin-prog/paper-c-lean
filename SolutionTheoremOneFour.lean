import Solution
import PaperC.Asymptotics.TheoremOneFourCanonical
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.DotProduct

noncomputable section

/-!
# Paper C external-audit solution: Theorem 1.4 and Corollary 11.3

This file reproduces the additional declaration layer of
`ChallengeTheoremOneFour.lean` without importing that Challenge.  `Solution`
already reproduces its standalone Mathlib-only base declarations.  The two
audited statements are then closed by the frozen Paper C canonical endpoints.
-/

open scoped BigOperators

namespace PaperCAudit

/-! ## Exact finite expectations and affine relation rank -/

noncomputable def valueLinear (M n : ℕ) :
    SampleSpace M →ₗ[F₂] F₂ where
  toFun := fun ω => valueBit ω n
  map_add' := by
    intro ω η
    simp [valueBit, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c ω
    simp [valueBit, Finset.mul_sum, mul_assoc]

noncomputable def uniformEventProbability {M : ℕ}
    (P : SampleSpace M → Prop) [DecidablePred P] : ℚ :=
  ((Finset.univ.filter P).card : ℚ) /
    (Fintype.card (SampleSpace M) : ℚ)

noncomputable def startProbability (N L x : ℕ) : ℚ := by
  classical
  exact uniformEventProbability (M := dyadicCutoff N L)
    (fun ω => startAt ω x L)

noncomputable def dyadicExpectation (N L : ℕ) : ℚ :=
  ∑ x ∈ dyadicBlock N, startProbability N L x

noncomputable def uniformExpectation {M : ℕ}
    (f : SampleSpace M → ℚ) : ℚ :=
  (∑ ω : SampleSpace M, f ω) /
    (Fintype.card (SampleSpace M) : ℚ)

namespace Affine

abbrev 𝔽₂ := PaperCAudit.F₂

open scoped Classical

local instance factPrimeTwo : Fact (Nat.Prime 2) :=
  Fact.mk Nat.prime_two

section Relations

variable {V β : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V]
variable [Fintype β] [DecidableEq β]

def dotLinear (w : β → 𝔽₂) : (β → 𝔽₂) →ₗ[𝔽₂] 𝔽₂ where
  toFun y := dotProduct w y
  map_add' y z := dotProduct_add w y z
  map_smul' c y := dotProduct_smul c w y

def relationFunctional (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (u : β → 𝔽₂) :
    V →ₗ[𝔽₂] 𝔽₂ :=
  (dotLinear u).comp A

def relationMap (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :
    (β → 𝔽₂) →ₗ[𝔽₂] (V →ₗ[𝔽₂] 𝔽₂) where
  toFun := relationFunctional A
  map_add' u v := by
    ext x
    simp [relationFunctional, dotLinear, add_dotProduct]
  map_smul' c u := by
    ext x
    simp [relationFunctional, dotLinear, smul_dotProduct]

abbrev RelationSpace (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :=
  LinearMap.ker (relationMap A)

end Relations

section RelationRank

variable {V β : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V]
variable [Fintype β]

local instance relationSpaceFintype
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :
    Fintype (RelationSpace A) :=
  Fintype.ofFinite _

def relationRho (A : V →ₗ[𝔽₂] (β → 𝔽₂)) : ℕ :=
  Module.finrank 𝔽₂ (RelationSpace A)

end RelationRank

noncomputable def startRow (M x L : ℕ) (i : Fin L) :
    SampleSpace M →ₗ[F₂] F₂ :=
  if i.1 = 0 then
    valueLinear M (x - 1) + valueLinear M x
  else
    valueLinear M x + valueLinear M (x + i.1)

noncomputable def startSystem (M x L : ℕ) :
    SampleSpace M →ₗ[F₂] (Fin L → F₂) :=
  LinearMap.pi (startRow M x L)

def twoStartRow (M x y L : ℕ) :
    Sum (Fin L) (Fin L) → SampleSpace M →ₗ[F₂] F₂
  | Sum.inl i => startRow M x L i
  | Sum.inr i => startRow M y L i

def twoStartSystem (M x y L : ℕ) :
    SampleSpace M →ₗ[F₂] (Sum (Fin L) (Fin L) → F₂) :=
  LinearMap.pi (twoStartRow M x y L)

end Affine

namespace RationalMassFinite

def separatedDyadicPairs (N L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun pair =>
    L < Nat.dist pair.1 pair.2

end RationalMassFinite

namespace ResidualMasses

abbrev SeparatedDyadicPair (N L : ℕ) :=
  {pair : ℕ × ℕ // pair ∈ RationalMassFinite.separatedDyadicPairs N L}

noncomputable def pairRho
    {N L : ℕ} (pair : SeparatedDyadicPair N L) : ℕ :=
  Affine.relationRho
    (Affine.twoStartSystem
      (dyadicCutoff N L) pair.1.1 pair.1.2 L)

end ResidualMasses

namespace PropositionElevenTwo

noncomputable def homogeneousWeight
    {N L : ℕ} (pair : ResidualMasses.SeparatedDyadicPair N L) : ℕ :=
  2 ^ ResidualMasses.pairRho pair - 1

noncomputable def homogeneousMassNat
    {N L : ℕ} (_hN : 2 ≤ N) : ℕ :=
  ∑ pair : ResidualMasses.SeparatedDyadicPair N L,
    homogeneousWeight pair

noncomputable def homogeneousMass
    (_A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (homogeneousMassNat (L := L) hN : ℝ)
  else 0

end PropositionElevenTwo

def UniformLittleOOn
    (admissible : ℕ → ℕ → Prop) (f g : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ≤ ε * |g N L|

def UniformHalfPowerSubpolynomialOn
    (admissible : ℕ → ℕ → Prop) (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ^ (2 * k) ≤ (N : ℝ) ^ (k + 1)

def UniformNegativeHalfPowerSubpolynomialOn
    (admissible : ℕ → ℕ → Prop) (f : ℕ → ℕ → ℝ) : Prop :=
  UniformHalfPowerSubpolynomialOn admissible
    (fun N L => (N : ℝ) * f N L)

namespace SectionTwelveMoments

noncomputable def uniformVariance
    {M : ℕ} (f : SampleSpace M → ℚ) : ℚ :=
  uniformExpectation
    (fun ω => (f ω - uniformExpectation f) ^ 2)

noncomputable def dyadicSecondFactorialMoment
    (N L : ℕ) : ℚ :=
  uniformExpectation
    (fun ω : DyadicSample N L =>
      (dyadicCount N L ω : ℚ) *
        ((dyadicCount N L ω : ℚ) - 1))

noncomputable def dyadicVariance (N L : ℕ) : ℚ :=
  uniformVariance
    (fun ω : DyadicSample N L => (dyadicCount N L ω : ℚ))

noncomputable def criticalMean (N L : ℕ) : ℝ :=
  (N : ℝ) / ((2 : ℕ) : ℝ) ^ L

noncomputable def dyadicFirstMomentPoissonError
    (N L : ℕ) : ℝ :=
  (dyadicExpectation N L : ℝ) - criticalMean N L

noncomputable def dyadicSecondFactorialPoissonError
    (N L : ℕ) : ℝ :=
  (dyadicSecondFactorialMoment N L : ℝ) -
    (criticalMean N L) ^ 2

noncomputable def dyadicVariancePoissonError
    (N L : ℕ) : ℝ :=
  (dyadicVariance N L : ℝ) - criticalMean N L

end SectionTwelveMoments

namespace PropositionElevenThree

noncomputable def quantitativeHomogeneousScale
    (c : ℝ) (N _L : ℕ) : ℝ :=
  (N : ℝ) ^ 2 *
    Real.exp
      (-c * Real.sqrt (Real.log N) /
        Real.log (Real.log N))

end PropositionElevenThree

end PaperCAudit

theorem paper_c_theorem_one_four_moments
    {C : ℝ} (hC : 0 ≤ C)
    (hES :
      PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement) :
    PaperCAudit.UniformNegativeHalfPowerSubpolynomialOn
        (PaperCAudit.CriticalRunWindow.InRunLengthWindow C)
        PaperCAudit.SectionTwelveMoments.dyadicFirstMomentPoissonError ∧
      PaperCAudit.UniformLittleOOn
        (PaperCAudit.CriticalRunWindow.InRunLengthWindow C)
        PaperCAudit.SectionTwelveMoments.dyadicSecondFactorialPoissonError
        (fun _ _ => 1) ∧
      PaperCAudit.UniformLittleOOn
        (PaperCAudit.CriticalRunWindow.InRunLengthWindow C)
        (PaperCAudit.PropositionElevenTwo.homogeneousMass 3)
        (fun N _ => (N : ℝ) ^ 2) ∧
      PaperCAudit.UniformLittleOOn
        (PaperCAudit.CriticalRunWindow.InRunLengthWindow C)
        PaperCAudit.SectionTwelveMoments.dyadicVariancePoissonError
        (fun _ _ => 1) := by
  exact
    PaperC.SectionTwelveMoments.theorem_one_four_canonical
      hC hES hDivisor

theorem paper_c_corollary_eleven_three
    {C : ℝ} (hC : 0 ≤ C)
    (hES :
      PaperCAudit.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PaperCAudit.PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ c_R : ℝ, 0 < c_R ∧
      PaperCAudit.UniformBigOOn
        (PaperCAudit.CriticalRunWindow.InRunLengthWindow C)
        (PaperCAudit.PropositionElevenTwo.homogeneousMass 3)
        (PaperCAudit.PropositionElevenThree.quantitativeHomogeneousScale
          c_R) := by
  exact
    PaperC.DyadicKappaQuantitative.corollary_eleven_three_canonical
      hC hES hDivisor

#print axioms paper_c_theorem_one_four_moments
#print axioms paper_c_corollary_eleven_three

end
