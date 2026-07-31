import PaperC.Asymptotics.ExactLengthBadStartMassCritical
import PaperC.Asymptotics.MarkedLaplaceCritical
import PaperC.Probability.MarkedCountVectorMixture
import PaperC.Probability.PoissonLaplaceFunctional
import PaperC.Probability.PoissonVectorMass
import PaperC.Probability.PrimeEncodedCountLaplace

/-!
# Corollary 14.9: the finite vector of exact-length counts

The module and public identifiers retain their pre-v045 `FourteenEight`
spelling for API compatibility; only the manuscript locator moved.

For fixed `E`, convergence in law of a vector in `ℕ^(E+1)` is recorded
pointwise on every joint atom.  The target mass is the product of the
Poisson masses with rates

`λ * 2^(-(e+1))`,  `0 ≤ e ≤ E`,

so the target coordinates are independent by construction.

The canonical final theorem is now derived directly from the complete marked
Laplace convergence of Section 14.4.  Prime encoding converts the finite
vector into a positive-integer-valued variable, and convergence of all
inverse-power transforms determines every joint atom.  The earlier retained
finite-law and averaged-conditional-law statements remain as useful transfer
variants.  No abstract audit proposition or bridge is introduced here.
-/

open scoped BigOperators NNReal Topology
open Filter ProbabilityTheory

namespace PaperC
namespace CorollaryFourteenEightCounts

open ExactLengthBadStartMassCritical
open ExactLengthCountVectorTransfer
open InfiniteExactLengthProbabilityTransfer
open MarkedLaplaceCritical
open MarkedCountVectorMixture
open PoissonLaplaceFunctional
open PoissonVectorMass
open PrimeEncodedCountLaplace
open PrimeEncodedCountVector
open DirichletAtomConvergence
open SpatialMarkedParameters

noncomputable section

/-- Poisson rate `λ 2^(-(e+1))` for the exact excess `e`. -/
def independentPoissonExactLengthRate
    (lam : ℝ≥0) (e : ℕ) : ℝ≥0 :=
  ⟨(lam : ℝ) * geometricMarkWeight e,
    mul_nonneg lam.2 (geometricMarkWeight_nonneg e)⟩

@[simp]
theorem coe_independentPoissonExactLengthRate
    (lam : ℝ≥0) (e : ℕ) :
    ((independentPoissonExactLengthRate lam e : ℝ≥0) : ℝ) =
      (lam : ℝ) / (2 : ℝ) ^ (e + 1) := by
  change (lam : ℝ) * geometricMarkWeight e = _
  simp only [geometricMarkWeight, div_eq_mul_inv, one_mul]

/--
Joint point mass of the independent Poisson vector with coordinates
`Pois(λ 2^(-(e+1)))`.
-/
def independentPoissonExactLengthVectorMass
    (lam : ℝ≥0) {E : ℕ}
    (k : ExactLengthCountVector E) : ℝ :=
  ∏ e : Fin (E + 1),
    poissonPMFReal
      (independentPoissonExactLengthRate lam e.1) (k e)

theorem independentPoissonExactLengthVectorMass_nonneg
    (lam : ℝ≥0) {E : ℕ}
    (k : ExactLengthCountVector E) :
    0 ≤ independentPoissonExactLengthVectorMass lam k := by
  unfold independentPoissonExactLengthVectorMass
  exact Finset.prod_nonneg fun _ _ ↦ poissonPMFReal_nonneg

/-! ## Prime-encoded target law -/

/--
The independent Poisson vector mass, pushed to the positive integers by
the injective prime code.
-/
def encodedIndependentPoissonExactLengthLaw
    (lam : ℝ≥0) (E : ℕ) (m : ℕ) : ℝ :=
  injectivePushforwardMass (@primeCode (E + 1))
    (independentPoissonExactLengthVectorMass lam) m

theorem encodedIndependentPoissonExactLengthLaw_nonneg
    (lam : ℝ≥0) (E m : ℕ) :
    0 ≤ encodedIndependentPoissonExactLengthLaw lam E m := by
  apply injectivePushforwardMass_nonneg
  exact independentPoissonExactLengthVectorMass_nonneg lam

theorem hasSum_encodedIndependentPoissonExactLengthLaw
    (lam : ℝ≥0) (E : ℕ) :
    HasSum (encodedIndependentPoissonExactLengthLaw lam E) 1 := by
  unfold encodedIndependentPoissonExactLengthLaw
  apply hasSum_injectivePushforwardMass primeCode_injective
  change HasSum
    (fun k : Fin (E + 1) → ℕ ↦
      ∏ e : Fin (E + 1),
        poissonPMFReal
          (independentPoissonExactLengthRate lam e.1) (k e)) 1
  exact hasSum_independentPoissonVectorMass
    (fun e : Fin (E + 1) ↦
      independentPoissonExactLengthRate lam e.1)

@[simp]
theorem encodedIndependentPoissonExactLengthLaw_zero
    (lam : ℝ≥0) (E : ℕ) :
    encodedIndependentPoissonExactLengthLaw lam E 0 = 0 := by
  unfold encodedIndependentPoissonExactLengthLaw
  apply injectivePushforwardMass_eq_zero_of_not_mem_range
  rintro ⟨k, hk⟩
  have hkpos := primeCode_pos k
  omega

theorem encodedIndependentPoissonExactLengthLaw_primeCode
    (lam : ℝ≥0) (E : ℕ) (k : ExactLengthCountVector E) :
    encodedIndependentPoissonExactLengthLaw lam E (primeCode k) =
      independentPoissonExactLengthVectorMass lam k := by
  unfold encodedIndependentPoissonExactLengthLaw
  exact injectivePushforwardMass_apply
    primeCode_injective _ _

/--
The inverse-power transform of the encoded target law is the finite product
of its scalar Poisson Laplace transforms.
-/
theorem inversePowerTransform_encodedIndependentPoissonExactLengthLaw
    (lam : ℝ≥0) (E s : ℕ) :
    inversePowerTransform
        (encodedIndependentPoissonExactLengthLaw lam E) s =
      ∏ e : Fin (E + 1),
        poissonLaplaceTransform
          (independentPoissonExactLengthRate lam e.1)
          ((s : ℝ) *
            Real.log
              ((Nat.nth Nat.Prime e.1 : ℕ) : ℝ)) := by
  unfold inversePowerTransform
    encodedIndependentPoissonExactLengthLaw
  rw [tsum_injectivePushforwardMass_mul
    primeCode_injective]
  rw [← (hasSum_independentPoissonVectorLaplace
    (fun e : Fin (E + 1) ↦
      independentPoissonExactLengthRate lam e.1)
    (fun e : Fin (E + 1) ↦
      (s : ℝ) *
        Real.log
          ((Nat.nth Nat.Prime e.1 : ℕ) : ℝ))
    (fun e ↦ by
      exact primeLogTest_nonneg
        (s := (s : ℝ)) (by positivity) 0 e.1)).tsum_eq]
  apply tsum_congr
  intro k
  rw [independentPoissonExactLengthVectorMass,
    inversePrimeCodeWeight_eq_prod]
  rw [Finset.prod_mul_distrib]

/--
The target inverse-power transform is exactly the limiting marked Laplace
functional produced by Section 14.4 for the prime-logarithmic test.
-/
theorem inversePowerTransform_encodedIndependentPoissonExactLengthLaw_eq_limit
    (lam : ℝ≥0) (E s : ℕ) :
    inversePowerTransform
        (encodedIndependentPoissonExactLengthLaw lam E) s =
      Real.exp
        (-((lam : ℝ) *
          ∫ t in Set.Ico (1 : ℝ) 2,
            ∑ e ∈ Finset.range (E + 1),
              (1 / (2 : ℝ) ^ (e + 1)) *
                (1 -
                  Real.exp
                    (-primeLogTest (s : ℝ) t e)))) := by
  rw [
    inversePowerTransform_encodedIndependentPoissonExactLengthLaw]
  simp_rw [poissonLaplaceTransform_eq]
  rw [← Real.exp_sum]
  simp only [primeLogTest]
  rw [MeasureTheory.integral_const]
  norm_num
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  ring

/--
Pointwise-law formulation of convergence of the complete exact-length count
vector to independent Poisson coordinates.
-/
def ExactLengthCountVectorConvergesToIndependentPoisson
    (Lseq : ℕ → ℕ) (E : ℕ) (lam : ℝ≥0) : Prop :=
  ∀ k : ExactLengthCountVector E,
    Tendsto
      (fun N ↦
        infiniteExactLengthCountVectorLaw N (Lseq N) E k)
      atTop
      (𝓝 (independentPoissonExactLengthVectorMass lam k))

/--
Along any sequence in the critical window, the complete removed
exact-length mass from Lemma 14.8 tends to zero.
-/
theorem totalRemovedInfiniteExactLengthProbability_tendsto_zero
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        CriticalRunWindow.InRunLengthWindow C N (Lseq N)) :
    Tendsto
      (fun N ↦
        totalRemovedInfiniteExactLengthProbability N (Lseq N) E)
      atTop (𝓝 0) := by
  have huniform :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          totalRemovedInfiniteExactLengthProbability N L E)
        (fun _ _ ↦ 1) := by
    simpa only [totalRemovedInfiniteExactLengthProbability] using
      lemma_fourteen_seven hC E
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Nmass, hNmass⟩ :=
    huniform (ε / 2) (by positivity)
  obtain ⟨Nwindow, hNwindow⟩ :=
    eventually_atTop.1 hwindow
  refine ⟨max Nmass Nwindow, ?_⟩
  intro N hN
  have hbound :=
    hNmass N ((le_max_left _ _).trans hN)
      (Lseq N)
      (hNwindow N ((le_max_right _ _).trans hN))
  rw [Real.dist_eq]
  simp only [abs_one, mul_one, sub_zero] at hbound ⊢
  exact hbound.trans_lt (by linarith)

/--
The other half of Corollary 14.9, reduced to the literal retained
finite-cylinder law supplied by the marked Stein--Chen/thinning argument.

The hypothesis is not an opaque statement: for every joint atom `k`, it is
exactly convergence of the already defined retained finite law to the
product of the desired Poisson masses.
-/
theorem corollary_fourteen_eight_counts_of_retained_finite_law
    {C : ℝ} (hC : 0 ≤ C)
    (lam : ℝ≥0) (E : ℕ)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hretained :
      ∀ k : ExactLengthCountVector E,
        Tendsto
          (fun N ↦
            finiteRetainedExactLengthCountVectorLaw
              N (Lseq N) E k)
          atTop
          (𝓝 (independentPoissonExactLengthVectorMass lam k))) :
    ExactLengthCountVectorConvergesToIndependentPoisson
      Lseq E lam := by
  have hremoved :=
    totalRemovedInfiniteExactLengthProbability_tendsto_zero
      hC E Lseq hwindow
  intro k
  have hretainedSource :
      Tendsto
        (fun N ↦
          infiniteRetainedExactLengthCountVectorLaw
            N (Lseq N) E k)
        atTop
        (𝓝 (independentPoissonExactLengthVectorMass lam k)) := by
    apply (hretained k).congr'
    exact Eventually.of_forall fun N ↦
      (infiniteRetainedExactLengthCountVectorLaw_eq_finite
        N (Lseq N) E k).symm
  have hdiffAbs :
      Tendsto
        (fun N ↦
          |infiniteExactLengthCountVectorLaw N (Lseq N) E k -
            infiniteRetainedExactLengthCountVectorLaw
              N (Lseq N) E k|)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ ↦ abs_nonneg _
    · exact Eventually.of_forall fun N ↦
        abs_infiniteExactLengthCountVectorLaw_sub_retained_le_mass
          N (Lseq N) E k
    · exact hremoved
  have hdiff :
      Tendsto
        (fun N ↦
          infiniteExactLengthCountVectorLaw N (Lseq N) E k -
            infiniteRetainedExactLengthCountVectorLaw
              N (Lseq N) E k)
        atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs] using hdiffAbs
  have hsum := hdiff.add hretainedSource
  convert hsum using 1
  · funext N
    ring
  · simp

/--
Equivalent endpoint in the conditional language used by the marked
Stein--Chen argument.  The finite averaging identity is exact, so the only
hypothesis remains pointwise convergence of the explicit averaged
conditional joint law.
-/
theorem corollary_fourteen_eight_counts_of_averaged_conditional_law
    {C : ℝ} (hC : 0 ≤ C)
    (lam : ℝ≥0) (E : ℕ)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hconditional :
      ∀ k : ExactLengthCountVector E,
        Tendsto
          (fun N ↦
            averagedConditionalRetainedExactLengthCountVectorLaw
              N (Lseq N) E k)
          atTop
          (𝓝 (independentPoissonExactLengthVectorMass lam k))) :
    ExactLengthCountVectorConvergesToIndependentPoisson
      Lseq E lam := by
  apply corollary_fourteen_eight_counts_of_retained_finite_law
    hC lam E Lseq hwindow
  intro k
  apply (hconditional k).congr'
  exact Eventually.of_forall fun N ↦
    averagedConditionalRetainedExactLengthCountVectorLaw_eq_finite
      N (Lseq N) E k

/-!
## Canonical closure from the marked Laplace theorem

Prime encoding turns the finite count vector into a positive-integer-valued
random variable.  The constant marked tests

`g_s(t,e) = s log(p_e)`

are precisely its inverse-power transforms.  The elementary Dirichlet
inversion lemma therefore converts the marked Laplace convergence of
Section 14.4 into convergence of every joint atom.
-/

/--
Corollary 14.9 under the canonical arithmetic and probabilistic inputs.

There is no additional retained-law, convergence-determining, or
de-truncation premise: those steps are discharged respectively by the
prime-code transform argument and the complete marked Laplace theorem.
-/
theorem corollary_fourteen_eight_counts
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C : ℝ} (hC : 0 ≤ C)
    (lam : ℝ≥0) (E : ℕ)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hscale :
      Tendsto
        (fun N ↦ criticalSpatialScale N (Lseq N))
        atTop (𝓝 (lam : ℝ))) :
    ExactLengthCountVectorConvergesToIndependentPoisson
      Lseq E lam := by
  have htransform :
      ∀ s : ℕ,
        Tendsto
          (fun N ↦ inversePowerTransform
            (finiteEncodedExactLengthCountLaw
              N (Lseq N) E) s)
          atTop
          (𝓝 (inversePowerTransform
            (encodedIndependentPoissonExactLengthLaw lam E) s)) := by
    intro s
    have hLap :=
      sectionFourteenFour_laplaceFunctional
        hAGG hC hES hConductor hDivisor
        (E := E)
        (N := fun N : ℕ ↦ N)
        (L := Lseq)
        (g := primeLogTest (s : ℝ))
        tendsto_id hwindow hscale
        (fun e _he ↦ continuousOn_primeLogTest
          (s : ℝ) e (Set.Icc (1 : ℝ) 2))
        (fun t e ↦ primeLogTest_nonneg
          (s := (s : ℝ)) (by positivity) t e)
    have hInversePower :
        Tendsto
          (fun N ↦ inversePowerTransform
            (finiteEncodedExactLengthCountLaw
              N (Lseq N) E) s)
          atTop
          (𝓝 (Real.exp
            (-((lam : ℝ) *
              ∫ t in Set.Ico (1 : ℝ) 2,
                ∑ e ∈ Finset.range (E + 1),
                  (1 / (2 : ℝ) ^ (e + 1)) *
                    (1 -
                      Real.exp
                        (-primeLogTest
                          (s : ℝ) t e)))))) := by
      apply hLap.congr'
      exact Eventually.of_forall fun N ↦
        (inversePowerTransform_finiteEncodedExactLengthCountLaw_eq
          N (Lseq N) E s).symm
    rw [
      inversePowerTransform_encodedIndependentPoissonExactLengthLaw_eq_limit]
    exact hInversePower
  have hatoms :=
    tendsto_atoms_of_inversePowerTransforms
      (p := fun N ↦
        finiteEncodedExactLengthCountLaw N (Lseq N) E)
      (q := encodedIndependentPoissonExactLengthLaw lam E)
      (fun N m ↦
        finiteEncodedExactLengthCountLaw_nonneg
          N (Lseq N) E m)
      (fun N ↦
        hasSum_finiteEncodedExactLengthCountLaw
          N (Lseq N) E)
      (encodedIndependentPoissonExactLengthLaw_nonneg lam E)
      (hasSum_encodedIndependentPoissonExactLengthLaw lam E)
      (by
        simp only [
          finiteEncodedExactLengthCountLaw_zero,
          encodedIndependentPoissonExactLengthLaw_zero]
        exact tendsto_const_nhds)
      htransform
  intro k
  have hk := hatoms (primeCode k)
  rw [encodedIndependentPoissonExactLengthLaw_primeCode] at hk
  apply hk.congr'
  exact Eventually.of_forall fun N ↦ by
    change
      finiteEncodedExactLengthCountLaw
          N (Lseq N) E (primeCode k) =
        infiniteExactLengthCountVectorLaw
          N (Lseq N) E k
    rw [finiteEncodedExactLengthCountLaw_primeCode,
      infiniteExactLengthCountVectorLaw_eq_finite]

end

end CorollaryFourteenEightCounts
end PaperC
