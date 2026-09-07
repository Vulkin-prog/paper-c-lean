import PaperCV282.AffineCrossoverPrimeClock

/-! # Eventual future neutrality at the actual hard prime cutoff

The truncation level is fixed before taking the sequence limit. The cutoff
and border inclusions are proved from the logarithmic window assumptions;
no uniform neutrality of infinitely many future coordinates is assumed.
-/
namespace PaperC.V282.AffineCrossoverFutureCutoff

open Filter Topology Affine MeasureTheory ProbabilityTheory InfiniteRademacher
open AffineBorderCylinders AffineBorderPrimeClock AffineCrossoverFuture
open AffineCrossoverPrimeClock CrossoverPrimeClockCutoff CrossoverPrimeClockStable
open MicroscopicBorderEvents HardPoissonRates GeometricClusterTarget

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

/-- Proof-independent statement of the finite-dimensional neutrality condition. -/
def FutureNeutralAt {Y : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]
    (G : SampleSpace Y →ₗ[F₂] W) (L K : ℕ) : Prop :=
  ∃ hLY : L ≤ Y, ∃ hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y,
    FutureNeutral G hLY hcut

theorem futureNeutralAt_iff {Y L K : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]
    (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y)
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y) :
    FutureNeutralAt G L K ↔ FutureNeutral G hLY hcut := by
  constructor
  · rintro ⟨hLY', hcut', h⟩
    exact h
  · exact fun h => ⟨hLY, hcut, h⟩

/-- The next-prime convention used by the affine projection also fits the genuine cutoff. -/
theorem future_projection_hard_cutoff_eventually (beta : ℝ) (hbeta : 0 < beta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L K : ℕ, 2^(K+1) ≤ L →
      (L+1 : ℝ) ≤ beta*Real.log M →
      L ≤ hardCutoff M ∧ Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ hardCutoff M := by
  obtain ⟨Mzero,hzero⟩ := clock_cylinder_hard_eventually beta hbeta
  refine ⟨Mzero,?_⟩
  intro M hM L K hL hupper
  obtain ⟨hc,hp⟩ := hzero M hM L (K+1) hL hupper
  exact ⟨(by omega), nth_prime_le_iff.mpr (by omega)⟩

theorem future_projection_cutoff_along_subsequence (sizes lengths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta : ℝ) (hbeta : 0 < beta)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n)) (K : ℕ) :
    ∀ᶠ n in atTop, lengths n ≤ hardCutoff (sizes n) ∧
      Nat.nth Nat.Prime (Nat.primeCounting (lengths n)+K) ≤ hardCutoff (sizes n) := by
  obtain ⟨Mzero,hzero⟩ := future_projection_hard_cutoff_eventually (beta+1) (by linarith)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  filter_upwards [hupper, hsizes.eventually (eventually_ge_atTop Mzero),
    hlengths.eventually (eventually_ge_atTop (2^(K+1))),
    hlog.eventually (eventually_ge_atTop (1 : ℝ))] with n hu hn hl hlogn
  change 1 ≤ Real.log (sizes n) at hlogn
  exact hzero (sizes n) hn (lengths n) K hl (by nlinarith)

/-- For each fixed K, eventual finite neutrality yields the exact nested conditional record law. -/
theorem capped_clock_law_eventually
    (cutoffs lengths : ℕ → ℕ) {W : ℕ → Type*}
    [∀ n, AddCommGroup (W n)] [∀ n, Module F₂ (W n)]
    (G : ∀ n, SampleSpace (cutoffs n) →ₗ[F₂] W n) (b : ∀ n, W n)
    (hstack : ∀ᶠ n in atTop, ∃ hLY : lengths n ≤ cutoffs n,
      Compatible ((G n).prod (borderProjection hLY)) (b n,0))
    (hneutral : ∀ K, ∀ᶠ n in atTop, FutureNeutralAt (G n) (lengths n) K) (K : ℕ) :
    ∀ᶠ n in atTop,
      (cond (cond infiniteRademacherMeasure (affineCylinder (G n) (b n))) (borderEvent (lengths n))).map
        (actualClockRecord (lengths n) K) =
        (geometricMeasure halfSuccess).map (fun j => (true,min j K)) := by
  filter_upwards [hstack, hneutral K] with n hs hn
  obtain ⟨hLY,hs⟩ := hs
  obtain ⟨_,hcut,hn⟩ := hn
  exact nested_conditional_actualClockRecord (G n) (b n) hLY hcut hs hn

end
end PaperC.V282.AffineCrossoverFutureCutoff
