import PaperC.Asymptotics.MaskedFirstMomentCritical
import PaperC.Probability.MarkedDetruncation
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Critical-window de-truncation for the marked process

This module completes the quantitative final paragraph of Section 14.
Combining the exact event inclusion from `MarkedDetruncation` with the
uniformly masked first moment of Proposition 14.1 gives

`P(some mark > E) ≤ N / 2^(L+E+1) + o(1)`.

Along every sequence for which `N / 2^L → λ`, this yields the literal
limsup bound

`limsup P(some mark > E) ≤ λ / 2^(E+1)`,

and hence uniform tightness of the mark coordinate.  The order of
quantifiers is the one in the manuscript: `E` is fixed before `N → ∞`.
-/

open scoped BigOperators Topology
open Filter MeasureTheory

namespace PaperC
namespace MarkedDetruncationCritical

open MarkedDetruncation

noncomputable section

noncomputable local instance instIsProbabilityMeasureInfiniteRademacher :
    IsProbabilityMeasure
      InfiniteRademacher.infiniteRademacherMeasure := by
  unfold InfiniteRademacher.infiniteRademacherMeasure
  infer_instance

/--
Adding a fixed mark cutoff to a run length only widens the fixed critical
window by `E + 1`.
-/
theorem shifted_runLength_mem
    {C : ℝ} {N L E : ℕ}
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    CriticalRunWindow.InRunLengthWindow
      (C + (E + 1 : ℕ)) N (L + E + 1) := by
  unfold CriticalRunWindow.InRunLengthWindow at hrun ⊢
  have hrewrite :
      (((L + E + 1 : ℕ) : ℝ) -
          Real.log N / Real.log 2) =
        ((L : ℝ) - Real.log N / Real.log 2) +
          ((E + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hrewrite]
  calc
    |((L : ℝ) - Real.log N / Real.log 2) +
        ((E + 1 : ℕ) : ℝ)|
        ≤
        |(L : ℝ) - Real.log N / Real.log 2| +
          |((E + 1 : ℕ) : ℝ)| :=
      abs_add_le _ _
    _ ≤ C + ((E + 1 : ℕ) : ℝ) := by
      exact add_le_add hrun (by
        rw [abs_of_nonneg]
        positivity)

/--
Proposition 14.1 at the shifted length, specialized to the full dyadic mask:
the expectation of longer starts is eventually bounded by its geometric
baseline plus an arbitrary error.
-/
theorem longStartExpectation_eventually_le_baseline_add
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ L : ℕ,
          CriticalRunWindow.InRunLengthWindow C N L →
          (dyadicExpectation N (L + E + 1) : ℝ) ≤
            (N : ℝ) / (2 : ℝ) ^ (L + E + 1) + ε := by
  let Cshift : ℝ := C + ((E + 1 : ℕ) : ℝ)
  have hCshift : 0 ≤ Cshift := by
    dsimp only [Cshift]
    positivity
  have hfirst :=
    MaskedFirstMomentCritical.maskedFirstMomentError_uniformLittleOOne
      hCshift
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hfirst ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  have hshift :
      CriticalRunWindow.InRunLengthWindow
        Cshift N (L + E + 1) := by
    simpa only [Cshift] using
      shifted_runLength_mem (E := E) hrun
  have herror :=
    hN₀ N hN (L + E + 1) hshift
      (dyadicBlock N) (by rfl)
  have hcard : (dyadicBlock N).card = N := by
    exact TouchingPairs.card_dyadicBlock N
  have hcast :
      |(dyadicExpectation N (L + E + 1) : ℝ) -
          (N : ℝ) / (2 : ℝ) ^ (L + E + 1)| ≤ ε := by
    simpa only [
      MaskedFirstMomentCritical.maskedFirstMomentErrorReal,
      MaskedFirstMoment.maskedDyadicExpectation,
      dyadicExpectation, hcard, Rat.cast_abs, Rat.cast_sub,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
      Rat.cast_ofNat] using herror
  linarith [le_abs_self
    ((dyadicExpectation N (L + E + 1) : ℝ) -
      (N : ℝ) / (2 : ℝ) ^ (L + E + 1))]

/--
Finite-`N` de-truncation estimate in the critical window:

`P(mark > E) ≤ N 2^(-(L+E+1)) + ε`

eventually, uniformly in `L`.
-/
theorem markTailProbability_eventually_le_baseline_add
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ L : ℕ,
          CriticalRunWindow.InRunLengthWindow C N L →
          infiniteMarkTailProbability N L E ≤
            (N : ℝ) / (2 : ℝ) ^ (L + E + 1) + ε := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ :=
    longStartExpectation_eventually_le_baseline_add hC E ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  exact
    (infiniteMarkTailProbability_le_longStartExpectation N L E).trans
      (hN₀ N hN L hrun)

/-- The mark-tail probability is nonnegative. -/
theorem infiniteMarkTailProbability_nonneg (N L E : ℕ) :
    0 ≤ infiniteMarkTailProbability N L E := by
  unfold infiniteMarkTailProbability
  exact ENNReal.toReal_nonneg

/-- The mark-tail probability is at most one. -/
theorem infiniteMarkTailProbability_le_one (N L E : ℕ) :
    infiniteMarkTailProbability N L E ≤ 1 := by
  unfold infiniteMarkTailProbability
  apply ENNReal.toReal_le_of_le_ofReal zero_le_one
  simpa only [ENNReal.ofReal_one, measure_univ] using
    (measure_mono
      (μ := InfiniteRademacher.infiniteRademacherMeasure)
      (Set.subset_univ (infiniteMarkTailEvent N L E)))

/--
Quantified form of the manuscript's limsup estimate.  This form is often more
convenient downstream than `Filter.limsup`: every positive slack is valid
from one common threshold onwards.
-/
theorem markTailProbability_eventual_geometric_bound
    {C lam : ℝ} (hC : 0 ≤ C)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hbalance :
      Tendsto
        (fun N : ℕ => (N : ℝ) / (2 : ℝ) ^ (Lseq N))
        atTop (𝓝 lam))
    (E : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        infiniteMarkTailProbability N (Lseq N) E ≤
          lam / (2 : ℝ) ^ (E + 1) + ε := by
  intro ε hε
  obtain ⟨Nfirst, hfirst⟩ :=
    markTailProbability_eventually_le_baseline_add hC E
      (ε / 2) (by linarith)
  obtain ⟨Nwindow, hNwindow⟩ := eventually_atTop.1 hwindow
  have hbalanceUpper :
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) / (2 : ℝ) ^ (Lseq N) < lam + ε / 2 :=
    (tendsto_order.1 hbalance).2 (lam + ε / 2) (by linarith)
  obtain ⟨Nbalance, hNbalance⟩ :=
    eventually_atTop.1 hbalanceUpper
  refine ⟨max Nfirst (max Nwindow Nbalance), ?_⟩
  intro N hN
  have hNfirst : Nfirst ≤ N :=
    (le_max_left Nfirst (max Nwindow Nbalance)).trans hN
  have htail :=
    hfirst N hNfirst (Lseq N)
      (hNwindow N
        ((le_trans (le_max_left Nwindow Nbalance)
          (le_max_right Nfirst (max Nwindow Nbalance))).trans hN))
  have hbal :=
    hNbalance N
      ((le_trans (le_max_right Nwindow Nbalance)
        (le_max_right Nfirst (max Nwindow Nbalance))).trans hN)
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (E + 1) := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hbaseRewrite :
      (N : ℝ) / (2 : ℝ) ^ (Lseq N + E + 1) =
        ((N : ℝ) / (2 : ℝ) ^ (Lseq N)) /
          (2 : ℝ) ^ (E + 1) := by
    rw [show Lseq N + E + 1 = Lseq N + (E + 1) by omega,
      pow_add]
    ring
  have hbaseBound :
      (N : ℝ) / (2 : ℝ) ^ (Lseq N + E + 1) ≤
        lam / (2 : ℝ) ^ (E + 1) + ε / 2 := by
    rw [hbaseRewrite]
    have hdiv :
        ((N : ℝ) / (2 : ℝ) ^ (Lseq N)) /
            (2 : ℝ) ^ (E + 1) ≤
          (lam + ε / 2) / (2 : ℝ) ^ (E + 1) :=
      div_le_div_of_nonneg_right hbal.le (by positivity)
    have herr :
        (ε / 2) / (2 : ℝ) ^ (E + 1) ≤ ε / 2 :=
      div_le_self (by linarith) hpow
    calc
      ((N : ℝ) / (2 : ℝ) ^ (Lseq N)) /
            (2 : ℝ) ^ (E + 1)
          ≤ (lam + ε / 2) / (2 : ℝ) ^ (E + 1) :=
        hdiv
      _ =
          lam / (2 : ℝ) ^ (E + 1) +
            (ε / 2) / (2 : ℝ) ^ (E + 1) := by
        ring
      _ ≤ lam / (2 : ℝ) ^ (E + 1) + ε / 2 :=
        add_le_add_right herr _
  exact htail.trans (by linarith)

/--
Literal limsup form of the final estimate in Section 14.
-/
theorem markTailProbability_limsup_le_geometric
    {C lam : ℝ} (hC : 0 ≤ C)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hbalance :
      Tendsto
        (fun N : ℕ => (N : ℝ) / (2 : ℝ) ^ (Lseq N))
        atTop (𝓝 lam))
    (E : ℕ) :
    limsup
        (fun N : ℕ =>
          infiniteMarkTailProbability N (Lseq N) E)
        atTop ≤
      lam / (2 : ℝ) ^ (E + 1) := by
  let p : ℕ → ℝ :=
    fun N => infiniteMarkTailProbability N (Lseq N) E
  have hpNonneg : ∀ N, 0 ≤ p N :=
    fun N => infiniteMarkTailProbability_nonneg N (Lseq N) E
  have hpOne : ∀ N, p N ≤ 1 :=
    fun N => infiniteMarkTailProbability_le_one N (Lseq N) E
  have hpLowerBounded :
      atTop.IsBoundedUnder (fun a b : ℝ => a ≥ b) p :=
    isBoundedUnder_of_eventually_ge
      (Eventually.of_forall hpNonneg)
  have hcob :
      atTop.IsCoboundedUnder (fun a b : ℝ => a ≤ b) p :=
    hpLowerBounded.isCoboundedUnder_le
  have hbdd :
      atTop.IsBoundedUnder (fun a b : ℝ => a ≤ b) p :=
    isBoundedUnder_of_eventually_le
      (Eventually.of_forall hpOne)
  rw [limsup_le_iff hcob hbdd]
  intro y hy
  let ε : ℝ :=
    (y - lam / (2 : ℝ) ^ (E + 1)) / 2
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  obtain ⟨N₀, hN₀⟩ :=
    markTailProbability_eventual_geometric_bound
      hC Lseq hwindow hbalance E ε hε
  exact eventually_atTop.2 ⟨N₀, fun N hN => by
    dsimp only [p]
    have hbound := hN₀ N hN
    dsimp only [ε] at hbound
    linarith⟩

/--
Uniform tightness of the mark coordinate along every critical subsequence
with `N / 2^L → λ`.
-/
theorem markTailProbabilities_uniformly_tight
    {C lam : ℝ} (hC : 0 ≤ C)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hbalance :
      Tendsto
        (fun N : ℕ => (N : ℝ) / (2 : ℝ) ^ (Lseq N))
        atTop (𝓝 lam)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ E N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        infiniteMarkTailProbability N (Lseq N) E ≤ ε := by
  intro ε hε
  have hpow :
      Tendsto (fun E : ℕ => (2 : ℝ) ^ (E + 1))
        atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt
      (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)
  have hgeom :
      Tendsto (fun E : ℕ => lam / (2 : ℝ) ^ (E + 1))
        atTop (𝓝 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hpow
    simpa only [div_eq_mul_inv, Function.comp_apply, mul_zero] using
      tendsto_const_nhds.mul hinv
  have hevent :
      ∀ᶠ E : ℕ in atTop,
        lam / (2 : ℝ) ^ (E + 1) < ε / 2 :=
    (tendsto_order.1 hgeom).2 (ε / 2) (by linarith)
  obtain ⟨E, hE⟩ := hevent.exists
  obtain ⟨N₀, hN₀⟩ :=
    markTailProbability_eventual_geometric_bound
      hC Lseq hwindow hbalance E (ε / 2) (by linarith)
  exact ⟨E, N₀, fun N hN => (hN₀ N hN).trans (by linarith)⟩

end

end MarkedDetruncationCritical
end PaperC
