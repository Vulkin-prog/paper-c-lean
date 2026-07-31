import PaperC.Analysis.CriticalWeightedDefect
import PaperC.Arithmetic.ChannelMultiplicityBounds
import PaperC.Asymptotics.FourPowLittleOHeight
import PaperC.Combinatorics.ShallowCorePairs
import PaperC.Probability.CriticalRunWindow

set_option maxHeartbeats 1800000

/-!
# The shallow-core systematic exponent in the critical window

For a pair in the shallow-core population of Proposition 7.5, let
`q = max(a,b)` be the height of its selected canonical channel.  If the
systematic exponent `σ` is positive, the canonical multiplicity is at least
two and the channel packing estimate gives

`q * σ ≤ L`.

Membership in the shallow-core population excludes the small-height sector,
so the same selected candidate satisfies

`sqrt(log(L+1)) < q`.

As `L+1` tends uniformly to infinity in the critical run-length window, this
proves that the finite maximum of `σ` is uniformly `o(L+1)`.  The empty
population and the pointwise branch `σ=0` are included explicitly.  The
generic height-exponentiation closure then yields

`4^maxShallowCoreSigma = N^o(1)`.
-/

namespace PaperC
namespace ShallowCoreSigmaCritical

open Affine.CanonicalRationalCode
open RationalMassFinite
open ResidualMasses
open ShallowCorePairs
open SmallHeightLargeProductPairs

noncomputable section

/--
Proof-independent version of the finite systematic-exponent maximum.  The
value below the harmless threshold `N=2` is zero.
-/
noncomputable def maxShallowCoreSigmaTotal
    (A N L : ℕ) : ℕ :=
  if hN : 2 ≤ N then
    maxShallowCoreSigma N A L hN
  else 0

/--
A power-of-four lower bound for the height forces the real logarithmic
square root above the corresponding natural threshold.
-/
private theorem cast_le_sqrt_log_of_four_pow_sq_le
    {M B : ℕ}
    (hpower : 4 ^ (M ^ 2) ≤ B) :
    (M : ℝ) ≤ Real.sqrt (Real.log (B : ℝ)) := by
  have hpowerReal :
      (((4 ^ (M ^ 2) : ℕ) : ℝ)) ≤ (B : ℝ) := by
    exact_mod_cast hpower
  have hlogPower :
      Real.log (((4 ^ (M ^ 2) : ℕ) : ℝ)) ≤
        Real.log (B : ℝ) :=
    Real.log_le_log (by positivity) hpowerReal
  have hlogFour :
      (1 : ℝ) ≤ Real.log 4 := by
    have hfour :
        Real.log (4 : ℝ) =
          Real.log 2 + Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0)]
    rw [hfour]
    nlinarith [Real.log_two_gt_d9]
  have hsqLogFour :
      ((M : ℝ) ^ 2) ≤
        ((M : ℝ) ^ 2) * Real.log 4 := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hlogFour (sq_nonneg (M : ℝ)))
  have hlogPower' :
      ((M : ℝ) ^ 2) * Real.log 4 ≤
        Real.log (B : ℝ) := by
    calc
      ((M : ℝ) ^ 2) * Real.log 4 =
          Real.log (((4 ^ (M ^ 2) : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Real.log_pow]
        push_cast
        ring
      _ ≤ Real.log (B : ℝ) := hlogPower
  exact Real.le_sqrt_of_sq_le (hsqLogFour.trans hlogPower')

/--
Pointwise shallow-core estimate.  The proof separates `σ=0`; in the positive
branch it exposes the selected canonical candidate and uses the channel
packing inequality.
-/
private theorem pairSigma_cast_le_epsilon_height
    {N A L M : ℕ} {hN : 2 ≤ N}
    {ε : ℝ} (hε : 0 < ε)
    (hM : 1 / ε < (M : ℝ))
    (hpower : 4 ^ (M ^ 2) ≤ L + 1)
    (pair : SeparatedDyadicPair N L)
    (hpair : pair ∈ shallowCorePairs N A L hN) :
    (pairSigma A pair : ℝ) ≤
      ε * ((L + 1 : ℕ) : ℝ) := by
  by_cases hsigmaZero : pairSigma A pair = 0
  · simp only [hsigmaZero, Nat.cast_zero]
    positivity
  · have hsigmaPos : 0 < pairSigma A pair :=
      Nat.pos_of_ne_zero hsigmaZero
    have hmultiplicity :
        2 ≤ canonicalMultiplicity
          A L pair.1.1 pair.1.2 := by
      apply two_le_canonicalMultiplicity_of_sigma_pos
      simpa only [pairSigma] using hsigmaPos
    obtain ⟨c, hchoice, _hmCandidate⟩ :=
      exists_canonical_candidate_of_two_le_multiplicity
        hmultiplicity
    have hnotSmall :
        ¬ HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 :=
      (mem_shallowCorePairs.mp hpair).2.1
    have hheightNotLe :
        ¬ ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) ≤
            Real.sqrt
              (Real.log ((L + 1 : ℕ) : ℝ)) := by
      intro hheight
      exact hnotSmall ⟨c, hchoice, hheight⟩
    have hsqrtLtHeight :
        Real.sqrt (Real.log ((L + 1 : ℕ) : ℝ)) <
          ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) :=
      lt_of_not_ge hheightNotLe
    have hMLeSqrt :
        (M : ℝ) ≤
          Real.sqrt (Real.log ((L + 1 : ℕ) : ℝ)) :=
      cast_le_sqrt_log_of_four_pow_sq_le hpower
    have hMltHeight :
        (M : ℝ) <
          ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) :=
      hMLeSqrt.trans_lt hsqrtLtHeight
    have hpackingNat :
        Nat.max c.1.1 c.1.2 *
            pairSigma A pair ≤ L := by
      have hpacking :=
        maxStep_mul_channelSigma_le
          L c.1.1 c.1.2
          (candidate_fst_pos c)
          (candidate_snd_pos c)
          (candidate_coprime c)
          (pairChannelError
            pair.1.1 pair.1.2 c.1.1 c.1.2)
      rw [← canonicalPairSigma_eq_channelSigma_of_choice
          hchoice] at hpacking
      simpa only [pairSigma] using hpacking
    have hpackingReal :
        ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) *
            (pairSigma A pair : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hpackingNat
    have hMpacking :
        (M : ℝ) * (pairSigma A pair : ℝ) ≤
          ((L + 1 : ℕ) : ℝ) := by
      calc
        (M : ℝ) * (pairSigma A pair : ℝ) ≤
            ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) *
              (pairSigma A pair : ℝ) :=
          mul_le_mul_of_nonneg_right hMltHeight.le
            (by positivity)
        _ ≤ (L : ℝ) := hpackingReal
        _ ≤ ((L + 1 : ℕ) : ℝ) := by
          push_cast
          linarith
    have hscale :
        (1 : ℝ) ≤ ε * (M : ℝ) := by
      have honeLt : (1 : ℝ) < (M : ℝ) * ε :=
        (div_lt_iff₀ hε).1 hM
      nlinarith
    calc
      (pairSigma A pair : ℝ) =
          1 * (pairSigma A pair : ℝ) := by ring
      _ ≤
          (ε * (M : ℝ)) *
            (pairSigma A pair : ℝ) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
      _ =
          ε * ((M : ℝ) * (pairSigma A pair : ℝ)) := by ring
      _ ≤ ε * ((L + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hMpacking hε.le

/--
The maximum systematic exponent on the shallow-core sector is uniformly
little-oh of the critical height `L+1`.
-/
theorem maxShallowCoreSigma_uniformLittleO
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L => (maxShallowCoreSigmaTotal A N L : ℝ))
      (fun _ L => ((L + 1 : ℕ) : ℝ)) := by
  intro ε hε
  obtain ⟨M : ℕ, hM⟩ :=
    exists_nat_gt (1 / ε)
  let T : ℕ := 4 ^ (M ^ 2)
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hNadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nheight, hNheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := CriticalRunWindow.upperConstant)
      CriticalRunWindow.lowerConstant_pos T
  refine
    ⟨max 2 (max Nwindow (max Nadm Nheight)), ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail :
      max Nwindow (max Nadm Nheight) ≤ N :=
    (le_max_right _ _).trans hN
  have hNwindowN : Nwindow ≤ N :=
    (le_max_left _ _).trans hNtail
  have hNtail' : max Nadm Nheight ≤ N :=
    (le_max_right _ _).trans hNtail
  have hNadmN : Nadm ≤ N :=
    (le_max_left _ _).trans hNtail'
  have hNheightN : Nheight ≤ N :=
    (le_max_right _ _).trans hNtail'
  have hfirst :=
    hNwindow N hNwindowN L hrun
  have hadmissible :
      CriticalWeightedDefect.Admissible
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1) :=
    hNadm N hNadmN (L + 1) hfirst.1
  have hheight : T ≤ L + 1 :=
    hNheight N hNheightN (L + 1) hadmissible
  have hmax :
      (maxShallowCoreSigma N A L hNtwo : ℝ) ≤
        ε * ((L + 1 : ℕ) : ℝ) := by
    by_cases hpopulation :
        shallowCorePairs N A L hNtwo = ∅
    · simp [maxShallowCoreSigma, hpopulation]
      positivity
    · apply maxShallowCoreSigma_cast_le
      · positivity
      · intro pair hpair
        exact pairSigma_cast_le_epsilon_height
          hε hM (by simpa only [T] using hheight)
          pair hpair
  rw [abs_of_nonneg
      (show 0 ≤ (maxShallowCoreSigmaTotal A N L : ℝ) by
        positivity),
    abs_of_nonneg
      (show 0 ≤ ((L + 1 : ℕ) : ℝ) by positivity)]
  simpa only [maxShallowCoreSigmaTotal, dif_pos hNtwo] using hmax

/--
Exponentiating the shallow-core systematic envelope produces a uniformly
subpolynomial factor in the critical run-length window.
-/
theorem four_pow_maxShallowCoreSigma_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (((4 ^ maxShallowCoreSigmaTotal A N L : ℕ) : ℝ))) := by
  have hupperNonneg :
      0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  apply
    FourPowLittleOHeight.uniformSubpolynomialOn_four_pow_of_uniformLittleO_height
      (maxShallowCoreSigmaTotal A)
      (fun _ L => ((L + 1 : ℕ) : ℝ))
      CriticalRunWindow.upperConstant hupperNonneg
  · exact maxShallowCoreSigma_uniformLittleO hC A
  · intro N L _hrun
    positivity
  · obtain ⟨Nwindow, hNwindow⟩ :=
      CriticalRunWindow.firstMomentWindow_eventually hC
    refine ⟨Nwindow, ?_⟩
    intro N hN L hrun
    exact (hNwindow N hN L hrun).1.2.2.2

end

end ShallowCoreSigmaCritical
end PaperC
