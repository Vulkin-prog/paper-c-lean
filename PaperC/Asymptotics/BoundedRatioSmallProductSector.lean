import PaperC.Asymptotics.BoundedRatioCorrectedDefectEnvelope
import PaperC.Asymptotics.BoundedRatioSectorClosure
import PaperC.Asymptotics.CriticalRationalMassEnvelopes
import PaperC.Asymptotics.LinearProduct
import PaperC.Asymptotics.QuadraticAndInterpolationClosure
import PaperC.Asymptotics.RationalPowerLittleO

set_option maxHeartbeats 3600000

/-!
# The bounded-ratio small-product sector

This file closes Lemma 17.14 on the literal first fibre of the ordered
Section 17 classifier.  The proof keeps the two branches from Proposition
7.3 visible:

* when `σ = 0`, the quadratic mass is bounded by the number of ambient
  pairs;
* when `σ > 0`, `4^σ ≤ 2(4^σ-1)` charges the branch to the complete
  bounded-ratio base-four rational mass.

On `P# ≤ N`, every selected residual prime is at least `L+2`.  Hence the
number `c#` of residual components is at most

`log₂ N / log₂ (L+2)`.

This gives a common subpolynomial residual factor.  The bounded-ratio
corrected-defect envelope supplies the other subpolynomial factor.  The two
branches are therefore `N^(2+o_{C,κ₀}(1))`; interpolation with the exact
bounded relational-host population gives `N^(7/4+o_{C,κ₀}(1))`, and hence
the little-oh statement required by `SmallPrimeProductSectorStabilityStatement`.
-/

namespace PaperC
namespace BoundedRatioSmallProductSector

open scoped BigOperators
open BoundedRatioGeometry
open BoundedRatioResidualMasses
open BoundedRatioSectorClosure
open CanonicalResidualComponents
open PropositionSixteenOne
open ResidualComponentCounts
open SectionElevenPartition

noncomputable section

/-! ## The residual-component budget supplied by `P# ≤ N` -/

/-- Real upper bound for natural-number division. -/
private theorem cast_nat_div_le_div
    {a b : ℕ} (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)).2
  exact_mod_cast Nat.div_mul_le_self a b

/-- The integral binary logarithm is bounded by the corresponding real one. -/
private theorem natLogTwo_cast_le_log_div
    {N : ℕ} (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
  have hpowNat :
      2 ^ Nat.log 2 N ≤ N :=
    Nat.pow_log_le_self 2 (by omega)
  have hpowReal :
      ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hpowNat
  have hlogs :=
    Real.log_le_log
      (by positivity :
        (0 : ℝ) < ((2 ^ Nat.log 2 N : ℕ) : ℝ))
      hpowReal
  rw [Nat.cast_pow, Real.log_pow] at hlogs
  have hlogTwoPos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  rw [le_div_iff₀ hlogTwoPos]
  simpa [mul_comm] using hlogs

/--
The number of canonical residual factors is at most the binary-logarithmic
quotient forced by `P# ≤ N`.
-/
theorem canonicalResidualComponentCount_le_logQuotient
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (hsmall : HasSmallCanonicalPrimeProduct A hN pair) :
    canonicalResidualComponentCount
        A pair.1.1 pair.1.2 L ≤
      Nat.log 2 N / Nat.log 2 (L + 2) := by
  let primes :=
    canonicalResidualCertificatePrimes
      (A := A) (L := L)
      (show 1 ≤ pair.1.1 by
        exact (by omega : 1 ≤ 2).trans
          (pair_coordinates_two_le hN pair).1)
      (show 1 ≤ pair.1.2 by
        exact (by omega : 1 ≤ 2).trans
          (pair_coordinates_two_le hN pair).2)
  let d := Nat.log 2 (L + 2)
  have hd : 0 < d := by
    dsimp only [d]
    exact Nat.log_pos (by norm_num) (by omega)
  have hfactor :
      ∀ p ∈ primes, L + 2 ≤ p := by
    intro p hp
    have hlarge :=
      prime_large_of_mem_canonicalResidualCertificatePrimes
        (show 1 ≤ pair.1.1 by
          exact (by omega : 1 ≤ 2).trans
            (pair_coordinates_two_le hN pair).1)
        (show 1 ≤ pair.1.2 by
          exact (by omega : 1 ≤ 2).trans
            (pair_coordinates_two_le hN pair).2)
        hp
    exact Nat.succ_le_iff.mpr hlarge.2
  have hbasePow :
      (L + 2) ^ primes.card ≤
        canonicalResidualPrimeProduct
          (A := A) (L := L)
          (show 1 ≤ pair.1.1 by
            exact (by omega : 1 ≤ 2).trans
              (pair_coordinates_two_le hN pair).1)
          (show 1 ≤ pair.1.2 by
            exact (by omega : 1 ≤ 2).trans
              (pair_coordinates_two_le hN pair).2) := by
    unfold canonicalResidualPrimeProduct
    change (L + 2) ^ primes.card ≤ ∏ p ∈ primes, p
    calc
      (L + 2) ^ primes.card =
          ∏ _p ∈ primes, (L + 2) := by simp
      _ ≤ ∏ p ∈ primes, p :=
        Finset.prod_le_prod
          (fun _p _hp ↦ Nat.zero_le _)
          hfactor
  have hdPow : 2 ^ d ≤ L + 2 := by
    dsimp only [d]
    exact Nat.pow_log_le_self 2 (by omega)
  have htwoPow :
      2 ^ (d * primes.card) ≤ N := by
    calc
      2 ^ (d * primes.card) =
          (2 ^ d) ^ primes.card := by
        rw [pow_mul]
      _ ≤ (L + 2) ^ primes.card :=
        Nat.pow_le_pow_left hdPow _
      _ ≤
          canonicalResidualPrimeProduct
            (A := A) (L := L)
            (show 1 ≤ pair.1.1 by
              exact (by omega : 1 ≤ 2).trans
                (pair_coordinates_two_le hN pair).1)
            (show 1 ≤ pair.1.2 by
              exact (by omega : 1 ≤ 2).trans
                (pair_coordinates_two_le hN pair).2) :=
        hbasePow
      _ ≤ N := hsmall
  have hlog :
      d * primes.card ≤ Nat.log 2 N := by
    exact Nat.le_log_of_pow_le (by norm_num) htwoPow
  have hcard :
      primes.card =
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L := by
    dsimp only [primes]
    exact
      canonicalResidualPrimeProduct_factorCount
        (pair_coordinates_two_le hN pair).1
        (pair_coordinates_two_le hN pair).2
  rw [← hcard]
  apply (Nat.le_div_iff_mul_le hd).2
  simpa only [Nat.mul_comm] using hlog

/-- Common exponent for the residual-component loss on `P# ≤ N`. -/
def smallProductComponentExponent (N L : ℕ) : ℕ :=
  Nat.log 2 N / Nat.log 2 (L + 2)

/-- Common fourth-power loss contributed by the residual components. -/
def smallProductComponentFactor (N L : ℕ) : ℝ :=
  ((4 ^ smallProductComponentExponent N L : ℕ) : ℝ)

/-- Membership in the first literal sector is exactly `P# ≤ N`. -/
theorem hasSmallCanonicalPrimeProduct_of_mem_smallProductSector
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ boundedRatioSectorPairs
        N M A L hN terminal .smallPrimeProduct) :
    HasSmallCanonicalPrimeProduct A hN pair := by
  have hsector :=
    mem_boundedRatioSectorPairs.mp hpair
  unfold boundedRatioSectorOf at hsector
  simpa only [sectorOf_eq_smallPrimeProduct_iff,
    boundedRatioSectorTests] using hsector

/-- Pointwise fourth-power component loss on the literal first sector. -/
theorem four_pow_componentCount_le_smallProductComponentFactor
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ boundedRatioSectorPairs
        N M A L hN terminal .smallPrimeProduct) :
    ((4 ^ canonicalResidualComponentCount
        A pair.1.1 pair.1.2 L : ℕ) : ℝ) ≤
      smallProductComponentFactor N L := by
  have hcount :=
    canonicalResidualComponentCount_le_logQuotient
      hN pair
      (hasSmallCanonicalPrimeProduct_of_mem_smallProductSector
        hpair)
  unfold smallProductComponentFactor
  exact_mod_cast
    (Nat.pow_le_pow_right (by norm_num : 0 < 4) hcount)

/-! ## Uniform subpolynomiality of the component loss -/

/--
The small-product component factor is uniformly subpolynomial in the
critical run-length window.
-/
theorem smallProductComponentFactor_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      smallProductComponentFactor := by
  let c₁ := CriticalRunWindow.lowerConstant
  let c₂ := CriticalRunWindow.upperConstant
  let D : ℝ := 16 / Real.log 2
  have hc₁ : 0 < c₁ := by
    simpa only [c₁] using CriticalRunWindow.lowerConstant_pos
  have hc₁c₂ : c₁ < c₂ := by
    simpa only [c₁, c₂] using
      CriticalRunWindow.lowerConstant_lt_upperConstant
  have hlogTwoPos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually hc₁ hc₁c₂
  obtain ⟨Nlog, hlog⟩ :=
    CriticalWeightedDefect.eventually_loglog_le_eight_log_height
      (c₂ := c₂) hc₁
  obtain ⟨Nheight, hheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := c₂) hc₁ 8
  have htwo :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          (((2 ^ (2 * smallProductComponentExponent N L) :
            ℕ) : ℝ))) := by
    apply
      ExpSqrtLog.uniformSubpolynomialOn_two_pow_log_div_loglog_eventually
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L => 2 * smallProductComponentExponent N L)
        D hD
    refine
      ⟨max Nwindow (max Nadm (max Nlog Nheight)), ?_⟩
    intro N hN L hrun
    have hNwindowN : Nwindow ≤ N :=
      (le_max_left _ _).trans hN
    have hNtail : max Nadm (max Nlog Nheight) ≤ N :=
      (le_max_right _ _).trans hN
    have hNadmN : Nadm ≤ N :=
      (le_max_left _ _).trans hNtail
    have hNlogHeight : max Nlog Nheight ≤ N :=
      (le_max_right _ _).trans hNtail
    have hNlogN : Nlog ≤ N :=
      (le_max_left _ _).trans hNlogHeight
    have hNheightN : Nheight ≤ N :=
      (le_max_right _ _).trans hNlogHeight
    have hcritical :
        CriticalWindowParameters.InCriticalWindow c₁ c₂ N (L + 1) := by
      simpa only [c₁, c₂] using
        (hwindow N hNwindowN L hrun).1
    have hadmissible :
        CriticalWeightedDefect.Admissible c₁ c₂ N (L + 1) :=
      hadm N hNadmN (L + 1) hcritical
    obtain ⟨hloglogPos, hloglogLe⟩ :=
      hlog N hNlogN (L + 1) hadmissible
    have hheightEight : 8 ≤ L + 1 :=
      hheight N hNheightN (L + 1) hadmissible
    have hrealLogHeight :
        Real.log (L + 1 : ℕ) ≤
          (Nat.log 2 (L + 1) : ℝ) :=
      CriticalWindowScale.real_log_le_nat_log_two hheightEight
    let d := Nat.log 2 (L + 2)
    have hdNat : 0 < d := by
      dsimp only [d]
      exact Nat.log_pos (by norm_num) (by omega)
    have hd : (0 : ℝ) < d := by exact_mod_cast hdNat
    have hlogHeightMono :
        (Nat.log 2 (L + 1) : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast
        Nat.log_mono_right (show L + 1 ≤ L + 2 by omega)
    have hloglogLeD :
        Real.log (Real.log N) ≤ 8 * (d : ℝ) := by
      exact hloglogLe.trans
        ((mul_le_mul_of_nonneg_left hrealLogHeight
            (by norm_num)).trans
          (mul_le_mul_of_nonneg_left hlogHeightMono
            (by norm_num)))
    have hNpositive : 1 ≤ N := by
      exact hadmissible.2.1.trans' (by omega)
    have hnumerator :
        (Nat.log 2 N : ℝ) ≤
          Real.log N / Real.log 2 :=
      natLogTwo_cast_le_log_div hNpositive
    have hquotient :
        (smallProductComponentExponent N L : ℝ) ≤
          (8 / Real.log 2) *
            Real.log N / Real.log (Real.log N) := by
      have hcastDiv :
          (smallProductComponentExponent N L : ℝ) ≤
            (Nat.log 2 N : ℝ) / (d : ℝ) := by
        simpa only [smallProductComponentExponent, d] using
          cast_nat_div_le_div hdNat
      refine hcastDiv.trans ?_
      apply (div_le_div_iff₀ hd hloglogPos).2
      calc
        (Nat.log 2 N : ℝ) * Real.log (Real.log N) ≤
            (Real.log N / Real.log 2) *
              Real.log (Real.log N) :=
          mul_le_mul_of_nonneg_right hnumerator hloglogPos.le
        _ ≤
            (Real.log N / Real.log 2) *
              (8 * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hloglogLeD
            (by positivity)
        _ =
            ((8 / Real.log 2) *
              Real.log N) * (d : ℝ) := by
          field_simp [hlogTwoPos.ne']
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      2 * (smallProductComponentExponent N L : ℝ) ≤
          2 *
            ((8 / Real.log 2) *
              Real.log N / Real.log (Real.log N)) :=
        mul_le_mul_of_nonneg_left hquotient (by norm_num)
      _ = D * Real.log N / Real.log (Real.log N) := by
        dsimp only [D]
        ring
  change
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (((4 ^ smallProductComponentExponent N L : ℕ) : ℝ)))
  simpa [pow_mul, pow_two] using htwo

/-! ## Finite `σ=0` and `σ>0` branches -/

/-- Canonical finite form of `τ ≤ D# + c#` on a bounded-ratio pair. -/
theorem pairTau_le_correctedDefect_add_componentCount
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    pairTau A hN pair ≤
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L := by
  have hp :=
    PropositionSixteenOne.mem_separatedBoundedRatioPairs.mp pair.2
  unfold pairTau
  apply
    residualTau_le_canonicalCorrected_add_residual
      (pair_coordinates_two_le hN pair).1
      (pair_coordinates_two_le hN pair).2
  · exact
      startWindow_le_boundedRatioCutoff
        hp.1 (show L ≤ L by rfl)
  · exact
      startWindow_le_boundedRatioCutoff
        hp.2.1 (show L ≤ L by rfl)

/-- Natural-valued common loss `4^Dmax 4^cmax`. -/
def smallProductLossNat
    (κ₀ A N L : ℕ) : ℕ :=
  4 ^
      BoundedRatioCorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
        κ₀ A N L *
    4 ^ smallProductComponentExponent N L

/-- Real form of the common loss. -/
def smallProductLoss
    (κ₀ A N L : ℕ) : ℝ :=
  (smallProductLossNat κ₀ A N L : ℝ)

/--
Every active first-sector quadratic weight is the common residual loss
times its systematic fourth-power weight.
-/
theorem quadraticResidualWeight_le_loss_mul_four_pow_pairSigma
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hM : M ≤ κ₀ * N)
    (terminal : TerminalPredicateFamily)
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .smallPrimeProduct) :
    quadraticResidualWeight A hN pair ≤
      smallProductLossNat κ₀ A N L *
        4 ^ pairSigma A pair := by
  have hsector :
      pair ∈ boundedRatioSectorPairs
        N M A L hN terminal .smallPrimeProduct :=
    activeSectorPairs_subset_sectorPairs
      hN terminal .smallPrimeProduct hpair
  have htau :=
    pairTau_le_correctedDefect_add_componentCount
      (A := A) hN pair
  have hdefect :=
    BoundedRatioCorrectedDefectEnvelope.canonicalCorrectedDefectCount_le_max
      (κ₀ := κ₀) (A := A) hM pair.2
  have hcomponent :=
    canonicalResidualComponentCount_le_logQuotient
      hN pair
      (hasSmallCanonicalPrimeProduct_of_mem_smallProductSector
        hsector)
  unfold quadraticResidualWeight smallProductLossNat
  calc
    4 ^ pairSigma A pair * (4 ^ pairTau A hN pair - 1) ≤
        4 ^ pairSigma A pair * 4 ^ pairTau A hN pair :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤
        4 ^ pairSigma A pair *
          4 ^
            (canonicalCorrectedDefectCount
                A pair.1.1 pair.1.2 L +
              canonicalResidualComponentCount
                A pair.1.1 pair.1.2 L) :=
      Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by norm_num) htau)
    _ =
        4 ^ pairSigma A pair *
          (4 ^ canonicalCorrectedDefectCount
              A pair.1.1 pair.1.2 L *
            4 ^ canonicalResidualComponentCount
              A pair.1.1 pair.1.2 L) := by
      rw [pow_add]
    _ ≤
        4 ^ pairSigma A pair *
          (4 ^
              BoundedRatioCorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
                κ₀ A N L *
            4 ^ smallProductComponentExponent N L) :=
      Nat.mul_le_mul_left _
        (Nat.mul_le_mul
          (Nat.pow_le_pow_right (by norm_num) hdefect)
          (Nat.pow_le_pow_right (by norm_num) hcomponent))
    _ =
        (4 ^
              BoundedRatioCorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
                κ₀ A N L *
            4 ^ smallProductComponentExponent N L) *
          4 ^ pairSigma A pair := by
      ring

/-- Active first-sector pairs in the exceptional branch `σ=0`. -/
noncomputable def sigmaZeroPairs
    (N M A L : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  (activeSectorPairs
    N M A L hN terminal .smallPrimeProduct).filter
      fun pair ↦ pairSigma A pair = 0

/-- Active first-sector pairs in the systematic branch `σ>0`. -/
noncomputable def positiveSigmaPairs
    (N M A L : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  (activeSectorPairs
    N M A L hN terminal .smallPrimeProduct).filter
      fun pair ↦ 0 < pairSigma A pair

@[simp]
theorem mem_sigmaZeroPairs
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ sigmaZeroPairs N M A L hN terminal ↔
      pair ∈
          activeSectorPairs
            N M A L hN terminal .smallPrimeProduct ∧
        pairSigma A pair = 0 := by
  simp [sigmaZeroPairs]

@[simp]
theorem mem_positiveSigmaPairs
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ positiveSigmaPairs N M A L hN terminal ↔
      pair ∈
          activeSectorPairs
            N M A L hN terminal .smallPrimeProduct ∧
        0 < pairSigma A pair := by
  simp [positiveSigmaPairs]

theorem disjoint_sigmaZeroPairs_positiveSigmaPairs
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    Disjoint
      (sigmaZeroPairs N M A L hN terminal)
      (positiveSigmaPairs N M A L hN terminal) := by
  rw [Finset.disjoint_left]
  intro pair hzero hpositive
  have hz := (mem_sigmaZeroPairs.mp hzero).2
  have hp := (mem_positiveSigmaPairs.mp hpositive).2
  omega

theorem sigmaZeroPairs_union_positiveSigmaPairs
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    sigmaZeroPairs N M A L hN terminal ∪
        positiveSigmaPairs N M A L hN terminal =
      activeSectorPairs
        N M A L hN terminal .smallPrimeProduct := by
  ext pair
  simp only [Finset.mem_union, mem_sigmaZeroPairs,
    mem_positiveSigmaPairs]
  constructor
  · rintro (hzero | hpositive)
    · exact hzero.1
    · exact hpositive.1
  · intro hactive
    by_cases hzero : pairSigma A pair = 0
    · exact Or.inl ⟨hactive, hzero⟩
    · exact Or.inr ⟨hactive, Nat.pos_of_ne_zero hzero⟩

/-- Quadratic mass of the exceptional branch. -/
noncomputable def sigmaZeroQuadraticMass
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) : ℕ :=
  quadraticResidualMass A hN
    (sigmaZeroPairs N M A L hN terminal)

/-- Quadratic mass of the systematic branch. -/
noncomputable def positiveSigmaQuadraticMass
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) : ℕ :=
  quadraticResidualMass A hN
    (positiveSigmaPairs N M A L hN terminal)

/-- Exact decomposition into the two Proposition 7.3 branches. -/
theorem activeSectorQuadraticResidualMass_eq_branches
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    activeSectorQuadraticResidualMass
        (M := M) (L := L) A hN terminal .smallPrimeProduct =
      sigmaZeroQuadraticMass
          (M := M) (L := L) A hN terminal +
        positiveSigmaQuadraticMass
          (M := M) (L := L) A hN terminal := by
  unfold activeSectorQuadraticResidualMass
    sigmaZeroQuadraticMass positiveSigmaQuadraticMass
    quadraticResidualMass
  rw [← Finset.sum_union
      (disjoint_sigmaZeroPairs_positiveSigmaPairs hN terminal),
    sigmaZeroPairs_union_positiveSigmaPairs hN terminal]

/-- Finite `σ=0` estimate: only the number of pairs remains. -/
theorem sigmaZeroQuadraticMass_le
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hM : M ≤ κ₀ * N)
    (terminal : TerminalPredicateFamily) :
    sigmaZeroQuadraticMass
        (M := M) (L := L) A hN terminal ≤
      smallProductLossNat κ₀ A N L *
        (sigmaZeroPairs N M A L hN terminal).card := by
  unfold sigmaZeroQuadraticMass quadraticResidualMass
  calc
    (∑ pair ∈ sigmaZeroPairs N M A L hN terminal,
        quadraticResidualWeight A hN pair) ≤
        ∑ _pair ∈ sigmaZeroPairs N M A L hN terminal,
          smallProductLossNat κ₀ A N L := by
      apply Finset.sum_le_sum
      intro pair hpair
      have hpoint :=
        quadraticResidualWeight_le_loss_mul_four_pow_pairSigma
          (κ₀ := κ₀) hN hM terminal
          (mem_sigmaZeroPairs.mp hpair).1
      simpa only [(mem_sigmaZeroPairs.mp hpair).2, pow_zero,
        mul_one] using hpoint
    _ =
        smallProductLossNat κ₀ A N L *
          (sigmaZeroPairs N M A L hN terminal).card := by
      simp [mul_comm]

/--
The systematic base-four mass of any bounded-ratio subtype population is a
subsum of the complete bounded-ratio rational mass.
-/
theorem sum_four_pow_pairSigma_sub_one_le_boundedRationalMass
    {N M A L : ℕ}
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    (∑ pair ∈ population,
        (4 ^ pairSigma A pair - 1)) ≤
      boundedRationalMass N M A L 4 := by
  classical
  let values : Finset (ℕ × ℕ) :=
    population.image Subtype.val
  have hvalues :
      values ⊆
        PropositionSixteenOne.separatedBoundedRatioPairs N M L := by
    intro pair hpair
    dsimp only [values] at hpair
    rw [Finset.mem_image] at hpair
    obtain ⟨z, _hz, rfl⟩ := hpair
    exact z.2
  have hsumImage :
      (∑ pair ∈ values,
          (4 ^ RationalMassFinite.canonicalPairSigma
              A L pair.1 pair.2 - 1)) =
        ∑ pair ∈ population,
          (4 ^ pairSigma A pair - 1) := by
    unfold values
    rw [Finset.sum_image]
    · rfl
    · intro pair _hpair other _hother hval
      exact Subtype.val_injective hval
  calc
    (∑ pair ∈ population,
        (4 ^ pairSigma A pair - 1)) =
        ∑ pair ∈ values,
          (4 ^ RationalMassFinite.canonicalPairSigma
              A L pair.1 pair.2 - 1) :=
      hsumImage.symm
    _ ≤
        ∑ pair ∈
          PropositionSixteenOne.separatedBoundedRatioPairs N M L,
          (4 ^ RationalMassFinite.canonicalPairSigma
              A L pair.1 pair.2 - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hvalues
      intro pair _hpair _hnot
      exact Nat.zero_le _
    _ = boundedRationalMass N M A L 4 := rfl

/-- For a positive exponent, `4^σ ≤ 2(4^σ-1)`. -/
theorem four_pow_le_two_mul_four_pow_sub_one
    {σ : ℕ} (hσ : 0 < σ) :
    4 ^ σ ≤ 2 * (4 ^ σ - 1) := by
  have hpow :
      4 ^ 1 ≤ 4 ^ σ :=
    Nat.pow_le_pow_right (by norm_num) hσ
  norm_num at hpow
  omega

/-- The systematic fourth-power sum of the positive branch. -/
theorem sum_four_pow_pairSigma_positive_le
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    (∑ pair ∈ positiveSigmaPairs N M A L hN terminal,
        4 ^ pairSigma A pair) ≤
      2 * boundedRationalMass N M A L 4 := by
  calc
    (∑ pair ∈ positiveSigmaPairs N M A L hN terminal,
        4 ^ pairSigma A pair) ≤
        ∑ pair ∈ positiveSigmaPairs N M A L hN terminal,
          2 * (4 ^ pairSigma A pair - 1) := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact
        four_pow_le_two_mul_four_pow_sub_one
          (mem_positiveSigmaPairs.mp hpair).2
    _ =
        2 *
          ∑ pair ∈ positiveSigmaPairs N M A L hN terminal,
            (4 ^ pairSigma A pair - 1) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * boundedRationalMass N M A L 4 :=
      Nat.mul_le_mul_left 2
        (sum_four_pow_pairSigma_sub_one_le_boundedRationalMass
          (positiveSigmaPairs N M A L hN terminal))

/-- Finite `σ>0` estimate charged to the base-four rational mass. -/
theorem positiveSigmaQuadraticMass_le
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hM : M ≤ κ₀ * N)
    (terminal : TerminalPredicateFamily) :
    positiveSigmaQuadraticMass
        (M := M) (L := L) A hN terminal ≤
      smallProductLossNat κ₀ A N L *
        (2 * boundedRationalMass N M A L 4) := by
  unfold positiveSigmaQuadraticMass quadraticResidualMass
  calc
    (∑ pair ∈ positiveSigmaPairs N M A L hN terminal,
        quadraticResidualWeight A hN pair) ≤
        ∑ pair ∈ positiveSigmaPairs N M A L hN terminal,
          smallProductLossNat κ₀ A N L *
            4 ^ pairSigma A pair := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact
        quadraticResidualWeight_le_loss_mul_four_pow_pairSigma
          (κ₀ := κ₀) hN hM terminal
          (mem_positiveSigmaPairs.mp hpair).1
    _ =
        smallProductLossNat κ₀ A N L *
          ∑ pair ∈ positiveSigmaPairs N M A L hN terminal,
            4 ^ pairSigma A pair := by
      rw [Finset.mul_sum]
    _ ≤
        smallProductLossNat κ₀ A N L *
          (2 * boundedRationalMass N M A L 4) :=
      Nat.mul_le_mul_left _
        (sum_four_pow_pairSigma_positive_le hN terminal)

/-! ## Endpoint-independent base-four rational envelope -/

/--
A common base-four rational-mass bound under `M ≤ κ₀N`.  This is the
base-four companion of `BoundedRatioGeometry.boundedRationalMass_two_le_common`.
-/
theorem boundedRationalMass_four_le_common
    {N M A L κ₀ : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ κ₀ * N)
    (hA : 1 ≤ A) :
    boundedRationalMass N M A L 4 ≤
      16 * (κ₀ + 1) * (L + 1) ^ 4 * N *
        4 ^ (L / 2) := by
  have hfinite :=
    boundedRationalMass_le N M A L 4 hNM hA (by norm_num)
  have hfactorTwo :
      1 + (M - N) / 2 ≤ (κ₀ + 1) * N := by
    calc
      1 + (M - N) / 2 ≤ 1 + (M - N) :=
        Nat.add_le_add_left (Nat.div_le_self (M - N) 2) 1
      _ ≤ N + κ₀ * N := by
        have hwidth : M - N ≤ κ₀ * N :=
          (Nat.sub_le M N).trans hM
        omega
      _ = (κ₀ + 1) * N := by ring
  have hfactorThree :
      1 + (M - N) / 3 ≤ (κ₀ + 1) * N := by
    calc
      1 + (M - N) / 3 ≤ 1 + (M - N) :=
        Nat.add_le_add_left (Nat.div_le_self (M - N) 3) 1
      _ ≤ N + κ₀ * N := by
        have hwidth : M - N ≤ κ₀ * N :=
          (Nat.sub_le M N).trans hM
        omega
      _ = (κ₀ + 1) * N := by ring
  have hHpos : 0 < L + 1 := Nat.succ_pos L
  have hL : L ≤ L + 1 := Nat.le_succ L
  have hlinear : 3 * L + 1 ≤ 4 * (L + 1) := by
    omega
  have hHpow : L + 1 ≤ (L + 1) ^ 4 := by
    calc
      L + 1 = (L + 1) ^ 1 := by simp
      _ ≤ (L + 1) ^ 4 :=
        Nat.pow_le_pow_right hHpos (by omega)
  have hsmall :
      2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
          4 ^ (L / 2) ≤
        8 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          4 ^ (L / 2) := by
    calc
      2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
            4 ^ (L / 2) ≤
          2 * ((4 * (L + 1)) * ((κ₀ + 1) * N)) *
            4 ^ (L / 2) :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left 2
            (Nat.mul_le_mul hlinear hfactorTwo))
      _ = 8 * (κ₀ + 1) * (L + 1) * N *
          4 ^ (L / 2) := by ring
      _ ≤ 8 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          4 ^ (L / 2) := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right N
            (Nat.mul_le_mul_left (8 * (κ₀ + 1)) hHpow))
  have htwoL : 2 * L ≤ 2 * (L + 1) :=
    Nat.mul_le_mul_left 2 hL
  have honeSquare : 1 ≤ (L + 1) * (L + 1) := by
    nlinarith
  have hinner :
      (2 * L) * L + 1 ≤
        (2 * (L + 1)) * (L + 1) +
          (L + 1) * (L + 1) :=
    Nat.add_le_add
      (Nat.mul_le_mul htwoL hL) honeSquare
  have hfront :
      L * (2 * L) ≤
        (L + 1) * (2 * (L + 1)) :=
    Nat.mul_le_mul hL htwoL
  have hlargePoly :
      L * (2 * L) * ((2 * L) * L + 1) ≤
        6 * (L + 1) ^ 4 := by
    calc
      L * (2 * L) * ((2 * L) * L + 1) ≤
          ((L + 1) * (2 * (L + 1))) *
            ((2 * (L + 1)) * (L + 1) +
              (L + 1) * (L + 1)) :=
        Nat.mul_le_mul hfront hinner
      _ = 6 * (L + 1) ^ 4 := by ring
  have hthirdHalf : L / 3 ≤ L / 2 :=
    Nat.div_le_div_left (by omega : 2 ≤ 3) (by omega)
  have hpow :
      4 ^ (L / 3) ≤ 4 ^ (L / 2) :=
    Nat.pow_le_pow_right (by norm_num) hthirdHalf
  have hlarge :
      L * (2 * L) * ((2 * L) * L + 1) *
          (1 + (M - N) / 3) * 4 ^ (L / 3) ≤
        6 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          4 ^ (L / 2) := by
    calc
      L * (2 * L) * ((2 * L) * L + 1) *
            (1 + (M - N) / 3) * 4 ^ (L / 3) ≤
          (6 * (L + 1) ^ 4) * ((κ₀ + 1) * N) *
            4 ^ (L / 2) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul hlargePoly hfactorThree)
          hpow
      _ = 6 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          4 ^ (L / 2) := by ring
  calc
    boundedRationalMass N M A L 4 ≤
        2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
            4 ^ (L / 2) +
          L * (2 * L) * ((2 * L) * L + 1) *
            (1 + (M - N) / 3) * 4 ^ (L / 3) :=
      hfinite
    _ ≤
        8 * (κ₀ + 1) * (L + 1) ^ 4 * N *
            4 ^ (L / 2) +
          6 * (κ₀ + 1) * (L + 1) ^ 4 * N *
            4 ^ (L / 2) :=
      Nat.add_le_add hsmall hlarge
    _ = 14 * (κ₀ + 1) * (L + 1) ^ 4 * N *
        4 ^ (L / 2) := by ring
    _ ≤ 16 * (κ₀ + 1) * (L + 1) ^ 4 * N *
        4 ^ (L / 2) := by
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right N
          (Nat.mul_le_mul_right ((L + 1) ^ 4)
            (Nat.mul_le_mul_right (κ₀ + 1) (by omega))))

/-- Subpolynomial factor in the common base-four rational envelope. -/
def boundedRationalMassFourResidual
    (C : ℝ) (κ₀ : ℕ) (_N L : ℕ) : ℝ :=
  (16 * (κ₀ + 1 : ℝ) *
      CriticalRunWindow.balanceConstant C) *
    (((L + 1 : ℕ) : ℝ) ^ 4)

/-- Endpoint-independent quadratic envelope for the base-four mass. -/
def boundedRationalMassFourEnvelope
    (C : ℝ) (κ₀ N L : ℕ) : ℝ :=
  (N : ℝ) *
    ((N : ℝ) *
      boundedRationalMassFourResidual C κ₀ N L)

theorem boundedRationalMassFourResidual_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedRationalMassFourResidual C κ₀) := by
  have hH :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hC
  have hH2 :=
    ExpSqrtLog.uniformSubpolynomialOn_mul hH hH
  have hH4 :=
    ExpSqrtLog.uniformSubpolynomialOn_mul hH2 hH2
  have hconst :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      (16 * (κ₀ + 1 : ℝ) *
        CriticalRunWindow.balanceConstant C)
      hH4
  convert hconst using 1
  funext N L
  unfold boundedRationalMassFourResidual
  ring

/-- The common base-four envelope is `N^(2+o_{C,κ₀}(1))`. -/
theorem boundedRationalMassFourEnvelope_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedRationalMassFourEnvelope C κ₀) := by
  let admissible := CriticalRunWindow.InRunLengthWindow C
  have hlinearN :
      UniformLinearSubpolynomialOn admissible
        (fun N _L => (N : ℝ)) := by
    apply UniformLinear.of_linear_mul_subpolynomial
      (ExpSqrtLog.uniformSubpolynomialOn_const admissible 1)
    refine ⟨0, ?_⟩
    intro N _hN L _hNL
    simp
  have hlinearResidual :
      UniformLinearSubpolynomialOn admissible
        (fun N L =>
          (N : ℝ) *
            boundedRationalMassFourResidual C κ₀ N L) := by
    apply UniformLinear.of_linear_mul_subpolynomial
      (boundedRationalMassFourResidual_uniformSubpolynomial hC κ₀)
    refine ⟨0, ?_⟩
    intro N _hN L _hNL
    have hresidual :
        0 ≤ boundedRationalMassFourResidual C κ₀ N L := by
      unfold boundedRationalMassFourResidual
      exact
        mul_nonneg
          (mul_nonneg (by positivity)
            (CriticalRunWindow.balanceConstant_nonneg C))
          (by positivity)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N),
      abs_of_nonneg hresidual]
  have hproduct :=
    UniformLinear.mul hlinearN hlinearResidual
  change
    UniformRationalPowerSubpolynomialOn 2 1 admissible
      (fun N L =>
        (N : ℝ) *
          ((N : ℝ) *
            boundedRationalMassFourResidual C κ₀ N L))
  exact hproduct

/-- Every admissible endpoint's base-four mass lies below the common envelope. -/
theorem boundedRationalMass_four_cast_le_envelope
    {C : ℝ} {κ₀ N M A L : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ κ₀ * N)
    (hA : 1 ≤ A)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    (boundedRationalMass N M A L 4 : ℝ) ≤
      boundedRationalMassFourEnvelope C κ₀ N L := by
  have hfinite :=
    boundedRationalMass_four_le_common
      (L := L) hN hNM hM hA
  have hfiniteCast :
      (boundedRationalMass N M A L 4 : ℝ) ≤
        (16 * (κ₀ + 1 : ℝ)) *
          (((L + 1 : ℕ) : ℝ) ^ 4) *
          (N : ℝ) *
          ((4 ^ (L / 2) : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  have hpow :=
    CriticalChannelPowers.four_pow_half_cast_le_balance_mul
      (show 0 < N by omega) hrun
  calc
    (boundedRationalMass N M A L 4 : ℝ) ≤
        (16 * (κ₀ + 1 : ℝ)) *
          (((L + 1 : ℕ) : ℝ) ^ 4) *
          (N : ℝ) *
          ((4 ^ (L / 2) : ℕ) : ℝ) :=
      hfiniteCast
    _ ≤
        (16 * (κ₀ + 1 : ℝ)) *
          (((L + 1 : ℕ) : ℝ) ^ 4) *
          (N : ℝ) *
          (CriticalRunWindow.balanceConstant C * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = boundedRationalMassFourEnvelope C κ₀ N L := by
      unfold boundedRationalMassFourEnvelope
        boundedRationalMassFourResidual
      ring

/-! ## Quadratic closure of the two branches -/

/-- The combined corrected-defect and residual-component loss is subpolynomial. -/
theorem smallProductLoss_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (smallProductLoss κ₀ A) := by
  have hcorrected :=
    BoundedRatioCorrectedDefectEnvelope.four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial
      hC κ₀ A
  have hcomponent :=
    smallProductComponentFactor_uniformSubpolynomial hC
  have hproduct :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      hcorrected hcomponent
  convert hproduct using 1
  funext N L
  unfold smallProductLoss smallProductLossNat
    smallProductComponentFactor
  norm_num

/-- Endpoint-independent envelope for the `σ=0` branch. -/
def sigmaZeroEnvelope
    (κ₀ A N L : ℕ) : ℝ :=
  (N : ℝ) *
    ((N : ℝ) *
      ((κ₀ : ℝ) ^ 2 * smallProductLoss κ₀ A N L))

/-- Endpoint-independent envelope for the `σ>0` branch. -/
def positiveSigmaEnvelope
    (C : ℝ) (κ₀ A N L : ℕ) : ℝ :=
  (2 * smallProductLoss κ₀ A N L) *
    boundedRationalMassFourEnvelope C κ₀ N L

/-- Complete endpoint-independent small-product quadratic envelope. -/
def smallProductQuadraticEnvelope
    (C : ℝ) (κ₀ A N L : ℕ) : ℝ :=
  sigmaZeroEnvelope κ₀ A N L +
    positiveSigmaEnvelope C κ₀ A N L

theorem sigmaZeroEnvelope_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (sigmaZeroEnvelope κ₀ A) := by
  let admissible := CriticalRunWindow.InRunLengthWindow C
  let residual : ℕ → ℕ → ℝ :=
    fun N L =>
      (κ₀ : ℝ) ^ 2 * smallProductLoss κ₀ A N L
  have hresidual :
      UniformSubpolynomialOn admissible residual := by
    simpa only [admissible, residual] using
      ExpSqrtLog.uniformSubpolynomialOn_const_mul
        ((κ₀ : ℝ) ^ 2)
        (smallProductLoss_uniformSubpolynomial hC κ₀ A)
  have hlinearN :
      UniformLinearSubpolynomialOn admissible
        (fun N _L => (N : ℝ)) := by
    apply UniformLinear.of_linear_mul_subpolynomial
      (ExpSqrtLog.uniformSubpolynomialOn_const admissible 1)
    refine ⟨0, ?_⟩
    intro N _hN L _hNL
    simp
  have hlinearResidual :
      UniformLinearSubpolynomialOn admissible
        (fun N L => (N : ℝ) * residual N L) := by
    apply UniformLinear.of_linear_mul_subpolynomial hresidual
    refine ⟨0, ?_⟩
    intro N _hN L _hNL
    have hres : 0 ≤ residual N L := by
      dsimp only [residual, smallProductLoss, smallProductLossNat]
      positivity
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N),
      abs_of_nonneg hres]
  have hproduct :=
    UniformLinear.mul hlinearN hlinearResidual
  change
    UniformRationalPowerSubpolynomialOn 2 1 admissible
      (fun N L =>
        (N : ℝ) *
          ((N : ℝ) *
            ((κ₀ : ℝ) ^ 2 * smallProductLoss κ₀ A N L)))
  exact hproduct

theorem positiveSigmaEnvelope_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (positiveSigmaEnvelope C κ₀ A) := by
  have hfactor :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L => 2 * smallProductLoss κ₀ A N L) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul 2
      (smallProductLoss_uniformSubpolynomial hC κ₀ A)
  change
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (2 * smallProductLoss κ₀ A N L) *
          boundedRationalMassFourEnvelope C κ₀ N L)
  exact
    UniformRationalPower.mul_subpolynomial (by omega : 0 < 1)
      (boundedRationalMassFourEnvelope_uniformQuadratic hC κ₀)
      hfactor

theorem smallProductQuadraticEnvelope_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (smallProductQuadraticEnvelope C κ₀ A) := by
  change
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        sigmaZeroEnvelope κ₀ A N L +
          positiveSigmaEnvelope C κ₀ A N L)
  exact
    UniformRationalPower.add_quadratic
      (sigmaZeroEnvelope_uniformQuadratic hC κ₀ A)
      (positiveSigmaEnvelope_uniformQuadratic hC κ₀ A)

/-- Finite `σ=0` branch below its endpoint-independent envelope. -/
theorem sigmaZeroQuadraticMass_cast_le_envelope
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hM : M ≤ κ₀ * N)
    (terminal : TerminalPredicateFamily) :
    (sigmaZeroQuadraticMass
        (M := M) (L := L) A hN terminal : ℝ) ≤
      sigmaZeroEnvelope κ₀ A N L := by
  have hbranch :=
    sigmaZeroQuadraticMass_le
      (A := A) (L := L) hN hM terminal
  have hcard :
      (sigmaZeroPairs N M A L hN terminal).card ≤
        (κ₀ * N) ^ 2 :=
    card_population_le_ratio_sq
      (sigmaZeroPairs N M A L hN terminal) hM
  have hnat :
      sigmaZeroQuadraticMass
          (M := M) (L := L) A hN terminal ≤
        smallProductLossNat κ₀ A N L *
          ((κ₀ * N) ^ 2) :=
    hbranch.trans
      (Nat.mul_le_mul_left _ hcard)
  have hcast :
      (sigmaZeroQuadraticMass
          (M := M) (L := L) A hN terminal : ℝ) ≤
        (smallProductLossNat κ₀ A N L : ℝ) *
          (((κ₀ * N) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    (sigmaZeroQuadraticMass
        (M := M) (L := L) A hN terminal : ℝ) ≤
        (smallProductLossNat κ₀ A N L : ℝ) *
          (((κ₀ * N) ^ 2 : ℕ) : ℝ) :=
      hcast
    _ = sigmaZeroEnvelope κ₀ A N L := by
      unfold sigmaZeroEnvelope smallProductLoss
      norm_num
      ring

/-- Finite `σ>0` branch below its endpoint-independent envelope. -/
theorem positiveSigmaQuadraticMass_cast_le_envelope
    {C : ℝ} {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hNM : N ≤ M) (hM : M ≤ κ₀ * N)
    (hA : 1 ≤ A)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L)
    (terminal : TerminalPredicateFamily) :
    (positiveSigmaQuadraticMass
        (M := M) (L := L) A hN terminal : ℝ) ≤
      positiveSigmaEnvelope C κ₀ A N L := by
  have hbranch :=
    positiveSigmaQuadraticMass_le
      (A := A) (L := L) hN hM terminal
  have hbranchCast :
      (positiveSigmaQuadraticMass
          (M := M) (L := L) A hN terminal : ℝ) ≤
        (smallProductLossNat κ₀ A N L : ℝ) *
          (2 * (boundedRationalMass N M A L 4 : ℝ)) := by
    exact_mod_cast hbranch
  have hrational :=
    boundedRationalMass_four_cast_le_envelope
      (C := C) (κ₀ := κ₀) (A := A)
      (show 1 ≤ N by omega) hNM hM hA hrun
  calc
    (positiveSigmaQuadraticMass
        (M := M) (L := L) A hN terminal : ℝ) ≤
        (smallProductLossNat κ₀ A N L : ℝ) *
          (2 * (boundedRationalMass N M A L 4 : ℝ)) :=
      hbranchCast
    _ ≤
        (smallProductLossNat κ₀ A N L : ℝ) *
          (2 * boundedRationalMassFourEnvelope C κ₀ N L) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hrational (by norm_num))
        (by positivity)
    _ = positiveSigmaEnvelope C κ₀ A N L := by
      unfold positiveSigmaEnvelope smallProductLoss
      ring

/-- The complete active first-sector quadratic mass is bounded uniformly. -/
theorem activeSectorQuadraticResidualMass_cast_le_envelope
    {C : ℝ} {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hNM : N ≤ M) (hM : M ≤ κ₀ * N)
    (hA : 1 ≤ A)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L)
    (terminal : TerminalPredicateFamily) :
    (activeSectorQuadraticResidualMass
        (M := M) (L := L) A hN terminal .smallPrimeProduct : ℝ) ≤
      smallProductQuadraticEnvelope C κ₀ A N L := by
  rw [activeSectorQuadraticResidualMass_eq_branches hN terminal]
  norm_num only [Nat.cast_add]
  exact add_le_add
    (sigmaZeroQuadraticMass_cast_le_envelope hN hM terminal)
    (positiveSigmaQuadraticMass_cast_le_envelope
      hN hNM hM hA hrun terminal)

/-! ## `N^(2+o)` quadratic mass and `N^(7/4+o)` interpolation -/

/-- Proof-independent quadratic mass of the literal first sector. -/
noncomputable def smallProductSectorQuadraticMass
    (A : ℕ) (terminal : TerminalPredicateFamily)
    (N M L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (sectorQuadraticResidualMass
      (M := M) (L := L) A hN terminal .smallPrimeProduct : ℝ)
  else 0

/-- Proof-independent linear mass of the literal first sector. -/
noncomputable def smallProductSectorLinearMass
    (A : ℕ) (terminal : TerminalPredicateFamily)
    (N M L : ℕ) : ℝ :=
  sectorResidualMass A terminal .smallPrimeProduct N M L

/-- Literal three-variable form of `N^(2+o_{C,κ₀}(1))`. -/
def UniformQuadraticInBoundedRatioWindow
    (C : ℝ) (κ₀ : ℕ)
    (f : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      |f N M L| ^ k ≤ (N : ℝ) ^ (2 * k + 1)

/-- Literal three-variable form of `N^(7/4+o_{C,κ₀}(1))`. -/
def UniformSevenFourthsInBoundedRatioWindow
    (C : ℝ) (κ₀ : ℕ)
    (f : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      |f N M L| ^ (4 * k) ≤
        (N : ℝ) ^ (7 * k + 1)

theorem smallProductSectorQuadraticMass_nonneg
    (A : ℕ) (terminal : TerminalPredicateFamily)
    (N M L : ℕ) :
    0 ≤ smallProductSectorQuadraticMass A terminal N M L := by
  unfold smallProductSectorQuadraticMass
  split_ifs
  · positivity
  · exact le_rfl

theorem smallProductQuadraticEnvelope_nonneg
    (C : ℝ) (κ₀ A N L : ℕ) :
    0 ≤ smallProductQuadraticEnvelope C κ₀ A N L := by
  unfold smallProductQuadraticEnvelope sigmaZeroEnvelope
    positiveSigmaEnvelope boundedRationalMassFourEnvelope
    boundedRationalMassFourResidual smallProductLoss
    smallProductLossNat
  have hbalance :
      0 ≤ CriticalRunWindow.balanceConstant C :=
    CriticalRunWindow.balanceConstant_nonneg C
  positivity

/-- The actual first-sector quadratic mass is below the common envelope. -/
theorem smallProductSectorQuadraticMass_le_envelope
    {C : ℝ} {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hNM : N ≤ M) (hM : M ≤ κ₀ * N)
    (hA : 1 ≤ A)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L)
    (terminal : TerminalPredicateFamily) :
    smallProductSectorQuadraticMass A terminal N M L ≤
      smallProductQuadraticEnvelope C κ₀ A N L := by
  rw [smallProductSectorQuadraticMass, dif_pos hN]
  rw [sectorQuadraticResidualMass_eq_active hN terminal
    .smallPrimeProduct]
  exact
    activeSectorQuadraticResidualMass_cast_le_envelope
      hN hNM hM hA hrun terminal

/--
Lemma 17.14, quadratic half:
`Q_res^(1) = N^(2+o_{C,κ₀}(1))`, uniformly in `M`.
-/
theorem smallProductSectorQuadraticMass_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (hA : 1 ≤ A)
    (terminal : TerminalPredicateFamily) :
    UniformQuadraticInBoundedRatioWindow C κ₀
      (smallProductSectorQuadraticMass A terminal) := by
  have henvelope :=
    smallProductQuadraticEnvelope_uniformQuadratic hC κ₀ A
  intro k hk
  obtain ⟨Nenv, hNenv⟩ := henvelope k hk
  refine ⟨max 2 Nenv, ?_⟩
  intro N hN M L hNM hM hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left _ _).trans hN
  have hNenvN : Nenv ≤ N :=
    (le_max_right _ _).trans hN
  have hfinite :=
    smallProductSectorQuadraticMass_le_envelope
      hNtwo (by omega) hM hA hrun terminal
  have hmassNonneg :=
    smallProductSectorQuadraticMass_nonneg
      A terminal N M L
  have henvelopeNonneg :=
    smallProductQuadraticEnvelope_nonneg C κ₀ A N L
  calc
    |smallProductSectorQuadraticMass A terminal N M L| ^ k ≤
        |smallProductQuadraticEnvelope C κ₀ A N L| ^ k := by
      rw [abs_of_nonneg hmassNonneg,
        abs_of_nonneg henvelopeNonneg]
      exact
        pow_le_pow_left₀ hmassNonneg hfinite k
    _ ≤ (N : ℝ) ^ (2 * k + 1) := by
      simpa only [one_mul] using hNenv N hNenvN L hrun

/-- Endpoint-independent interpolated linear envelope. -/
noncomputable def smallProductLinearEnvelope
    (C : ℝ) (κ₀ A N L : ℕ) : ℝ :=
  Real.sqrt
      (BoundedRatioRelationalHostsCritical.boundedRelationalHostEnvelope
        κ₀ N L) *
    Real.sqrt (smallProductQuadraticEnvelope C κ₀ A N L)

theorem smallProductLinearEnvelope_nonneg
    (C : ℝ) (κ₀ A N L : ℕ) :
    0 ≤ smallProductLinearEnvelope C κ₀ A N L := by
  unfold smallProductLinearEnvelope
  positivity

/-- The common interpolated envelope is `N^(7/4+o_{C,κ₀}(1))`. -/
theorem smallProductLinearEnvelope_uniformSevenFourths
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformRationalPowerSubpolynomialOn 7 4
      (CriticalRunWindow.InRunLengthWindow C)
      (smallProductLinearEnvelope C κ₀ A) := by
  let hosts : ℕ → ℕ → ℝ :=
    BoundedRatioRelationalHostsCritical.boundedRelationalHostEnvelope κ₀
  let quadratic : ℕ → ℕ → ℝ :=
    smallProductQuadraticEnvelope C κ₀ A
  have hhosts :
      UniformThreeHalvesSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) hosts := by
    simpa only [hosts] using
      BoundedRatioRelationalHostsCritical.boundedRelationalHostEnvelope_uniformThreeHalves
        hC κ₀
  have hquadratic :
      UniformRationalPowerSubpolynomialOn 2 1
        (CriticalRunWindow.InRunLengthWindow C) quadratic := by
    simpa only [quadratic] using
      smallProductQuadraticEnvelope_uniformQuadratic hC κ₀ A
  apply
    UniformRationalPower.interpolate_threeHalves_quadratic
      hhosts hquadratic
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  have hhostNonneg :
      0 ≤ hosts N L := by
    dsimp only [hosts]
    unfold
      BoundedRatioRelationalHostsCritical.boundedRelationalHostEnvelope
      BoundedRatioRelationalHostsCritical.boundedRelationalHostResidual
    positivity
  have hquadraticNonneg :
      0 ≤ quadratic N L := by
    simpa only [quadratic] using
      smallProductQuadraticEnvelope_nonneg C κ₀ A N L
  have hlinearNonneg :
      0 ≤ smallProductLinearEnvelope C κ₀ A N L :=
    smallProductLinearEnvelope_nonneg C κ₀ A N L
  refine
    ⟨hhostNonneg, hquadraticNonneg, hlinearNonneg, ?_⟩
  rfl

/--
Finite interpolation with both endpoint-dependent factors replaced by their
common envelopes.
-/
theorem smallProductSectorLinearMass_le_envelope
    {C : ℝ} {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hNM : N ≤ M) (hM : M ≤ κ₀ * N)
    (hL : L ≤ N) (hA : 1 ≤ A)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L)
    (terminal : TerminalPredicateFamily) :
    smallProductSectorLinearMass A terminal N M L ≤
      smallProductLinearEnvelope C κ₀ A N L := by
  unfold smallProductSectorLinearMass
  rw [sectorResidualMass, dif_pos hN]
  have hinterp :=
    sectorResidualMassNat_cast_le_host_sqrt_mul_quadratic_sqrt
      (M := M) (A := A) (L := L)
      hN terminal .smallPrimeProduct
  have hhost :=
    BoundedRatioRelationalHostsCritical.card_boundedRelationalHosts_cast_le_common
      hN hNM hM hL
  have hquadratic :=
    activeSectorQuadraticResidualMass_cast_le_envelope
      hN hNM hM hA hrun terminal
  exact hinterp.trans <|
    calc
      Real.sqrt
            ((BoundedRatioRelationalHosts.boundedRelationalHosts
              N M L).card : ℝ) *
          Real.sqrt
            (activeSectorQuadraticResidualMass
              (M := M) (L := L) A hN terminal
                .smallPrimeProduct : ℝ) ≤
          Real.sqrt
              (BoundedRatioRelationalHostsCritical.boundedRelationalHostEnvelope
                κ₀ N L) *
            Real.sqrt
              (smallProductQuadraticEnvelope C κ₀ A N L) := by
        exact
          mul_le_mul
            (Real.sqrt_le_sqrt hhost)
            (Real.sqrt_le_sqrt hquadratic)
            (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = smallProductLinearEnvelope C κ₀ A N L := rfl

/--
Lemma 17.14, linear half:
`R_res^(1) = N^(7/4+o_{C,κ₀}(1))`, uniformly in `M`.
-/
theorem smallProductSectorLinearMass_uniformSevenFourths
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (hA : 1 ≤ A)
    (terminal : TerminalPredicateFamily) :
    UniformSevenFourthsInBoundedRatioWindow C κ₀
      (smallProductSectorLinearMass A terminal) := by
  have henvelope :=
    smallProductLinearEnvelope_uniformSevenFourths hC κ₀ A
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  have hupperNonneg :
      0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  obtain ⟨Nlength, hlength⟩ :=
    ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually
      CriticalRunWindow.upperConstant hupperNonneg 1 (by omega)
  intro k hk
  obtain ⟨Nenv, hNenv⟩ := henvelope k hk
  refine ⟨max 2 (max Nwindow (max Nlength Nenv)), ?_⟩
  intro N hN M L hNM hM hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail : max Nwindow (max Nlength Nenv) ≤ N :=
    (le_max_right _ _).trans hN
  have hNwindow : Nwindow ≤ N :=
    (le_max_left _ _).trans hNtail
  have hNtail' : max Nlength Nenv ≤ N :=
    (le_max_right _ _).trans hNtail
  have hNlength : Nlength ≤ N :=
    (le_max_left _ _).trans hNtail'
  have hNenvN : Nenv ≤ N :=
    (le_max_right _ _).trans hNtail'
  have hfirst := hwindow N hNwindow L hrun
  have hLplusTwoReal :
      (((L + 1) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    simpa using
      hlength N hNlength (L + 1) hfirst.1.2.2.2
  have hL : L ≤ N := by
    have hLplusTwo : (L + 1) + 1 ≤ N := by
      exact_mod_cast hLplusTwoReal
    omega
  have hfinite :=
    smallProductSectorLinearMass_le_envelope
      hNtwo (by omega) hM hL hA hrun terminal
  have hmassNonneg :
      0 ≤ smallProductSectorLinearMass A terminal N M L := by
    unfold smallProductSectorLinearMass sectorResidualMass
    simp only [dif_pos hNtwo]
    positivity
  have henvelopeNonneg :=
    smallProductLinearEnvelope_nonneg C κ₀ A N L
  calc
    |smallProductSectorLinearMass A terminal N M L| ^ (4 * k) ≤
        |smallProductLinearEnvelope C κ₀ A N L| ^ (4 * k) := by
      rw [abs_of_nonneg hmassNonneg,
        abs_of_nonneg henvelopeNonneg]
      exact
        pow_le_pow_left₀ hmassNonneg hfinite _
    _ ≤ (N : ℝ) ^ (7 * k + 1) :=
      hNenv N hNenvN L hrun

/--
The interpolated envelope is uniformly little-oh of `N²`.
-/
theorem smallProductLinearEnvelope_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (smallProductLinearEnvelope C κ₀ A)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  exact
    UniformRationalPower.littleO_natPower_of_lt
      (by omega : 7 < 2 * 4)
      (smallProductLinearEnvelope_uniformSevenFourths hC κ₀ A)

/--
Unconditional closure of the internal Lemma 17.14 bridge.
-/
theorem smallPrimeProductSectorStability
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (hA : 1 ≤ A)
    (terminal : TerminalPredicateFamily) :
    SmallPrimeProductSectorStabilityStatement C κ₀ A terminal := by
  have henvelope :=
    smallProductLinearEnvelope_uniformLittleOQuadratic hC κ₀ A
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  have hupperNonneg :
      0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  obtain ⟨Nlength, hlength⟩ :=
    ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually
      CriticalRunWindow.upperConstant hupperNonneg 1 (by omega)
  unfold SmallPrimeProductSectorStabilityStatement
  apply
    uniformLittleOInBoundedRatioWindow_of_nonnegative_envelope
      henvelope
  · intro N M L
    unfold sectorResidualMass
    split_ifs
    · positivity
    · exact le_rfl
  · exact smallProductLinearEnvelope_nonneg C κ₀ A
  · refine ⟨max 2 (max Nwindow Nlength), ?_⟩
    intro N hN M L hNM hM hrun
    have hNtwo : 2 ≤ N :=
      (le_max_left _ _).trans hN
    have hNtail : max Nwindow Nlength ≤ N :=
      (le_max_right _ _).trans hN
    have hNwindow : Nwindow ≤ N :=
      (le_max_left _ _).trans hNtail
    have hNlength : Nlength ≤ N :=
      (le_max_right _ _).trans hNtail
    have hfirst := hwindow N hNwindow L hrun
    have hLplusTwoReal :
        (((L + 1) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      simpa using
        hlength N hNlength (L + 1) hfirst.1.2.2.2
    have hL : L ≤ N := by
      have hLplusTwo : (L + 1) + 1 ≤ N := by
        exact_mod_cast hLplusTwoReal
      omega
    simpa only [smallProductSectorLinearMass] using
      smallProductSectorLinearMass_le_envelope
        hNtwo (by omega) hM hL hA hrun terminal

end

end BoundedRatioSmallProductSector
end PaperC
