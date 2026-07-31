import PaperC.Asymptotics.LinearPower
import PaperC.Arithmetic.RationalMassFinite
import PaperC.Combinatorics.DefectiveVertexIntervalBound
import PaperC.Probability.CriticalRunWindow

/-!
# Uniform envelope for the corrected defect

For fixed rational-code cutoff exponent `A`, this file takes the finite
maximum of the corrected defect `D#` over all separated ordered pairs in a
dyadic block.  The pointwise estimate of Lemma 6.4 passes to this maximum,
including the empty population, and the resulting factor `4^max D#` is
uniformly subpolynomial in the manuscript's literal run-length window.
-/

namespace PaperC
namespace CorrectedDefectEnvelope

open Affine
open RationalMassFinite
open ResidualComponentCounts

noncomputable section

/--
Largest canonical corrected-defect count among the separated ordered pairs
in the dyadic block.
-/
noncomputable def maxCanonicalCorrectedDefectCount
    (A N L : ℕ) : ℕ :=
  (separatedDyadicPairs N L).sup fun pair =>
    canonicalCorrectedDefectCount A pair.1 pair.2 L

/-- Every separated dyadic pair is bounded by the finite envelope. -/
theorem canonicalCorrectedDefectCount_le_max
    {A N L x y : ℕ}
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    canonicalCorrectedDefectCount A x y L ≤
      maxCanonicalCorrectedDefectCount A N L := by
  unfold maxCanonicalCorrectedDefectCount
  exact
    Finset.le_sup
      (f := fun pair =>
        canonicalCorrectedDefectCount A pair.1 pair.2 L)
      hpair

/--
Pass a pointwise real bound to the finite maximum.  The explicit
nonnegativity assumption is exactly what is needed when the separated-pair
population is empty.
-/
theorem maxCanonicalCorrectedDefectCount_cast_le
    {A N L : ℕ} {R : ℝ}
    (hR : 0 ≤ R)
    (hpoint :
      ∀ pair ∈ separatedDyadicPairs N L,
        (canonicalCorrectedDefectCount
            A pair.1 pair.2 L : ℝ) ≤ R) :
    (maxCanonicalCorrectedDefectCount A N L : ℝ) ≤ R := by
  classical
  have aux :
      ∀ s : Finset (ℕ × ℕ),
        (∀ pair ∈ s,
          (canonicalCorrectedDefectCount
              A pair.1 pair.2 L : ℝ) ≤ R) →
        ((s.sup fun pair =>
            canonicalCorrectedDefectCount
              A pair.1 pair.2 L : ℕ) : ℝ) ≤ R := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _h
        simpa using hR
    | @insert pair s hpairNotMem ih =>
        intro hs
        rw [Finset.sup_insert, Nat.cast_max]
        apply max_le
        · exact hs pair (Finset.mem_insert_self pair s)
        · apply ih
          intro other hother
          exact hs other (Finset.mem_insert_of_mem hother)
  exact aux (separatedDyadicPairs N L) hpoint

/--
Uniform logarithm-over-logarithm bound for the largest corrected defect.

The constants and threshold are independent of `A`: the underlying
pointwise estimate is uniform in the selected canonical channel.
-/
theorem maxCanonicalCorrectedDefectCount_log_bound_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
        CriticalRunWindow.InRunLengthWindow C N L →
        ∀ A,
          (maxCanonicalCorrectedDefectCount A N L : ℝ) ≤
            K * (Real.log N / Real.log (Real.log N)) := by
  let c₁ := CriticalRunWindow.lowerConstant
  let c₂ := CriticalRunWindow.upperConstant
  have hc₁ : 0 < c₁ := by
    simpa only [c₁] using CriticalRunWindow.lowerConstant_pos
  have hc₁c₂ : c₁ < c₂ := by
    simpa only [c₁, c₂] using
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨K, hK, Npoint, hpoint⟩ :=
    DefectiveVertexIntervalBound.canonicalCorrectedDefectCount_uniform_on_dyadicBlock
      hc₁ hc₁c₂
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  have hc₂ : 0 ≤ c₂ := hc₁.le.trans hc₁c₂.le
  obtain ⟨Nlength, hlength⟩ :=
    ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually
      c₂ hc₂ 1 (by omega)
  obtain ⟨Nlog, hNlog⟩ :=
    exists_nat_gt (Real.exp (Real.exp 0))
  let N₀ := max Nwindow
    (max Nlength (max Nlog (max Npoint 2)))
  refine ⟨K, hK, N₀, ?_⟩
  intro N hN L hrun A
  have hNwindow : Nwindow ≤ N :=
    (le_max_left Nwindow
      (max Nlength (max Nlog (max Npoint 2)))).trans hN
  have hNtail :
      max Nlength (max Nlog (max Npoint 2)) ≤ N :=
    (le_max_right Nwindow
      (max Nlength (max Nlog (max Npoint 2)))).trans hN
  have hNlength : Nlength ≤ N :=
    (le_max_left Nlength (max Nlog (max Npoint 2))).trans hNtail
  have hNtail' : max Nlog (max Npoint 2) ≤ N :=
    (le_max_right Nlength (max Nlog (max Npoint 2))).trans hNtail
  have hNlogN : Nlog ≤ N :=
    (le_max_left Nlog (max Npoint 2)).trans hNtail'
  have hNpointTwo : max Npoint 2 ≤ N :=
    (le_max_right Nlog (max Npoint 2)).trans hNtail'
  have hfirst := hwindow N hNwindow L hrun
  have hcritical :
      CriticalWindowParameters.InCriticalWindow c₁ c₂ N (L + 1) := by
    simpa only [c₁, c₂] using hfirst.1
  have hLplusTwoReal :
      (((L + 1) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    have hlength' :=
      hlength N hNlength (L + 1) hfirst.1.2.2.2
    norm_num only [pow_one, Nat.cast_add, Nat.cast_one] at hlength' ⊢
    exact hlength'
  have hLheight : L + 1 ≤ N := by
    have hLplusTwo : (L + 1) + 1 ≤ N := by
      exact_mod_cast hLplusTwoReal
    omega
  have hthreshold :
      Real.exp (Real.exp 0) < (N : ℝ) :=
    hNlog.trans_le (by exact_mod_cast hNlogN)
  have hlogN :
      Real.exp 0 < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos (Real.exp 0)) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hlogNpos : 0 < Real.log N :=
    (Real.exp_pos 0).trans hlogN
  have hloglogNpos : 0 < Real.log (Real.log N) := by
    have hone : 1 < Real.log N := by
      simpa only [Real.exp_zero] using hlogN
    exact Real.log_pos hone
  have hscaleNonneg :
      0 ≤ Real.log N / Real.log (Real.log N) :=
    div_nonneg hlogNpos.le hloglogNpos.le
  apply maxCanonicalCorrectedDefectCount_cast_le
    (mul_nonneg hK hscaleNonneg)
  intro pair hpair
  have hmem := mem_separatedDyadicPairs.mp hpair
  exact
    hpoint N hNpointTwo L hcritical hLheight
      A pair.1 pair.2 hmem.1 hmem.2.1

/--
The uniform corrected-defect loss required in Proposition 7.3:
`4^(max D#) = N^(o_C(1))`.
-/
theorem four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (((4 ^ maxCanonicalCorrectedDefectCount A N L : ℕ) : ℝ))) := by
  obtain ⟨K, hK, Nbound, hbound⟩ :=
    maxCanonicalCorrectedDefectCount_log_bound_eventually hC
  have htwo :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          (((2 ^ (2 * maxCanonicalCorrectedDefectCount A N L) :
              ℕ) : ℝ))) := by
    apply
      ExpSqrtLog.uniformSubpolynomialOn_two_pow_log_div_loglog_eventually
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L => 2 * maxCanonicalCorrectedDefectCount A N L)
        (2 * K) (mul_nonneg (by norm_num) hK)
    refine ⟨Nbound, ?_⟩
    intro N hN L hrun
    have hmax := hbound N hN L hrun A
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      2 * (maxCanonicalCorrectedDefectCount A N L : ℝ) ≤
          2 * (K * (Real.log N / Real.log (Real.log N))) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ =
          (2 * K) * Real.log N / Real.log (Real.log N) := by
        ring
  simpa [pow_mul, pow_two] using htwo

end

end CorrectedDefectEnvelope
end PaperC
