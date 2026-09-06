import PaperCV282.IntermediateDefectCover
import PaperCV282.IntermediateDefectScales
import PaperCV282.PostQuadraticPrimeBounds

/-! # Precise intermediate two-defect counting on a whole logarithmic band -/
namespace PaperC.V282.IntermediateDefectCount

open Filter IntermediateDefectCover IntermediateDefectScales PostQuadraticPrimeBounds
open LemmaFifteenThree SquarefreeSmoothCount HighZoneTwoDefects WindowValues

noncomputable section

/-- The finite coefficient and kernel envelope becomes its explicit logarithmic exponent. -/
theorem assemble_finite_count
    {c K : ℝ} {N L : ℕ} {s : Finset ℕ}
    (hfinite :
      (s.card : ℝ) ≤
        ((squarefreeSmoothUpTo (L + 1) (3 * N)).card : ℝ) ^ 2 *
          (((L + 1 : ℕ) : ℝ)) ^ 2 *
          PellInput.expLogLogBound c (3 * N))
    (hkernel :
      ((squarefreeSmoothUpTo (L + 1) (3 * N)).card : ℝ) ≤
        Real.exp
          ((2 * Real.log 2) *
            (((L + 1 : ℕ) : ℝ) /
              Real.log ((L + 1 : ℕ) : ℝ))))
    (hexponent :
      (4 * Real.log 2) *
            (((L + 1 : ℕ) : ℝ) /
              Real.log ((L + 1 : ℕ) : ℝ)) +
          2 * Real.log ((L + 1 : ℕ) : ℝ) +
          c *
            (Real.log ((3 * N : ℕ) : ℝ) /
              Real.log (Real.log ((3 * N : ℕ) : ℝ))) ≤
        K * ((L : ℝ) / Real.log (L : ℝ))) :
    (s.card : ℝ) ≤
      Real.exp (K * ((L : ℝ) / Real.log (L : ℝ))) := by
  let D : ℝ :=
    ((squarefreeSmoothUpTo (L + 1) (3 * N)).card : ℝ)
  let E : ℝ :=
    (2 * Real.log 2) *
      (((L + 1 : ℕ) : ℝ) /
        Real.log ((L + 1 : ℕ) : ℝ))
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hExpNonneg : 0 ≤ Real.exp E := (Real.exp_pos E).le
  have hD : D ≤ Real.exp E := by
    simpa only [D, E] using hkernel
  have hDsq : D ^ 2 ≤ Real.exp E ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD)
      (add_nonneg hDnonneg hExpNonneg)]
  have hremainingNonneg :
      0 ≤ (((L + 1 : ℕ) : ℝ)) ^ 2 *
        PellInput.expLogLogBound c (3 * N) := by
    unfold PellInput.expLogLogBound
    positivity
  have hproduct :
      D ^ 2 * (((L + 1 : ℕ) : ℝ)) ^ 2 *
          PellInput.expLogLogBound c (3 * N) ≤
        Real.exp
          ((4 * Real.log 2) *
              (((L + 1 : ℕ) : ℝ) /
                Real.log ((L + 1 : ℕ) : ℝ)) +
            2 * Real.log ((L + 1 : ℕ) : ℝ) +
            c *
              (Real.log ((3 * N : ℕ) : ℝ) /
                Real.log (Real.log ((3 * N : ℕ) : ℝ)))) := by
    calc
      D ^ 2 * (((L + 1 : ℕ) : ℝ)) ^ 2 *
            PellInput.expLogLogBound c (3 * N)
          ≤ Real.exp E ^ 2 *
            (((L + 1 : ℕ) : ℝ)) ^ 2 *
              PellInput.expLogLogBound c (3 * N) := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_right hDsq hremainingNonneg)
      _ = Real.exp
          ((4 * Real.log 2) *
              (((L + 1 : ℕ) : ℝ) /
                Real.log ((L + 1 : ℕ) : ℝ)) +
            2 * Real.log ((L + 1 : ℕ) : ℝ) +
            c *
              (Real.log ((3 * N : ℕ) : ℝ) /
                Real.log (Real.log ((3 * N : ℕ) : ℝ)))) := by
        have hBpos :
            0 < (((L + 1 : ℕ) : ℝ)) := by positivity
        have hExpE :
            Real.exp E ^ 2 = Real.exp (2 * E) := by
          rw [← Real.exp_nat_mul]
          norm_num
        have hBexp :
            (((L + 1 : ℕ) : ℝ)) ^ 2 =
              Real.exp
                (2 * Real.log ((L + 1 : ℕ) : ℝ)) := by
          calc
            (((L + 1 : ℕ) : ℝ)) ^ 2 =
                (Real.exp
                  (Real.log ((L + 1 : ℕ) : ℝ))) ^ 2 := by
              rw [Real.exp_log hBpos]
            _ = Real.exp
                (2 * Real.log ((L + 1 : ℕ) : ℝ)) := by
              simpa using
                (Real.exp_nat_mul
                  (Real.log ((L + 1 : ℕ) : ℝ)) 2).symm
        rw [hExpE, hBexp]
        unfold PellInput.expLogLogBound
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [E]
        ring
  calc
    (s.card : ℝ)
        ≤ D ^ 2 * (((L + 1 : ℕ) : ℝ)) ^ 2 *
            PellInput.expLogLogBound c (3 * N) := by
      simpa only [D] using hfinite
    _ ≤ Real.exp
          ((4 * Real.log 2) *
              (((L + 1 : ℕ) : ℝ) /
                Real.log ((L + 1 : ℕ) : ℝ)) +
            2 * Real.log ((L + 1 : ℕ) : ℝ) +
            c *
              (Real.log ((3 * N : ℕ) : ℝ) /
                Real.log (Real.log ((3 * N : ℕ) : ℝ)))) :=
      hproduct
    _ ≤ Real.exp
          (K * ((L : ℝ) / Real.log (L : ℝ))) :=
      Real.exp_le_exp.mpr hexponent

/-! ## Lemma 15.3 -/

/-- A single global interval of starts has the precise exponential bound.
The threshold precedes the word length and the arbitrary finite mask. -/
theorem global_two_defect_count_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℕ) →
      (L + 1 : ℕ) ≤ betaMax * Real.log M →
      ∀ s : Finset ℕ,
      (∀ x ∈ s, (L + 1) ^ 2 + 2 < x ∧ x ≤ 2 * M ∧
        2 ≤ (defectIndices (L + 1) x (L + 1)).card) →
      (s.card : ℝ) ≤ Real.exp (K * ((L : ℝ) / Real.log L)) := by
  obtain ⟨c, hc, Mpell, hpell⟩ := finite_two_defect_count hNR
  obtain ⟨Bpnt, hpnt⟩ := SquarefreeSmoothCritical.primeNumberTheorem_implies_squarefreeSmooth_bound
    (primeNumberTheorem_of_remainder hPNT)
  obtain ⟨Blog, hBlog⟩ := log_sq_le_self_eventually
  obtain ⟨Madm, hMadm⟩ := CriticalWeightedDefect.admissible_eventually hbetaMin hbeta
  obtain ⟨Mheight, hheight⟩ := CriticalWeightedDefect.height_tends_to_infinity
    (c₂ := betaMax) hbetaMin (max 5 (max Bpnt Blog))
  obtain ⟨Mlogs, hlogs⟩ := log_const_le_loglog_eventually (hbetaMin.trans hbeta)
  refine ⟨countingConstant betaMin c, countingConstant_nonneg hbetaMin hc,
    max 3 (max Mpell (max Madm (max Mheight Mlogs))), ?_⟩
  intro M hM L hlo hup s hs
  have hwindow : CriticalWindowParameters.InCriticalWindow betaMin betaMax M (L + 1) :=
    ⟨hbetaMin, hbeta, hlo, hup⟩
  have hadm := hMadm M (by omega) (L + 1) hwindow
  have hBlarge := hheight M (by omega) (L + 1) hadm
  have hL : 2 ≤ L := by omega
  have hBN : L + 1 ≤ M := by
    have hlin := hadm.2.2.2.1
    have hreal : ((L + 1 : ℕ) : ℝ) ≤ M := by linarith
    exact_mod_cast hreal
  have hfinite := hpell (L + 1) M (by omega) hBN s hs
  have hkernel := hpnt (L + 1) (by omega) (3 * M)
  obtain ⟨hloglog, hlogMax⟩ := hlogs M (by omega)
  have hexponent := combined_exponent_le_band hbetaMin hbeta hc (by omega : 3 ≤ M) hL
    hwindow hloglog hlogMax (hBlog (L + 1) (by omega))
  exact assemble_finite_count hfinite hkernel hexponent

/-- Lemma 7.2, with an explicit finite population of actual two-defect windows.
The constant and threshold are uniform in every X between 2L² and M. -/
theorem lemma_seven_two
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℕ) →
      (L + 1 : ℕ) ≤ betaMax * Real.log M →
      ∀ X : ℕ, 2 * L ^ 2 ≤ X → X ≤ M →
      (((Finset.Ico X (2 * X)).filter
        (fun x => 2 ≤ (defectIndices (L + 1) x (L + 1)).card)).card : ℝ) ≤
        Real.exp (K * ((L : ℝ) / Real.log L)) := by
  classical
  obtain ⟨K, hK, Mzero, h⟩ := global_two_defect_count_eventually
    betaMin betaMax hbetaMin hbeta hPNT hNR
  obtain ⟨Madm, hadm⟩ := CriticalWeightedDefect.admissible_eventually hbetaMin hbeta
  obtain ⟨Mheight, hheight⟩ := CriticalWeightedDefect.height_tends_to_infinity
    (c₂ := betaMax) hbetaMin 5
  refine ⟨K, hK, max Mzero (max Madm Mheight), ?_⟩
  intro M hM L hlo hup X hXL hXM
  have hLlarge := hheight M (by omega) (L + 1) (hadm M (by omega) (L + 1) ⟨hbetaMin,hbeta,hlo,hup⟩)
  apply h M (by omega) L hlo hup
  intro x hx
  obtain ⟨hx, hd⟩ := Finset.mem_filter.mp hx
  obtain ⟨hXx, hxX⟩ := Finset.mem_Ico.mp hx
  refine ⟨?_, by omega, hd⟩
  have hlocal : (L + 1) ^ 2 + 2 < 2 * L ^ 2 := by nlinarith
  omega

/-- The literal log M / loglog M formulation of Lemma 7.2. -/
theorem lemma_seven_two_ambient_scale
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℕ) →
      (L + 1 : ℕ) ≤ betaMax * Real.log M →
      ∀ X : ℕ, 2 * L ^ 2 ≤ X → X ≤ M →
      (((Finset.Ico X (2 * X)).filter
        (fun x => 2 ≤ (defectIndices (L + 1) x (L + 1)).card)).card : ℝ) ≤
        Real.exp (C * (Real.log M / Real.log (Real.log M))) := by
  obtain ⟨K, hK, Mc, hc⟩ := lemma_seven_two betaMin betaMax hbetaMin hbeta hPNT hNR
  obtain ⟨Ms, hs⟩ := logarithmic_scales_eventually betaMin betaMax hbetaMin hbeta
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  refine ⟨K * (2 * betaMax), by positivity, max Mc Ms, ?_⟩
  intro M hM L hlo hup X hXL hXM
  apply (hc M (by omega) L hlo hup X hXL hXM).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (hs M (by omega) L hlo hup).2 hK
  simpa only [mul_assoc] using hh

end
end PaperC.V282.IntermediateDefectCount
