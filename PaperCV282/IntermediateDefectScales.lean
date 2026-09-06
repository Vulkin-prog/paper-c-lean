import PaperC.Asymptotics.LemmaFifteenThree

/-! # Counting exponents in every fixed logarithmic band -/
namespace PaperC.V282.IntermediateDefectScales

open Filter LemmaFifteenThree

noncomputable section

/-- A coefficient for the global two-defect count in the L/log L scale. -/
def countingConstant (betaMin c : ℝ) : ℝ :=
  2 * (4 * Real.log 2 + 2 + 4 * c / betaMin)

/-- The counting constant is nonnegative throughout its intended domain. -/
theorem countingConstant_nonneg {betaMin c : ℝ} (hb : 0 < betaMin) (hc : 0 ≤ c) :
    0 ≤ countingConstant betaMin c := by unfold countingConstant; positivity

/-- Kernel choices, offsets and the precise Pell exponent fit in one band-uniform bound. -/
theorem combined_exponent_le_band
    {betaMin betaMax c : ℝ} (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hc : 0 ≤ c)
    {N L : ℕ}
    (hN : 3 ≤ N)
    (hL : 2 ≤ L)
    (hwindow :
      CriticalWindowParameters.InCriticalWindow
        betaMin
        betaMax N (L + 1))
    (hloglogN : 0 < Real.log (Real.log (N : ℝ)))
    (hlogc₂ :
      Real.log betaMax ≤
        Real.log (Real.log (N : ℝ)))
    (hlogSq :
      Real.log ((L + 1 : ℕ) : ℝ) ^ 2 ≤
        ((L + 1 : ℕ) : ℝ)) :
    (4 * Real.log 2) *
          (((L + 1 : ℕ) : ℝ) /
            Real.log ((L + 1 : ℕ) : ℝ)) +
        2 * Real.log ((L + 1 : ℕ) : ℝ) +
        c *
          (Real.log ((3 * N : ℕ) : ℝ) /
            Real.log (Real.log ((3 * N : ℕ) : ℝ))) ≤
      countingConstant betaMin c *
        ((L : ℝ) / Real.log (L : ℝ)) := by
  let B : ℕ := L + 1
  let c₁ : ℝ := betaMin
  let c₂ : ℝ := betaMax
  have hc₁ : 0 < c₁ := by
    simpa only [c₁] using hbetaMin
  have hc₁c₂ : c₁ < c₂ := by
    simpa only [c₁, c₂] using hbeta
  have hBtwo : 2 ≤ B := by
    dsimp [B]
    omega
  have hlogBpos : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast hBtwo)
  have hBdivNonneg :
      0 ≤ (B : ℝ) / Real.log (B : ℝ) :=
    div_nonneg (Nat.cast_nonneg B) hlogBpos.le
  have hcompare :
      Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) ≤
        (2 / c₁) *
          ((B : ℝ) / Real.log (B : ℝ)) := by
    apply
      DefectiveVertexIntervalBound.log_div_loglog_le_two_div_lower_mul_height_div_log
        hc₁ hc₁c₂
    · simpa only [c₁, c₂, B] using hwindow
    · exact Real.log_pos
        (by
          have : (1 : ℝ) < (N : ℝ) := by
            exact_mod_cast (show 1 < N by omega)
          exact this)
    · exact hloglogN
    · exact_mod_cast hBtwo
    · simpa only [c₂] using hlogc₂
  have hthree :=
    three_mul_log_div_loglog_le_two hN hloglogN
  have hPell :
      c *
          (Real.log ((3 * N : ℕ) : ℝ) /
            Real.log (Real.log ((3 * N : ℕ) : ℝ))) ≤
        (4 * c / c₁) *
          ((B : ℝ) / Real.log (B : ℝ)) := by
    calc
      c *
            (Real.log ((3 * N : ℕ) : ℝ) /
              Real.log (Real.log ((3 * N : ℕ) : ℝ)))
          ≤ c *
            (2 *
              (Real.log (N : ℝ) /
                Real.log (Real.log (N : ℝ)))) :=
        mul_le_mul_of_nonneg_left hthree hc
      _ ≤ c *
            (2 *
              ((2 / c₁) *
                ((B : ℝ) / Real.log (B : ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcompare (by norm_num)) hc
      _ = (4 * c / c₁) *
            ((B : ℝ) / Real.log (B : ℝ)) := by ring
  have hsquare :
      2 * Real.log (B : ℝ) ≤
        2 * ((B : ℝ) / Real.log (B : ℝ)) := by
    have hrewrite :
        2 * ((B : ℝ) / Real.log (B : ℝ)) =
          (2 * (B : ℝ)) / Real.log (B : ℝ) := by ring
    rw [hrewrite, le_div_iff₀ hlogBpos]
    have hlogSqB :
        Real.log (B : ℝ) ^ 2 ≤ (B : ℝ) := by
      simpa only [B] using hlogSq
    nlinarith [hlogSqB, show
      Real.log (B : ℝ) * Real.log (B : ℝ) =
        Real.log (B : ℝ) ^ 2 by ring]
  have hBtoL :
      (B : ℝ) / Real.log (B : ℝ) ≤
        2 * ((L : ℝ) / Real.log (L : ℝ)) := by
    simpa only [B] using succ_div_log_le_two_mul_div_log hL
  have hcoefficient :
      0 ≤ 4 * Real.log 2 + 2 + 4 * c / c₁ := by
    have hlogTwo : 0 ≤ Real.log (2 : ℝ) :=
      Real.log_nonneg (by norm_num)
    positivity
  calc
    (4 * Real.log 2) *
            (((L + 1 : ℕ) : ℝ) /
              Real.log ((L + 1 : ℕ) : ℝ)) +
          2 * Real.log ((L + 1 : ℕ) : ℝ) +
          c *
            (Real.log ((3 * N : ℕ) : ℝ) /
              Real.log (Real.log ((3 * N : ℕ) : ℝ)))
        ≤ (4 * Real.log 2) *
              ((B : ℝ) / Real.log (B : ℝ)) +
            2 * ((B : ℝ) / Real.log (B : ℝ)) +
            (4 * c / c₁) *
              ((B : ℝ) / Real.log (B : ℝ)) := by
          dsimp only [B] at hsquare hPell ⊢
          linarith
    _ = (4 * Real.log 2 + 2 + 4 * c / c₁) *
          ((B : ℝ) / Real.log (B : ℝ)) := by ring
    _ ≤ (4 * Real.log 2 + 2 + 4 * c / c₁) *
          (2 * ((L : ℝ) / Real.log (L : ℝ))) :=
      mul_le_mul_of_nonneg_left hBtoL hcoefficient
    _ = countingConstant betaMin c *
          ((L : ℝ) / Real.log (L : ℝ)) := by
      dsimp [countingConstant, c₁]
      ring


/-- Both conventional counting scales are uniformly comparable on the whole band. -/
theorem logarithmic_scales_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℕ) →
      (L + 1 : ℕ) ≤ betaMax * Real.log M →
      (betaMin / 4) * (Real.log M / Real.log (Real.log M)) ≤ (L : ℝ) / Real.log L ∧
      (L : ℝ) / Real.log L ≤ (2 * betaMax) * (Real.log M / Real.log (Real.log M)) := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨Ma, ha⟩ := CriticalWeightedDefect.admissible_eventually hbetaMin hbeta
  obtain ⟨Mh, hh⟩ := CriticalWeightedDefect.height_tends_to_infinity
    (c₂ := betaMax) hbetaMin 3
  have hll := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (max (Real.log betaMax) (max 1 (-2 * Real.log (betaMin / 2)))))
  obtain ⟨Ml, hl⟩ := eventually_atTop.mp hll
  refine ⟨max 3 (max Ma (max Mh Ml)), ?_⟩
  intro M hM L hlo hup
  have hwindow : CriticalWindowParameters.InCriticalWindow betaMin betaMax M (L + 1) :=
    ⟨hbetaMin, hbeta, hlo, hup⟩
  have hheight := hh M (by omega) (L + 1) (ha M (by omega) (L + 1) hwindow)
  have hL : 2 ≤ L := by omega
  have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast hL)
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogs := hl M (by omega)
  change max (Real.log betaMax) (max 1 (-2 * Real.log (betaMin / 2))) ≤
    Real.log (Real.log M) at hlogs
  have hllpos : 0 < Real.log (Real.log M) := by
    have := (le_max_left 1 (-2 * Real.log (betaMin / 2))).trans
      ((le_max_right (Real.log betaMax) _).trans hlogs)
    linarith
  have hlc : Real.log betaMax ≤ Real.log (Real.log M) := (le_max_left _ _).trans hlogs
  have hcompare := DefectiveVertexIntervalBound.log_div_loglog_le_two_div_lower_mul_height_div_log
    hbetaMin hbeta hwindow hlogM hllpos (by exact_mod_cast (show 1 < L + 1 by omega)) hlc
  have hsucc := succ_div_log_le_two_mul_div_log hL
  have hlow : Real.log M / Real.log (Real.log M) ≤
      (4 / betaMin) * ((L : ℝ) / Real.log L) := by
    calc
      _ ≤ (2 / betaMin) * (((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ)) := hcompare
      _ ≤ (2 / betaMin) * (2 * ((L : ℝ) / Real.log L)) := by gcongr
      _ = _ := by ring
  have hleft : (betaMin / 4) * (Real.log M / Real.log (Real.log M)) ≤ (L : ℝ) / Real.log L := by
    have h := mul_le_mul_of_nonneg_left hlow (show 0 ≤ betaMin / 4 by positivity)
    have he : betaMin / 4 * (4 / betaMin * ((L : ℝ) / Real.log L)) = (L : ℝ) / Real.log L := by field_simp
    rwa [he] at h
  have hLlower : betaMin / 2 * Real.log M ≤ (L : ℝ) := by
    push_cast at hlo
    have hLp : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
    linarith
  have hlogLower := Real.log_le_log (mul_pos (by positivity : 0 < betaMin / 2) hlogM) hLlower
  rw [Real.log_mul (by positivity : betaMin / 2 ≠ 0) hlogM.ne'] at hlogLower
  have hlogConst : -2 * Real.log (betaMin / 2) ≤ Real.log (Real.log M) :=
    (le_max_right 1 _).trans ((le_max_right (Real.log betaMax) _).trans hlogs)
  have hlogHalf : Real.log (Real.log M) / 2 ≤ Real.log L := by linarith
  have hLupper : (L : ℝ) ≤ betaMax * Real.log M := by push_cast at hup; linarith
  refine ⟨hleft, ?_⟩
  calc
    (L : ℝ) / Real.log L ≤ (betaMax * Real.log M) / Real.log L :=
      div_le_div_of_nonneg_right hLupper hlogL.le
    _ ≤ (betaMax * Real.log M) / (Real.log (Real.log M) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlogHalf
    _ = _ := by ring

end
end PaperC.V282.IntermediateDefectScales
