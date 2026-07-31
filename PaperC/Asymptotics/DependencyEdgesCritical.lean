import PaperC.Analysis.DependencyEdgeBound
import PaperC.Analysis.TerminalPrimeCutoff
import PaperC.Asymptotics.CriticalRationalMassEnvelopes

/-!
# Dependency edges in the critical run-length window

`DependencyEdgeBound` gives the fully explicit finite estimate

`E_Y ≤ (L+1)²
  (28 N²/(Y log₂ Y) + 6 N²/Y + 3N)`.

Here we specialize it to the literal Section 13 cutoff

`Y = ⌊(L+1)² log(L+1)⌋`.

The proof deliberately keeps an integer accuracy parameter `m`.  Once
`m ≤ log(L+1)`, the floor definition gives

`m (L+1)² ≤ Y`.

In the critical window, `L+1` tends uniformly to infinity, while its
already-certified subpolynomial estimate with exponent three gives
`(L+1)³ ≤ N` eventually.  These two facts reduce the normalized edge count
to `37/m`.  Choosing `m > 37/ε` proves the literal uniform `o_C(N²)`
conclusion without adding an analytic bridge.
-/

namespace PaperC
namespace DependencyEdgesCritical

open TerminalPrimeCutoff

/--
The floor cutoff retains every integral multiple of `B²` lying below its
real defining scale.
-/
theorem mul_sq_le_terminalPrimeCutoff
    {m B : ℕ}
    (hlog : (m : ℝ) ≤ Real.log (B : ℝ)) :
    m * B ^ 2 ≤ terminalPrimeCutoff B := by
  rw [terminalPrimeCutoff,
    Nat.le_floor_iff (terminalPrimeScale_nonneg B)]
  simp only [terminalPrimeScale, Nat.cast_mul, Nat.cast_pow]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hlog
      (sq_nonneg (B : ℝ))

/--
Finite `37/m` envelope.  This lemma isolates all arithmetic used by the
asymptotic wrapper:

* `m B² ≤ Y` controls both reciprocal-cutoff terms;
* `B³ ≤ N` and `m ≤ B` control the linear-in-`N` term.
-/
theorem card_orderedDependencyEdges_cast_le_div
    {N L Y m : ℕ}
    (hm : 1 ≤ m)
    (hB : 2 ≤ L + 1)
    (hMY : m * (L + 1) ^ 2 ≤ Y)
    (hBcube : (L + 1) ^ 3 ≤ N)
    (hmB : m ≤ L + 1) :
    ((LargePrimeDependencyGraph.orderedDependencyEdges N L Y).card : ℚ) ≤
      37 * (N : ℚ) ^ 2 / (m : ℚ) := by
  have hN : 2 ≤ N := by
    have : 2 ^ 3 ≤ N := (Nat.pow_le_pow_left hB 3).trans hBcube
    norm_num at this ⊢
    omega
  have hLN : L ≤ N := by
    have hLB : L ≤ L + 1 := by omega
    have hBcube_ge : L + 1 ≤ (L + 1) ^ 3 := by
      nlinarith [show 1 ≤ L + 1 by omega]
    exact hLB.trans (hBcube_ge.trans hBcube)
  have hLY : L ≤ Y := by
    have hmBsq : (L + 1) ^ 2 ≤ m * (L + 1) ^ 2 := by
      exact Nat.le_mul_of_pos_left _ (by omega)
    have hBsq : L ≤ (L + 1) ^ 2 := by
      nlinarith
    exact hBsq.trans (hmBsq.trans hMY)
  have hY : 4 ≤ Y := by
    have hmBsq : (L + 1) ^ 2 ≤ m * (L + 1) ^ 2 := by
      exact Nat.le_mul_of_pos_left _ (by omega)
    have : 4 ≤ (L + 1) ^ 2 := by nlinarith
    exact this.trans (hmBsq.trans hMY)
  have hlogY : 1 ≤ Nat.log 2 Y := by
    exact Nat.log_pos (by norm_num) (by omega)
  have hmQ : (0 : ℚ) < (m : ℚ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hYQ : (0 : ℚ) < (Y : ℚ) := by
    exact_mod_cast (show 0 < Y by omega)
  have hlogYQ : (0 : ℚ) < (Nat.log 2 Y : ℚ) := by
    exact_mod_cast (show 0 < Nat.log 2 Y by omega)
  have hBsq_div_Y :
      ((L + 1 : ℕ) : ℚ) ^ 2 / (Y : ℚ) ≤
        1 / (m : ℚ) := by
    apply (div_le_div_iff₀ hYQ hmQ).2
    have hMY' : (L + 1) ^ 2 * m ≤ Y := by
      simpa only [mul_comm] using hMY
    have hMYQ :
        (((L + 1) ^ 2 * m : ℕ) : ℚ) ≤ (Y : ℚ) := by
      exact_mod_cast hMY'
    simpa only [Nat.cast_mul, Nat.cast_pow, one_mul] using hMYQ
  have hY_le_Ylog :
      (Y : ℚ) ≤ (Y : ℚ) * (Nat.log 2 Y : ℚ) := by
    calc
      (Y : ℚ) = (Y : ℚ) * 1 := by ring
      _ ≤ (Y : ℚ) * (Nat.log 2 Y : ℚ) := by
        gcongr
        exact_mod_cast hlogY
  have hBsq_div_Ylog :
      ((L + 1 : ℕ) : ℚ) ^ 2 /
          ((Y : ℚ) * (Nat.log 2 Y : ℚ)) ≤
        1 / (m : ℚ) := by
    calc
      ((L + 1 : ℕ) : ℚ) ^ 2 /
          ((Y : ℚ) * (Nat.log 2 Y : ℚ)) ≤
          ((L + 1 : ℕ) : ℚ) ^ 2 / (Y : ℚ) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hYQ
        · exact hY_le_Ylog
      _ ≤ 1 / (m : ℚ) := hBsq_div_Y
  have hmBsqN :
      (m : ℚ) * ((L + 1 : ℕ) : ℚ) ^ 2 ≤
        (N : ℚ) := by
    have hmBsqNat :
        m * (L + 1) ^ 2 ≤ (L + 1) ^ 3 := by
      calc
        m * (L + 1) ^ 2 ≤
            (L + 1) * (L + 1) ^ 2 :=
          Nat.mul_le_mul_right _ hmB
        _ = (L + 1) ^ 3 := by ring
    exact_mod_cast hmBsqNat.trans hBcube
  have hBsqN_div :
      ((L + 1 : ℕ) : ℚ) ^ 2 * (N : ℚ) ≤
        (N : ℚ) ^ 2 / (m : ℚ) := by
    apply (le_div_iff₀ hmQ).2
    calc
      ((L + 1 : ℕ) : ℚ) ^ 2 * (N : ℚ) * (m : ℚ) =
          ((m : ℚ) * ((L + 1 : ℕ) : ℚ) ^ 2) * (N : ℚ) := by
        ring
      _ ≤ (N : ℚ) * (N : ℚ) :=
        mul_le_mul_of_nonneg_right hmBsqN (by positivity)
      _ = (N : ℚ) ^ 2 := by ring
  have hedge :=
    DependencyEdgeBound.card_orderedDependencyEdges_cast_le
      (N := N) (L := L) (Y := Y) hN hLN hLY hY
  calc
    ((LargePrimeDependencyGraph.orderedDependencyEdges N L Y).card : ℚ) ≤
        ((L + 1 : ℕ) : ℚ) ^ 2 *
          (28 * (N : ℚ) ^ 2 /
              ((Y : ℚ) * (Nat.log 2 Y : ℚ)) +
            6 * (N : ℚ) ^ 2 / (Y : ℚ) +
            3 * (N : ℚ)) :=
      (by
        simpa only [Nat.cast_add, Nat.cast_one] using hedge)
    _ =
        28 * (N : ℚ) ^ 2 *
            (((L + 1 : ℕ) : ℚ) ^ 2 /
              ((Y : ℚ) * (Nat.log 2 Y : ℚ))) +
          6 * (N : ℚ) ^ 2 *
            (((L + 1 : ℕ) : ℚ) ^ 2 / (Y : ℚ)) +
          3 * (((L + 1 : ℕ) : ℚ) ^ 2 * (N : ℚ)) := by
      ring
    _ ≤
        28 * (N : ℚ) ^ 2 * (1 / (m : ℚ)) +
          6 * (N : ℚ) ^ 2 * (1 / (m : ℚ)) +
          3 * ((N : ℚ) ^ 2 / (m : ℚ)) := by
      gcongr
    _ = 37 * (N : ℚ) ^ 2 / (m : ℚ) := by
      ring

/--
At the literal terminal cutoff, the finite envelope only needs a lower bound
for `log(L+1)` and the cubic critical-window estimate.
-/
theorem card_orderedDependencyEdges_terminalCutoff_cast_le_div
    {N L m : ℕ}
    (hm : 1 ≤ m)
    (hlog : (m : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ))
    (hBcube : (L + 1) ^ 3 ≤ N) :
    ((LargePrimeDependencyGraph.orderedDependencyEdges N L
        (terminalPrimeCutoff (L + 1))).card : ℚ) ≤
      37 * (N : ℚ) ^ 2 / (m : ℚ) := by
  have hB : 2 ≤ L + 1 := by
    have honeLog :
        (1 : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ) := by
      have h1m : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hm
      exact h1m.trans hlog
    have hlogPos :
        0 < Real.log ((L + 1 : ℕ) : ℝ) :=
      zero_lt_one.trans_le honeLog
    have hone :
        (1 : ℝ) < ((L + 1 : ℕ) : ℝ) :=
      (Real.log_pos_iff (by positivity)).mp hlogPos
    exact_mod_cast hone
  have hmB :
      m ≤ L + 1 := by
    exact_mod_cast hlog.trans (Real.log_le_self (by positivity))
  exact
    card_orderedDependencyEdges_cast_le_div hm hB
      (mul_sq_le_terminalPrimeCutoff hlog) hBcube hmB

/--
The run length plus one tends uniformly to infinity in the literal critical
window.
-/
theorem runLengthAddOne_tends_to_infinity
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ M : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
        M ≤ L + 1 := by
  intro M
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nheight, hheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      CriticalRunWindow.lowerConstant_pos M
  refine ⟨max Nwindow (max Nadm Nheight), ?_⟩
  intro N hN L hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hNtail :
      max Nadm Nheight ≤ N :=
    (le_max_right Nwindow (max Nadm Nheight)).trans hN
  exact
    hheight N ((le_max_right Nadm Nheight).trans hNtail) (L + 1)
      (hadm N ((le_max_left Nadm Nheight).trans hNtail)
        (L + 1) hw.1)

/--
Lemma 13.6, at the literal terminal cutoff, in the manuscript's critical
run-length window:

`E_Y = o_C(N²)`, uniformly for `|L-log₂ N| ≤ C`.

No conditional independence statement is used here: this is solely the
certified arithmetic bound for the number of ordered dependency edges.
-/
theorem orderedDependencyEdges_terminalCutoff_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ((LargePrimeDependencyGraph.orderedDependencyEdges N L
          (terminalPrimeCutoff (L + 1))).card : ℝ))
      (fun N _ => (N : ℝ) ^ 2) := by
  have hsubpoly :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial hC
  intro ε hε
  obtain ⟨m : ℕ, hmLarge⟩ :=
    exists_nat_gt (37 / ε)
  have hm : 1 ≤ m := by
    have hpositive : (0 : ℝ) < 37 / ε := by positivity
    have : (0 : ℝ) < (m : ℝ) := hpositive.trans hmLarge
    exact_mod_cast this
  let M : ℕ := ⌈Real.exp (m : ℝ)⌉₊
  obtain ⟨Nheight, hheight⟩ :=
    runLengthAddOne_tends_to_infinity hC M
  obtain ⟨Ncube, hcube⟩ := hsubpoly 3 (by omega)
  refine ⟨max Nheight Ncube, ?_⟩
  intro N hN L hrun
  have hMN :
      M ≤ L + 1 :=
    hheight N ((le_max_left _ _).trans hN) L hrun
  have hexp :
      Real.exp (m : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
    calc
      Real.exp (m : ℝ) ≤ (M : ℝ) := by
        exact Nat.le_ceil _
      _ ≤ ((L + 1 : ℕ) : ℝ) := by
        exact_mod_cast hMN
  have hlog :
      (m : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ) := by
    have hlogMono :=
      Real.log_le_log (Real.exp_pos (m : ℝ)) hexp
    simpa only [Real.log_exp] using hlogMono
  have hcubeReal :=
    hcube N ((le_max_right _ _).trans hN) L hrun
  have hcubeNat : (L + 1) ^ 3 ≤ N := by
    have hnonneg :
        (0 : ℝ) ≤ (((L + 1 : ℕ) : ℝ)) := by positivity
    rw [abs_of_nonneg hnonneg] at hcubeReal
    exact_mod_cast hcubeReal
  have hfiniteQ :=
    card_orderedDependencyEdges_terminalCutoff_cast_le_div
      hm hlog hcubeNat
  have hfinite :
      ((LargePrimeDependencyGraph.orderedDependencyEdges N L
          (terminalPrimeCutoff (L + 1))).card : ℝ) ≤
        37 * (N : ℝ) ^ 2 / (m : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hfiniteQ
    push_cast at hcast
    norm_num at hcast ⊢
    exact hcast
  have hmPos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hcoefficient :
      37 / (m : ℝ) < ε := by
    exact (div_lt_iff₀ hmPos).2 (by
      simpa only [mul_comm] using
        ((div_lt_iff₀ hε).mp hmLarge))
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have htarget :
      37 * (N : ℝ) ^ 2 / (m : ℝ) ≤
        ε * (N : ℝ) ^ 2 := by
    calc
      37 * (N : ℝ) ^ 2 / (m : ℝ) =
          (37 / (m : ℝ)) * (N : ℝ) ^ 2 := by ring
      _ ≤ ε * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefficient.le hNnonneg
  simpa only [abs_of_nonneg (by positivity :
      0 ≤
        ((LargePrimeDependencyGraph.orderedDependencyEdges N L
          (terminalPrimeCutoff (L + 1))).card : ℝ)),
    abs_of_nonneg hNnonneg] using hfinite.trans htarget

end DependencyEdgesCritical
end PaperC
