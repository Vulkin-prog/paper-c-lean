import PaperC.Combinatorics.BoundedRatioRelationalHosts
import PaperC.Analysis.RelationalHostBound
import PaperC.Asymptotics.ExpSqrtLog
import PaperC.Asymptotics.ThreeHalvesPower
import PaperC.Probability.CriticalRunWindow

set_option maxHeartbeats 1800000

/-!
# The bounded-ratio relational-host estimate

The finite certificate estimate on `[N,M)` has the form

`O_{κ₀}((L+1) N sqrt(M+L) exp(4 sqrt(L+1)))`.

For `M ≤ κ₀N`, this is `N sqrt(N)` times a uniformly subpolynomial
factor.  This module records the resulting fully quantified
`N^(3/2+o_{C,κ₀}(1))` estimate, uniformly in both `M` and `L`.
-/

namespace PaperC
namespace BoundedRatioRelationalHostsCritical

open scoped BigOperators
open BoundedRatioRelationalHosts

noncomputable section

/-! ## Scalar extension and the explicit finite real bound -/

/-- Real-valued form of the bounded-interval kernel-sum estimate. -/
theorem card_boundedRelationalHosts_cast_le_kernelSum
    {κ₀ N M L : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) :
    ((boundedRelationalHosts N M L).card : ℝ) ≤
      4 * (κ₀ + 1 : ℝ) * (L + 1 : ℝ) * (N : ℝ) *
        ∑ n ∈ Finset.Icc 1 (M + L),
          LargeKernelWeightedCounting.largeKernelWeight (L + 1) n := by
  have hq :=
    card_boundedRelationalHosts_cast_le_kernelSumQ
      hN hNM hMκ hL
  have hsumCast :
      ((∑ n ∈ Finset.Icc 1 (M + L),
          RelationalHosts.largeKernelWeightQ (L + 1) n : ℚ) : ℝ) =
        ∑ n ∈ Finset.Icc 1 (M + L),
          LargeKernelWeightedCounting.largeKernelWeight
            (L + 1) n := by
    simp only [Rat.cast_sum,
      RelationalHostBound.cast_largeKernelWeightQ]
  calc
    ((boundedRelationalHosts N M L).card : ℝ) =
        ((((boundedRelationalHosts N M L).card : ℚ) : ℝ)) := by
      simp
    _ ≤
        ((4 * (κ₀ + 1 : ℚ) * (L + 1 : ℚ) * (N : ℚ) *
          ∑ n ∈ Finset.Icc 1 (M + L),
            RelationalHosts.largeKernelWeightQ (L + 1) n : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).2 hq
    _ =
        4 * (κ₀ + 1 : ℝ) * (L + 1 : ℝ) * (N : ℝ) *
          ∑ n ∈ Finset.Icc 1 (M + L),
            LargeKernelWeightedCounting.largeKernelWeight
              (L + 1) n := by
      simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat,
        Rat.cast_natCast, hsumCast]
      norm_num

/-- Euler-product closure of the exact finite bound. -/
theorem card_boundedRelationalHosts_cast_le_exp_bound
    {κ₀ N M L : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) :
    ((boundedRelationalHosts N M L).card : ℝ) ≤
      4 * (κ₀ + 1 : ℝ) * (L + 1 : ℝ) * (N : ℝ) *
        Real.sqrt ((M + L : ℕ) : ℝ) *
        Real.exp (4 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
  have hfinite :=
    card_boundedRelationalHosts_cast_le_kernelSum
      hN hNM hMκ hL
  have hsum :=
    RelationalHostBound.sum_largeKernelWeight_le_sqrt_mul_exp
      (L + 1) (M + L) (by omega)
  have hsum' :
      (∑ n ∈ Finset.Icc 1 (M + L),
          LargeKernelWeightedCounting.largeKernelWeight (L + 1) n) ≤
        Real.sqrt ((M + L : ℕ) : ℝ) *
          Real.exp (4 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsum
  have hprefactor :
      0 ≤ 4 * (κ₀ + 1 : ℝ) * (L + 1 : ℝ) * (N : ℝ) := by
    positivity
  calc
    ((boundedRelationalHosts N M L).card : ℝ) ≤
        4 * (κ₀ + 1 : ℝ) * (L + 1 : ℝ) * (N : ℝ) *
          ∑ n ∈ Finset.Icc 1 (M + L),
            LargeKernelWeightedCounting.largeKernelWeight (L + 1) n :=
      hfinite
    _ ≤
        4 * (κ₀ + 1 : ℝ) * (L + 1 : ℝ) * (N : ℝ) *
          (Real.sqrt ((M + L : ℕ) : ℝ) *
            Real.exp (4 * Real.sqrt ((L + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum' hprefactor
    _ =
        4 * (κ₀ + 1 : ℝ) * (L + 1 : ℝ) * (N : ℝ) *
          Real.sqrt ((M + L : ℕ) : ℝ) *
          Real.exp (4 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
      ring

/-! ## A common endpoint-independent envelope -/

/-- The subpolynomial factor remaining after extracting `N sqrt N`. -/
noncomputable def boundedRelationalHostResidual
    (κ₀ _N L : ℕ) : ℝ :=
  (4 * (κ₀ + 1 : ℝ) * Real.sqrt (κ₀ + 1)) *
    ((L + 1 : ℝ) *
      Real.exp (4 * Real.sqrt ((L + 1 : ℕ) : ℝ)))

/-- Common envelope for every endpoint `M ≤ κ₀N`. -/
noncomputable def boundedRelationalHostEnvelope
    (κ₀ N L : ℕ) : ℝ :=
  (N : ℝ) * Real.sqrt N *
    boundedRelationalHostResidual κ₀ N L

/-- The explicit finite estimate is dominated by the common envelope. -/
theorem card_boundedRelationalHosts_cast_le_common
    {κ₀ N M L : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) :
    ((boundedRelationalHosts N M L).card : ℝ) ≤
      boundedRelationalHostEnvelope κ₀ N L := by
  have hfinite :=
    card_boundedRelationalHosts_cast_le_exp_bound
      hN hNM hMκ hL
  have hcutoff : M + L ≤ (κ₀ + 1) * N := by
    calc
      M + L ≤ κ₀ * N + N := Nat.add_le_add hMκ hL
      _ = (κ₀ + 1) * N := by ring
  have hsqrt :
      Real.sqrt ((M + L : ℕ) : ℝ) ≤
        Real.sqrt (((κ₀ + 1) * N : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hcutoff)
  have hprefactor :
      0 ≤
        4 * (κ₀ + 1 : ℝ) * (L + 1 : ℝ) * (N : ℝ) := by
    positivity
  have hexp :
      0 ≤ Real.exp (4 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
    positivity
  calc
    ((boundedRelationalHosts N M L).card : ℝ) ≤
        4 * (κ₀ + 1 : ℝ) * (L + 1 : ℝ) * (N : ℝ) *
          Real.sqrt ((M + L : ℕ) : ℝ) *
          Real.exp (4 * Real.sqrt ((L + 1 : ℕ) : ℝ)) :=
      hfinite
    _ ≤
        4 * (κ₀ + 1 : ℝ) * (L + 1 : ℝ) * (N : ℝ) *
          Real.sqrt (((κ₀ + 1) * N : ℕ) : ℝ) *
          Real.exp (4 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt hprefactor)
          hexp
    _ = boundedRelationalHostEnvelope κ₀ N L := by
      rw [show (((κ₀ + 1) * N : ℕ) : ℝ) =
          (κ₀ + 1 : ℝ) * (N : ℝ) by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ κ₀ + 1)]
      unfold boundedRelationalHostEnvelope
        boundedRelationalHostResidual
      ring

/-! ## Uniform subpolynomial and three-halves closure -/

private def HeightAdmissible (D : ℝ) (N L : ℕ) : Prop :=
  ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N

private theorem boundedRelationalHostResidual_uniformSubpolynomial_height
    (κ₀ : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    UniformSubpolynomialOn (HeightAdmissible D)
      (boundedRelationalHostResidual κ₀) := by
  have hlinear :
      UniformSubpolynomialOn (HeightAdmissible D)
        (fun _ L => (L + 1 : ℝ)) := by
    apply
      ExpSqrtLog.uniformSubpolynomialOn_linear_log_add_one
        (HeightAdmissible D) (fun _ L => L) D hD
    intro N L hNL
    have hLcast :
        (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ L
    exact hLcast.trans hNL
  have hexponential :
      UniformSubpolynomialOn (HeightAdmissible D)
        (fun _ L =>
          Real.exp
            (4 * Real.sqrt ((L + 1 : ℕ) : ℝ))) := by
    exact
      ExpSqrtLog.uniformSubpolynomialOn_exp_sqrt_of_le_log
        (HeightAdmissible D) (fun _ L => L + 1)
        4 D (by norm_num) hD
        (fun N L hNL ↦ hNL)
  have hproduct :
      UniformSubpolynomialOn (HeightAdmissible D)
        (fun N L =>
          (L + 1 : ℝ) *
            Real.exp
              (4 * Real.sqrt ((L + 1 : ℕ) : ℝ))) :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      hlinear hexponential
  unfold boundedRelationalHostResidual
  exact
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      (4 * (κ₀ + 1 : ℝ) * Real.sqrt (κ₀ + 1))
      hproduct

/-- The residual factor is uniformly subpolynomial in the literal
run-length window. -/
theorem boundedRelationalHostResidual_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedRelationalHostResidual κ₀) := by
  have hupperNonneg :
      0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  have hheight :=
    boundedRelationalHostResidual_uniformSubpolynomial_height
      κ₀ CriticalRunWindow.upperConstant hupperNonneg
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro k hk
  obtain ⟨Nheight, hNheight⟩ := hheight k hk
  refine ⟨max Nwindow Nheight, ?_⟩
  intro N hN L hrun
  have hNwindow : Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have hNheightN : Nheight ≤ N :=
    (le_max_right _ _).trans hN
  have hfirst := hwindow N hNwindow L hrun
  exact
    hNheight N hNheightN L
      (show HeightAdmissible CriticalRunWindow.upperConstant N L by
        exact hfirst.1.2.2.2)

/-- The common endpoint-independent envelope is
`N^(3/2+o_{C,κ₀}(1))`. -/
theorem boundedRelationalHostEnvelope_uniformThreeHalves
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformThreeHalvesSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedRelationalHostEnvelope κ₀) := by
  apply
    UniformThreeHalves.of_linear_sqrt_mul_subpolynomial
      (boundedRelationalHostResidual_uniformSubpolynomial hC κ₀)
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  have hresidual :
      0 ≤ boundedRelationalHostResidual κ₀ N L := by
    unfold boundedRelationalHostResidual
    positivity
  have henvelope :
      0 ≤ boundedRelationalHostEnvelope κ₀ N L := by
    unfold boundedRelationalHostEnvelope
    positivity
  rw [abs_of_nonneg henvelope, abs_of_nonneg hresidual]
  rfl

/--
Three-variable reciprocal-power formulation of
`N^(3/2+o_{C,κ₀}(1))`, uniform in every endpoint
`2N ≤ M ≤ κ₀N`.
-/
def UniformThreeHalvesInBoundedRatioWindow
    (C : ℝ) (κ₀ : ℕ)
    (f : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      |f N M L| ^ (2 * k) ≤ (N : ℝ) ^ (3 * k + 1)

/-- Uniform bounded-ratio form of Lemma 4.2. -/
theorem card_boundedRelationalHosts_uniformThreeHalves
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformThreeHalvesInBoundedRatioWindow C κ₀
      (fun N M L =>
        ((boundedRelationalHosts N M L).card : ℝ)) := by
  have henvelope :=
    boundedRelationalHostEnvelope_uniformThreeHalves hC κ₀
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
  refine
    ⟨max 2 (max Nwindow (max Nlength Nenv)), ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nwindow (max Nlength Nenv))).trans hN
  have hNtail :
      max Nwindow (max Nlength Nenv) ≤ N :=
    (le_max_right 2 (max Nwindow (max Nlength Nenv))).trans hN
  have hNwindow : Nwindow ≤ N :=
    (le_max_left Nwindow (max Nlength Nenv)).trans hNtail
  have hNtail' : max Nlength Nenv ≤ N :=
    (le_max_right Nwindow (max Nlength Nenv)).trans hNtail
  have hNlength : Nlength ≤ N :=
    (le_max_left Nlength Nenv).trans hNtail'
  have hNenvN : Nenv ≤ N :=
    (le_max_right Nlength Nenv).trans hNtail'
  have hfirst := hwindow N hNwindow L hrun
  have hLplusTwoReal :
      (((L + 1) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    simpa using
      hlength N hNlength (L + 1) hfirst.1.2.2.2
  have hL : L ≤ N := by
    have hLplusTwo : (L + 1) + 1 ≤ N := by
      exact_mod_cast hLplusTwoReal
    omega
  have hbase : N ≤ M := by omega
  have hfinite :=
    card_boundedRelationalHosts_cast_le_common
      hNtwo hbase hMκ hL
  have hcardNonneg :
      0 ≤ ((boundedRelationalHosts N M L).card : ℝ) := by
    positivity
  have henvelopeNonneg :
      0 ≤ boundedRelationalHostEnvelope κ₀ N L := by
    unfold boundedRelationalHostEnvelope
      boundedRelationalHostResidual
    positivity
  calc
    |((boundedRelationalHosts N M L).card : ℝ)| ^ (2 * k) ≤
        |boundedRelationalHostEnvelope κ₀ N L| ^ (2 * k) := by
      rw [abs_of_nonneg hcardNonneg,
        abs_of_nonneg henvelopeNonneg]
      exact
        pow_le_pow_left₀ hcardNonneg hfinite _
    _ ≤ (N : ℝ) ^ (3 * k + 1) :=
      hNenv N hNenvN L hrun

end

end BoundedRatioRelationalHostsCritical
end PaperC
