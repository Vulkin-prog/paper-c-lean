import PaperCV282.TerminalContainerLowerBounds

/-! # Matching exponents for the literal one-dimensional container (3.20) -/
namespace PaperC.V282.TerminalContainerSharpness

open Real Filter TerminalContainerLowerBounds TerminalSliceContainer TerminalKernelCount
open SizeTwoHostAsymptotics MacroscopicCanonicalCode PrimeEulerPNT
open scoped Topology

noncomputable section

theorem card_determinantCapValues_le_three_quarters_eventually
    (C epsilon : ℝ) (hC : 0≤C) (hepsilon : 0<epsilon) :
    ∃ Xzero : ℕ,∀ X≥Xzero,∀ L : ℕ,(L+1 : ℝ)≤C*log X →
      ((boundedLargeKernelValues (L+1) (Nat.sqrt (6*X*(L+1))) (3*X)).card : ℝ)≤
        (X : ℝ)^(3/4+epsilon) := by
  obtain ⟨Xfactor,hfactor⟩ := polynomial_euler_le_rpow_eventually C (4*sqrt (sqrt 6))
    epsilon hC hepsilon
  refine ⟨max Xfactor 2,?_⟩
  intro X hX L hL
  have hXp : (0 : ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hB : (1 : ℝ)≤L+1 := by have hh := Nat.cast_nonneg (α := ℝ) L;linarith
  have hf := hfactor X (by omega) L (by simpa using hL)
  rw [abs_of_nonneg (by positivity)] at hf
  have hp : (L+1 : ℝ)≤(L+1 : ℝ)^5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB (by omega : (1 : ℕ)≤5)
  have hexp : exp (2*sqrt (L+1 : ℝ))≤exp (4*sqrt (L+1 : ℝ)) := by
    apply exp_le_exp.mpr
    nlinarith [sqrt_nonneg (L+1 : ℝ)]
  have hsmall : 4*sqrt (sqrt 6)*(L+1 : ℝ)*exp (2*sqrt (L+1 : ℝ))≤(X : ℝ)^epsilon := by
    apply le_trans _ hf
    gcongr
  have hkernel := card_kernelValues_le_three_quarters_envelope
    (by omega : 0<X) (by omega : 1≤L+1) (sqrt_nonneg 6) (nat_sqrt_terminal_cap_le X (L+1))
  apply hkernel.trans
  calc
    _ ≤ (X : ℝ)^epsilon*(X : ℝ)^(3/4 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Nat.cast_add,Nat.cast_one] using hsmall
    _ = _ := by rw [← rpow_add hXp];congr 1;ring

/-- The printed container is X^(3/4+o(1)); this does not assert sharpness of terminal pair counts. -/
theorem terminal_container_three_quarters_sharp
    (hPNT : PrimeNumberTheoremRemainder) (C epsilon : ℝ) (hC : 0≤C) (hepsilon : 0<epsilon) :
    ∃ Xzero : ℕ,∀ X≥Xzero,∀ L : ℕ,(L+1 : ℝ)≤C*log X →
      (X : ℝ)^(3/4-epsilon)≤
        ((boundedLargeKernelValues (L+1) (Nat.sqrt (6*X*(L+1))) (3*X)).card : ℝ) ∧
      ((boundedLargeKernelValues (L+1) (Nat.sqrt (6*X*(L+1))) (3*X)).card : ℝ)≤
        (X : ℝ)^(3/4+epsilon) := by
  obtain ⟨Xlo,hlo⟩ := card_determinantCapValues_ge_three_quarters_eventually hPNT epsilon hepsilon
  obtain ⟨Xhi,hhi⟩ := card_determinantCapValues_le_three_quarters_eventually C epsilon hC hepsilon
  exact ⟨max Xlo Xhi,fun X hX L hL => ⟨hlo X (by omega) (L+1) (by omega),hhi X (by omega) L hL⟩⟩

/-- Every strictly smaller power eventually fails, even with an arbitrary fixed coefficient. -/
theorem smaller_power_lt_container_eventually (hPNT : PrimeNumberTheoremRemainder)
    (a C : ℝ) (ha : a<3/4) :
    ∃ Xzero : ℕ,∀ X≥Xzero,∀ B : ℕ,1≤B →
      C*(X : ℝ)^a<((boundedLargeKernelValues B (Nat.sqrt (6*X*B)) (3*X)).card : ℝ) := by
  let epsilon : ℝ := (3/4-a)/2
  have hepsilon : 0<epsilon := by dsimp [epsilon];linarith
  obtain ⟨Xlo,hlo⟩ := card_determinantCapValues_ge_three_quarters_eventually hPNT epsilon hepsilon
  have hp := (tendsto_rpow_atTop hepsilon).comp tendsto_natCast_atTop_atTop
  obtain ⟨Xp,hp⟩ := eventually_atTop.1 (hp.eventually (eventually_gt_atTop C))
  refine ⟨max Xlo (max Xp 1),?_⟩
  intro X hX B hB
  have hXp : (0 : ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hpow : (X : ℝ)^(3/4-epsilon)=(X : ℝ)^a*(X : ℝ)^epsilon := by
    rw [← rpow_add hXp]
    congr 1
    dsimp [epsilon]
    ring
  apply lt_of_lt_of_le _ (hlo X (by omega) B hB)
  rw [hpow,mul_comm C]
  exact mul_lt_mul_of_pos_left (hp X (by omega)) (rpow_pos_of_pos hXp a)

end
end PaperC.V282.TerminalContainerSharpness
