import PaperCV282.TerminalContainerLowerFinite
import PaperCV282.MediumPrimeScaling

/-! # The three-quarter exponent is attained by the actual value container -/
namespace PaperC.V282.TerminalContainerLowerBounds

open Filter Real TerminalContainerLowerFinite TerminalKernelCount PrimesUpTo
open PrimeEulerPNT PostQuadraticPrimeBounds
open scoped Topology

noncomputable section

theorem real_sqrt_le_two_nat_sqrt (n : ℕ) (hn : 4≤n) :
    sqrt (n : ℝ)≤2*(Nat.sqrt n : ℝ) := by
  have hlo : 1≤Nat.sqrt n := Nat.le_sqrt'.mpr (by omega)
  have hhi : (n : ℝ)<((Nat.sqrt n : ℝ)+1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' n
  have hnr : (1 : ℝ)≤Nat.sqrt n := by exact_mod_cast hlo
  have hs := sq_sqrt (Nat.cast_nonneg n)
  nlinarith [sqrt_nonneg (n : ℝ)]

theorem prime_square_family_lower_eventually (hPNT : PrimeNumberTheoremRemainder) :
    ∃ Xzero : ℕ,∀ X≥Xzero,
      (X : ℝ)^(3/4 : ℝ)/(16*log X)≤
        (count (Nat.sqrt X) : ℝ)*Nat.sqrt (Nat.sqrt X) := by
  obtain ⟨Pzero,hP⟩ := eventually_atTop.1 ((primeCounting_normalized_tendsto_one hPNT).eventually
    (eventually_ge_nhds (by norm_num : (1/2 : ℝ)<1)))
  refine ⟨max (Pzero^2) 16,?_⟩
  intro X hX
  have hX16 : 16≤X := by omega
  have hR4 : 4≤Nat.sqrt X := Nat.le_sqrt'.mpr (by omega)
  have hRP : Pzero≤Nat.sqrt X := Nat.le_sqrt'.mpr (by omega)
  have hp := hP (Nat.sqrt X) hRP
  rw [← prime_count_eq_nat] at hp
  have hrp : (0 : ℝ)<Nat.sqrt X := by exact_mod_cast (show 0<Nat.sqrt X by omega)
  have hl : 0<log (X : ℝ) := log_pos (by exact_mod_cast (show 1<X by omega))
  have hc : (sqrt (X : ℝ))/4≤(count (Nat.sqrt X) : ℝ)*log X := by
    have hnorm := (le_div_iff₀ hrp).mp hp
    have hs := real_sqrt_le_two_nat_sqrt X (by omega)
    have hlog : log (Nat.sqrt X : ℝ)≤log (X : ℝ) :=
      log_le_log hrp (by exact_mod_cast Nat.sqrt_le_self X)
    have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (count (Nat.sqrt X)))
    nlinarith
  have ha : sqrt (sqrt (X : ℝ))/4≤(Nat.sqrt (Nat.sqrt X) : ℝ) := by
    have h1 := real_sqrt_le_two_nat_sqrt X (by omega)
    have h2 := real_sqrt_le_two_nat_sqrt (Nat.sqrt X) hR4
    have h3 : sqrt (sqrt (X : ℝ))/2≤sqrt (Nat.sqrt X : ℝ) := by
      apply (le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr
      nlinarith [sq_sqrt (sqrt_nonneg (X : ℝ))]
    linarith
  have hprod := mul_le_mul hc ha (by positivity) (by positivity)
  have hpow : sqrt (X : ℝ)*sqrt (sqrt (X : ℝ))=(X : ℝ)^(3/4 : ℝ) := by
    rw [sqrt_eq_rpow,sqrt_eq_rpow,← rpow_mul (Nat.cast_nonneg X),← rpow_add (by positivity : (0 : ℝ)<X)]
    norm_num
  apply (div_le_iff₀ (by positivity : 0<16*log (X : ℝ))).mpr
  rw [← hpow]
  nlinarith only [hprod]

/-- The lower bound uses the true finite set, uniformly before its width and kernel cap. -/
theorem card_kernelValues_ge_three_quarters_eventually
    (hPNT : PrimeNumberTheoremRemainder) (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ Xzero : ℕ,∀ X≥Xzero,∀ B T : ℕ,Nat.sqrt X≤T →
      (X : ℝ)^(3/4-epsilon)≤((boundedLargeKernelValues B T (3*X)).card : ℝ) := by
  obtain ⟨Xfamily,hfamily⟩ := prime_square_family_lower_eventually hPNT
  have hlog := ((isLittleO_log_rpow_atTop hepsilon).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨Xlog,hlog⟩ := eventually_atTop.1 (hlog.eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ)<1/16)))
  refine ⟨max Xfamily (max Xlog 2),?_⟩
  intro X hX B T hT
  have hXp : (0 : ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hlp : 0<log (X : ℝ) := log_pos (by exact_mod_cast (show 1<X by omega))
  have hh := hlog X (by omega)
  have hpower : 16*log (X : ℝ)≤(X : ℝ)^epsilon := by
    have h := (div_le_iff₀ (rpow_pos_of_pos hXp epsilon)).mp hh
    linarith
  have hsmall : (X : ℝ)^(3/4-epsilon)≤(X : ℝ)^(3/4 : ℝ)/(16*log X) := by
    rw [rpow_sub hXp]
    exact div_le_div_of_nonneg_left (rpow_nonneg hXp.le _) (by positivity) hpower
  have hfinite := prime_square_family_card_le B T (3*X) (Nat.sqrt X) (Nat.sqrt (Nat.sqrt X)) hT
    (show Nat.sqrt X*Nat.sqrt (Nat.sqrt X)^2≤3*X from
      (Nat.mul_le_mul_left _ (Nat.sqrt_le' _)).trans (by
        have hh := Nat.sqrt_le X
        nlinarith))
  exact hsmall.trans ((hfamily X (by omega)).trans (by exact_mod_cast hfinite))

/-- In particular the literal determinant cap of the terminal proof attains that exponent. -/
theorem card_determinantCapValues_ge_three_quarters_eventually
    (hPNT : PrimeNumberTheoremRemainder) (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ Xzero : ℕ,∀ X≥Xzero,∀ B : ℕ,1≤B →
      (X : ℝ)^(3/4-epsilon)≤((boundedLargeKernelValues B (Nat.sqrt (6*X*B)) (3*X)).card : ℝ) := by
  obtain ⟨Xzero,hX⟩ := card_kernelValues_ge_three_quarters_eventually hPNT epsilon hepsilon
  exact ⟨Xzero,fun X hx B hB => hX X hx B _ (Nat.sqrt_le_sqrt (by nlinarith))⟩

end
end PaperC.V282.TerminalContainerLowerBounds
