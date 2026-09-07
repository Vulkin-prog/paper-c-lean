import PaperCV282.CrossoverPrimeClockCylinder
import Mathlib.NumberTheory.Bertrand

/-! # Every fixed number of future prime signs fits inside the hard cutoff

Bertrand's theorem, already proved in mathlib, suffices. No additional
literature statement about prime gaps is assumed.
-/
namespace PaperC.V282.CrossoverPrimeClockCutoff

open Filter MeasureTheory InfiniteRademacher InfiniteCylinderTransfer
open MicroscopicBorderEvents BulkMicroscopicRecord CrossoverPrimeClockCylinder HardPoissonRates

theorem primeCounting_double {n : ℕ} (hn : 1 ≤ n) :
    Nat.primeCounting n+1 ≤ Nat.primeCounting (2*n) := by
  obtain ⟨p,hp,hnp,hp2⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hlo : Nat.primeCounting n ≤ Nat.primeCounting' p :=
    Nat.monotone_primeCounting' (show n+1 ≤ p by omega)
  have hhi : Nat.primeCounting' p < Nat.primeCounting (2*n) := by
    apply nth_prime_le_iff.mp
    simpa [Nat.primeCounting',Nat.nth_count hp] using hp2
  omega

theorem primeCounting_dyadic {L : ℕ} (hL : 1 ≤ L) (K : ℕ) :
    Nat.primeCounting L+K ≤ Nat.primeCounting (2^K*L) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hn : 1 ≤ 2^K*L := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hh := primeCounting_double hn
    have he : 2^(K+1)*L = 2*(2^K*L) := by rw [pow_succ]; ring
    rw [he]
    omega

/-- Even the elementary dyadic bound lies in the microscopic cylinder eventually. -/
theorem future_primes_le_microscopic {L K : ℕ} (hL : 2^K ≤ L) :
    Nat.primeCounting L+K ≤ Nat.primeCounting (2*L^2+L) := by
  have hpos : 1 ≤ 2^K := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact (primeCounting_dyadic (by omega) K).trans
    (Nat.monotone_primeCounting (by nlinarith : 2^K*L ≤ 2*L^2+L))

/-- The threshold is independent of the allowed length and of the recorded values. -/
theorem clock_cylinder_hard_eventually (beta : ℝ) (hbeta : 0 < beta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L K : ℕ, 2^K ≤ L →
      (L+1 : ℝ) ≤ beta*Real.log M →
      2*L^2+L ≤ hardCutoff M ∧ Nat.primeCounting L+K ≤ Nat.primeCounting (hardCutoff M) := by
  obtain ⟨Mzero,hzero⟩ := microscopic_cylinder_le_hardCutoff_eventually beta hbeta
  refine ⟨Mzero,?_⟩
  intro M hM L K hL hupper
  have hc := hzero M hM L hupper
  exact ⟨hc,(future_primes_le_microscopic hL).trans (Nat.monotone_primeCounting hc)⟩

theorem measurable_borderClockRecord_hard_eventually (beta : ℝ) (hbeta : 0 < beta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L K : ℕ, 2^K ≤ L →
      (L+1 : ℝ) ≤ beta*Real.log M →
      Measurable[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance]
        (borderClockRecord L K) := by
  obtain ⟨Mzero,hzero⟩ := clock_cylinder_hard_eventually beta hbeta
  refine ⟨Mzero,?_⟩
  intro M hM L K hL hupper
  obtain ⟨hc,hp⟩ := hzero M hM L K hL hupper
  exact measurable_borderClockRecord_fullFY hc hp

end PaperC.V282.CrossoverPrimeClockCutoff
