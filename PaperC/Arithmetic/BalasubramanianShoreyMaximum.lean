import PaperC.Arithmetic.BalasubramanianShoreyInput
import PaperC.Arithmetic.DefectivePredicate
import Mathlib.Analysis.Asymptotics.Lemmas

set_option maxHeartbeats 1200000

/-!
# The pointwise defect maximum of Lemma 15.4

This file performs the part not supplied by the external theorem:

* every `B`-defective vertex is written canonically as `s a²`;
* the product of any finite family of such vertices is `b y²`;
* every prime factor of `b` is at most `B`;
* Theorem 1 of Balasubramanian--Shorey then bounds a family whose
  cardinality reaches `μ_B(θ₀)`.
-/

namespace PaperC
namespace BalasubramanianShoreyMaximum

open scoped BigOperators
open Filter
open DefectCounting
open DefectivePredicate
open BalasubramanianShoreyInput

noncomputable section

/-- The canonical squarefree kernel retained in the defective decomposition. -/
def canonicalOddPart (n : ℕ) : ℕ :=
  (oddPrimeSupport n).prod id

/-- Product of the canonical odd parts over a set of offsets. -/
def blockOddPart (m : ℕ) (offsets : Finset ℕ) : ℕ :=
  ∏ d ∈ offsets, canonicalOddPart (m + d)

/-- Product of the canonical square parts over a set of offsets. -/
def blockSquarePart (m : ℕ) (offsets : Finset ℕ) : ℕ :=
  ∏ d ∈ offsets, canonicalSquarePart (m + d)

/-- Offsets of the `B`-defective vertices in `{m+1, ..., m+B}`. -/
def defectiveOffsets (B m : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 B).filter fun d ↦ HDefective B (m + d)

@[simp]
theorem mem_defectiveOffsets {B m d : ℕ} :
    d ∈ defectiveOffsets B m ↔
      1 ≤ d ∧ d ≤ B ∧ HDefective B (m + d) := by
  simp [defectiveOffsets, and_assoc]

private theorem canonicalOddPart_ne_zero
    {n : ℕ} (hn : n ≠ 0) :
    canonicalOddPart n ≠ 0 := by
  intro hzero
  have hdecomp :=
    canonical_odd_mul_sq_decomposition hn
  rw [show (oddPrimeSupport n).prod id =
    canonicalOddPart n by rfl, hzero] at hdecomp
  simp at hdecomp
  exact hn hdecomp

private theorem canonicalSquarePart_ne_zero
    {n : ℕ} (hn : n ≠ 0) :
    canonicalSquarePart n ≠ 0 := by
  intro hzero
  have hdecomp :=
    canonical_odd_mul_sq_decomposition hn
  rw [hzero] at hdecomp
  simp at hdecomp
  exact hn hdecomp

/--
Multiplying the canonical decompositions gives one square times a kernel
whose prime support is small.
-/
theorem defectiveProduct_decomposition
    {m : ℕ} {offsets : Finset ℕ}
    (hpositive : ∀ d ∈ offsets, 0 < m + d) :
    (∏ d ∈ offsets, (m + d)) =
      blockOddPart m offsets *
        blockSquarePart m offsets ^ 2 := by
  classical
  calc
    (∏ d ∈ offsets, (m + d)) =
        ∏ d ∈ offsets,
          (canonicalOddPart (m + d) *
            canonicalSquarePart (m + d) ^ 2) := by
      apply Finset.prod_congr rfl
      intro d hd
      exact canonical_odd_mul_sq_decomposition
        (Nat.ne_of_gt (hpositive d hd))
    _ =
        (∏ d ∈ offsets, canonicalOddPart (m + d)) *
          (∏ d ∈ offsets,
            canonicalSquarePart (m + d) ^ 2) := by
      rw [Finset.prod_mul_distrib]
    _ =
        blockOddPart m offsets *
          blockSquarePart m offsets ^ 2 := by
      simp only [blockOddPart, blockSquarePart,
        Finset.prod_pow]

/-- The product of canonical odd parts has no prime factor above `B`. -/
theorem blockOddPart_isSmoothAt
    {B m : ℕ} {offsets : Finset ℕ}
    (hdefective :
      ∀ d ∈ offsets, HDefective B (m + d)) :
    IsSmoothAt B (blockOddPart m offsets) := by
  classical
  intro p hp
  have hpPrime : p.Prime :=
    Nat.prime_of_mem_primeFactors hp
  have hpDiv :
      p ∣ blockOddPart m offsets :=
    Nat.dvd_of_mem_primeFactors hp
  rw [blockOddPart] at hpDiv
  obtain ⟨d, hd, hpKernel⟩ :=
    (hpPrime.prime.dvd_finsetProd_iff
      (fun d : ℕ ↦ canonicalOddPart (m + d))).mp hpDiv
  rw [canonicalOddPart] at hpKernel
  obtain ⟨q, hq, hpq⟩ :=
    (hpPrime.prime.dvd_finsetProd_iff id).mp hpKernel
  have hqSmall :=
    oddPrimeSupport_subset_smallPrimesUpTo
      (hdefective d hd) hq
  have hqData := mem_smallPrimesUpTo.mp hqSmall
  have hpqEq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hpPrime hqData.1).mp hpq
  simpa [hpqEq] using hqData.2

private theorem blockOddPart_pos
    {m : ℕ} {offsets : Finset ℕ}
    (hpositive : ∀ d ∈ offsets, 0 < m + d) :
    0 < blockOddPart m offsets := by
  classical
  apply Nat.pos_of_ne_zero
  rw [blockOddPart, Finset.prod_ne_zero_iff]
  intro d hd
  exact canonicalOddPart_ne_zero
    (Nat.ne_of_gt (hpositive d hd))

private theorem blockSquarePart_pos
    {m : ℕ} {offsets : Finset ℕ}
    (hpositive : ∀ d ∈ offsets, 0 < m + d) :
    0 < blockSquarePart m offsets := by
  classical
  apply Nat.pos_of_ne_zero
  rw [blockSquarePart, Finset.prod_ne_zero_iff]
  intro d hd
  exact canonicalSquarePart_ne_zero
    (Nat.ne_of_gt (hpositive d hd))

/--
The defective offsets themselves satisfy equation (1) of
Balasubramanian--Shorey as soon as at least two are present.
-/
theorem defectiveOffsets_denseSquareSubproduct
    {B m : ℕ}
    (htwo : 2 ≤ (defectiveOffsets B m).card) :
    DenseSquareSubproduct B m (defectiveOffsets B m)
      (blockOddPart m (defectiveOffsets B m))
      (blockSquarePart m (defectiveOffsets B m)) := by
  classical
  have hsubset :
      defectiveOffsets B m ⊆ Finset.Icc 1 B := by
    intro d hd
    exact Finset.mem_Icc.mpr
      ⟨(mem_defectiveOffsets.mp hd).1,
        (mem_defectiveOffsets.mp hd).2.1⟩
  have hcard :
      (defectiveOffsets B m).card ≤ B := by
    calc
      (defectiveOffsets B m).card ≤
          (Finset.Icc 1 B).card :=
        Finset.card_le_card hsubset
      _ ≤ B := by
        rw [Nat.card_Icc]
        omega
  have hpositive :
      ∀ d ∈ defectiveOffsets B m, 0 < m + d := by
    intro d hd
    have := (mem_defectiveOffsets.mp hd).1
    omega
  refine ⟨htwo, hcard, hsubset,
    blockOddPart_pos hpositive,
    blockSquarePart_pos hpositive, ?_, ?_⟩
  · exact defectiveProduct_decomposition hpositive
  · apply blockOddPart_isSmoothAt
    intro d hd
    exact (mem_defectiveOffsets.mp hd).2.2

/-! ## The analytic size of `μ_B(θ)` -/

/-- For fixed `θ`, the parenthesized factor in `μ_B(θ)` tends to one. -/
theorem muRatio_tendsto_one (θ : ℝ) :
    Tendsto
      (fun B : ℕ ↦
        1 -
          Real.log (Real.log (B : ℝ)) /
            Real.log (B : ℝ) +
          Real.log (Real.log (Real.log (B : ℝ))) /
            Real.log (B : ℝ) +
          θ / Real.log (B : ℝ))
      atTop (nhds 1) := by
  have hlogNat :
      Tendsto (fun B : ℕ ↦ Real.log (B : ℝ))
        atTop atTop :=
    Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop
  have hlogLog :
      Tendsto
        (fun B : ℕ ↦
          Real.log (Real.log (B : ℝ)) /
            Real.log (B : ℝ))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        hlogNat
  have hlogLogLittleO :
      (fun x : ℝ ↦ Real.log (Real.log x)) =o[atTop]
        (fun x : ℝ ↦ x) := by
    have hfirst :=
      Real.isLittleO_log_id_atTop.comp_tendsto
        Real.tendsto_log_atTop
    exact hfirst.trans Real.isLittleO_log_id_atTop
  have hlogLogLog :
      Tendsto
        (fun B : ℕ ↦
          Real.log (Real.log (Real.log (B : ℝ))) /
            Real.log (B : ℝ))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      hlogLogLittleO.tendsto_div_nhds_zero.comp hlogNat
  have htheta :
      Tendsto
        (fun B : ℕ ↦ θ / Real.log (B : ℝ))
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlogNat
  convert
    ((tendsto_const_nhds.sub hlogLog).add hlogLogLog).add
      htheta using 1
  norm_num

/-- In particular `μ_B(θ) ≥ 2` for all sufficiently large `B`. -/
theorem eventually_two_le_mu (θ : ℝ) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, 2 ≤ mu B θ := by
  have hhalf :
      ∀ᶠ B : ℕ in atTop,
        (1 / 2 : ℝ) <
          1 -
            Real.log (Real.log (B : ℝ)) /
              Real.log (B : ℝ) +
            Real.log (Real.log (Real.log (B : ℝ))) /
              Real.log (B : ℝ) +
            θ / Real.log (B : ℝ) :=
    (muRatio_tendsto_one θ).eventually
      (Ioi_mem_nhds (by norm_num))
  have hlarge :
      ∀ᶠ B : ℕ in atTop, 4 ≤ B :=
    eventually_ge_atTop 4
  have heventually :
      ∀ᶠ B : ℕ in atTop, 2 ≤ mu B θ := by
    filter_upwards [hhalf, hlarge] with B hratio hB
    unfold mu
    have hcast : (4 : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hB
    nlinarith
  exact eventually_atTop.mp heventually

/-! ## Lemma 15.4 -/

private theorem defectiveOffsets_card_lt_mu_of_bridge
    {θ₀ : ℝ} {C₂ B m : ℕ}
    (hbridge :
      ∀ (k m : ℕ) (offsets : Finset ℕ) (b y : ℕ),
        27 ≤ k →
        k ^ 2 < m →
        mu k θ₀ ≤ (offsets.card : ℝ) →
        DenseSquareSubproduct k m offsets b y →
        k ≤ C₂)
    (hB : 27 ≤ B)
    (hBC : C₂ < B)
    (hm : B ^ 2 < m)
    (hmu : 2 ≤ mu B θ₀) :
    ((defectiveOffsets B m).card : ℝ) < mu B θ₀ := by
  by_contra hnot
  have hthreshold :
      mu B θ₀ ≤ ((defectiveOffsets B m).card : ℝ) :=
    le_of_not_gt hnot
  have htwoReal :
      (2 : ℝ) ≤ ((defectiveOffsets B m).card : ℝ) :=
    hmu.trans hthreshold
  have htwo :
      2 ≤ (defectiveOffsets B m).card := by
    exact_mod_cast htwoReal
  have hbound :=
    hbridge B m (defectiveOffsets B m)
      (blockOddPart m (defectiveOffsets B m))
      (blockSquarePart m (defectiveOffsets B m))
      hB hm hthreshold
      (defectiveOffsets_denseSquareSubproduct htwo)
  omega

/--
Lemma 15.4 in the manuscript's block coordinates: for all sufficiently
large `B`, every block `{m+1, ..., m+B}` with `m>B²` has fewer than
`μ_B(θ₀)` defective vertices.
-/
theorem defectiveOffsets_card_lt_mu_eventually
    (hBS : BalasubramanianShoreyStatement) :
    ∃ θ₀ : ℝ, ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ m,
      B ^ 2 < m →
      ((defectiveOffsets B m).card : ℝ) < mu B θ₀ := by
  obtain ⟨θ₀, C₂, hbridge⟩ := hBS
  obtain ⟨Bμ, hBμ⟩ := eventually_two_le_mu θ₀
  refine ⟨θ₀, max 27 (max (C₂ + 1) Bμ), ?_⟩
  intro B hB m hm
  have h27 : 27 ≤ B :=
    (le_max_left 27 (max (C₂ + 1) Bμ)).trans hB
  have htail :
      max (C₂ + 1) Bμ ≤ B :=
    (le_max_right 27 (max (C₂ + 1) Bμ)).trans hB
  have hCB : C₂ < B := by
    have := (le_max_left (C₂ + 1) Bμ).trans htail
    omega
  have hmu :
      2 ≤ mu B θ₀ :=
    hBμ B ((le_max_right (C₂ + 1) Bμ).trans htail)
  exact defectiveOffsets_card_lt_mu_of_bridge
    hbridge h27 hCB hm hmu

/-- The same statement in the manuscript coordinates `m = x - 2`. -/
theorem defectiveWindow_card_lt_mu_eventually
    (hBS : BalasubramanianShoreyStatement) :
    ∃ θ₀ : ℝ, ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ x,
      B ^ 2 + 2 < x →
      ((defectiveOffsets B (x - 2)).card : ℝ) <
        mu B θ₀ := by
  obtain ⟨θ₀, B₀, hmaximum⟩ :=
    defectiveOffsets_card_lt_mu_eventually hBS
  refine ⟨θ₀, B₀, ?_⟩
  intro B hB x hx
  exact hmaximum B hB (x - 2) (by omega)

/--
Literal `mₓ ≤ B - g_B` form of Lemma 15.4, with
`g_B = B - μ_B(θ₀)`.  The preceding strict inequality is slightly stronger.
-/
theorem defectiveWindow_card_le_complement_gap_eventually
    (hBS : BalasubramanianShoreyStatement) :
    ∃ θ₀ : ℝ, ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ x,
      B ^ 2 + 2 < x →
      ((defectiveOffsets B (x - 2)).card : ℝ) ≤
        (B : ℝ) - gap B θ₀ := by
  obtain ⟨θ₀, B₀, hmaximum⟩ :=
    defectiveWindow_card_lt_mu_eventually hBS
  refine ⟨θ₀, B₀, ?_⟩
  intro B hB x hx
  have hstrict := hmaximum B hB x hx
  unfold gap
  linarith

end

end BalasubramanianShoreyMaximum
end PaperC
