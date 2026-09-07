import PaperC.Diophantine.TerminalPartnerPell
import PaperC.Affine.RationalChannelCode
import PaperCV282.PolynomialPellCount
import PaperCV282.MacroscopicSmoothKernels
import PaperCV282.MacroscopicCanonicalCode

/-!
# Terminal partners on a larger-start slice

The varying partner is any start between 2 and 2X. Two prescribed coprime
nontrivial large kernels give a genuine Pell equation. The canonical small
parts are summed only after each fixed fibre is counted. No comparison
between the partner and X is required.
-/

namespace PaperC.V282.TerminalPartnerCount

open Affine RationalChannelCode LargeOddKernel DefectivePredicate TerminalPartnerPell
open SquarefreeSmoothCount PolynomialPellCount MacroscopicSmoothKernels LogarithmicWordPowers
open scoped BigOperators

noncomputable section

/-- A partner with two offsets, kernels and canonical small parts fixed. -/
def fixedKernelPartnerFiber (X L R S a b : ℕ) (j v : Fin (L + 1)) : Finset ℕ :=
  (Finset.Icc 2 (2 * X)).filter fun y =>
    largeOddKernel (L + 1) (startCompleteVertexLabel y L j) = R ∧
    largeOddKernel (L + 1) (startCompleteVertexLabel y L v) = S ∧
    smallOddPart (L + 1) (startCompleteVertexLabel y L j) = a ∧
    smallOddPart (L + 1) (startCompleteVertexLabel y L v) = b

theorem mem_fixedKernelPartnerFiber {X L R S a b y : ℕ} {j v : Fin (L + 1)} :
    y ∈ fixedKernelPartnerFiber X L R S a b j v ↔
      (2 ≤ y ∧ y ≤ 2 * X) ∧
      largeOddKernel (L + 1) (startCompleteVertexLabel y L j) = R ∧
      largeOddKernel (L + 1) (startCompleteVertexLabel y L v) = S ∧
      smallOddPart (L + 1) (startCompleteVertexLabel y L j) = a ∧
      smallOddPart (L + 1) (startCompleteVertexLabel y L v) = b := by
  simp [fixedKernelPartnerFiber]

/-- Every actual label of a positive partner lies in the common enlarged cutoff. -/
theorem partner_label_pos_le {X L y : ℕ} (hy : 2 ≤ y) (hyX : y ≤ 2 * X)
    (hL : L ≤ X) (j : Fin (L + 1)) :
    0 < startCompleteVertexLabel y L j ∧ startCompleteVertexLabel y L j ≤ 3 * X := by
  refine ⟨startCompleteVertexLabel_pos hy j, ?_⟩
  unfold startCompleteVertexLabel
  split <;> omega

/-- The actual canonical small part is in the finite smooth coefficient container. -/
theorem smallOddPart_mem_cutoff {B n Z : ℕ} (hn : 0 < n) (hnZ : n ≤ Z) :
    smallOddPart B n ∈ squarefreeSmoothUpTo B Z := by
  rw [mem_squarefreeSmoothUpTo]
  refine ⟨Nat.one_le_iff_ne_zero.mpr (smallOddPart_ne_zero B n),
    (Nat.le_of_dvd hn (smallOddPart_dvd B n)).trans hnZ,
    smallOddPart_squarefree B n, ?_⟩
  intro p hp
  rw [primeFactors_smallOddPart] at hp
  exact (prime_and_small_of_mem_smallOddPrimeSupport hp).2

/-- The right offsets give a nonzero Pell difference, with no loss at offset minus one. -/
theorem partner_offset_difference {L : ℕ} {j v : Fin (L + 1)} (hjv : j ≠ v) :
    channelVertexOffset j - channelVertexOffset v ≠ 0 ∧
      (channelVertexOffset j - channelVertexOffset v).natAbs ≤ L := by
  have hne : j.val ≠ v.val := fun h => hjv (Fin.ext h)
  unfold channelVertexOffset
  constructor
  · omega
  · have hh : |((j.val : ℤ) - 1) - ((v.val : ℤ) - 1)| ≤ (L : ℤ) :=
      abs_le.mpr ⟨by omega, by omega⟩
    rw [Int.abs_eq_natAbs] at hh
    exact_mod_cast hh

/-- Every fixed canonical-coefficient fibre has the internal polynomial Pell count.
Nonempty fibres themselves supply the coefficient-height and nonsquare certificates. -/
theorem card_fixedKernelPartnerFiber_le_rpow_eventually
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ, L ≤ X → ∀ R S a b : ℕ,
      1 < R → 1 < S → R.Coprime S → ∀ j v : Fin (L + 1), j ≠ v →
      ((fixedKernelPartnerFiber X L R S a b j v).card : ℝ) ≤ (X : ℝ) ^ epsilon := by
  classical
  obtain ⟨Xpell, hpell⟩ := pellBox_atMost_rpow_eventually 2 epsilon hepsilon
  refine ⟨max Xpell 3, ?_⟩
  intro X hX L hL R S a b hR hS hRS j v hjv
  have hXthree : 3 ≤ X := (le_max_right _ _).trans hX
  have hcut : 3 * X ≤ X ^ 2 := by nlinarith
  by_cases hempty : fixedKernelPartnerFiber X L R S a b j v = ∅
  · rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨y0, hy0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨hy0range, hr0, hs0, ha0, hb0⟩ := mem_fixedKernelPartnerFiber.mp hy0
  have hm0 := partner_label_pos_le hy0range.1 hy0range.2 hL j
  have hn0 := partner_label_pos_le hy0range.1 hy0range.2 hL v
  have hA : 0 < R * a := by
    rw [← hr0, ← ha0]
    exact Nat.mul_pos (Nat.pos_of_ne_zero (largeOddKernel_ne_zero _ _))
      (Nat.pos_of_ne_zero (smallOddPart_ne_zero _ _))
  have hC : 0 < S * b := by
    rw [← hs0, ← hb0]
    exact Nat.mul_pos (Nat.pos_of_ne_zero (largeOddKernel_ne_zero _ _))
      (Nat.pos_of_ne_zero (smallOddPart_ne_zero _ _))
  have hAheight : R * a ≤ X ^ 2 := by
    rw [← hr0, ← ha0]
    exact (canonical_terminal_coefficient_le hm0.1.ne').trans (hm0.2.trans hcut)
  have hCheight : S * b ≤ X ^ 2 := by
    rw [← hs0, ← hb0]
    exact (canonical_terminal_coefficient_le hn0.1.ne').trans (hn0.2.trans hcut)
  have hratio : ¬ IsSquare (((R * a : ℕ) : ℚ) / ((S * b : ℕ) : ℚ)) := by
    have hh := canonical_terminal_coefficient_ratio_not_isSquare
      (B := L + 1) (m := startCompleteVertexLabel y0 L j) (n := startCompleteVertexLabel y0 L v)
      (by simpa only [hr0] using hR) (by simpa only [hs0] using hS)
      (by simpa only [hr0, hs0] using hRS)
    simpa only [hr0, hs0, ha0, hb0] using hh
  have hd := partner_offset_difference hjv
  have hbox := terminalPartnerWitnessBox_atMost
    (hpell X ((le_max_left _ _).trans hX) (R * a) (S * b) (3 * X)
      (channelVertexOffset j - channelVertexOffset v) hA hC hratio hd.1
      hAheight hCheight hcut (hd.2.trans (hL.trans (by nlinarith))))
  let f : ℕ → TerminalPartnerWitness := fun y =>
    canonicalPartnerWitness (startCompleteVertexLabel y L j) (startCompleteVertexLabel y L v) y
  have hf : ∀ y ∈ fixedKernelPartnerFiber X L R S a b j v,
      terminalPartnerWitnessBox R S a b (channelVertexOffset j) (channelVertexOffset v) (3 * X) (f y) := by
    intro y hy
    obtain ⟨hyrange, hr, hs, ha, hb⟩ := mem_fixedKernelPartnerFiber.mp hy
    have hm := partner_label_pos_le hyrange.1 hyrange.2 hL j
    have hn := partner_label_pos_le hyrange.1 hyrange.2 hL v
    have hz := (canonicalSquarePart_le_sqrt (B := L + 1) hm.1.ne').trans
      ((Nat.sqrt_le_self _).trans hm.2)
    have hw := (canonicalSquarePart_le_sqrt (B := L + 1) hn.1.ne').trans
      ((Nat.sqrt_le_self _).trans hn.2)
    simpa only [f, ha, hb] using canonical_decompositions_give_partner_box hm.1.ne' hn.1.ne'
      (startCompleteVertexLabel_cast (by omega : 1 ≤ y) j).symm
      (startCompleteVertexLabel_cast (by omega : 1 ≤ y) v).symm hr hs hz hw
  have hcount := hbox ((fixedKernelPartnerFiber X L R S a b j v).image f) (by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    exact hf y hy)
  have hinj : Function.Injective f := by
    intro y z hyz
    have hh := congrArg TerminalPartnerWitness.partner hyz
    change (y : ℤ) = (z : ℤ) at hh
    exact_mod_cast hh
  simpa only [Finset.card_image_of_injective _ hinj] using hcount

/-- All positive partners displaying two prescribed kernels at distinct offsets. -/
def kernelPartnerStarts (X L R S : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (2 * X)).filter fun y => ∃ j v : Fin (L + 1), j ≠ v ∧
    largeOddKernel (L + 1) (startCompleteVertexLabel y L j) = R ∧
    largeOddKernel (L + 1) (startCompleteVertexLabel y L v) = S

theorem mem_kernelPartnerStarts {X L R S y : ℕ} :
    y ∈ kernelPartnerStarts X L R S ↔ (2 ≤ y ∧ y ≤ 2 * X) ∧
      ∃ j v : Fin (L + 1), j ≠ v ∧
        largeOddKernel (L + 1) (startCompleteVertexLabel y L j) = R ∧
        largeOddKernel (L + 1) (startCompleteVertexLabel y L v) = S := by
  simp [kernelPartnerStarts]

/-- Summing genuine small parts and distinct offsets gives the exact finite loss. -/
theorem card_kernelPartnerStarts_le_of_fixed_fibres
    {X L R S : ℕ} {bound : ℝ} (hL : L ≤ X) (hbound : 0 ≤ bound)
    (hf : ∀ j v : Fin (L + 1), j ≠ v →
      ∀ a ∈ squarefreeSmoothUpTo (L + 1) (3 * X),
      ∀ b ∈ squarefreeSmoothUpTo (L + 1) (3 * X),
      ((fixedKernelPartnerFiber X L R S a b j v).card : ℝ) ≤ bound) :
    ((kernelPartnerStarts X L R S).card : ℝ) ≤
      (L + 1 : ℝ) ^ 2 * ((squarefreeSmoothUpTo (L + 1) (3 * X)).card : ℝ) ^ 2 * bound := by
  classical
  let D := squarefreeSmoothUpTo (L + 1) (3 * X)
  let O : Finset (Fin (L + 1) × Fin (L + 1)) := Finset.univ.filter fun jv => jv.1 ≠ jv.2
  have hcover : kernelPartnerStarts X L R S ⊆ O.biUnion fun jv => D.biUnion fun a =>
      D.biUnion fun b => fixedKernelPartnerFiber X L R S a b jv.1 jv.2 := by
    intro y hy
    obtain ⟨hyrange, j, v, hjv, hr, hs⟩ := mem_kernelPartnerStarts.mp hy
    have hm := partner_label_pos_le hyrange.1 hyrange.2 hL j
    have hn := partner_label_pos_le hyrange.1 hyrange.2 hL v
    apply Finset.mem_biUnion.mpr
    refine ⟨(j, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjv⟩, Finset.mem_biUnion.mpr ?_⟩
    refine ⟨smallOddPart (L + 1) (startCompleteVertexLabel y L j),
      smallOddPart_mem_cutoff hm.1 hm.2, Finset.mem_biUnion.mpr ?_⟩
    exact ⟨smallOddPart (L + 1) (startCompleteVertexLabel y L v),
      smallOddPart_mem_cutoff hn.1 hn.2,
      mem_fixedKernelPartnerFiber.mpr ⟨hyrange, hr, hs, rfl, rfl⟩⟩
  have hcard : (kernelPartnerStarts X L R S).card ≤
      ∑ jv ∈ O, ∑ a ∈ D, ∑ b ∈ D, (fixedKernelPartnerFiber X L R S a b jv.1 jv.2).card := by
    refine (Finset.card_le_card hcover).trans ?_
    exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun jv _ =>
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a _ => Finset.card_biUnion_le))
  have hO : (O.card : ℝ) ≤ (L + 1 : ℝ) ^ 2 := by
    have hn := Finset.card_filter_le (Finset.univ : Finset (Fin (L + 1) × Fin (L + 1)))
      (fun jv => jv.1 ≠ jv.2)
    have hh : O.card ≤ (L + 1) ^ 2 := by simpa only [O, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, pow_two] using hn
    exact_mod_cast hh
  have hreal : ((kernelPartnerStarts X L R S).card : ℝ) ≤
      ∑ jv ∈ O, ∑ a ∈ D, ∑ b ∈ D, ((fixedKernelPartnerFiber X L R S a b jv.1 jv.2).card : ℝ) := by
    exact_mod_cast hcard
  calc
    _ ≤ _ := hreal
    _ ≤ ∑ _jv ∈ O, ∑ _a ∈ D, ∑ _b ∈ D, bound := by
      apply Finset.sum_le_sum
      intro jv hjv
      exact Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb =>
        hf jv.1 jv.2 (Finset.mem_filter.mp hjv).2 a ha b hb
    _ = (O.card : ℝ) * (D.card : ℝ) ^ 2 * bound := by simp [pow_two, mul_assoc]
    _ ≤ _ := by dsimp [D]; gcongr

/-- The complete two-kernel partner population is uniformly subpolynomial. -/
theorem card_kernelPartnerStarts_le_rpow_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      betaMin * Real.log X ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log X →
      ∀ R S : ℕ, 1 < R → 1 < S → R.Coprime S →
      ((kernelPartnerStarts X L R S).card : ℝ) ≤ (X : ℝ) ^ epsilon := by
  have heps : 0 < epsilon / 4 := by positivity
  obtain ⟨Xfixed, hfixed⟩ := card_fixedKernelPartnerFiber_le_rpow_eventually (epsilon / 4) heps
  obtain ⟨Xsmooth, hsmooth⟩ := card_squarefreeSmoothUpTo_le_rpow_eventually
    betaMin betaMax (epsilon / 4) hbetaMin hbetaMax heps
  obtain ⟨Xoffset, hoffset⟩ := polynomial_factor_le_rpow_eventually
    betaMax hbetaMax.le 1 2 (epsilon / 4) heps
  obtain ⟨Xlength, hlength⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    betaMax 1 hbetaMax.le (by norm_num) 1 (by omega)
  refine ⟨max Xfixed (max Xsmooth (max Xoffset (max Xlength 1))), ?_⟩
  intro X hX L hlower hupper R S hR hS hRS
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlen := hlength X (by omega) (L + 1) (by simpa using hupper)
  have hL : L ≤ X := by
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hlen
    exact_mod_cast (show (L : ℝ) ≤ X by linarith)
  have hs := hsmooth X (by omega) L hlower hupper (3 * X)
  have ho : (L + 1 : ℝ) ^ 2 ≤ (X : ℝ) ^ (epsilon / 4) := by
    simpa only [one_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L + 1 : ℝ) ^ 2)]
      using hoffset X (by omega) L (by simpa using hupper)
  have hf := card_kernelPartnerStarts_le_of_fixed_fibres hL (by positivity : 0 ≤ (X : ℝ) ^ (epsilon / 4))
    (fun j v hjv a _ b _ => hfixed X (by omega) L hL R S a b hR hS hRS j v hjv)
  calc
    _ ≤ _ := hf
    _ ≤ (X : ℝ) ^ (epsilon / 4) * ((X : ℝ) ^ (epsilon / 4)) ^ 2 * (X : ℝ) ^ (epsilon / 4) := by gcongr
    _ = _ := by rw [pow_two, ← mul_assoc, ← Real.rpow_add hXpos, ← Real.rpow_add hXpos,
      ← Real.rpow_add hXpos]; congr 1; ring

/-- Candidate partners of a fixed first start with two coprime nontrivial window kernels. -/
def twoKernelPartnerStarts (X L x : ℕ) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (L + 1) × Fin (L + 1))).filter fun iu =>
    1 < largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.1) ∧
    1 < largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.2) ∧
    (largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.1)).Coprime
      (largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.2))).biUnion fun iu =>
    kernelPartnerStarts X L
      (largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.1))
      (largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.2))

theorem mem_twoKernelPartnerStarts {X L x y : ℕ} :
    y ∈ twoKernelPartnerStarts X L x ↔ ∃ i u : Fin (L + 1),
      1 < largeOddKernel (L + 1) (startCompleteVertexLabel x L i) ∧
      1 < largeOddKernel (L + 1) (startCompleteVertexLabel x L u) ∧
      (largeOddKernel (L + 1) (startCompleteVertexLabel x L i)).Coprime
        (largeOddKernel (L + 1) (startCompleteVertexLabel x L u)) ∧
      y ∈ kernelPartnerStarts X L
        (largeOddKernel (L + 1) (startCompleteVertexLabel x L i))
        (largeOddKernel (L + 1) (startCompleteVertexLabel x L u)) := by
  simp only [twoKernelPartnerStarts, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.exists, and_assoc]

/-- The candidate population retains the genuine positive upper-slice range. -/
theorem twoKernelPartnerStarts_subset (X L x : ℕ) :
    twoKernelPartnerStarts X L x ⊆ Finset.Icc 2 (2 * X) := by
  intro y hy
  obtain ⟨i, u, _, _, _, hy⟩ := mem_twoKernelPartnerStarts.mp hy
  exact Finset.mem_Icc.mpr (mem_kernelPartnerStarts.mp hy).1

/-- Summation over both fixed-start offsets is only a squared window-length loss. -/
theorem card_twoKernelPartnerStarts_le_of_kernel_counts
    {X L x : ℕ} {bound : ℝ} (hbound : 0 ≤ bound)
    (hf : ∀ R S : ℕ, 1 < R → 1 < S → R.Coprime S →
      ((kernelPartnerStarts X L R S).card : ℝ) ≤ bound) :
    ((twoKernelPartnerStarts X L x).card : ℝ) ≤ (L + 1 : ℝ) ^ 2 * bound := by
  classical
  let O : Finset (Fin (L + 1) × Fin (L + 1)) := Finset.univ.filter fun iu =>
    1 < largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.1) ∧
    1 < largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.2) ∧
    (largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.1)).Coprime
      (largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.2))
  have hO : (O.card : ℝ) ≤ (L + 1 : ℝ) ^ 2 := by
    have hn : O.card ≤ (L + 1) ^ 2 := by
      exact (Finset.card_filter_le _ _).trans_eq (by simp [pow_two])
    exact_mod_cast hn
  have hfinite : ((twoKernelPartnerStarts X L x).card : ℝ) ≤
      ∑ iu ∈ O, ((kernelPartnerStarts X L
        (largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.1))
        (largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.2))).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := O)
      (t := fun iu => kernelPartnerStarts X L
        (largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.1))
        (largeOddKernel (L + 1) (startCompleteVertexLabel x L iu.2))))
  calc
    _ ≤ _ := hfinite
    _ ≤ ∑ _iu ∈ O, bound := by
      apply Finset.sum_le_sum
      intro iu hiu
      have hh := (Finset.mem_filter.mp hiu).2
      exact hf _ _ hh.1 hh.2.1 hh.2.2
    _ = (O.card : ℝ) * bound := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hO hbound

/-- The partner bound of Lemma 3.23, uniformly before the fixed first start.
The entire candidate set is counted; no comparability assumption on a partner is imposed. -/
theorem card_twoKernelPartnerStarts_le_rpow_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      betaMin * Real.log X ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log X →
      ∀ x : ℕ, ((twoKernelPartnerStarts X L x).card : ℝ) ≤ (X : ℝ) ^ epsilon := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Xkernel, hkernel⟩ := card_kernelPartnerStarts_le_rpow_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbetaMax heps
  obtain ⟨Xoffset, hoffset⟩ := polynomial_factor_le_rpow_eventually
    betaMax hbetaMax.le 1 2 (epsilon / 2) heps
  refine ⟨max Xkernel (max Xoffset 1), ?_⟩
  intro X hX L hlower hupper x
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have ho : (L + 1 : ℝ) ^ 2 ≤ (X : ℝ) ^ (epsilon / 2) := by
    simpa only [one_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L + 1 : ℝ) ^ 2)]
      using hoffset X (by omega) L (by simpa using hupper)
  have hf := card_twoKernelPartnerStarts_le_of_kernel_counts (x := x)
    (by positivity : 0 ≤ (X : ℝ) ^ (epsilon / 2)) (hkernel X (by omega) L hlower hupper)
  calc
    _ ≤ _ := hf
    _ ≤ (X : ℝ) ^ (epsilon / 2) * (X : ℝ) ^ (epsilon / 2) :=
      mul_le_mul_of_nonneg_right ho (by positivity)
    _ = _ := by rw [← Real.rpow_add hXpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

end
end PaperC.V282.TerminalPartnerCount
