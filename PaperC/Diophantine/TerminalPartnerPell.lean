import PaperC.Arithmetic.LargeOddKernel
import PaperC.Diophantine.PellInput
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1600000

/-!
# Pell reduction for partners of a fixed terminal start

This file formalizes the arithmetic and finite-counting part of Step 3 in
the proof of Theorem 10.1.  For fixed offsets `j ≠ v`, the two canonical
large-kernel decompositions

`y + j = R a z²`,  `y + v = S b w²`

subtract to

`R a z² - S b w² = j - v`.

The products `R*a` and `S*b` are squarefree because the small and large
odd supports are disjoint.  When `R,S > 1` are coprime, their quotient is
not a rational square: a prime in `R` cannot cancel against either `S` or
the small part `b`.

The final theorem transfers the registered generalized-Pell input to the
terminal-partner count while keeping that internal bridge as an ordinary
explicit hypothesis.
-/

namespace PaperC
namespace TerminalPartnerPell

open LargeOddKernel
open DefectivePredicate

/-! ## Squarefree rational quotients -/

private theorem squarefree_isSquare_eq_one
    {n : ℕ} (hnSquarefree : Squarefree n)
    (hnSquare : IsSquare n) :
    n = 1 := by
  obtain ⟨r, hr⟩ := hnSquare
  have hrpow : n = r ^ 2 := by
    simpa only [pow_two] using hr
  by_cases hrOne : r = 1
  · simpa [hrOne] using hrpow
  have hsquarefreePow : Squarefree (r ^ 2) := by
    rwa [← hrpow]
  have hexponent :=
    (Nat.squarefree_pow_iff hrOne
      (by norm_num : (2 : ℕ) ≠ 0)).mp hsquarefreePow
  omega

/--
Two positive, squarefree and distinct natural numbers have a nonsquare
rational quotient.  Common prime factors are allowed: reduction by the gcd
leaves squarefree coprime numerator and denominator.
-/
theorem not_isSquare_ratio_of_squarefree_of_ne
    {A C : ℕ}
    (hApos : 0 < A) (hCpos : 0 < C)
    (hAsquarefree : Squarefree A)
    (hCsquarefree : Squarefree C)
    (hAC : A ≠ C) :
    ¬IsSquare ((A : ℚ) / (C : ℚ)) := by
  intro hsquare
  let g := Nat.gcd A C
  let A' := A / g
  let C' := C / g
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left C hApos
  have hAeq : A' * g = A := by
    dsimp [A', g]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left A C)
  have hCeq : C' * g = C := by
    dsimp [C', g]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right A C)
  have hA'pos : 0 < A' := by
    by_contra hzero
    have hA'zero : A' = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hA'zero, zero_mul] at hAeq
    omega
  have hC'pos : 0 < C' := by
    by_contra hzero
    have hC'zero : C' = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hC'zero, zero_mul] at hCeq
    omega
  have hA'squarefree : Squarefree A' :=
    hAsquarefree.squarefree_of_dvd
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left A C))
  have hC'squarefree : Squarefree C' :=
    hCsquarefree.squarefree_of_dvd
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right A C))
  have hcoprime : Nat.Coprime A' C' := by
    dsimp [A', C', g]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hratio :
      (A : ℚ) / (C : ℚ) =
        (A' : ℚ) / (C' : ℚ) := by
    have hCne : (C : ℚ) ≠ 0 := by
      exact_mod_cast hCpos.ne'
    have hC'ne : (C' : ℚ) ≠ 0 := by
      exact_mod_cast hC'pos.ne'
    field_simp
    exact_mod_cast (by
      rw [← hAeq, ← hCeq]
      ring)
  have hsquare' :
      IsSquare ((A' : ℚ) / (C' : ℚ)) := by
    rwa [← hratio]
  have hnum :
      (((A' : ℚ) / (C' : ℚ)).num) = (A' : ℤ) := by
    apply Rat.num_div_eq_of_coprime
    · exact_mod_cast hC'pos
    · simpa using hcoprime
  have hden :
      ((((A' : ℚ) / (C' : ℚ)).den : ℤ)) = (C' : ℤ) := by
    apply Rat.den_div_eq_of_coprime
    · exact_mod_cast hC'pos
    · simpa using hcoprime
  have hsquareData := Rat.isSquare_iff.mp hsquare'
  have hA'square : IsSquare A' := by
    rw [← Int.isSquare_natCast_iff]
    rw [← hnum]
    exact hsquareData.1
  have hC'square : IsSquare C' := by
    rw [← Int.isSquare_natCast_iff]
    rw [← hden]
    exact_mod_cast hsquareData.2
  have hA'one :=
    squarefree_isSquare_eq_one hA'squarefree hA'square
  have hC'one :=
    squarefree_isSquare_eq_one hC'squarefree hC'square
  apply hAC
  rw [← hAeq, ← hCeq, hA'one, hC'one]

/-! ## Canonical terminal coefficients -/

/--
The canonical decomposition, reordered in the form used in Step 3:

`n = R * a * z²`.
-/
theorem canonical_terminal_factorization
    {B n R : ℕ}
    (hn : n ≠ 0)
    (hR : largeOddKernel B n = R) :
    n =
      R * smallOddPart B n *
        canonicalSquarePart n ^ 2 := by
  calc
    n =
        canonicalSquarePart n ^ 2 *
          smallOddPart B n *
            largeOddKernel B n :=
      canonical_largeOddKernel_decomposition
        (B := B) hn
    _ =
        R * smallOddPart B n *
          canonicalSquarePart n ^ 2 := by
      rw [hR]
      ring

/-- The canonical terminal coefficient divides the represented integer. -/
theorem canonical_terminal_coefficient_dvd
    {B n : ℕ} (hn : n ≠ 0) :
    largeOddKernel B n * smallOddPart B n ∣ n := by
  refine ⟨canonicalSquarePart n ^ 2, ?_⟩
  calc
    n =
        canonicalSquarePart n ^ 2 *
          smallOddPart B n *
            largeOddKernel B n :=
      canonical_largeOddKernel_decomposition
        (B := B) hn
    _ =
        largeOddKernel B n *
          smallOddPart B n *
            canonicalSquarePart n ^ 2 := by
      ring

/-- A positive label bounds its canonical terminal coefficient. -/
theorem canonical_terminal_coefficient_le
    {B n : ℕ} (hn : n ≠ 0) :
    largeOddKernel B n * smallOddPart B n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
    (canonical_terminal_coefficient_dvd hn)

/-- The canonical square root is bounded by the square root of its label. -/
theorem canonicalSquarePart_le_sqrt
    {B n : ℕ} (hn : n ≠ 0) :
    canonicalSquarePart n ≤ Nat.sqrt n := by
  apply Nat.le_sqrt'.mpr
  have hcoefficientPos :
      0 <
        largeOddKernel B n *
          smallOddPart B n :=
    Nat.mul_pos
      (Nat.pos_of_ne_zero
        (largeOddKernel_ne_zero B n))
      (Nat.pos_of_ne_zero
        (smallOddPart_ne_zero B n))
  calc
    canonicalSquarePart n ^ 2 ≤
        (largeOddKernel B n *
          smallOddPart B n) *
            canonicalSquarePart n ^ 2 :=
      Nat.le_mul_of_pos_left _ hcoefficientPos
    _ = n := by
      rw [← canonical_terminal_factorization
        hn rfl]

/-- Each canonical coefficient `large kernel × small part` is squarefree. -/
theorem canonical_terminal_coefficient_squarefree
    (B n : ℕ) :
    Squarefree
      (largeOddKernel B n * smallOddPart B n) := by
  apply
    (Nat.squarefree_mul
      (smallOddPart_coprime_largeOddKernel B n).symm).mpr
  exact
    ⟨largeOddKernel_squarefree B n,
      smallOddPart_squarefree B n⟩

/--
The coefficient quotient occurring for two terminal components is
nonsquare.  The assumptions `R,S > 1` and `R.Coprime S` are exactly the
large-kernel conclusions of Lemma 9.12.
-/
theorem canonical_terminal_coefficient_ratio_not_isSquare
    {B m n : ℕ}
    (hR :
      1 < largeOddKernel B m)
    (_hS :
      1 < largeOddKernel B n)
    (hcoprime :
      Nat.Coprime
        (largeOddKernel B m)
        (largeOddKernel B n)) :
    ¬IsSquare
      (((largeOddKernel B m *
          smallOddPart B m : ℕ) : ℚ) /
        ((largeOddKernel B n *
          smallOddPart B n : ℕ) : ℚ)) := by
  let R := largeOddKernel B m
  let S := largeOddKernel B n
  let a := smallOddPart B m
  let b := smallOddPart B n
  have hRpos : 0 < R :=
    Nat.pos_of_ne_zero (largeOddKernel_ne_zero B m)
  have hSpos : 0 < S :=
    Nat.pos_of_ne_zero (largeOddKernel_ne_zero B n)
  have hapos : 0 < a :=
    Nat.pos_of_ne_zero (smallOddPart_ne_zero B m)
  have hbpos : 0 < b :=
    Nat.pos_of_ne_zero (smallOddPart_ne_zero B n)
  have hApos : 0 < R * a := Nat.mul_pos hRpos hapos
  have hCpos : 0 < S * b := Nat.mul_pos hSpos hbpos
  have hAsquarefree : Squarefree (R * a) := by
    dsimp [R, a]
    exact canonical_terminal_coefficient_squarefree B m
  have hCsquarefree : Squarefree (S * b) := by
    dsimp [S, b]
    exact canonical_terminal_coefficient_squarefree B n
  have hRne : R ≠ 1 := by
    dsimp [R]
    omega
  obtain ⟨p, hpPrime, hpR⟩ :=
    Nat.exists_prime_and_dvd hRne
  have hpLarge : B < p := by
    dsimp [R] at hpR
    exact
      (prime_dvd_largeOddKernel_iff_large_odd
        hpPrime).mp hpR |>.1
  have hpNotS : ¬p ∣ S := by
    have hpCoprime : Nat.Coprime p S := by
      exact hcoprime.of_dvd_left hpR
    exact hpPrime.coprime_iff_not_dvd.mp hpCoprime
  have hpNotb : ¬p ∣ b := by
    intro hpb
    dsimp [b] at hpb
    have hpSmall :=
      (prime_dvd_smallOddPart_iff_small_odd
        hpPrime).mp hpb
    omega
  have hpNotC : ¬p ∣ S * b := by
    intro hpC
    rcases hpPrime.dvd_mul.mp hpC with hpS | hpb
    · exact hpNotS hpS
    · exact hpNotb hpb
  have hAC : R * a ≠ S * b := by
    intro heq
    apply hpNotC
    rw [← heq]
    exact dvd_mul_of_dvd_left hpR a
  exact
    not_isSquare_ratio_of_squarefree_of_ne
      hApos hCpos hAsquarefree hCsquarefree hAC

/-! ## The partner witness and its Pell image -/

/-- A partner start together with the two canonical square roots. -/
structure TerminalPartnerWitness where
  partner : ℤ
  leftRoot : ℕ
  rightRoot : ℕ
deriving DecidableEq

/-- The canonical square roots attached to two positive partner labels. -/
noncomputable def canonicalPartnerWitness
    (m n : ℕ) (partner : ℤ) :
    TerminalPartnerWitness where
  partner := partner
  leftRoot := canonicalSquarePart m
  rightRoot := canonicalSquarePart n

/--
Two fixed terminal decompositions, including a symmetric height bound for
the square roots.
-/
def terminalPartnerWitnessBox
    (R S a b : ℕ) (j v : ℤ) (H : ℕ)
    (w : TerminalPartnerWitness) : Prop :=
  w.partner + j =
      (R * a : ℕ) * w.leftRoot ^ 2 ∧
    w.partner + v =
      (S * b : ℕ) * w.rightRoot ^ 2 ∧
    w.leftRoot ≤ H ∧
    w.rightRoot ≤ H

/-- Forget the determined partner and retain the two Pell variables. -/
def partnerToPell
    (w : TerminalPartnerWitness) : ℤ × ℤ :=
  (w.leftRoot, w.rightRoot)

/--
Two equalities of large kernels, together with the two canonical
decompositions, produce exactly a terminal-partner witness.
-/
theorem canonical_decompositions_give_partner_box
    {B m n R S H : ℕ} {partner j v : ℤ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hleft : partner + j = (m : ℤ))
    (hright : partner + v = (n : ℤ))
    (hR : largeOddKernel B m = R)
    (hS : largeOddKernel B n = S)
    (hz :
      canonicalSquarePart m ≤ H)
    (hw :
      canonicalSquarePart n ≤ H) :
    terminalPartnerWitnessBox
      R S
      (smallOddPart B m)
      (smallOddPart B n)
      j v H
      (canonicalPartnerWitness m n partner) := by
  refine ⟨?_, ?_, hz, hw⟩
  · simp only [canonicalPartnerWitness]
    rw [hleft]
    exact_mod_cast canonical_terminal_factorization hm hR
  · simp only [canonicalPartnerWitness]
    rw [hright]
    exact_mod_cast canonical_terminal_factorization hn hS

/--
Subtracting the two terminal decompositions gives
`R a z² - S b w² = j-v`.
-/
theorem terminalPartnerWitness_maps_to_pell
    {R S a b H : ℕ} {j v : ℤ}
    {w : TerminalPartnerWitness}
    (hw : terminalPartnerWitnessBox
      R S a b j v H w) :
    PellInput.pellBox
      (R * a) (S * b) (j - v) H
      (partnerToPell w) := by
  rcases hw with ⟨hleft, hright, hz, hw⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold PellInput.pellEquation partnerToPell
    push_cast at hleft hright ⊢
    nlinarith
  · simpa [partnerToPell] using hz
  · simpa [partnerToPell] using hw

/--
Direct canonical form of the Step 3 reduction.  This theorem combines the
two kernel equalities, both canonical decompositions, and subtraction into
one Pell-box conclusion.
-/
theorem canonical_decompositions_give_pell
    {B m n R S H : ℕ} {partner j v : ℤ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hleft : partner + j = (m : ℤ))
    (hright : partner + v = (n : ℤ))
    (hR : largeOddKernel B m = R)
    (hS : largeOddKernel B n = S)
    (hz :
      canonicalSquarePart m ≤ H)
    (hw :
      canonicalSquarePart n ≤ H) :
    PellInput.pellBox
      (R * smallOddPart B m)
      (S * smallOddPart B n)
      (j - v) H
      (partnerToPell
        (canonicalPartnerWitness m n partner)) := by
  apply terminalPartnerWitness_maps_to_pell
  exact canonical_decompositions_give_partner_box
    hm hn hleft hright hR hS hz hw

/--
The Pell image is injective on any family of genuine terminal-partner
witnesses: either displayed decomposition recovers the partner.
-/
theorem partnerToPell_injective_on
    {R S a b H : ℕ} {j v : ℤ}
    {u w : TerminalPartnerWitness}
    (hu : terminalPartnerWitnessBox R S a b j v H u)
    (hw : terminalPartnerWitnessBox R S a b j v H w)
    (huw : partnerToPell u = partnerToPell w) :
    u = w := by
  have hz :
      u.leftRoot = w.leftRoot := by
    have hzInt :
        (u.leftRoot : ℤ) =
          (w.leftRoot : ℤ) :=
      congrArg (fun z : ℤ × ℤ ↦ z.1) huw
    exact_mod_cast hzInt
  have hroot :
      u.rightRoot = w.rightRoot := by
    have hwInt :
        (u.rightRoot : ℤ) =
          (w.rightRoot : ℤ) :=
      congrArg (fun z : ℤ × ℤ ↦ z.2) huw
    exact_mod_cast hwInt
  have hpartner : u.partner = w.partner := by
    have huEq := hu.1
    have hwEq := hw.1
    rw [hz] at huEq
    omega
  cases u
  cases w
  simp_all

/-- Any finite Pell count transfers unchanged to terminal partners. -/
theorem terminalPartnerWitnessBox_atMost
    {R S a b H : ℕ} {j v : ℤ} {bound : ℝ}
    (hPell :
      PellInput.HasAtMostSolutionsReal
        (PellInput.pellBox
          (R * a) (S * b) (j - v) H)
        bound) :
    PellInput.HasAtMostSolutionsReal
      (terminalPartnerWitnessBox R S a b j v H)
      bound := by
  intro s hs
  let f : TerminalPartnerWitness → ℤ × ℤ :=
    partnerToPell
  have himage :
      ∀ solution ∈ s.image f,
        PellInput.pellBox
          (R * a) (S * b) (j - v) H
          solution := by
    intro solution hsolution
    obtain ⟨w, hw, rfl⟩ :=
      Finset.mem_image.mp hsolution
    exact terminalPartnerWitness_maps_to_pell
      (hs w hw)
  have hcount := hPell (s.image f) himage
  have hcard :
      (s.image f).card = s.card := by
    rw [Finset.card_image_iff]
    intro u hu w hw huw
    exact partnerToPell_injective_on
      (hs u hu) (hs w hw) huw
  rwa [hcard] at hcount

/-! ## Polynomial box and the explicit generalized-Pell bridge -/

/--
Polynomial-box count for fixed terminal coefficients.  The hypotheses are
the concrete small/large support conclusions needed to derive both
squarefreeness and nonsquareness internally.
-/
def TerminalPartnerPolynomialBoxStatement : Prop :=
  ∀ K : ℕ, 0 < K →
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ∀ (B m n : ℕ) (j v : ℤ),
          m ≠ 0 →
          n ≠ 0 →
          1 < largeOddKernel B m →
          1 < largeOddKernel B n →
          Nat.Coprime
            (largeOddKernel B m)
            (largeOddKernel B n) →
          j ≠ v →
          largeOddKernel B m * smallOddPart B m ≤ N ^ K →
          largeOddKernel B n * smallOddPart B n ≤ N ^ K →
          (j - v).natAbs ≤ N ^ K →
          PellInput.HasAtMostSolutionsReal
            (terminalPartnerWitnessBox
              (largeOddKernel B m)
              (largeOddKernel B n)
              (smallOddPart B m)
              (smallOddPart B n)
              j v (N ^ K))
            (PellInput.expLogLogBound c N)

/--
Step 3 of Theorem 10.1, conditional only on the registered generalized-Pell
input.  All coefficient properties, the Pell reduction, and the finite
count transfer are proved in Lean.
-/
theorem terminalPartnerPolynomialBox_of_generalizedPell
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    TerminalPartnerPolynomialBoxStatement := by
  have hPell' :
      PellInput.PellPolynomialBoxStatement :=
    PellInput.pellPolynomialBox_of_generalizedPell hPell
  intro K hK
  obtain ⟨c, hc, N₀, hN₀⟩ := hPell' K hK
  refine ⟨c, hc, N₀, ?_⟩
  intro N hN B m n j v hm hn hR hS
    hcoprime hj hAbound hSbbound hdeltaBound
  have hApos :
      0 <
        largeOddKernel B m *
          smallOddPart B m :=
    Nat.mul_pos
      (Nat.pos_of_ne_zero
        (largeOddKernel_ne_zero B m))
      (Nat.pos_of_ne_zero
        (smallOddPart_ne_zero B m))
  have hCpos :
      0 <
        largeOddKernel B n *
          smallOddPart B n :=
    Nat.mul_pos
      (Nat.pos_of_ne_zero
        (largeOddKernel_ne_zero B n))
      (Nat.pos_of_ne_zero
        (smallOddPart_ne_zero B n))
  have hAsquarefree :=
    canonical_terminal_coefficient_squarefree B m
  have hCsquarefree :=
    canonical_terminal_coefficient_squarefree B n
  have hnonsquare :=
    canonical_terminal_coefficient_ratio_not_isSquare
      hR hS hcoprime
  have hdelta : j - v ≠ 0 :=
    sub_ne_zero.mpr hj
  have hcount :=
    hN₀ N hN
      (largeOddKernel B m * smallOddPart B m)
      (largeOddKernel B n * smallOddPart B n)
      (j - v)
      hApos hCpos hAsquarefree hCsquarefree
      hnonsquare hdelta hAbound hSbbound hdeltaBound
  exact terminalPartnerWitnessBox_atMost hcount

end TerminalPartnerPell
end PaperC
