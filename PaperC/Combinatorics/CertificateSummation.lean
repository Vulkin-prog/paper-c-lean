import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Unordered certificate summation

This file formalizes the combinatorial `1 / r!` step in Paper C, Lemma 7.1.
An unordered certificate of size `r` has exactly `r!` orderings.  Comparing
the sum over injective ordered selections with the larger sum over all ordered
selections gives the elementary-symmetric bound

`∑_{|T|=r} ∏_{i∈T} wᵢ ≤ (∑ᵢ wᵢ)^r / r!`

for nonnegative rational weights.
-/

namespace PaperC
namespace CRT

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An unordered `r`-element subset of the available indices `s`. -/
abbrev UnorderedCertificate (s : Finset ι) (r : ℕ) :=
  {T : Finset ι // T ∈ s.powersetCard r}

/-- An unordered certificate together with one of its orderings. -/
abbrev OrderedCertificate (s : Finset ι) (r : ℕ) :=
  Σ T : UnorderedCertificate s r, Fin r ↪ T.1

theorem unorderedCertificate_subset
    {s : Finset ι} {r : ℕ} (T : UnorderedCertificate s r) :
    T.1 ⊆ s :=
  (mem_powersetCard.mp T.2).1

@[simp]
theorem unorderedCertificate_card
    {s : Finset ι} {r : ℕ} (T : UnorderedCertificate s r) :
    T.1.card = r :=
  (mem_powersetCard.mp T.2).2

/-- Forget the certificate and retain its ordered list of indices in `s`. -/
def orderedCertificateToFunction
    {s : Finset ι} {r : ℕ} (z : OrderedCertificate s r) :
    Fin r → s :=
  fun j ↦
    ⟨(z.2 j).1, unorderedCertificate_subset z.1 (z.2 j).2⟩

private theorem certificateOrdering_bijective
    {s : Finset ι} {r : ℕ} (T : UnorderedCertificate s r)
    (e : Fin r ↪ T.1) :
    Function.Bijective (e : Fin r → T.1) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨e.injective, by simp⟩

theorem orderedCertificateToFunction_injective
    {s : Finset ι} {r : ℕ} :
    Function.Injective
      (orderedCertificateToFunction :
        OrderedCertificate s r → (Fin r → s)) := by
  rintro ⟨T, e⟩ ⟨U, f⟩ h
  have he := (certificateOrdering_bijective T e).2
  have hf := (certificateOrdering_bijective U f).2
  have hTU : T = U := by
    apply Subtype.ext
    apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := he ⟨x, hx⟩
      have hj' := congrArg Subtype.val (congrFun h j)
      have hfx : (f j).1 = x := by
        simpa [orderedCertificateToFunction, hj] using hj'.symm
      simpa [hfx] using (f j).2
    · intro hx
      obtain ⟨j, hj⟩ := hf ⟨x, hx⟩
      have hj' := congrArg Subtype.val (congrFun h j)
      have hex : (e j).1 = x := by
        simpa [orderedCertificateToFunction, hj] using hj'
      simpa [hex] using (e j).2
  subst U
  have hef : e = f := by
    apply DFunLike.ext _ _
    intro j
    apply Subtype.ext
    simpa [orderedCertificateToFunction] using
      congrArg Subtype.val (congrFun h j)
  subst f
  rfl

/-- The canonical embedding of ordered certificates into all ordered selections. -/
def orderedCertificateEmbedding
    {s : Finset ι} {r : ℕ} :
    OrderedCertificate s r ↪ (Fin r → s) :=
  ⟨orderedCertificateToFunction,
    orderedCertificateToFunction_injective⟩

/-- The weighted sum over unordered certificates of fixed size. -/
def certificateWeightSum
    (s : Finset ι) (r : ℕ) (w : ι → ℚ) : ℚ :=
  ∑ T : UnorderedCertificate s r, ∏ i ∈ T.1, w i

private theorem ordering_product_eq_certificate_product
    {s : Finset ι} {r : ℕ} (w : ι → ℚ)
    (T : UnorderedCertificate s r) (e : Fin r ↪ T.1) :
    (∏ j, w (e j).1) = ∏ i ∈ T.1, w i := by
  calc
    (∏ j, w (e j).1) = ∏ i : T.1, w i.1 :=
      (certificateOrdering_bijective T e).prod_comp
        (fun i : T.1 ↦ w i.1)
    _ = ∏ i ∈ T.1, w i := by
      exact Finset.prod_coe_sort T.1 w

/-- Every unordered `r`-certificate has exactly `r!` weighted orderings. -/
theorem orderedCertificate_sum_eq_factorial_mul
    (s : Finset ι) (r : ℕ) (w : ι → ℚ) :
    (∑ z : OrderedCertificate s r,
        ∏ j, w (orderedCertificateToFunction z j).1) =
      (r.factorial : ℚ) * certificateWeightSum s r w := by
  rw [Fintype.sum_sigma]
  simp_rw [orderedCertificateToFunction,
    ordering_product_eq_certificate_product]
  have hcard :
      ∀ T : UnorderedCertificate s r,
        Fintype.card (Fin r ↪ T.1) = r.factorial := by
    intro T
    rw [Fintype.card_embedding_eq, Fintype.card_fin,
      Fintype.card_coe, unorderedCertificate_card,
      Nat.descFactorial_self]
  simp_rw [Finset.sum_const, Finset.card_univ, hcard,
    nsmul_eq_mul]
  unfold certificateWeightSum
  rw [Finset.mul_sum]

/--
The sum over ordered injective selections is at most the sum over all ordered
selections, provided the weights are nonnegative.
-/
theorem orderedCertificate_sum_le_all_functions
    (s : Finset ι) (r : ℕ) (w : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ z : OrderedCertificate s r,
        ∏ j, w (orderedCertificateToFunction z j).1) ≤
      ∑ f : Fin r → s, ∏ j, w (f j).1 := by
  classical
  let E : OrderedCertificate s r ↪ (Fin r → s) :=
    orderedCertificateEmbedding
  let g : (Fin r → s) → ℚ := fun f ↦ ∏ j, w (f j).1
  calc
    (∑ z : OrderedCertificate s r,
        ∏ j, w (orderedCertificateToFunction z j).1) =
        ∑ f ∈ (Finset.univ.map E), g f := by
          rw [Finset.sum_map]
          rfl
    _ ≤ ∑ f ∈ (Finset.univ : Finset (Fin r → s)), g f := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simp
      · intro f _ _
        dsimp [g]
        exact Finset.prod_nonneg fun j _ ↦ hw (f j).1 (f j).2
    _ = ∑ f : Fin r → s, ∏ j, w (f j).1 := by
      simp [g]

/--
The exact elementary-symmetric estimate furnishing the `1/r!` factor in
Lemma 7.1.
-/
theorem factorial_mul_certificateWeightSum_le_pow_sum
    (s : Finset ι) (r : ℕ) (w : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (r.factorial : ℚ) * certificateWeightSum s r w ≤
      (∑ i ∈ s, w i) ^ r := by
  rw [← orderedCertificate_sum_eq_factorial_mul]
  refine (orderedCertificate_sum_le_all_functions s r w hw).trans_eq ?_
  simpa only [Finset.sum_coe_sort] using
    (Fintype.sum_pow (fun i : s ↦ w i.1) r).symm

/-- Division form of the preceding bound. -/
theorem certificateWeightSum_le_pow_sum_div_factorial
    (s : Finset ι) (r : ℕ) (w : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    certificateWeightSum s r w ≤
      (∑ i ∈ s, w i) ^ r / r.factorial := by
  rw [le_div_iff₀]
  · simpa [mul_comm] using
      factorial_mul_certificateWeightSum_le_pow_sum s r w hw
  · positivity

/--
Specialization to the one-dimensional cell weights `u Eₚ / p` occurring in
equation (7.1).
-/
theorem certificateCellWeightSum_le
    (s : Finset ι) (r : ℕ)
    (cellCount modulus : ι → ℕ) (u : ℚ)
    (hu : 0 ≤ u) (hmodulus : ∀ i ∈ s, 0 < modulus i) :
    certificateWeightSum s r
        (fun i ↦ u * (cellCount i : ℚ) / (modulus i : ℚ)) ≤
      (u * ∑ i ∈ s, (cellCount i : ℚ) / (modulus i : ℚ)) ^ r /
        r.factorial := by
  have hw :
      ∀ i ∈ s,
        0 ≤ u * (cellCount i : ℚ) / (modulus i : ℚ) := by
    intro i hi
    apply div_nonneg
    · exact mul_nonneg hu (by positivity)
    · exact_mod_cast (hmodulus i hi).le
  simpa [Finset.mul_sum, div_eq_mul_inv, mul_assoc] using
    certificateWeightSum_le_pow_sum_div_factorial
      s r (fun i ↦ u * (cellCount i : ℚ) / (modulus i : ℚ)) hw

/--
Specialization to the two-dimensional weights `u M / p²` occurring in
equation (7.2).
-/
theorem certificatePairCellWeightSum_le
    (s : Finset ι) (r : ℕ)
    (modulus : ι → ℕ) (M : ℕ) (u : ℚ)
    (hu : 0 ≤ u) (hmodulus : ∀ i ∈ s, 0 < modulus i) :
    certificateWeightSum s r
        (fun i ↦ u * (M : ℚ) / (modulus i : ℚ) ^ 2) ≤
      (u * (M : ℚ) *
          ∑ i ∈ s, 1 / (modulus i : ℚ) ^ 2) ^ r /
        r.factorial := by
  have hw :
      ∀ i ∈ s,
        0 ≤ u * (M : ℚ) / (modulus i : ℚ) ^ 2 := by
    intro i hi
    apply div_nonneg
    · exact mul_nonneg hu (by positivity)
    · have hp : (0 : ℚ) < (modulus i : ℚ) := by
        exact_mod_cast hmodulus i hi
      exact (pow_pos hp 2).le
  have hrewrite :
      (∑ i ∈ s, u * (M : ℚ) / (modulus i : ℚ) ^ 2) =
        u * (M : ℚ) * ∑ i ∈ s, 1 / (modulus i : ℚ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hp : (modulus i : ℚ) ≠ 0 := by
      exact_mod_cast (hmodulus i hi).ne'
    field_simp
  simpa [hrewrite] using
    certificateWeightSum_le_pow_sum_div_factorial
      s r (fun i ↦ u * (M : ℚ) / (modulus i : ℚ) ^ 2) hw

/--
Finite partial-sum form of the exponential-series majorant.  Taking
`R = card s + 1` covers every possible certificate size.
-/
theorem sum_certificateWeightSum_le_exponentialMajorant
    (s : Finset ι) (R : ℕ) (w : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ r ∈ Finset.range R, certificateWeightSum s r w) ≤
      ∑ r ∈ Finset.range R,
        (∑ i ∈ s, w i) ^ r / r.factorial := by
  apply Finset.sum_le_sum
  intro r hr
  exact certificateWeightSum_le_pow_sum_div_factorial s r w hw

end CRT
end PaperC
