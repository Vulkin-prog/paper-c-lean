import PaperC.Combinatorics.CertificateCRTInstantiation

/-!
# Covering an actual population by CRT certificates

Lemma 7.1 bounds a sum over all admissible certificates.  To apply that
bound to a concrete population, one still has to prove that every pair in
the population is a solution of one of those certificates.  This file
formalizes that elementary but essential covering step.

The assignment of a certificate may depend on the pair.  No injectivity of
that assignment is required: the union bound automatically groups all pairs
which choose the same certificate.
-/

namespace PaperC
namespace CRT

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-- The interval solution finset attached to one unordered certificate. -/
noncomputable def certificateSolutions
    {s : Finset ι} {r : ℕ}
    (residue modulus : ι → ℕ)
    (a b : ℕ)
    (T : UnorderedCertificate s r) : Finset ℕ :=
  {x ∈ Ico a b |
      ∀ i ∈ T.1.toList, x ≡ residue i [MOD modulus i]}

@[simp]
theorem card_certificateSolutions
    {s : Finset ι} {r : ℕ}
    (residue modulus : ι → ℕ)
    (a b : ℕ)
    (T : UnorderedCertificate s r) :
    (certificateSolutions residue modulus a b T).card =
      certificateSolutionCount residue modulus a b T := by
  rfl

/-- The one-dimensional solution set retained in the certificate mass. -/
noncomputable def admissibleCertificateSolutions
    {s : Finset ι} {r : ℕ}
    (residue modulus : ι → ℕ)
    (a b N : ℕ)
    (T : UnorderedCertificate s r) : Finset ℕ :=
  if CertificateAdmissible modulus N T then
    certificateSolutions residue modulus a b T
  else ∅

/--
One-dimensional population cover.  This is the version used after fixing a
nontrivial rational channel and projecting its start pairs to one coordinate.
-/
theorem card_population_le_sum_admissibleCertificateSolutionCount
    {s : Finset ι} {r : ℕ}
    (population : Finset ℕ)
    (assignment : ℕ → UnorderedCertificate s r)
    (residue modulus : ι → ℕ)
    (a b N : ℕ)
    (hadmissible :
      ∀ x ∈ population,
        CertificateAdmissible modulus N (assignment x))
    (hsolution :
      ∀ x ∈ population,
        x ∈ certificateSolutions residue modulus a b (assignment x)) :
    population.card ≤
      ∑ T : UnorderedCertificate s r,
        if CertificateAdmissible modulus N T then
          certificateSolutionCount residue modulus a b T
        else 0 := by
  classical
  let cover : Finset ℕ :=
    (Finset.univ : Finset (UnorderedCertificate s r)).biUnion
      (admissibleCertificateSolutions residue modulus a b N)
  have hsubset : population ⊆ cover := by
    intro x hx
    dsimp [cover]
    rw [Finset.mem_biUnion]
    refine ⟨assignment x, Finset.mem_univ _, ?_⟩
    simp only [admissibleCertificateSolutions,
      if_pos (hadmissible x hx)]
    exact hsolution x hx
  calc
    population.card ≤ cover.card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ T ∈
          (Finset.univ : Finset (UnorderedCertificate s r)),
          (admissibleCertificateSolutions
            residue modulus a b N T).card := by
      dsimp [cover]
      exact Finset.card_biUnion_le
    _ = ∑ T : UnorderedCertificate s r,
          if CertificateAdmissible modulus N T then
            certificateSolutionCount residue modulus a b T
          else 0 := by
      apply Finset.sum_congr rfl
      intro T _hT
      by_cases hT : CertificateAdmissible modulus N T
      · simp [admissibleCertificateSolutions, hT]
      · simp [admissibleCertificateSolutions, hT]

/--
Membership-dependent version of the one-dimensional cover.  It avoids an
arbitrary default certificate when a certificate is naturally constructed
only from the proof that `x` belongs to the population.
-/
theorem card_population_le_sum_admissibleCertificateSolutionCount'
    {s : Finset ι} {r : ℕ}
    (population : Finset ℕ)
    (assignment :
      ∀ x, x ∈ population → UnorderedCertificate s r)
    (residue modulus : ι → ℕ)
    (a b N : ℕ)
    (hadmissible :
      ∀ x (hx : x ∈ population),
        CertificateAdmissible modulus N (assignment x hx))
    (hsolution :
      ∀ x (hx : x ∈ population),
        x ∈ certificateSolutions residue modulus a b
          (assignment x hx)) :
    population.card ≤
      ∑ T : UnorderedCertificate s r,
        if CertificateAdmissible modulus N T then
          certificateSolutionCount residue modulus a b T
        else 0 := by
  classical
  let cover : Finset ℕ :=
    (Finset.univ : Finset (UnorderedCertificate s r)).biUnion
      (admissibleCertificateSolutions residue modulus a b N)
  have hsubset : population ⊆ cover := by
    intro x hx
    dsimp [cover]
    rw [Finset.mem_biUnion]
    refine ⟨assignment x hx, Finset.mem_univ _, ?_⟩
    simp only [admissibleCertificateSolutions,
      if_pos (hadmissible x hx)]
    exact hsolution x hx
  calc
    population.card ≤ cover.card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ T ∈
          (Finset.univ : Finset (UnorderedCertificate s r)),
          (admissibleCertificateSolutions
            residue modulus a b N T).card := by
      dsimp [cover]
      exact Finset.card_biUnion_le
    _ = ∑ T : UnorderedCertificate s r,
          if CertificateAdmissible modulus N T then
            certificateSolutionCount residue modulus a b T
          else 0 := by
      apply Finset.sum_congr rfl
      intro T _hT
      by_cases hT : CertificateAdmissible modulus N T
      · simp [admissibleCertificateSolutions, hT]
      · simp [admissibleCertificateSolutions, hT]

/-- Weighted lower bridge into the one-dimensional certificate mass. -/
theorem pow_mul_card_population_le_admissibleCertificateSolutionMass
    {s : Finset ι} {r : ℕ}
    (population : Finset ℕ)
    (assignment : ℕ → UnorderedCertificate s r)
    (residue modulus : ι → ℕ)
    (a b N : ℕ)
    (u : ℚ) (hu : 0 ≤ u)
    (hadmissible :
      ∀ x ∈ population,
        CertificateAdmissible modulus N (assignment x))
    (hsolution :
      ∀ x ∈ population,
        x ∈ certificateSolutions residue modulus a b (assignment x)) :
    u ^ r * (population.card : ℚ) ≤
      admissibleCertificateSolutionMass
        s r residue modulus a b N u := by
  have hcardNat :=
    card_population_le_sum_admissibleCertificateSolutionCount
      population assignment residue modulus a b N
      hadmissible hsolution
  have hcard :
      (population.card : ℚ) ≤
        ∑ T : UnorderedCertificate s r,
          if CertificateAdmissible modulus N T then
            (certificateSolutionCount residue modulus a b T : ℚ)
          else 0 := by
    exact_mod_cast hcardNat
  calc
    u ^ r * (population.card : ℚ) ≤
        u ^ r *
          ∑ T : UnorderedCertificate s r,
            if CertificateAdmissible modulus N T then
              (certificateSolutionCount residue modulus a b T : ℚ)
            else 0 :=
      mul_le_mul_of_nonneg_left hcard (pow_nonneg hu r)
    _ = admissibleCertificateSolutionMass
          s r residue modulus a b N u := by
      simp [admissibleCertificateSolutionMass, Finset.mul_sum,
        mul_ite]

/-- Weighted membership-dependent one-dimensional population cover. -/
theorem pow_mul_card_population_le_admissibleCertificateSolutionMass'
    {s : Finset ι} {r : ℕ}
    (population : Finset ℕ)
    (assignment :
      ∀ x, x ∈ population → UnorderedCertificate s r)
    (residue modulus : ι → ℕ)
    (a b N : ℕ)
    (u : ℚ) (hu : 0 ≤ u)
    (hadmissible :
      ∀ x (hx : x ∈ population),
        CertificateAdmissible modulus N (assignment x hx))
    (hsolution :
      ∀ x (hx : x ∈ population),
        x ∈ certificateSolutions residue modulus a b
          (assignment x hx)) :
    u ^ r * (population.card : ℚ) ≤
      admissibleCertificateSolutionMass
        s r residue modulus a b N u := by
  have hcardNat :=
    card_population_le_sum_admissibleCertificateSolutionCount'
      population assignment residue modulus a b N
      hadmissible hsolution
  have hcard :
      (population.card : ℚ) ≤
        ∑ T : UnorderedCertificate s r,
          if CertificateAdmissible modulus N T then
            (certificateSolutionCount residue modulus a b T : ℚ)
          else 0 := by
    exact_mod_cast hcardNat
  calc
    u ^ r * (population.card : ℚ) ≤
        u ^ r *
          ∑ T : UnorderedCertificate s r,
            if CertificateAdmissible modulus N T then
              (certificateSolutionCount residue modulus a b T : ℚ)
            else 0 :=
      mul_le_mul_of_nonneg_left hcard (pow_nonneg hu r)
    _ = admissibleCertificateSolutionMass
          s r residue modulus a b N u := by
      simp [admissibleCertificateSolutionMass, Finset.mul_sum,
        mul_ite]

/-- The rectangular solution finset attached to one unordered certificate. -/
noncomputable def certificatePairSolutions
    {s : Finset ι} {r : ℕ}
    (residue₁ residue₂ modulus : ι → ℕ)
    (a₁ b₁ a₂ b₂ : ℕ)
    (T : UnorderedCertificate s r) : Finset (ℕ × ℕ) :=
  {x ∈ Ico a₁ b₁ |
      ∀ i ∈ T.1.toList, x ≡ residue₁ i [MOD modulus i]} ×ˢ
    {y ∈ Ico a₂ b₂ |
      ∀ i ∈ T.1.toList, y ≡ residue₂ i [MOD modulus i]}

@[simp]
theorem card_certificatePairSolutions
    {s : Finset ι} {r : ℕ}
    (residue₁ residue₂ modulus : ι → ℕ)
    (a₁ b₁ a₂ b₂ : ℕ)
    (T : UnorderedCertificate s r) :
    (certificatePairSolutions
      residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T).card =
      certificatePairSolutionCount
        residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T := by
  rfl

/--
The solution set retained in the certificate mass: inadmissible
certificates contribute the empty set.
-/
noncomputable def admissibleCertificatePairSolutions
    {s : Finset ι} {r : ℕ}
    (residue₁ residue₂ modulus : ι → ℕ)
    (a₁ b₁ a₂ b₂ N : ℕ)
    (T : UnorderedCertificate s r) : Finset (ℕ × ℕ) :=
  if CertificateAdmissible modulus N T then
    certificatePairSolutions
      residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T
  else ∅

/--
If every pair in a finite population chooses an admissible certificate and
satisfies all of its congruences, then the population cardinality is at most
the sum of the corresponding rectangular CRT solution counts.
-/
theorem card_population_le_sum_admissibleCertificatePairSolutionCount
    {s : Finset ι} {r : ℕ}
    (population : Finset (ℕ × ℕ))
    (assignment : ℕ × ℕ → UnorderedCertificate s r)
    (residue₁ residue₂ modulus : ι → ℕ)
    (a₁ b₁ a₂ b₂ N : ℕ)
    (hadmissible :
      ∀ pair ∈ population,
        CertificateAdmissible modulus N (assignment pair))
    (hsolution :
      ∀ pair ∈ population,
        pair ∈ certificatePairSolutions
          residue₁ residue₂ modulus a₁ b₁ a₂ b₂
          (assignment pair)) :
    population.card ≤
      ∑ T : UnorderedCertificate s r,
        if CertificateAdmissible modulus N T then
          certificatePairSolutionCount
            residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T
        else 0 := by
  classical
  let cover : Finset (ℕ × ℕ) :=
    (Finset.univ : Finset (UnorderedCertificate s r)).biUnion
      (admissibleCertificatePairSolutions
        residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N)
  have hsubset : population ⊆ cover := by
    intro pair hpair
    dsimp [cover]
    rw [Finset.mem_biUnion]
    refine ⟨assignment pair, Finset.mem_univ _, ?_⟩
    simp only [admissibleCertificatePairSolutions,
      if_pos (hadmissible pair hpair)]
    exact hsolution pair hpair
  calc
    population.card ≤ cover.card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ T ∈
          (Finset.univ : Finset (UnorderedCertificate s r)),
          (admissibleCertificatePairSolutions
            residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N T).card := by
      dsimp [cover]
      exact Finset.card_biUnion_le
    _ = ∑ T : UnorderedCertificate s r,
          if CertificateAdmissible modulus N T then
            certificatePairSolutionCount
              residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T
          else 0 := by
      apply Finset.sum_congr rfl
      intro T _hT
      by_cases hT : CertificateAdmissible modulus N T
      · simp [admissibleCertificatePairSolutions, hT]
      · simp [admissibleCertificatePairSolutions, hT]

/--
Membership-dependent two-dimensional population cover.  This is the form
used when the ambient certificate is extracted from the pair's canonical
data and hence only exists canonically under the population predicate.
-/
theorem card_population_le_sum_admissibleCertificatePairSolutionCount'
    {s : Finset ι} {r : ℕ}
    (population : Finset (ℕ × ℕ))
    (assignment :
      ∀ pair, pair ∈ population → UnorderedCertificate s r)
    (residue₁ residue₂ modulus : ι → ℕ)
    (a₁ b₁ a₂ b₂ N : ℕ)
    (hadmissible :
      ∀ pair (hpair : pair ∈ population),
        CertificateAdmissible modulus N (assignment pair hpair))
    (hsolution :
      ∀ pair (hpair : pair ∈ population),
        pair ∈ certificatePairSolutions
          residue₁ residue₂ modulus a₁ b₁ a₂ b₂
          (assignment pair hpair)) :
    population.card ≤
      ∑ T : UnorderedCertificate s r,
        if CertificateAdmissible modulus N T then
          certificatePairSolutionCount
            residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T
        else 0 := by
  classical
  let cover : Finset (ℕ × ℕ) :=
    (Finset.univ : Finset (UnorderedCertificate s r)).biUnion
      (admissibleCertificatePairSolutions
        residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N)
  have hsubset : population ⊆ cover := by
    intro pair hpair
    dsimp [cover]
    rw [Finset.mem_biUnion]
    refine ⟨assignment pair hpair, Finset.mem_univ _, ?_⟩
    simp only [admissibleCertificatePairSolutions,
      if_pos (hadmissible pair hpair)]
    exact hsolution pair hpair
  calc
    population.card ≤ cover.card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ T ∈
          (Finset.univ : Finset (UnorderedCertificate s r)),
          (admissibleCertificatePairSolutions
            residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N T).card := by
      dsimp [cover]
      exact Finset.card_biUnion_le
    _ = ∑ T : UnorderedCertificate s r,
          if CertificateAdmissible modulus N T then
            certificatePairSolutionCount
              residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T
          else 0 := by
      apply Finset.sum_congr rfl
      intro T _hT
      by_cases hT : CertificateAdmissible modulus N T
      · simp [admissibleCertificatePairSolutions, hT]
      · simp [admissibleCertificatePairSolutions, hT]

/--
Weighted population-cover form.  This is the exact lower bridge into
`admissibleCertificatePairSolutionMass`.
-/
theorem pow_mul_card_population_le_admissibleCertificatePairSolutionMass
    {s : Finset ι} {r : ℕ}
    (population : Finset (ℕ × ℕ))
    (assignment : ℕ × ℕ → UnorderedCertificate s r)
    (residue₁ residue₂ modulus : ι → ℕ)
    (a₁ b₁ a₂ b₂ N : ℕ)
    (u : ℚ) (hu : 0 ≤ u)
    (hadmissible :
      ∀ pair ∈ population,
        CertificateAdmissible modulus N (assignment pair))
    (hsolution :
      ∀ pair ∈ population,
        pair ∈ certificatePairSolutions
          residue₁ residue₂ modulus a₁ b₁ a₂ b₂
          (assignment pair)) :
    u ^ r * (population.card : ℚ) ≤
      admissibleCertificatePairSolutionMass
        s r residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N u := by
  have hcardNat :=
    card_population_le_sum_admissibleCertificatePairSolutionCount
      population assignment residue₁ residue₂ modulus
      a₁ b₁ a₂ b₂ N hadmissible hsolution
  have hcard :
      (population.card : ℚ) ≤
        ∑ T : UnorderedCertificate s r,
          if CertificateAdmissible modulus N T then
            (certificatePairSolutionCount
              residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T : ℚ)
          else 0 := by
    exact_mod_cast hcardNat
  calc
    u ^ r * (population.card : ℚ) ≤
        u ^ r *
          ∑ T : UnorderedCertificate s r,
            if CertificateAdmissible modulus N T then
              (certificatePairSolutionCount
                residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T : ℚ)
            else 0 :=
      mul_le_mul_of_nonneg_left hcard (pow_nonneg hu r)
    _ = admissibleCertificatePairSolutionMass
          s r residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N u := by
      simp [admissibleCertificatePairSolutionMass, Finset.mul_sum,
        mul_ite]

/-- Weighted membership-dependent two-dimensional population cover. -/
theorem pow_mul_card_population_le_admissibleCertificatePairSolutionMass'
    {s : Finset ι} {r : ℕ}
    (population : Finset (ℕ × ℕ))
    (assignment :
      ∀ pair, pair ∈ population → UnorderedCertificate s r)
    (residue₁ residue₂ modulus : ι → ℕ)
    (a₁ b₁ a₂ b₂ N : ℕ)
    (u : ℚ) (hu : 0 ≤ u)
    (hadmissible :
      ∀ pair (hpair : pair ∈ population),
        CertificateAdmissible modulus N (assignment pair hpair))
    (hsolution :
      ∀ pair (hpair : pair ∈ population),
        pair ∈ certificatePairSolutions
          residue₁ residue₂ modulus a₁ b₁ a₂ b₂
          (assignment pair hpair)) :
    u ^ r * (population.card : ℚ) ≤
      admissibleCertificatePairSolutionMass
        s r residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N u := by
  have hcardNat :=
    card_population_le_sum_admissibleCertificatePairSolutionCount'
      population assignment residue₁ residue₂ modulus
      a₁ b₁ a₂ b₂ N hadmissible hsolution
  have hcard :
      (population.card : ℚ) ≤
        ∑ T : UnorderedCertificate s r,
          if CertificateAdmissible modulus N T then
            (certificatePairSolutionCount
              residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T : ℚ)
          else 0 := by
    exact_mod_cast hcardNat
  calc
    u ^ r * (population.card : ℚ) ≤
        u ^ r *
          ∑ T : UnorderedCertificate s r,
            if CertificateAdmissible modulus N T then
              (certificatePairSolutionCount
                residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T : ℚ)
            else 0 :=
      mul_le_mul_of_nonneg_left hcard (pow_nonneg hu r)
    _ = admissibleCertificatePairSolutionMass
          s r residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N u := by
      simp [admissibleCertificatePairSolutionMass, Finset.mul_sum,
        mul_ite]

end

end CRT
end PaperC
