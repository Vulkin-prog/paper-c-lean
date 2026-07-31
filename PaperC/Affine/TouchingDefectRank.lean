import PaperC.Affine.TouchingSystem
import PaperC.Affine.Normalization
import PaperC.Arithmetic.DefectivePredicate
import PaperC.Coding.IntervalDefectBound
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

set_option maxHeartbeats 1200000

/-!
# Relation rank for two touching starts

The rows of `touchingSystem M x L` form a double star.  Its left root is
`x - 1`; the two centres are `x` and `x + L`; and the vertex `x + L - 1`
is simultaneously a leaf of the first star and the root of the second.

This module maps a row coefficient vector to its boundary on all non-root
vertices, proves that map injective, and then shows that a relation can have
nonzero boundary only at `(2*L)`-defective vertices.
-/

namespace PaperC
namespace Affine
namespace TouchingDefectRank

open scoped BigOperators

noncomputable section

/-- The natural-number label of a non-root vertex of the double start tree. -/
def touchingVertexLabel (x L : ℕ) :
    Sum (Fin L) (Fin L) → ℕ
  | Sum.inl j => x + j.1
  | Sum.inr j => x + L + j.1

theorem touchingVertexLabel_injective
    (x L : ℕ) :
    Function.Injective (touchingVertexLabel x L) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          apply congrArg Sum.inl
          apply Fin.ext
          simpa [touchingVertexLabel] using
            Nat.add_left_cancel hij
      | inr j =>
          exfalso
          simp only [touchingVertexLabel] at hij
          have hi := i.2
          omega
  | inr i =>
      cases j with
      | inl j =>
          exfalso
          simp only [touchingVertexLabel] at hij
          have hj := j.2
          omega
      | inr j =>
          apply congrArg Sum.inr
          apply Fin.ext
          simp only [touchingVertexLabel] at hij
          omega

/--
Boundary coordinates on the non-root vertices of the double start tree.

On the first block, coordinate zero is the first centre and hence sees the
sum of all first-block coefficients.  The last first-block vertex also sees
the boundary row of the second block.  (For `L = 1`, both contributions occur
at the same vertex.)  The second block has the usual star boundary.
-/
def touchingInteriorBoundary (L : ℕ) :
    (Sum (Fin L) (Fin L) → F₂) →ₗ[F₂]
      (Sum (Fin L) (Fin L) → F₂) where
  toFun u s :=
    match s with
    | Sum.inl j =>
        (if j.1 = 0 then
          ∑ i : Fin L, u (Sum.inl i)
        else
          u (Sum.inl j)) +
        if j.1 + 1 = L then
          u (Sum.inr
            ⟨0, Nat.zero_lt_of_lt j.2⟩)
        else
          0
    | Sum.inr j =>
        if j.1 = 0 then
          ∑ i : Fin L, u (Sum.inr i)
        else
          u (Sum.inr j)
  map_add' u v := by
    funext s
    cases s with
    | inl j =>
        by_cases hj0 : j.1 = 0
        · by_cases hL1 : 1 = L
          · simp [hj0, hL1, Finset.sum_add_distrib]
            ring
          · simp [hj0, hL1, Finset.sum_add_distrib]
        · by_cases hjlast : j.1 + 1 = L
          · simp [hj0, hjlast]
            ring
          · simp [hj0, hjlast]
    | inr j =>
        by_cases hj0 : j.1 = 0
        · simp [hj0, Finset.sum_add_distrib]
        · simp [hj0]
  map_smul' c u := by
    funext s
    cases s with
    | inl j =>
        by_cases hj0 : j.1 = 0
        · by_cases hL1 : 1 = L
          · simp [hj0, hL1]
            rw [← Finset.mul_sum]
            ring
          · simp [hj0, hL1]
            rw [← Finset.mul_sum]
        · by_cases hjlast : j.1 + 1 = L <;>
            simp [hj0, hjlast, mul_add]
    | inr j =>
        by_cases hj0 : j.1 = 0
        · simp only [hj0, if_pos, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply]
          rw [Finset.mul_sum]
        · simp [hj0]

/-- The non-root boundary determines every edge coefficient of the double tree. -/
theorem touchingInteriorBoundary_injective
    {L : ℕ} (hL : 0 < L) :
    Function.Injective (touchingInteriorBoundary L) := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro u hu
  have hboundary : touchingInteriorBoundary L u = 0 :=
    LinearMap.mem_ker.mp hu
  let z : Fin L := ⟨0, hL⟩
  have hright_nonzero :
      ∀ i : Fin L, i.1 ≠ 0 → u (Sum.inr i) = 0 := by
    intro i hi
    have hb := congrFun hboundary (Sum.inr i)
    simpa [touchingInteriorBoundary, hi] using hb
  have hright_sum :
      ∑ i : Fin L, u (Sum.inr i) = 0 := by
    have hb := congrFun hboundary (Sum.inr z)
    simpa [z, touchingInteriorBoundary] using hb
  have hright_sum_single :
      ∑ i : Fin L, u (Sum.inr i) = u (Sum.inr z) := by
    classical
    apply Finset.sum_eq_single z
    · intro i _hi hiz
      apply hright_nonzero i
      intro hi0
      apply hiz
      apply Fin.ext
      simpa [z] using hi0
    · simp
  have hright_zero : u (Sum.inr z) = 0 := by
    rw [← hright_sum_single]
    exact hright_sum
  have hright_all : ∀ i : Fin L, u (Sum.inr i) = 0 := by
    intro i
    by_cases hi : i.1 = 0
    · have hiz : i = z := by
        apply Fin.ext
        simpa [z] using hi
      simpa [hiz] using hright_zero
    · exact hright_nonzero i hi
  have hleft_nonzero :
      ∀ i : Fin L, i.1 ≠ 0 → u (Sum.inl i) = 0 := by
    intro i hi
    have hb := congrFun hboundary (Sum.inl i)
    by_cases hilast : i.1 + 1 = L
    · have hrzero :
          u (Sum.inr ⟨0, Nat.zero_lt_of_lt i.2⟩) = 0 :=
        hright_all _
      simpa [touchingInteriorBoundary, hi, hilast, hrzero] using hb
    · simpa [touchingInteriorBoundary, hi, hilast] using hb
  have hleft_sum :
      ∑ i : Fin L, u (Sum.inl i) = 0 := by
    have hb := congrFun hboundary (Sum.inl z)
    by_cases hlast : z.1 + 1 = L
    · have hrzero :
          u (Sum.inr ⟨0, Nat.zero_lt_of_lt z.2⟩) = 0 :=
        hright_all _
      simpa [z, touchingInteriorBoundary, hlast, hrzero] using hb
    · simpa [z, touchingInteriorBoundary, hlast] using hb
  have hleft_sum_single :
      ∑ i : Fin L, u (Sum.inl i) = u (Sum.inl z) := by
    classical
    apply Finset.sum_eq_single z
    · intro i _hi hiz
      apply hleft_nonzero i
      intro hi0
      apply hiz
      apply Fin.ext
      simpa [z] using hi0
    · simp
  have hleft_zero : u (Sum.inl z) = 0 := by
    rw [← hleft_sum_single]
    exact hleft_sum
  have hleft_all : ∀ i : Fin L, u (Sum.inl i) = 0 := by
    intro i
    by_cases hi : i.1 = 0
    · have hiz : i = z := by
        apply Fin.ext
        simpa [z] using hi
      simpa [hiz] using hleft_zero
    · exact hleft_nonzero i hi
  funext s
  cases s with
  | inl i => exact hleft_all i
  | inr i => exact hright_all i

/-- The parity-vector edge attached to a row of the touching system. -/
def touchingEdgeParity (x L p : ℕ) :
    Sum (Fin L) (Fin L) → F₂
  | Sum.inl i =>
      if i.1 = 0 then
        parityVec (x - 1) p + parityVec x p
      else
        parityVec x p + parityVec (x + i.1) p
  | Sum.inr i =>
      if i.1 = 0 then
        parityVec (x + L - 1) p + parityVec (x + L) p
      else
        parityVec (x + L) p + parityVec (x + L + i.1) p

/-- Binary incidence of a touching-system row at a non-root vertex. -/
def touchingIncidence (L : ℕ)
    (v e : Sum (Fin L) (Fin L)) : F₂ :=
  match v, e with
  | Sum.inl j, Sum.inl i =>
      if j.1 = 0 then 1 else if i = j then 1 else 0
  | Sum.inl j, Sum.inr i =>
      if _hlast : j.1 + 1 = L then
        if i = ⟨0, Nat.zero_lt_of_lt j.2⟩ then 1 else 0
      else
        0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr j, Sum.inr i =>
      if j.1 = 0 then 1 else if i = j then 1 else 0

/--
The explicit boundary map is the incidence sum of the double tree.
-/
theorem touchingInteriorBoundary_apply_eq_sum_incidence
    {L : ℕ} (u : Sum (Fin L) (Fin L) → F₂)
    (v : Sum (Fin L) (Fin L)) :
    touchingInteriorBoundary L u v =
      ∑ e : Sum (Fin L) (Fin L),
        u e * touchingIncidence L v e := by
  classical
  rw [Fintype.sum_sum_type]
  cases v with
  | inl j =>
      by_cases hj0 : j.1 = 0
      · by_cases hjlast : j.1 + 1 = L
        · simp [touchingInteriorBoundary, touchingIncidence,
            hj0, hjlast, Finset.sum_add_distrib]
        · simp [touchingInteriorBoundary, touchingIncidence,
            hj0, hjlast, Finset.sum_add_distrib]
      · by_cases hjlast : j.1 + 1 = L
        · simp [touchingInteriorBoundary, touchingIncidence,
            hj0, hjlast]
        · simp [touchingInteriorBoundary, touchingIncidence,
            hj0, hjlast]
  | inr j =>
      by_cases hj0 : j.1 = 0
      · simp [touchingInteriorBoundary, touchingIncidence, hj0]
      · simp [touchingInteriorBoundary, touchingIncidence, hj0]

private theorem valueBit_single
    {M n p : ℕ} (hp : p.Prime) (hpM : p ≤ M) :
    valueBit
        (M := M)
        (Pi.single
          (⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩ : PrimeUpTo M) 1)
        n =
      parityVec n p := by
  classical
  let q : PrimeUpTo M :=
    ⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩
  rw [valueBit]
  rw [Fintype.sum_eq_single q]
  · simp [q]
  · intro r hrq
    have hrq' :
        r ≠ (⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩ : PrimeUpTo M) := by
      simpa only [q] using hrq
    simp [Pi.single_apply, hrq']

/-- Prime-coordinate equation satisfied by every touching-system relation. -/
private theorem touching_relation_prime_equation
    {M x L p : ℕ}
    (u : RelationSpace (touchingSystem M x L))
    (hp : p.Prime) (hpM : p ≤ M) :
    ∑ s : Sum (Fin L) (Fin L),
        (u : Sum (Fin L) (Fin L) → F₂) s *
          touchingEdgeParity x L p s =
      0 := by
  classical
  let q : PrimeUpTo M :=
    ⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩
  let ω : SampleSpace M := Pi.single q 1
  have hrel :
      relationFunctional
          (touchingSystem M x L)
          (u : Sum (Fin L) (Fin L) → F₂) ω =
        0 := by
    have hu :
        relationMap (touchingSystem M x L)
            (u : Sum (Fin L) (Fin L) → F₂) =
          0 :=
      LinearMap.mem_ker.mp u.2
    have huω := DFunLike.congr_fun hu ω
    change
      relationFunctional
          (touchingSystem M x L)
          (u : Sum (Fin L) (Fin L) → F₂) ω =
        0 at huω
    exact huω
  rw [relationFunctional_apply] at hrel
  change
    (∑ s : Sum (Fin L) (Fin L),
      (u : Sum (Fin L) (Fin L) → F₂) s *
        touchingSystem M x L ω s) = 0 at hrel
  calc
    ∑ s : Sum (Fin L) (Fin L),
        (u : Sum (Fin L) (Fin L) → F₂) s *
          touchingEdgeParity x L p s =
        ∑ s : Sum (Fin L) (Fin L),
          (u : Sum (Fin L) (Fin L) → F₂) s *
            touchingSystem M x L ω s := by
          apply Finset.sum_congr rfl
          intro s _hs
          congr 1
          cases s with
          | inl i =>
              simp only [touchingEdgeParity,
                touchingSystem_apply_inl, startSystem_apply]
              dsimp only [ω, q]
              simp_rw [valueBit_single hp hpM]
          | inr i =>
              simp only [touchingEdgeParity,
                touchingSystem_apply_inr, startSystem_apply]
              dsimp only [ω, q]
              simp_rw [valueBit_single hp hpM]
    _ = 0 := hrel

private theorem exists_large_prime_coordinate_of_not_hDefective
    {H n : ℕ} (h : ¬DefectivePredicate.HDefective H n) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ parityVec n p ≠ 0 := by
  simp only [DefectivePredicate.HDefective] at h
  push Not at h
  exact h

/--
If `p` divides one natural number but their distance is strictly below `p`,
then it cannot divide a distinct second number.
-/
private theorem not_dvd_of_dvd_and_dist_lt
    {a b p : ℕ} (hpa : p ∣ a) (hab : a ≠ b)
    (hdist : Nat.dist a b < p) :
    ¬p ∣ b := by
  intro hpb
  obtain ⟨ka, hka⟩ := hpa
  obtain ⟨kb, hkb⟩ := hpb
  have hpdist : p ∣ Nat.dist a b := by
    refine ⟨Nat.dist ka kb, ?_⟩
    calc
      Nat.dist a b = Nat.dist (p * ka) (p * kb) := by
        rw [hka, hkb]
      _ = p * Nat.dist ka kb := Nat.dist_mul_left p ka kb
  have hpos : 0 < Nat.dist a b := Nat.dist_pos_of_ne hab
  have hple : p ≤ Nat.dist a b := Nat.le_of_dvd hpos hpdist
  omega

/--
A nonzero parity coordinate above `2L` is private at its vertex throughout
the complete double-start tree, including the omitted root `x-1`.
-/
private theorem private_prime_on_touching_vertices
    {x L p : ℕ} (hx : 2 ≤ x) (hpL : 2 * L < p)
    {s : Sum (Fin L) (Fin L)}
    (hsp : parityVec (touchingVertexLabel x L s) p ≠ 0) :
    parityVec (x - 1) p = 0 ∧
      ∀ t : Sum (Fin L) (Fin L), t ≠ s →
        parityVec (touchingVertexLabel x L t) p = 0 := by
  have hpFactor :
      (touchingVertexLabel x L s).factorization p ≠ 0 := by
    intro hz
    apply hsp
    rw [parityVec_apply, hz]
    rfl
  have hpDvd : p ∣ touchingVertexLabel x L s := by
    by_contra hnot
    exact hpFactor (Nat.factorization_eq_zero_of_not_dvd hnot)
  have hrootNe : touchingVertexLabel x L s ≠ x - 1 := by
    cases s with
    | inl i =>
        simp only [touchingVertexLabel]
        omega
    | inr i =>
        simp only [touchingVertexLabel]
        omega
  have hrootDist :
      Nat.dist (touchingVertexLabel x L s) (x - 1) < p := by
    cases s with
    | inl i =>
        simp only [touchingVertexLabel, Nat.dist]
        have hi := i.2
        omega
    | inr i =>
        simp only [touchingVertexLabel, Nat.dist]
        have hi := i.2
        omega
  have hpRoot : ¬p ∣ x - 1 :=
    not_dvd_of_dvd_and_dist_lt hpDvd hrootNe hrootDist
  constructor
  · rw [parityVec_apply,
      Nat.factorization_eq_zero_of_not_dvd hpRoot]
    rfl
  · intro t hts
    have hlabelNe :
        touchingVertexLabel x L s ≠ touchingVertexLabel x L t := by
      intro h
      exact hts
        ((touchingVertexLabel_injective x L h).symm)
    have hdist :
        Nat.dist
            (touchingVertexLabel x L s)
            (touchingVertexLabel x L t) <
          p := by
      cases s with
      | inl i =>
          cases t with
          | inl j =>
              simp only [touchingVertexLabel, Nat.dist]
              have hi := i.2
              have hj := j.2
              omega
          | inr j =>
              simp only [touchingVertexLabel, Nat.dist]
              have hi := i.2
              have hj := j.2
              omega
      | inr i =>
          cases t with
          | inl j =>
              simp only [touchingVertexLabel, Nat.dist]
              have hi := i.2
              have hj := j.2
              omega
          | inr j =>
              simp only [touchingVertexLabel, Nat.dist]
              have hi := i.2
              have hj := j.2
              omega
    have hpOther : ¬p ∣ touchingVertexLabel x L t :=
      not_dvd_of_dvd_and_dist_lt hpDvd hlabelNe hdist
    rw [parityVec_apply,
      Nat.factorization_eq_zero_of_not_dvd hpOther]
    rfl

/--
At a coordinate private to `s`, every touching-row parity vector is the
incidence bit at `s`, multiplied by the nonzero coordinate at `s`.
-/
private theorem touchingEdgeParity_eq_incidence_mul
    {x L p : ℕ} (hL : 0 < L)
    {s : Sum (Fin L) (Fin L)}
    (hroot : parityVec (x - 1) p = 0)
    (hother :
      ∀ t : Sum (Fin L) (Fin L), t ≠ s →
        parityVec (touchingVertexLabel x L t) p = 0)
    (e : Sum (Fin L) (Fin L)) :
    touchingEdgeParity x L p e =
      touchingIncidence L s e *
        parityVec (touchingVertexLabel x L s) p := by
  let z : Fin L := ⟨0, hL⟩
  let last : Fin L := ⟨L - 1, by omega⟩
  cases s with
  | inl j =>
      change
        touchingEdgeParity x L p e =
          touchingIncidence L (Sum.inl j) e *
            parityVec (x + j.1) p
      have hleft (i : Fin L) :
          parityVec (x + i.1) p =
            if i = j then parityVec (x + j.1) p else 0 := by
        by_cases hij : i = j
        · subst i
          simp
        · have hne : Sum.inl i ≠ (Sum.inl j : Sum (Fin L) (Fin L)) := by
            intro h
            exact hij (Sum.inl.inj h)
          simpa [touchingVertexLabel, hij] using
            hother (Sum.inl i) hne
      have hright (i : Fin L) :
          parityVec (x + L + i.1) p = 0 := by
        simpa [touchingVertexLabel] using
          hother (Sum.inr i) (by simp)
      have hy : parityVec (x + L) p = 0 := by
        simpa [z] using hright z
      have hx :
          parityVec x p =
            if z = j then parityVec (x + j.1) p else 0 := by
        simpa [z] using hleft z
      have hbridge :
          parityVec (x + L - 1) p =
            if last = j then parityVec (x + j.1) p else 0 := by
        have hlabel : x + L - 1 = x + last.1 := by
          simp only [last]
          omega
        rw [hlabel]
        exact hleft last
      cases e with
      | inl i =>
          by_cases hj0 : j.1 = 0
          · have hjz : j = z := by
              apply Fin.ext
              simpa [z] using hj0
            subst j
            by_cases hi0 : i.1 = 0
            · have hiz : i = z := by
                apply Fin.ext
                simpa [z] using hi0
              subst i
              simp [touchingEdgeParity, touchingIncidence,
                hroot, z]
            · have hiz : i ≠ z := by
                intro h
                apply hi0
                simpa [z] using congrArg Fin.val h
              have hileaf : parityVec (x + i.1) p = 0 := by
                rw [hleft i, if_neg hiz]
              simp [touchingEdgeParity, touchingIncidence,
                hroot, hileaf, hi0, hiz, z]
          · have hjz : z ≠ j := by
              intro h
              apply hj0
              simpa [z] using (congrArg Fin.val h).symm
            by_cases hi0 : i.1 = 0
            · have hiz : i = z := by
                apply Fin.ext
                simpa [z] using hi0
              subst i
              simp [touchingEdgeParity, touchingIncidence,
                hroot, hx, hj0, hjz, z]
            · by_cases hij : i = j
              · subst i
                simp [touchingEdgeParity, touchingIncidence,
                  hroot, hx, hj0, hi0, hjz, z]
              · have hileaf : parityVec (x + i.1) p = 0 := by
                  rw [hleft i, if_neg hij]
                simp [touchingEdgeParity, touchingIncidence,
                  hroot, hx, hileaf, hj0, hi0, hij, hjz, z]
      | inr i =>
          by_cases hjlast : j.1 + 1 = L
          · have hjEqLast : j = last := by
              apply Fin.ext
              simp only [last]
              omega
            subst j
            by_cases hi0 : i.1 = 0
            · have hiz : i = z := by
                apply Fin.ext
                simpa [z] using hi0
              subst i
              simp [touchingEdgeParity, touchingIncidence,
                hbridge, hy, hjlast, z, last]
            · have hiz : i ≠ z := by
                intro h
                apply hi0
                simpa [z] using congrArg Fin.val h
              simp [touchingEdgeParity, touchingIncidence,
                hy, hright, hi0, hiz, z, last]
          · have hlastj : last ≠ j := by
              intro h
              apply hjlast
              have hv := congrArg Fin.val h
              simp only [last] at hv
              omega
            by_cases hi0 : i.1 = 0
            · have hiz : i = z := by
                apply Fin.ext
                simpa [z] using hi0
              subst i
              simp [touchingEdgeParity, touchingIncidence,
                hbridge, hy, hjlast, hlastj, z, last]
            · simp [touchingEdgeParity, touchingIncidence,
                hy, hright, hjlast, hlastj, hi0, z, last]
  | inr j =>
      change
        touchingEdgeParity x L p e =
          touchingIncidence L (Sum.inr j) e *
            parityVec (x + L + j.1) p
      have hleft (i : Fin L) :
          parityVec (x + i.1) p = 0 := by
        simpa [touchingVertexLabel] using
          hother (Sum.inl i) (by simp)
      have hright (i : Fin L) :
          parityVec (x + L + i.1) p =
            if i = j then parityVec (x + L + j.1) p else 0 := by
        by_cases hij : i = j
        · subst i
          simp
        · have hne : Sum.inr i ≠ (Sum.inr j : Sum (Fin L) (Fin L)) := by
            intro h
            exact hij (Sum.inr.inj h)
          simpa [touchingVertexLabel, hij] using
            hother (Sum.inr i) hne
      have hx : parityVec x p = 0 := by
        simpa [z] using hleft z
      have hbridge : parityVec (x + L - 1) p = 0 := by
        have hlabel : x + L - 1 = x + last.1 := by
          simp only [last]
          omega
        rw [hlabel]
        exact hleft last
      have hcenter :
          parityVec (x + L) p =
            if z = j then parityVec (x + L + j.1) p else 0 := by
        simpa [z] using hright z
      cases e with
      | inl i =>
          by_cases hi0 : i.1 = 0
          · simp [touchingEdgeParity, touchingIncidence,
              hroot, hx, hleft, hi0]
          · simp [touchingEdgeParity, touchingIncidence,
              hx, hleft, hi0]
      | inr i =>
          by_cases hj0 : j.1 = 0
          · have hjz : j = z := by
              apply Fin.ext
              simpa [z] using hj0
            subst j
            by_cases hi0 : i.1 = 0
            · have hiz : i = z := by
                apply Fin.ext
                simpa [z] using hi0
              subst i
              simp [touchingEdgeParity, touchingIncidence,
                hbridge, z]
            · have hiz : i ≠ z := by
                intro h
                apply hi0
                simpa [z] using congrArg Fin.val h
              have hileaf : parityVec (x + L + i.1) p = 0 := by
                rw [hright i, if_neg hiz]
              simp [touchingEdgeParity, touchingIncidence,
                hileaf, hi0, hiz, z]
          · have hjz : z ≠ j := by
              intro h
              apply hj0
              simpa [z] using (congrArg Fin.val h).symm
            by_cases hi0 : i.1 = 0
            · have hiz : i = z := by
                apply Fin.ext
                simpa [z] using hi0
              subst i
              simp [touchingEdgeParity, touchingIncidence,
                hbridge, hcenter, hj0, hjz, z]
            · by_cases hij : i = j
              · subst i
                simp [touchingEdgeParity, touchingIncidence,
                  hcenter, hj0, hi0, hjz, z]
              · have hileaf : parityVec (x + L + i.1) p = 0 := by
                  rw [hright i, if_neg hij]
                simp [touchingEdgeParity, touchingIncidence,
                  hcenter, hileaf, hj0, hi0, hij, hjz, z]

/--
The boundary of a touching-system relation vanishes at every non-defective
non-root vertex.
-/
theorem touchingInteriorBoundary_eq_zero_of_not_hDefective
    {N x L : ℕ} (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hL : 0 < L)
    (u : RelationSpace
      (touchingSystem (dyadicCutoff N (2 * L)) x L))
    (s : Sum (Fin L) (Fin L))
    (hs :
      ¬DefectivePredicate.HDefective
        (2 * L) (touchingVertexLabel x L s)) :
    touchingInteriorBoundary L
        (u : Sum (Fin L) (Fin L) → F₂) s =
      0 := by
  obtain ⟨p, hp, hpL, hsp⟩ :=
    exists_large_prime_coordinate_of_not_hDefective hs
  have hx2 : 2 ≤ x := two_le_of_mem_dyadicBlock hN hx
  have hpFactor :
      (touchingVertexLabel x L s).factorization p ≠ 0 := by
    intro hz
    apply hsp
    rw [parityVec_apply, hz]
    rfl
  have hpDvd : p ∣ touchingVertexLabel x L s := by
    by_contra hnot
    exact hpFactor (Nat.factorization_eq_zero_of_not_dvd hnot)
  have hpLeVertex : p ≤ touchingVertexLabel x L s :=
    Nat.le_of_dvd (by
      cases s with
      | inl i =>
          simp only [touchingVertexLabel]
          omega
      | inr i =>
          simp only [touchingVertexLabel]
          omega) hpDvd
  have hxUpper :
      x < 2 * N :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
  have hvertexCutoff :
      touchingVertexLabel x L s ≤ dyadicCutoff N (2 * L) := by
    unfold dyadicCutoff
    cases s with
    | inl i =>
        simp only [touchingVertexLabel]
        have hi := i.2
        omega
    | inr i =>
        simp only [touchingVertexLabel]
        have hi := i.2
        omega
  have hpCutoff : p ≤ dyadicCutoff N (2 * L) :=
    hpLeVertex.trans hvertexCutoff
  obtain ⟨hroot, hother⟩ :=
    private_prime_on_touching_vertices hx2 hpL hsp
  have heq :=
    touching_relation_prime_equation u hp hpCutoff
  have hedge (e : Sum (Fin L) (Fin L)) :
      touchingEdgeParity x L p e =
        touchingIncidence L s e *
          parityVec (touchingVertexLabel x L s) p :=
    touchingEdgeParity_eq_incidence_mul hL hroot hother e
  have hmul :
      touchingInteriorBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) s *
          parityVec (touchingVertexLabel x L s) p =
        0 := by
    calc
      touchingInteriorBoundary L
            (u : Sum (Fin L) (Fin L) → F₂) s *
            parityVec (touchingVertexLabel x L s) p =
          (∑ e : Sum (Fin L) (Fin L),
              (u : Sum (Fin L) (Fin L) → F₂) e *
                touchingIncidence L s e) *
            parityVec (touchingVertexLabel x L s) p := by
              rw [touchingInteriorBoundary_apply_eq_sum_incidence]
      _ = ∑ e : Sum (Fin L) (Fin L),
            (u : Sum (Fin L) (Fin L) → F₂) e *
              (touchingIncidence L s e *
                parityVec (touchingVertexLabel x L s) p) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro e _he
            ring
      _ = ∑ e : Sum (Fin L) (Fin L),
            (u : Sum (Fin L) (Fin L) → F₂) e *
              touchingEdgeParity x L p e := by
            apply Finset.sum_congr rfl
            intro e _he
            rw [hedge e]
      _ = 0 := heq
  exact (mul_eq_zero.mp hmul).resolve_right hsp

/-- Defective non-root vertices of the double start tree. -/
noncomputable def touchingDefectIndices
    (x L : ℕ) : Finset (Sum (Fin L) (Fin L)) := by
  classical
  exact Finset.univ.filter
    (fun s =>
      DefectivePredicate.HDefective
        (2 * L) (touchingVertexLabel x L s))

/-- Restriction of the double-tree boundary to its defective vertices. -/
def touchingDefectRestriction
    (N x L : ℕ) :
    RelationSpace
        (touchingSystem (dyadicCutoff N (2 * L)) x L) →ₗ[F₂]
      ((s : ↥(touchingDefectIndices x L)) → F₂) where
  toFun u s :=
    touchingInteriorBoundary L
      (u : Sum (Fin L) (Fin L) → F₂) s.1
  map_add' u v := by
    funext s
    change
      touchingInteriorBoundary L
          (((u + v :
            RelationSpace
              (touchingSystem (dyadicCutoff N (2 * L)) x L)) :
                Sum (Fin L) (Fin L) → F₂)) s.1 =
        touchingInteriorBoundary L
            (u : Sum (Fin L) (Fin L) → F₂) s.1 +
          touchingInteriorBoundary L
            (v : Sum (Fin L) (Fin L) → F₂) s.1
    rw [show
      ((u + v :
        RelationSpace
          (touchingSystem (dyadicCutoff N (2 * L)) x L)) :
            Sum (Fin L) (Fin L) → F₂) =
        (u : Sum (Fin L) (Fin L) → F₂) +
          (v : Sum (Fin L) (Fin L) → F₂) by rfl,
      LinearMap.map_add]
    rfl
  map_smul' c u := by
    funext s
    change
      touchingInteriorBoundary L
          (((c • u :
            RelationSpace
              (touchingSystem (dyadicCutoff N (2 * L)) x L)) :
                Sum (Fin L) (Fin L) → F₂)) s.1 =
        c • touchingInteriorBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) s.1
    rw [show
      ((c • u :
        RelationSpace
          (touchingSystem (dyadicCutoff N (2 * L)) x L)) :
            Sum (Fin L) (Fin L) → F₂) =
        c • (u : Sum (Fin L) (Fin L) → F₂) by rfl,
      LinearMap.map_smul]
    rfl

/--
Relations between the touching rows are determined by boundary coordinates
at defective vertices.
-/
theorem touchingDefectRestriction_injective
    {N x L : ℕ} (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hL : 0 < L) :
    Function.Injective (touchingDefectRestriction N x L) := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro u hu
  have hrestrict : touchingDefectRestriction N x L u = 0 :=
    LinearMap.mem_ker.mp hu
  have hboundary :
      touchingInteriorBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) =
        0 := by
    funext s
    by_cases hs :
        DefectivePredicate.HDefective
          (2 * L) (touchingVertexLabel x L s)
    · let sd : ↥(touchingDefectIndices x L) :=
        ⟨s, by simp [touchingDefectIndices, hs]⟩
      have hsZero := congrFun hrestrict sd
      simpa [touchingDefectRestriction, sd] using hsZero
    · exact touchingInteriorBoundary_eq_zero_of_not_hDefective
        hN hx hL u s hs
  have huZero :
      (u : Sum (Fin L) (Fin L) → F₂) = 0 :=
    touchingInteriorBoundary_injective hL
      (by simpa using hboundary)
  apply Subtype.ext
  exact huZero

/--
The defective vertices of the double tree inject into the concrete interval
defect set on `[x, x + 2L]`.
-/
theorem card_touchingDefectIndices_le
    {x L : ℕ} (hx : 2 ≤ x) :
    (touchingDefectIndices x L).card ≤
      (IntervalDefectBound.defectsInInterval (2 * L) x).card := by
  classical
  let label : Sum (Fin L) (Fin L) → ℕ :=
    touchingVertexLabel x L
  have hlabel : Function.Injective label :=
    touchingVertexLabel_injective x L
  have hsubset :
      (touchingDefectIndices x L).image label ⊆
        IntervalDefectBound.defectsInInterval (2 * L) x := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨s, hs, hn⟩ := hn
    dsimp only [label] at hn
    subst n
    have hsDefective :
        DefectivePredicate.HDefective
          (2 * L) (touchingVertexLabel x L s) := by
      simpa [touchingDefectIndices] using hs
    have hnNe : touchingVertexLabel x L s ≠ 0 := by
      cases s with
      | inl i =>
          simp only [touchingVertexLabel]
          omega
      | inr i =>
          simp only [touchingVertexLabel]
          omega
    let rep : DefectCounting.HDefectRepresentation
        (2 * L) (touchingVertexLabel x L s) :=
      Classical.choice
        ((DefectivePredicate.hDefective_iff_exists_HDefectRepresentation
          hnNe).mp hsDefective)
    rw [IntervalDefectBound.mem_defectsInInterval]
    constructor
    · apply DefectCounting.mem_defectValues_of_HDefectRepresentation rep
      cases s with
      | inl i =>
          simp only [touchingVertexLabel]
          have hi := i.2
          omega
      | inr i =>
          simp only [touchingVertexLabel]
          have hi := i.2
          omega
    · constructor
      · cases s with
        | inl i =>
            simp only [touchingVertexLabel]
            omega
        | inr i =>
            simp only [touchingVertexLabel]
            omega
      · cases s with
        | inl i =>
            simp only [touchingVertexLabel]
            have hi := i.2
            omega
        | inr i =>
            simp only [touchingVertexLabel]
            have hi := i.2
            omega
  calc
    (touchingDefectIndices x L).card =
        ((touchingDefectIndices x L).image label).card := by
      symm
      exact Finset.card_image_of_injective _ hlabel
    _ ≤ (IntervalDefectBound.defectsInInterval (2 * L) x).card :=
      Finset.card_le_card hsubset

/--
Structural rank estimate for two touching starts, in the exact form needed
for Lemma 3.4(ii).
-/
theorem relationRho_touchingSystem_le_card_defectsInInterval
    {N x L : ℕ} (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hL : 0 < L) :
    relationRho
        (touchingSystem (dyadicCutoff N (2 * L)) x L) ≤
      (IntervalDefectBound.defectsInInterval (2 * L) x).card := by
  have hrank :
      relationRho
          (touchingSystem (dyadicCutoff N (2 * L)) x L) ≤
        (touchingDefectIndices x L).card := by
    unfold relationRho
    calc
      Module.finrank F₂
          (RelationSpace
            (touchingSystem (dyadicCutoff N (2 * L)) x L)) ≤
          Module.finrank F₂
            ((s : ↥(touchingDefectIndices x L)) → F₂) :=
        LinearMap.finrank_le_finrank_of_injective
          (touchingDefectRestriction_injective hN hx hL)
      _ = (touchingDefectIndices x L).card := by
        rw [Module.finrank_fintype_fun_eq_card]
        simp
  exact hrank.trans
    (card_touchingDefectIndices_le
      (two_le_of_mem_dyadicBlock hN hx))

end

end TouchingDefectRank
end Affine
end PaperC
