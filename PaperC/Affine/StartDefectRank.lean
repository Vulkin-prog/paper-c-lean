import PaperC.Affine.Normalization
import PaperC.Affine.StartSystem
import PaperC.Arithmetic.DefectivePredicate
import PaperC.Coding.IntervalDefectBound
import PaperC.LinearAlgebra.PrivatePivots
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

set_option maxHeartbeats 800000

/-!
# The start-system relation defect is supported on defective vertices

The rows of `startSystem M x L` are the edges of the star with centre `x`,
left root `x - 1`, and remaining leaves `x + i` for `0 < i < L`.
For a row coefficient vector `u`, its boundary on the non-root vertices is

* `∑ i, u i` at the centre `x`;
* `u i` at the leaf `x + i`, for `i > 0`.

This boundary map is injective.  If `u` is a relation between the start rows,
then its boundary vanishes at every non-`(L+1)`-defective vertex: an odd prime
coordinate above `L+1` is private inside the start window.  Restricting the
boundary to defective vertices is consequently injective on the relation
space, which bounds `relationRho` by the number of local defects.
-/

namespace PaperC
namespace Affine
namespace StartDefectRank

open scoped BigOperators

noncomputable section

/--
The boundary coordinates of a coefficient vector on the non-root vertices
`x, x+1, ..., x+L-1` of the start star.  The definition is independent of
`x`, so only `L` occurs in the map.
-/
def startInteriorBoundary (L : ℕ) :
    (Fin L → F₂) →ₗ[F₂] (Fin L → F₂) where
  toFun u j := if j.1 = 0 then ∑ i : Fin L, u i else u j
  map_add' u v := by
    funext j
    by_cases hj : j.1 = 0
    · simp [hj, Finset.sum_add_distrib]
    · simp [hj]
  map_smul' c u := by
    funext j
    by_cases hj : j.1 = 0
    · simp only [hj, if_pos, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      rw [Finset.mul_sum]
    · simp [hj]

@[simp]
theorem startInteriorBoundary_apply_zero
    {L : ℕ} (hL : 0 < L) (u : Fin L → F₂) :
    startInteriorBoundary L u ⟨0, hL⟩ = ∑ i : Fin L, u i := by
  simp [startInteriorBoundary]

theorem startInteriorBoundary_apply_ne_zero
    {L : ℕ} (u : Fin L → F₂) (j : Fin L) (hj : j.1 ≠ 0) :
    startInteriorBoundary L u j = u j := by
  simp [startInteriorBoundary, hj]

/-- The non-root boundary coordinates determine all start-edge coefficients. -/
theorem startInteriorBoundary_injective
    {L : ℕ} (hL : 0 < L) :
    Function.Injective (startInteriorBoundary L) := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro u hu
  have hboundary : startInteriorBoundary L u = 0 :=
    LinearMap.mem_ker.mp hu
  let z : Fin L := ⟨0, hL⟩
  have hsum : ∑ i : Fin L, u i = 0 := by
    have hz := congrFun hboundary z
    simpa [z, startInteriorBoundary] using hz
  have hnonzero : ∀ i : Fin L, i.1 ≠ 0 → u i = 0 := by
    intro i hi
    have hi' := congrFun hboundary i
    simpa [startInteriorBoundary, hi] using hi'
  have hsum_single : ∑ i : Fin L, u i = u z := by
    classical
    apply Finset.sum_eq_single z
    · intro i _hi hiz
      apply hnonzero i
      intro hi0
      apply hiz
      apply Fin.ext
      simpa [z] using hi0
    · simp
  have huz : u z = 0 := by
    rw [← hsum_single]
    exact hsum
  funext i
  by_cases hi : i.1 = 0
  · have hiz : i = z := by
      apply Fin.ext
      simpa [z] using hi
    simpa [hiz] using huz
  · exact hnonzero i hi

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
    have hqr : q ≠ r := Ne.symm hrq
    have hqr' :
        (⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩ : PrimeUpTo M) ≠ r := by
      exact hqr
    have hrq' :
        r ≠ (⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩ : PrimeUpTo M) := by
      exact hrq
    simp [Pi.single_apply, hrq']

/--
Every relation between start rows gives, at each represented prime coordinate,
the corresponding parity-vector equation.
-/
private theorem relation_prime_equation
    {M x L p : ℕ}
    (u : RelationSpace (startSystem M x L))
    (hp : p.Prime) (hpM : p ≤ M) :
    ∑ i : Fin L, (u : Fin L → F₂) i *
        (if i.1 = 0 then
          parityVec (x - 1) p + parityVec x p
        else
          parityVec x p + parityVec (x + i.1) p) =
      0 := by
  classical
  let q : PrimeUpTo M :=
    ⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩
  let ω : SampleSpace M := Pi.single q 1
  have hrel :
      relationFunctional (startSystem M x L) (u : Fin L → F₂) ω = 0 := by
    have hu :
        relationMap (startSystem M x L) (u : Fin L → F₂) = 0 :=
      LinearMap.mem_ker.mp u.2
    have huω := DFunLike.congr_fun hu ω
    change
      relationFunctional (startSystem M x L) (u : Fin L → F₂) ω =
        0 at huω
    exact huω
  rw [relationFunctional_apply] at hrel
  dsimp only [ω, q] at hrel
  simp only [dotProduct, startSystem_apply] at hrel
  simp_rw [valueBit_single hp hpM] at hrel
  exact hrel

private theorem exists_large_prime_coordinate_of_not_hDefective
    {H n : ℕ} (h : ¬DefectivePredicate.HDefective H n) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ parityVec n p ≠ 0 := by
  simp only [DefectivePredicate.HDefective] at h
  push Not at h
  exact h

/--
A prime coordinate above the diameter of the start window, nonzero at
`x+j`, vanishes at every other non-root start vertex and at the left root.
-/
private theorem private_prime_on_start_vertices
    {x L p : ℕ} (hx : 2 ≤ x) (hpL : L + 1 < p)
    {j : Fin L} (hjp : parityVec (x + j.1) p ≠ 0) :
    parityVec (x - 1) p = 0 ∧
      ∀ k : Fin L, k ≠ j → parityVec (x + k.1) p = 0 := by
  have hpFactor :
      (x + j.1).factorization p ≠ 0 := by
    intro hz
    apply hjp
    rw [parityVec_apply, hz]
    rfl
  have hpDvd : p ∣ x + j.1 := by
    by_contra hnot
    exact hpFactor (Nat.factorization_eq_zero_of_not_dvd hnot)
  have hrootNe : x + j.1 ≠ x - 1 := by omega
  have hrootDist : Nat.dist (x + j.1) (x - 1) < L + 1 := by
    simp only [Nat.dist]
    omega
  have hpRoot : ¬p ∣ x - 1 :=
    PrivatePivots.not_dvd_of_dvd_and_dist_lt
      hpDvd hrootNe hpL hrootDist
  constructor
  · rw [parityVec_apply,
      Nat.factorization_eq_zero_of_not_dvd hpRoot]
    rfl
  · intro k hkj
    have hvertexNe : x + j.1 ≠ x + k.1 := by
      intro h
      apply hkj
      apply Fin.ext
      omega
    have hdist : Nat.dist (x + j.1) (x + k.1) < L + 1 := by
      rw [Nat.dist_add_add_left]
      simp only [Nat.dist]
      have hjlt := j.2
      have hklt := k.2
      omega
    have hpOther : ¬p ∣ x + k.1 :=
      PrivatePivots.not_dvd_of_dvd_and_dist_lt
        hpDvd hvertexNe hpL hdist
    rw [parityVec_apply,
      Nat.factorization_eq_zero_of_not_dvd hpOther]
    rfl

/--
The boundary of a start-row relation vanishes at every non-defective
non-root vertex.
-/
theorem startInteriorBoundary_eq_zero_of_not_hDefective
    {N x L : ℕ} (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (u : RelationSpace (startSystem (dyadicCutoff N L) x L))
    (j : Fin L)
    (hj :
      ¬DefectivePredicate.HDefective (L + 1) (x + j.1)) :
    startInteriorBoundary L (u : Fin L → F₂) j = 0 := by
  obtain ⟨p, hp, hpL, hjp⟩ :=
    exists_large_prime_coordinate_of_not_hDefective hj
  have hx2 : 2 ≤ x := two_le_of_mem_dyadicBlock hN hx
  have hpDvd : p ∣ x + j.1 := by
    have hpFactor :
        (x + j.1).factorization p ≠ 0 := by
      intro hz
      apply hjp
      rw [parityVec_apply, hz]
      rfl
    by_contra hnot
    exact hpFactor (Nat.factorization_eq_zero_of_not_dvd hnot)
  have hpLeVertex : p ≤ x + j.1 :=
    Nat.le_of_dvd (by omega) hpDvd
  have hpCutoff : p ≤ dyadicCutoff N L := by
    have hxUpper :
        x < 2 * N :=
      (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
    unfold dyadicCutoff
    exact hpLeVertex.trans (by omega)
  have hprivate :=
    private_prime_on_start_vertices hx2 hpL hjp
  have heq :=
    relation_prime_equation u hp hpCutoff
  by_cases hj0 : j.1 = 0
  · have hjEq : j = ⟨0, by omega⟩ := by
      apply Fin.ext
      simpa using hj0
    have hcenter : parityVec x p ≠ 0 := by
      simpa [hj0] using hjp
    have hroot : parityVec (x - 1) p = 0 := hprivate.1
    have hleaves :
        ∀ i : Fin L, i.1 ≠ 0 →
          parityVec (x + i.1) p = 0 := by
      intro i hi
      exact hprivate.2 i (by
        intro hij
        subst i
        exact hi hj0)
    have heq' :
        (∑ i : Fin L, (u : Fin L → F₂) i) *
            parityVec x p =
          0 := by
      calc
        (∑ i : Fin L, (u : Fin L → F₂) i) *
              parityVec x p =
            ∑ i : Fin L,
              (u : Fin L → F₂) i * parityVec x p := by
              rw [Finset.sum_mul]
        _ = ∑ i : Fin L, (u : Fin L → F₂) i *
              (if i.1 = 0 then
                parityVec (x - 1) p + parityVec x p
              else
                parityVec x p + parityVec (x + i.1) p) := by
              apply Finset.sum_congr rfl
              intro i _hi
              by_cases hi0 : i.1 = 0
              · simp [hi0, hroot]
              · simp [hi0, hleaves i hi0]
        _ = 0 := heq
    have hsum : ∑ i : Fin L, (u : Fin L → F₂) i = 0 :=
      (mul_eq_zero.mp heq').resolve_right hcenter
    simpa [startInteriorBoundary, hj0] using hsum
  · have hjPrivate :
        ∀ k : Fin L, k ≠ j →
          parityVec (x + k.1) p = 0 :=
      hprivate.2
    have hcenter : parityVec x p = 0 := by
      have hjNeCenter : j ≠ ⟨0, by omega⟩ := by
        intro h
        apply hj0
        simpa using congrArg Fin.val h
      simpa using
        hjPrivate (⟨0, by omega⟩ : Fin L) (Ne.symm hjNeCenter)
    have hroot : parityVec (x - 1) p = 0 := hprivate.1
    have heq' :
        (u : Fin L → F₂) j * parityVec (x + j.1) p = 0 := by
      calc
        (u : Fin L → F₂) j * parityVec (x + j.1) p =
            ∑ i : Fin L, (u : Fin L → F₂) i *
              (if i = j then parityVec (x + j.1) p else 0) := by
              symm
              simp
        _ = ∑ i : Fin L, (u : Fin L → F₂) i *
              (if i.1 = 0 then
                parityVec (x - 1) p + parityVec x p
              else
                parityVec x p + parityVec (x + i.1) p) := by
              apply Finset.sum_congr rfl
              intro i _hi
              by_cases hij : i = j
              · subst i
                simp [hj0, hcenter]
              · by_cases hi0 : i.1 = 0
                · simp [hi0, hroot, hcenter, hij]
                · simp [hi0, hcenter, hij, hjPrivate i hij]
        _ = 0 := heq
    have huj : (u : Fin L → F₂) j = 0 :=
      (mul_eq_zero.mp heq').resolve_right hjp
    simpa [startInteriorBoundary, hj0] using huj

/-- Indices of defective non-root vertices in the start star. -/
noncomputable def startDefectIndices (x L : ℕ) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter
    (fun j : Fin L =>
      DefectivePredicate.HDefective (L + 1) (x + j.1))

/-- Restriction of the interior boundary to defective vertices. -/
def startDefectRestriction
    (N x L : ℕ) :
    RelationSpace (startSystem (dyadicCutoff N L) x L) →ₗ[F₂]
      ((j : ↥(startDefectIndices x L)) → F₂) where
  toFun u j :=
    startInteriorBoundary L (u : Fin L → F₂) j.1
  map_add' u v := by
    funext j
    change
      startInteriorBoundary L
          (((u + v :
            RelationSpace (startSystem (dyadicCutoff N L) x L)) :
              Fin L → F₂)) j.1 =
        startInteriorBoundary L (u : Fin L → F₂) j.1 +
          startInteriorBoundary L (v : Fin L → F₂) j.1
    rw [show
      ((u + v :
        RelationSpace (startSystem (dyadicCutoff N L) x L)) :
          Fin L → F₂) =
        (u : Fin L → F₂) + (v : Fin L → F₂) by rfl,
      LinearMap.map_add]
    rfl
  map_smul' c u := by
    funext j
    change
      startInteriorBoundary L
          (((c • u :
            RelationSpace (startSystem (dyadicCutoff N L) x L)) :
              Fin L → F₂)) j.1 =
        c • startInteriorBoundary L (u : Fin L → F₂) j.1
    rw [show
      ((c • u :
        RelationSpace (startSystem (dyadicCutoff N L) x L)) :
          Fin L → F₂) =
        c • (u : Fin L → F₂) by rfl,
      LinearMap.map_smul]
    rfl

/--
Relations are determined by their boundary values at defective non-root
vertices.
-/
theorem startDefectRestriction_injective
    {N x L : ℕ} (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hL : 0 < L) :
    Function.Injective (startDefectRestriction N x L) := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro u hu
  have hrestrict : startDefectRestriction N x L u = 0 :=
    LinearMap.mem_ker.mp hu
  have hboundary :
      startInteriorBoundary L (u : Fin L → F₂) = 0 := by
    funext j
    by_cases hj :
        DefectivePredicate.HDefective (L + 1) (x + j.1)
    · let jd : ↥(startDefectIndices x L) :=
        ⟨j, by simp [startDefectIndices, hj]⟩
      have hjzero := congrFun hrestrict jd
      simpa [startDefectRestriction, jd] using hjzero
    · exact startInteriorBoundary_eq_zero_of_not_hDefective
        hN hx u j hj
  have huZero : (u : Fin L → F₂) = 0 :=
    startInteriorBoundary_injective hL
      (by simpa using hboundary)
  apply Subtype.ext
  exact huZero

/--
The number of defective non-root start vertices is bounded by the concrete
interval defect set used in Proposition 3.2.
-/
theorem card_startDefectIndices_le
    {x L : ℕ} (hx : 2 ≤ x) :
    (startDefectIndices x L).card ≤
      (IntervalDefectBound.defectsInInterval (L + 1) x).card := by
  classical
  let label : Fin L → ℕ := fun j => x + j.1
  have hlabel : Function.Injective label := by
    intro i j hij
    apply Fin.ext
    dsimp only [label] at hij
    omega
  have hsubset :
      (startDefectIndices x L).image label ⊆
        IntervalDefectBound.defectsInInterval (L + 1) x := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨j, hj, hn⟩ := hn
    dsimp only [label] at hn
    subst n
    have hjDefective :
        DefectivePredicate.HDefective (L + 1) (x + j.1) := by
      simpa [startDefectIndices] using hj
    have hnNe : x + j.1 ≠ 0 := by omega
    let rep : DefectCounting.HDefectRepresentation
        (L + 1) (x + j.1) :=
      Classical.choice
        ((DefectivePredicate.hDefective_iff_exists_HDefectRepresentation
          hnNe).mp hjDefective)
    rw [IntervalDefectBound.mem_defectsInInterval]
    constructor
    · apply DefectCounting.mem_defectValues_of_HDefectRepresentation rep
      omega
    · constructor <;> omega
  calc
    (startDefectIndices x L).card =
        ((startDefectIndices x L).image label).card := by
      symm
      exact Finset.card_image_of_injective _ hlabel
    _ ≤ (IntervalDefectBound.defectsInInterval (L + 1) x).card :=
      Finset.card_le_card hsubset

/--
The structural rank estimate required by Corollary 3.3: the relation defect
of the start system is at most the number of `(L+1)`-defective values in the
local interval.
-/
theorem relationRho_startSystem_le_card_defectsInInterval
    {N x L : ℕ} (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hL : 0 < L) :
    relationRho (startSystem (dyadicCutoff N L) x L) ≤
      (IntervalDefectBound.defectsInInterval (L + 1) x).card := by
  have hrank :
      relationRho (startSystem (dyadicCutoff N L) x L) ≤
        (startDefectIndices x L).card := by
    unfold relationRho
    calc
      Module.finrank F₂
          (RelationSpace (startSystem (dyadicCutoff N L) x L)) ≤
          Module.finrank F₂
            ((j : ↥(startDefectIndices x L)) → F₂) :=
        LinearMap.finrank_le_finrank_of_injective
          (startDefectRestriction_injective hN hx hL)
      _ = (startDefectIndices x L).card := by
        rw [Module.finrank_fintype_fun_eq_card]
        simp
  exact hrank.trans
    (card_startDefectIndices_le (two_le_of_mem_dyadicBlock hN hx))

end

end StartDefectRank
end Affine
end PaperC
