import PaperC.Probability.SectionTwelveMoments
import Mathlib.LinearAlgebra.Pi

set_option maxHeartbeats 1800000

/-!
# Mixed-length affine systems

This file formalizes the finite affine core of Lemma 14.6.

For a row count `q ≥ 2`, an exact run based at `x` uses the same homogeneous
rows as `startSystem M x q`.  Its right-hand side is one at the left boundary
row and at the last row, and zero on the intervening constancy rows.  Two
possibly different row counts `q` and `r` are stacked in
`mixedLengthSystem`.

The first main theorem is the exact normalized identity

`P(K(x,q) ∩ K(y,r)) = 2^(-q-r) η 2^ρ`

in the finite prime-sign cylinder.  The second main theorem proves the
monotonicity assertion from Lemma 14.6: if `q,r ≤ Q`, zero-extension of row
coefficients embeds the mixed relation space into the relation space of the
two common length-`Q` systems.  In particular its dimension is no larger.

No arithmetic or asymptotic bridge is used here.
-/

namespace PaperC
namespace MixedLengthAffine

open Affine

noncomputable section

/-! ## One exact-length event -/

/--
Right-hand side of an exact-run system with `q` rows.

Row zero imposes the left sign change.  The last row imposes the right sign
change.  All rows strictly between them impose equality with the value at the
start.
-/
def exactLengthRhs (q : ℕ) : Fin q → F₂ :=
  fun i => if i.1 = 0 ∨ i.1 + 1 = q then 1 else 0

@[simp]
theorem exactLengthRhs_apply (q : ℕ) (i : Fin q) :
    exactLengthRhs q i =
      if i.1 = 0 ∨ i.1 + 1 = q then 1 else 0 :=
  rfl

/--
Bit-valued version of the exact-run event represented by `exactLengthRhs`.

For `q = L + e + 1`, its middle condition says that the values from `x`
through `x + L + e - 1` are constant, while the first and last equations give
the two sign changes in the statement of Lemma 14.6.
-/
def ExactLengthEvent (g : ℕ → F₂) (x q : ℕ) : Prop :=
  g (x - 1) + g x = 1 ∧
    (∀ j : ℕ, 0 < j → j + 1 < q → g x = g (x + j)) ∧
    g x + g (x + (q - 1)) = 1

/-- Finite-cylinder exact-run event. -/
def exactLengthAt {M : ℕ}
    (ω : SampleSpace M) (x q : ℕ) : Prop :=
  ExactLengthEvent (valueBit ω) x q

/--
For at least two rows, the exact-run event is exactly the affine fiber with
the last right-hand-side entry changed from zero to one.
-/
theorem startSystem_eq_exactLengthRhs_iff
    {M x q : ℕ} (ω : SampleSpace M) (hq : 2 ≤ q) :
    startSystem M x q ω = exactLengthRhs q ↔
      exactLengthAt ω x q := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hzero := congrFun h (⟨0, by omega⟩ : Fin q)
      simpa using hzero
    · intro j hj0 hjlast
      have hjq : j < q := by omega
      have hrow := congrFun h (⟨j, hjq⟩ : Fin q)
      have hsum :
          valueBit ω x + valueBit ω (x + j) = 0 := by
        simpa [Nat.ne_of_gt hj0, show j + 1 ≠ q by omega] using hrow
      exact (Affine.add_eq_zero_iff_eq _ _).mp hsum
    · have hlast :=
        congrFun h (⟨q - 1, by omega⟩ : Fin q)
      have hpred : q - 1 + 1 = q := by omega
      simpa [show q - 1 ≠ 0 by omega, hpred] using hlast
  · rintro ⟨hleft, hmiddle, hright⟩
    funext i
    by_cases hi0 : i.1 = 0
    · simpa [hi0] using hleft
    · by_cases hilast : i.1 + 1 = q
      · have hi : i.1 = q - 1 := by omega
        have hpred : q - 1 + 1 = q := by omega
        simpa [hi, show q - 1 ≠ 0 by omega, hpred] using hright
      · have hmiddle' :
          valueBit ω x = valueBit ω (x + i.1) :=
        hmiddle i.1 (Nat.zero_lt_of_ne_zero hi0) (by omega)
        have hsum :
            valueBit ω x + valueBit ω (x + i.1) = 0 :=
          (Affine.add_eq_zero_iff_eq _ _).mpr hmiddle'
        simpa [hi0, hilast] using hsum

/-! ## The mixed system and its affine identity -/

/-- One row of the stack with row counts `q` and `r`. -/
def mixedLengthRow (M x y q r : ℕ) :
    Sum (Fin q) (Fin r) → SampleSpace M →ₗ[F₂] F₂
  | Sum.inl i => startRow M x q i
  | Sum.inr i => startRow M y r i

/-- Stack of the homogeneous systems of two exact runs of mixed lengths. -/
def mixedLengthSystem (M x y q r : ℕ) :
    SampleSpace M →ₗ[F₂] (Sum (Fin q) (Fin r) → F₂) :=
  LinearMap.pi (mixedLengthRow M x y q r)

/-- Stack of the two exact-run right-hand sides. -/
def mixedLengthRhs (q r : ℕ) :
    Sum (Fin q) (Fin r) → F₂
  | Sum.inl i => exactLengthRhs q i
  | Sum.inr i => exactLengthRhs r i

@[simp]
theorem mixedLengthSystem_apply_inl
    (M x y q r : ℕ) (ω : SampleSpace M) (i : Fin q) :
    mixedLengthSystem M x y q r ω (Sum.inl i) =
      startSystem M x q ω i :=
  rfl

@[simp]
theorem mixedLengthSystem_apply_inr
    (M x y q r : ℕ) (ω : SampleSpace M) (i : Fin r) :
    mixedLengthSystem M x y q r ω (Sum.inr i) =
      startSystem M y r ω i :=
  rfl

@[simp]
theorem mixedLengthRhs_apply_inl
    (q r : ℕ) (i : Fin q) :
    mixedLengthRhs q r (Sum.inl i) = exactLengthRhs q i :=
  rfl

@[simp]
theorem mixedLengthRhs_apply_inr
    (q r : ℕ) (i : Fin r) :
    mixedLengthRhs q r (Sum.inr i) = exactLengthRhs r i :=
  rfl

/-- The mixed affine fiber is precisely the intersection of the two events. -/
theorem mixedLengthSystem_eq_rhs_iff
    {M x y q r : ℕ} (ω : SampleSpace M)
    (hq : 2 ≤ q) (hr : 2 ≤ r) :
    mixedLengthSystem M x y q r ω = mixedLengthRhs q r ↔
      exactLengthAt ω x q ∧ exactLengthAt ω y r := by
  rw [← startSystem_eq_exactLengthRhs_iff ω hq,
    ← startSystem_eq_exactLengthRhs_iff ω hr]
  constructor
  · intro h
    constructor
    · funext i
      exact congrFun h (Sum.inl i)
    · funext i
      exact congrFun h (Sum.inr i)
  · rintro ⟨hx, hy⟩
    funext i
    cases i with
    | inl i => exact congrFun hx i
    | inr i => exact congrFun hy i

/-- Uniform finite-cylinder probability of two mixed exact-run events. -/
def mixedExactLengthProbability
    (M x y q r : ℕ) : ℚ :=
  by
    classical
    exact uniformEventProbability (M := M)
      (fun ω => exactLengthAt ω x q ∧ exactLengthAt ω y r)

/-- Event probability equals the uniform probability of the mixed affine fiber. -/
theorem mixedExactLengthProbability_eq_uniformSolutionProbability
    (M x y q r : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r) :
    mixedExactLengthProbability M x y q r =
      uniformSolutionProbability
        (mixedLengthSystem M x y q r)
        (mixedLengthRhs q r) := by
  classical
  unfold mixedExactLengthProbability uniformEventProbability
    uniformSolutionProbability
  congr 1
  rw [Fintype.card_subtype]
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (mixedLengthSystem_eq_rhs_iff ω hq hr).symm

/--
Exact affine identity at arbitrary mixed row counts.  This is the first
assertion of Lemma 14.6 in finite-cylinder form.
-/
theorem mixedExactLengthProbability_eq_eta_mul_two_pow_rho_div
    (M x y q r : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r) :
    mixedExactLengthProbability M x y q r =
      ((relationEta
          (mixedLengthSystem M x y q r)
          (mixedLengthRhs q r) : ℚ) *
        (2 : ℚ) ^
          relationRho (mixedLengthSystem M x y q r)) /
        (2 : ℚ) ^ (q + r) := by
  rw [mixedExactLengthProbability_eq_uniformSolutionProbability
    M x y q r hq hr,
    SectionTwelveMoments.uniformSolutionProbability_eq_eta_mul_two_pow_rho_div]
  congr 1
  simp [Fintype.card_sum]

/-!
## Zero-extension of relations

The rest of the file implements the second paragraph of the proof of Lemma
14.5 literally.  The inclusion sends row `i` of a shorter block to row `i` of
the common block; coefficients outside the two shorter blocks are zero.
-/

/-- Inclusion of two mixed row sets into two common row sets. -/
def mixedIndexEmbedding
    {q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q) :
    Sum (Fin q) (Fin r) → Sum (Fin Q) (Fin Q)
  | Sum.inl i => Sum.inl (Fin.castLE hq i)
  | Sum.inr i => Sum.inr (Fin.castLE hr i)

/-- The mixed row inclusion is injective. -/
theorem mixedIndexEmbedding_injective
    {q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q) :
    Function.Injective (mixedIndexEmbedding hq hr) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp only [mixedIndexEmbedding, Sum.inl.injEq] at hij
          apply congrArg Sum.inl
          exact Fin.ext
            (congrArg (fun z : Fin Q => z.1) hij)
      | inr j =>
          simp [mixedIndexEmbedding] at hij
  | inr i =>
      cases j with
      | inl j =>
          simp [mixedIndexEmbedding] at hij
      | inr j =>
          simp only [mixedIndexEmbedding, Sum.inr.injEq] at hij
          apply congrArg Sum.inr
          exact Fin.ext
            (congrArg (fun z : Fin Q => z.1) hij)

/--
Zero-extension of mixed row coefficients to the two common length-`Q`
blocks.
-/
def zeroExtendMixedCoefficients
    {q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q) :
    (Sum (Fin q) (Fin r) → F₂) →ₗ[F₂]
      (Sum (Fin Q) (Fin Q) → F₂) :=
  Function.ExtendByZero.linearMap F₂ (mixedIndexEmbedding hq hr)

@[simp]
theorem zeroExtendMixedCoefficients_apply_embedding
    {q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q)
    (u : Sum (Fin q) (Fin r) → F₂)
    (i : Sum (Fin q) (Fin r)) :
    zeroExtendMixedCoefficients hq hr u
        (mixedIndexEmbedding hq hr i) =
      u i := by
  exact (mixedIndexEmbedding_injective hq hr).extend_apply u 0 i

/-- Zero-extension of coefficients is injective. -/
theorem zeroExtendMixedCoefficients_injective
    {q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q) :
    Function.Injective (zeroExtendMixedCoefficients hq hr) := by
  intro u v huv
  funext i
  have hi := congrFun huv (mixedIndexEmbedding hq hr i)
  simpa using hi

/-- Each shorter homogeneous row is literally the corresponding common row. -/
theorem mixedLengthSystem_apply_embedding
    {M x y q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q)
    (ω : SampleSpace M) (i : Sum (Fin q) (Fin r)) :
    twoStartSystem M x y Q ω (mixedIndexEmbedding hq hr i) =
      mixedLengthSystem M x y q r ω i := by
  cases i with
  | inl i =>
      simp only [mixedIndexEmbedding, twoStartSystem_apply_inl,
        mixedLengthSystem_apply_inl, startSystem_apply, Fin.val_castLE]
  | inr i =>
      simp only [mixedIndexEmbedding, twoStartSystem_apply_inr,
        mixedLengthSystem_apply_inr, startSystem_apply, Fin.val_castLE]

/--
Dotting a common row vector with zero-extended coefficients is the same as
dotting its restriction with the original coefficients.
-/
theorem dotProduct_zeroExtendMixedCoefficients
    {q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q)
    (u : Sum (Fin q) (Fin r) → F₂)
    (w : Sum (Fin Q) (Fin Q) → F₂) :
    dotProduct (zeroExtendMixedCoefficients hq hr u) w =
      dotProduct u (fun i => w (mixedIndexEmbedding hq hr i)) := by
  classical
  let emb := mixedIndexEmbedding hq hr
  have hemb : Function.Injective emb :=
    mixedIndexEmbedding_injective hq hr
  let imageRows : Finset (Sum (Fin Q) (Fin Q)) :=
    Finset.univ.image emb
  simp only [dotProduct, zeroExtendMixedCoefficients,
    Function.ExtendByZero.linearMap_apply]
  calc
    (∑ j : Sum (Fin Q) (Fin Q),
        Function.extend emb u 0 j * w j) =
        ∑ j ∈ imageRows, Function.extend emb u 0 j * w j := by
      symm
      apply Finset.sum_subset
      · simp [imageRows]
      · intro j _hj hjnot
        have hjrange : ¬∃ i, emb i = j := by
          intro hex
          obtain ⟨i, hi⟩ := hex
          apply hjnot
          simp [imageRows, ← hi]
        rw [Function.extend_apply' u
          (0 : Sum (Fin Q) (Fin Q) → F₂) j hjrange]
        simp
    _ = ∑ i : Sum (Fin q) (Fin r),
        Function.extend emb u 0 (emb i) * w (emb i) := by
      rw [show imageRows = Finset.univ.image emb by rfl]
      apply Finset.sum_image
      intro i _ j _ hij
      exact hemb hij
    _ = ∑ i : Sum (Fin q) (Fin r), u i * w (emb i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hemb.extend_apply]

/-- Zero-extension sends every mixed relation to a common-length relation. -/
theorem zeroExtendMixedCoefficients_mem_relationSpace
    {M x y q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q)
    (u : RelationSpace (mixedLengthSystem M x y q r)) :
    zeroExtendMixedCoefficients hq hr
        (u : Sum (Fin q) (Fin r) → F₂) ∈
      RelationSpace (twoStartSystem M x y Q) := by
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro ω
  rw [relationMap_apply, relationFunctional_apply,
    dotProduct_zeroExtendMixedCoefficients]
  simp_rw [mixedLengthSystem_apply_embedding hq hr]
  have hu :
      relationMap (mixedLengthSystem M x y q r)
          (u : Sum (Fin q) (Fin r) → F₂) = 0 :=
    LinearMap.mem_ker.mp u.2
  have huω := DFunLike.congr_fun hu ω
  simpa only [relationMap_apply, relationFunctional_apply,
    LinearMap.zero_apply] using huω

/-- Linear zero-extension map between the two relation spaces. -/
def mixedRelationEmbedding
    {M x y q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q) :
    RelationSpace (mixedLengthSystem M x y q r) →ₗ[F₂]
      RelationSpace (twoStartSystem M x y Q) :=
  (zeroExtendMixedCoefficients hq hr).domRestrict
    (RelationSpace (mixedLengthSystem M x y q r))
    |>.codRestrict
      (RelationSpace (twoStartSystem M x y Q))
      (zeroExtendMixedCoefficients_mem_relationSpace hq hr)

/-- The relation-space map obtained by zero-extension is injective. -/
theorem mixedRelationEmbedding_injective
    {M x y q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q) :
    Function.Injective (mixedRelationEmbedding (M := M) (x := x) (y := y)
      hq hr) := by
  intro u v huv
  apply Subtype.ext
  apply zeroExtendMixedCoefficients_injective hq hr
  exact congrArg Subtype.val huv

/--
Relation defect cannot increase when the two shorter row sets are embedded
in common length-`Q` row sets.  This is the second assertion of Lemma 14.6.
-/
theorem mixed_relationRho_le_common
    {M x y q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q) :
    relationRho (mixedLengthSystem M x y q r) ≤
      relationRho (twoStartSystem M x y Q) := by
  unfold relationRho
  exact LinearMap.finrank_le_finrank_of_injective
    (mixedRelationEmbedding_injective (M := M) (x := x) (y := y)
      hq hr)

/-! ## Manuscript parameters `qₑ = L + e + 1` -/

/-- Number of affine rows attached to excess length `e`. -/
def excessRowCount (L e : ℕ) : ℕ :=
  L + e + 1

/--
Lemma 14.6's normalized identity, with the manuscript parameters displayed
verbatim.
-/
theorem mixedExcessProbability_eq_eta_mul_two_pow_rho_div
    (M x y L e f : ℕ) (hL : 1 ≤ L) :
    mixedExactLengthProbability M x y
        (excessRowCount L e) (excessRowCount L f) =
      ((relationEta
          (mixedLengthSystem M x y
            (excessRowCount L e) (excessRowCount L f))
          (mixedLengthRhs
            (excessRowCount L e) (excessRowCount L f)) : ℚ) *
        (2 : ℚ) ^
          relationRho
            (mixedLengthSystem M x y
              (excessRowCount L e) (excessRowCount L f))) /
        (2 : ℚ) ^
          (excessRowCount L e + excessRowCount L f) := by
  apply mixedExactLengthProbability_eq_eta_mul_two_pow_rho_div
  · simp [excessRowCount]
    omega
  · simp [excessRowCount]
    omega

/--
Lemma 14.6's defect domination for `e,f ≤ E` and
`Q = L + E + 1`.
-/
theorem mixedExcess_relationRho_le_common
    {M x y L e f E : ℕ} (he : e ≤ E) (hf : f ≤ E) :
    relationRho
        (mixedLengthSystem M x y
          (excessRowCount L e) (excessRowCount L f)) ≤
      relationRho
        (twoStartSystem M x y (excessRowCount L E)) := by
  apply mixed_relationRho_le_common
  · simp [excessRowCount]
    omega
  · simp [excessRowCount]
    omega

end

end MixedLengthAffine
end PaperC
