import PaperCPrel8.PivotGeometry
import PaperCPrel8.PrivateForcing

/-! # Forcing actual prime signs and the complete conditional sample law

The source sample is assembled from an arbitrary finite background law and an
independent uniform private-prime block. Every observable below is an observable
of the complete prime assignment, rather than only of its displayed word.
-/
namespace PaperC.Prel8.PrimeForcing
open PaperC.V282.PrescribedValues PaperC.Prel8.PivotGeometry
open PaperC.IndependentThinning PaperC.ArratiaGoldsteinGordonInput
open PaperC.V282.SteinFiniteExpectation
open scoped BigOperators
noncomputable section
variable {M : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Add a specified binary block at the selected actual prime coordinates. -/
def liftBlock (q : ι → PrimeUpTo M) (c : ι → F₂) : SampleSpace M :=
  ∑ a, c a • Pi.single (q a) 1

/-- Deterministic forcing: correct the current word by changing only its pivots. -/
def forceWord (v : ι → ℕ) (q : ι → PrimeUpTo M) (word : ι → F₂)
    (ω : SampleSpace M) : SampleSpace M :=
  ω + liftBlock q (word - valueSystem M v ω)

/-- A private prime block is a right inverse of the actual arithmetic value system. -/
theorem value_liftBlock (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (c : ι → F₂) : valueSystem M v (liftBlock q c) = c := by
  classical
  simp only [liftBlock, map_sum, map_smul, hq]
  funext a
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]

omit [DecidableEq ι] in
theorem liftBlock_add (q : ι → PrimeUpTo M) (c d : ι → F₂) :
    liftBlock q (c+d) = liftBlock q c + liftBlock q d := by
  simp [liftBlock, add_smul, Finset.sum_add_distrib]

/-- Every prescribed raw-value word is hit exactly. -/
theorem forceWord_hits (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (ω : SampleSpace M) :
    valueSystem M v (forceWord v q word ω) = word := by
  rw [forceWord, map_add, value_liftBlock v q hq]
  exact add_sub_cancel _ _

omit [DecidableEq ι] in
/-- Already satisfied words are fixed, including all their unobserved signs. -/
theorem forceWord_fixes (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (word : ι → F₂) (ω : SampleSpace M) (h : valueSystem M v ω = word) :
    forceWord v q word ω = ω := by
  simp [forceWord, h, liftBlock]

omit [DecidableEq ι] in
/-- All nonpivot coordinates stay pointwise unchanged. -/
theorem forceWord_preserves_nonpivot (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (word : ι → F₂) (ω : SampleSpace M) (p : PrimeUpTo M)
    (hp : ∀ a, p ≠ q a) : forceWord v q word ω p = ω p := by
  classical
  simp [forceWord, liftBlock, Finset.sum_apply, hp]

omit [DecidableEq ι] in
/-- Small primes are preserved whenever every chosen pivot is above the cutoff. -/
theorem forceWord_preserves_small (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (word : ι → F₂) (ω : SampleSpace M) (Y : ℕ)
    (hqY : ∀ a, Y < (q a).val.val) (p : PrimeUpTo M) (hp : p.val.val ≤ Y) :
    forceWord v q word ω p = ω p := by
  apply forceWord_preserves_nonpivot
  intro a he
  have := hqY a
  rw [← he] at this
  omega

omit [DecidableEq ι] in
/-- A value with no selected prime divisor is unchanged; even valuations may be ignored. -/
theorem forceWord_preserves_value (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (word : ι → F₂) (ω : SampleSpace M) (n : ℕ)
    (hn : ∀ a, ¬(q a).val.val ∣ n) :
    valueBit (forceWord v q word ω) n = valueBit ω n := by
  change valueLinear M n (ω + liftBlock q _) = valueLinear M n ω
  rw [map_add]
  suffices h : valueLinear M n (liftBlock q (word-valueSystem M v ω)) = 0 by
    rw [h, add_zero]
  simp only [liftBlock, map_sum, map_smul, valueLinear_apply, valueBit_prime_basis]
  simp [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd (hn _)]

/-- Directed footprint: it is not asserted to be a dependency graph. -/
def directedFootprint (G : Finset ℕ) (Q : ℕ) (q : ι → PrimeUpTo M) : Finset ℕ := by
  classical
  exact G.filter fun k => ∃ a, ∃ b : Fin (Q+1), (q a).val.val ∣ k+b.val

omit [DecidableEq ι] in
/-- The entire raw window outside the directed footprint is untouched. -/
theorem forceWord_outside_footprint (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (word : ι → F₂) (ω : SampleSpace M) (G : Finset ℕ) (Q k : ℕ)
    (hk : k ∈ G) (hout : k ∉ directedFootprint G Q q) (b : Fin (Q+1)) :
    valueBit (forceWord v q word ω) (k+b.val) = valueBit ω (k+b.val) := by
  apply forceWord_preserves_value
  intro a ha
  exact hout (Finset.mem_filter.mpr ⟨hk, ⟨a,b,ha⟩⟩)

/-- Adding a uniform private block to a background sample. -/
def assemble (q : ι → PrimeUpTo M) (r : SampleSpace M) (c : ι → F₂) : SampleSpace M :=
  r + liftBlock q c

/-- On each background fibre, the word event prescribes exactly one private block. -/
theorem assemble_word_iff (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (r : SampleSpace M) (c : ι → F₂) :
    valueSystem M v (assemble q r c) = word ↔ c = word-valueSystem M v r := by
  rw [assemble, map_add, value_liftBlock v q hq]
  constructor <;> intro h
  · rw [← h]; abel
  · rw [h]; abel

/-- Forcing agrees with replacing that independent block, on the complete sample. -/
theorem forceWord_assemble (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (r : SampleSpace M) (c : ι → F₂) :
    forceWord v q word (assemble q r c) =
      assemble q r (word-valueSystem M v r) := by
  simp only [forceWord, assemble, map_add, value_liftBlock v q hq]
  rw [add_assoc, ← liftBlock_add]
  congr 2
  abel

/-- Exact conditioning against any observable of the full arithmetic sample. -/
theorem exact_prime_conditional_expectation (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (μ : FinitePMF (SampleSpace M)) (f : SampleSpace M → ℝ) :
    finitePMFExpectation (productPMF μ (FinitePMF.uniform (ι → F₂)))
      (fun z => f (forceWord v q word (assemble q z.1 z.2))) =
    finitePMFExpectation (productPMF μ (FinitePMF.uniform (ι → F₂)))
      (fun z => if valueSystem M v (assemble q z.1 z.2) = word
        then f (assemble q z.1 z.2) else 0) / (Fintype.card (ι → F₂) : ℝ)⁻¹ := by
  have h := PrivateForcing.exact_conditional_expectation μ
    (fun r => word-valueSystem M v r) (fun z => f (assemble q z.1 z.2))
  simp only [PrivateForcing.force, forceWord_assemble v q hq,
    assemble_word_iff v q hq] at h ⊢
  convert h using 1
  congr!

/-- Randomizing a block on top of a uniform cylinder preserves its complete law. -/
theorem uniform_assemble_expectation (q : ι → PrimeUpTo M) (f : SampleSpace M → ℝ) :
    finitePMFExpectation
      (productPMF (FinitePMF.uniform (SampleSpace M)) (FinitePMF.uniform (ι → F₂)))
      (fun z => f (assemble q z.1 z.2)) =
    finitePMFExpectation (FinitePMF.uniform (SampleSpace M)) f := by
  classical
  have hs (c : ι → F₂) : (∑ r : SampleSpace M, f (assemble q r c)) = ∑ r, f r := by
    exact Equiv.sum_comp (Equiv.addRight (liftBlock q c)) f
  unfold finitePMFExpectation productPMF
  simp only [FinitePMF.uniform, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hs]
  simp
  field_simp

/-- The deterministic modification has the exact conditional law in the original uniform cylinder. -/
theorem uniform_conditional_expectation (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (f : SampleSpace M → ℝ) :
    finitePMFExpectation (FinitePMF.uniform (SampleSpace M)) (fun ω => f (forceWord v q word ω)) =
    finitePMFExpectation (FinitePMF.uniform (SampleSpace M))
      (fun ω => if valueSystem M v ω = word then f ω else 0) /
        (Fintype.card (ι → F₂) : ℝ)⁻¹ := by
  have h := exact_prime_conditional_expectation v q hq word (FinitePMF.uniform (SampleSpace M)) f
  rw [uniform_assemble_expectation q (fun ω => f (forceWord v q word ω)),
    uniform_assemble_expectation q (fun ω => if valueSystem M v ω = word then f ω else 0)] at h
  exact h

/-- The arithmetic pivots discharge the private-basis assumption of the forcing map. -/
theorem actual_window_forced {j B : ℕ} (hj : 0 < j) (hM : j+B ≤ M+1)
    (h1 : ∀ a : Fin B, 1 < OddPrimePivot.largestOddPrime (j+a.val))
    (hB : ∀ a : Fin B, B ≤ OddPrimePivot.largestOddPrime (j+a.val))
    (word : Fin B → F₂) (ω : SampleSpace M) :
    valueSystem M (fun a : Fin B => j+a.val)
      (forceWord (fun a : Fin B => j+a.val) (cylinderPivot hj hM h1) word ω) = word :=
  forceWord_hits _ _ (cylinderPivot_basis hj hM h1 hB) word ω

end
end PaperC.Prel8.PrimeForcing
