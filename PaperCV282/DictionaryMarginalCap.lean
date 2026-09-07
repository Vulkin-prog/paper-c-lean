import PaperCV282.TwoWindowParity
import PaperCV282.InfiniteConditionalWords
import PaperC.Probability.SectionThirteenCouplings

/-!
# A genuine dictionary marginal ceiling before summing pairs

Words prescribe all B values, beginning at x-1. Membership in a dictionary
is a Boolean event because a sample has exactly one word. The joint mass
is both the sum of the labelled joint probabilities and at most the
single-site marginal. Its second bound uses the full value relation space.
-/

namespace PaperC.V282.DictionaryMarginalCap

open Affine PrescribedValues WindowValues InfiniteWordTransfer
open ConditionalStartProbability ArratiaGoldsteinGordonInput SectionThirteenCouplings
open TwoWindowParity
open scoped BigOperators

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The reference density of a dictionary of B-letter words. -/
def dictionaryDensity (B : ℕ) (W : Finset (Fin B → F₂)) : ℝ :=
  (W.card : ℝ) / (2 : ℝ) ^ B

/-- The actual Boolean event obtained by grouping all words at one site. -/
def dictionaryIndicator (M x B : ℕ) (W : Finset (Fin B → F₂))
    (omega : SampleSpace M) : Bool := by
  classical
  exact decide (valueSystem M (vertex x B) omega ∈ W)

/-- Complete valuation rows for two generic B-letter windows. -/
def jointValueSystem (M x y B : ℕ) :
    SampleSpace M →ₗ[F₂] (Sum (Fin B) (Fin B) → F₂) :=
  valueSystem M (Sum.elim (vertex x B) (vertex y B))

/-- The actual joint probability of two specified words in the finite source cylinder. -/
def wordJointProbability (M x y B : ℕ) (u v : Fin B → F₂) : ℝ :=
  eventProbability (fullUniformPMF M) (fun omega =>
    omega ∈ finiteWordEvent M x B u ∧ omega ∈ finiteWordEvent M y B v)

/-- The probability that both sites belong to the dictionary. -/
def dictionaryJointProbability (M x y B : ℕ) (W : Finset (Fin B → F₂)) : ℝ :=
  eventProbability (fullUniformPMF M) (fun omega =>
    dictionaryIndicator M x B W omega = true ∧ dictionaryIndicator M y B W omega = true)

theorem dictionaryDensity_nonneg (B : ℕ) (W : Finset (Fin B → F₂)) :
    0 ≤ dictionaryDensity B W := by unfold dictionaryDensity; positivity

theorem dictionaryDensity_pos {B : ℕ} {W : Finset (Fin B → F₂)} (hW : W.Nonempty) :
    0 < dictionaryDensity B W := by
  unfold dictionaryDensity
  exact div_pos (by exact_mod_cast hW.card_pos) (by positivity)

/-- The density is at most one for every set of distinct words, even the empty dictionary. -/
theorem dictionaryDensity_le_one (B : ℕ) (W : Finset (Fin B → F₂)) :
    dictionaryDensity B W ≤ 1 := by
  have hcard := Finset.card_le_univ W
  have hc : W.card ≤ 2 ^ B := by simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using hcard
  unfold dictionaryDensity
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast hc

@[simp]
theorem dictionaryIndicator_eq_true (M x B : ℕ) (W : Finset (Fin B → F₂)) (omega : SampleSpace M) :
    dictionaryIndicator M x B W omega = true ↔ valueSystem M (vertex x B) omega ∈ W := by
  classical
  simp [dictionaryIndicator]

/-- The sum of the mutually exclusive word indicators is exactly a single indicator. -/
theorem sum_word_indicators_eq_dictionary (M x B : ℕ) (W : Finset (Fin B → F₂))
    (omega : SampleSpace M) :
    (∑ b ∈ W, if omega ∈ finiteWordEvent M x B b then (1 : ℕ) else 0) =
      if dictionaryIndicator M x B W omega = true then 1 else 0 := by
  classical
  simp only [finiteWordEvent, Set.mem_setOf_eq, ← valueSystem_eq_iff, dictionaryIndicator_eq_true]
  rw [Finset.sum_ite_eq]

/-- Disjoint value fibres turn a membership event into its exact sum of event probabilities. -/
theorem eventProbability_mem_eq_sum {Omega T : Type*} [Fintype Omega]
    (mu : FinitePMF Omega) (f : Omega → T) (s : Finset T) :
    eventProbability mu (fun omega => f omega ∈ s) =
      ∑ t ∈ s, eventProbability mu (fun omega => f omega = t) := by
  classical
  unfold eventProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hs : f omega ∈ s
  · have hsum : (∑ t ∈ s, if f omega = t then mu.prob omega else 0) = mu.prob omega := by
      rw [Finset.sum_eq_single (f omega)]
      · simp
      · intro t ht htf
        simp [Ne.symm htf]
      · intro hn
        exact False.elim (hn hs)
    simpa only [if_pos hs] using hsum.symm
  · have hsum : (∑ t ∈ s, if f omega = t then mu.prob omega else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have hn : f omega ≠ t := by
        intro he
        exact hs (he ▸ ht)
      simp only [if_neg hn]
    simpa only [if_neg hs] using hsum.symm

/-- The same disjointness identity for the pair of displayed words. -/
theorem eventProbability_joint_mem_eq_sum {Omega T : Type*} [Fintype Omega]
    (mu : FinitePMF Omega) (f g : Omega → T) (s : Finset T) :
    eventProbability mu (fun omega => f omega ∈ s ∧ g omega ∈ s) =
      ∑ u ∈ s, ∑ v ∈ s, eventProbability mu (fun omega => f omega = u ∧ g omega = v) := by
  classical
  have h := eventProbability_mem_eq_sum mu (fun omega => (f omega,g omega)) (s ×ˢ s)
  simpa only [Finset.mem_product, Finset.sum_product, Prod.mk.injEq] using h

/-- Monotonicity of actual finite event probabilities. -/
theorem eventProbability_mono {Omega : Type*} [Fintype Omega]
    (mu : FinitePMF Omega) (P Q : Omega → Prop) (hPQ : ∀ omega, P omega → Q omega) :
    eventProbability mu P ≤ eventProbability mu Q := by
  classical
  unfold eventProbability
  apply Finset.sum_le_sum
  intro omega _
  by_cases hp : P omega
  · simp only [if_pos hp, if_pos (hPQ omega hp)]
    rfl
  · simp only [if_neg hp]
    split_ifs <;> first | exact mu.nonneg omega | rfl

/-- Uniform event probabilities for affine equations are exactly the real fibre probabilities. -/
theorem eventProbability_affine_eq {V beta : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [DecidableEq V] [Fintype beta] [DecidableEq beta]
    (A : V →ₗ[F₂] (beta → F₂)) (b : beta → F₂) :
    eventProbability (FinitePMF.uniform V) (fun omega => A omega = b) =
      (uniformSolutionProbability A b : ℝ) := by
  classical
  unfold eventProbability FinitePMF.uniform uniformSolutionProbability
  rw [Fintype.card_subtype]
  push_cast
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- The homogeneous full-value relation weight bounds every affine right-hand side. -/
theorem affine_probability_le_relation_weight {V beta : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [DecidableEq V] [Fintype beta] [DecidableEq beta]
    (A : V →ₗ[F₂] (beta → F₂)) (b : beta → F₂) :
    (uniformSolutionProbability A b : ℝ) ≤
      (2 : ℝ) ^ relationRho A / (2 : ℝ) ^ Fintype.card beta := by
  rw [probability_eq_eta_weight]
  push_cast
  rcases relationEta_eq_zero_or_one A b with h | h
  · rw [h]
    norm_num
    positivity
  · rw [h]
    norm_num

/-- Specified joint words are exactly the affine equations on both complete windows. -/
theorem wordJointProbability_eq_affine (M x y B : ℕ) (u v : Fin B → F₂) :
    wordJointProbability M x y B u v =
      (uniformSolutionProbability (jointValueSystem M x y B) (Sum.elim u v) : ℝ) := by
  rw [← eventProbability_affine_eq]
  unfold wordJointProbability fullUniformPMF
  congr 1
  funext omega
  apply propext
  simp only [finiteWordEvent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hu,hv⟩
    funext i
    cases i with
    | inl i => exact hu i
    | inr i => exact hv i
  · intro h
    exact ⟨fun i => congrFun h (Sum.inl i), fun i => congrFun h (Sum.inr i)⟩

/-- The grouped joint probability is the exact labelled double sum. -/
theorem dictionaryJointProbability_eq_sum (M x y B : ℕ) (W : Finset (Fin B → F₂)) :
    dictionaryJointProbability M x y B W =
      ∑ u ∈ W, ∑ v ∈ W, wordJointProbability M x y B u v := by
  unfold dictionaryJointProbability wordJointProbability
  simp only [dictionaryIndicator_eq_true]
  have h := eventProbability_joint_mem_eq_sum (fullUniformPMF M)
    (fun omega => valueSystem M (vertex x B) omega)
    (fun omega => valueSystem M (vertex y B) omega) W
  simpa only [valueSystem_eq_iff, finiteWordEvent, Set.mem_setOf_eq] using h

/-- Summing the homogeneous bound over distinct prescribed right-hand sides costs m squared. -/
theorem dictionaryJointProbability_le_affine (M x y B : ℕ) (W : Finset (Fin B → F₂)) :
    dictionaryJointProbability M x y B W ≤
      dictionaryDensity B W ^ 2 * (2 : ℝ) ^ relationRho (jointValueSystem M x y B) := by
  rw [dictionaryJointProbability_eq_sum]
  have h := Finset.sum_le_sum (s := W) (fun u _ => Finset.sum_le_sum (s := W)
    (fun v _ => affine_probability_le_relation_weight (jointValueSystem M x y B) (Sum.elim u v)))
  simp only [← wordJointProbability_eq_affine, Fintype.card_sum, Fintype.card_fin,
    Finset.sum_const, nsmul_eq_mul] at h
  apply h.trans_eq
  unfold dictionaryDensity
  rw [pow_add]
  ring

/-- A genuinely good window has the exact unconditional marginal for every word. -/
theorem word_probability_eq_of_good_window {M Y x B : ℕ}
    (hx : 2 ≤ x) (hcut : x - 1 + B ≤ M + 1) (hBY : B ≤ Y)
    (hgood : ∀ i : Fin B, ¬DefectivePredicate.HDefective Y (vertex x B i)) (b : Fin B → F₂) :
    eventProbability (fullUniformPMF M) (fun omega => omega ∈ finiteWordEvent M x B b) =
      1 / (2 : ℝ) ^ B := by
  have h := probability_eq_baseline_of_private_coordinates (valueSystem M (vertex x B)) b ?_
  · have hr := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at hr
    rw [← eventProbability_affine_eq] at hr
    simpa only [Fintype.card_fin, fullUniformPMF, valueSystem_eq_iff, finiteWordEvent, Set.mem_setOf_eq] using hr
  · intro i
    obtain ⟨p,_,hdiag,hoff⟩ := private_prime_of_not_defective hx hcut hBY i (hgood i)
    exact ⟨Pi.single p 1, valueSystem_prime_basis M (vertex x B) i p hdiag hoff⟩

/-- One good marginal already bounds the grouped joint event, with no hypothesis on its partner. -/
theorem dictionaryJointProbability_le_marginal {M Y x y B : ℕ}
    (hx : 2 ≤ x) (hcut : x - 1 + B ≤ M + 1) (hBY : B ≤ Y)
    (hgood : ∀ i : Fin B, ¬DefectivePredicate.HDefective Y (vertex x B i))
    (W : Finset (Fin B → F₂)) :
    dictionaryJointProbability M x y B W ≤ dictionaryDensity B W := by
  unfold dictionaryJointProbability
  apply (eventProbability_mono (fullUniformPMF M) _
    (fun omega => dictionaryIndicator M x B W omega = true) (fun _ h => h.1)).trans_eq
  simp only [dictionaryIndicator_eq_true]
  rw [eventProbability_mem_eq_sum]
  have heq (b : Fin B → F₂) :
      eventProbability (fullUniformPMF M) (fun omega => valueSystem M (vertex x B) omega = b) =
        1 / (2 : ℝ) ^ B := by
    simpa only [valueSystem_eq_iff, finiteWordEvent, Set.mem_setOf_eq] using
      word_probability_eq_of_good_window hx hcut hBY hgood b
  simp only [heq, Finset.sum_const, nsmul_eq_mul, dictionaryDensity]
  ring

/-- The elementary cap is taken before any summation over pairs. -/
theorem min_marginal_le_capped_defect {a z : ℝ} :
    min a (a ^ 2 * z) ≤ a ^ 2 * (1 + min (1 / a) (z - 1)) := by
  by_cases hz : z - 1 ≤ 1 / a
  · rw [min_eq_right hz]
    have h := min_le_right a (a ^ 2 * z)
    nlinarith
  · rw [min_eq_left (le_of_not_ge hz)]
    by_cases ha0 : a = 0
    · simp [ha0]
    · have haa : a ^ 2 * (1 / a) = a := by field_simp
      have h := min_le_left a (a ^ 2 * z)
      nlinarith [sq_nonneg a]

/-- Equation (5.6), at the level of actual probabilities on a generic B-letter window. -/
theorem dictionary_joint_cap {M Y x y B : ℕ}
    (hx : 2 ≤ x) (hcut : x - 1 + B ≤ M + 1) (hBY : B ≤ Y)
    (hgood : ∀ i : Fin B, ¬DefectivePredicate.HDefective Y (vertex x B i))
    (W : Finset (Fin B → F₂)) :
    dictionaryJointProbability M x y B W ≤
      min (dictionaryDensity B W)
        (dictionaryDensity B W ^ 2 * (2 : ℝ) ^ relationRho (jointValueSystem M x y B)) ∧
    dictionaryJointProbability M x y B W ≤
      dictionaryDensity B W ^ 2 *
        (1 + min (1 / dictionaryDensity B W) ((2 : ℝ) ^ relationRho (jointValueSystem M x y B) - 1)) := by
  have h := le_min (dictionaryJointProbability_le_marginal hx hcut hBY hgood W)
    (dictionaryJointProbability_le_affine M x y B W)
  exact ⟨h, h.trans min_marginal_le_capped_defect⟩

/-- The generic full-value system is exactly the historical B=L+1 system at positive starts. -/
theorem jointValueSystem_eq_twoValueSystem {M x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    jointValueSystem M x y (L + 1) = twoValueSystem M x y L :=
  (twoValueSystem_eq_consecutive hx hy).symm

end
end PaperC.V282.DictionaryMarginalCap
