import PaperCV282.DictionaryFieldRates
import PaperCV282.DictionaryMarginalCap
import PaperCV282.WordOverlap

/-!
# The actual word field of independent fair bits

The finite sample consists of independent uniform bits at integer coordinates,
not multiplicative values. Its prefix contains every coordinate used by the
field. Every site and dictionary label is retained.
-/
namespace PaperC.V282.IidWordField

open Affine ArratiaGoldsteinGordonInput ConditionalDependencyGraph
open DictionaryFieldModel DictionaryFieldTransfer DictionaryFieldRates
open DictionaryMarginalCap WordOverlap WindowValues PrescribedValues
open SectionTwelveMoments FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

@[reducible]
def IidSample (C : ℕ) := Fin C → F₂

/-- The genuine product of C independent uniform binary coordinates. -/
def iidUniformPMF (C : ℕ) : FinitePMF (IidSample C) := FinitePMF.uniform _

/-- The finite iid event law is the literal uniform counting probability. -/
theorem eventProbability_iidUniformPMF_eq (C : ℕ) (P : IidSample C → Prop) :
    eventProbability (iidUniformPMF C) P = (finiteUniformProbability P : ℝ) := by
  unfold iidUniformPMF eventProbability finiteUniformProbability FinitePMF.uniform
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_subtype]
  push_cast
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- A prefix is extended only to write occurrences uniformly; all events below stay inside it. -/
def iidSequence (C : ℕ) (omega : IidSample C) (n : ℕ) : F₂ :=
  if h : n < C then omega ⟨n,h⟩ else 0

def iidWordIndicator (C x B : ℕ) (b : Fin B → F₂) (omega : IidSample C) : Bool :=
  decide (Occurs (iidSequence C omega) x b)

theorem iidWordIndicator_eq_true (C x B : ℕ) (b : Fin B → F₂) (omega : IidSample C) :
    iidWordIndicator C x B b omega = true ↔ Occurs (iidSequence C omega) x b := by
  simp [iidWordIndicator]

/-- Coordinate projection onto every letter of the displayed word. -/
def iidWordSystem (C x B : ℕ) (hcut : x - 1 + B ≤ C) :
    IidSample C →ₗ[F₂] (Fin B → F₂) :=
  LinearMap.pi (fun i => LinearMap.proj (⟨vertex x B i, by
    have hi := i.isLt
    unfold vertex
    omega⟩ : Fin C))

theorem iidWordSystem_eq_iff (C x B : ℕ) (hcut : x - 1 + B ≤ C)
    (omega : IidSample C) (b : Fin B → F₂) :
    iidWordSystem C x B hcut omega = b ↔ Occurs (iidSequence C omega) x b := by
  have hc (i : Fin B) : vertex x B i < C := by have hi := i.isLt; unfold vertex; omega
  constructor
  · intro h i
    have hi := congrFun h i
    simpa [iidWordSystem,iidSequence,hc i] using hi
  · intro h
    funext i
    simpa [iidWordSystem,iidSequence,hc i] using h i

/-- Every letter has its own actual bit coordinate in the iid prefix. -/
theorem iidWordSystem_private_coordinates (C x B : ℕ) (hcut : x - 1 + B ≤ C)
    (i : Fin B) : ∃ omega : IidSample C,
      iidWordSystem C x B hcut omega = Pi.single i 1 := by
  let q : Fin C := ⟨vertex x B i, by have hi := i.isLt; unfold vertex; omega⟩
  refine ⟨Pi.single q 1, ?_⟩
  funext j
  by_cases hji : j = i
  · subst j
    simp [iidWordSystem,q]
  · have hq : (⟨vertex x B j, by have hj := j.isLt; unfold vertex; omega⟩ : Fin C) ≠ q := by
      intro he
      apply hji
      apply Fin.ext
      have hv := congrArg Fin.val he
      dsimp [q,vertex] at hv
      omega
    simp [iidWordSystem,hji,hq]

/-- Exact iid word probability, including every prescribed bit. -/
theorem iid_word_probability (C x B : ℕ) (hcut : x - 1 + B ≤ C) (b : Fin B → F₂) :
    eventProbability (iidUniformPMF C) (fun omega => Occurs (iidSequence C omega) x b) =
      1 / (2 : ℝ)^B := by
  have h := probability_eq_baseline_of_private_coordinates (iidWordSystem C x B hcut) b
    (iidWordSystem_private_coordinates C x B hcut)
  have hr := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at hr
  rw [← eventProbability_affine_eq] at hr
  simpa only [iidUniformPMF,iidWordSystem_eq_iff,Fintype.card_fin] using hr

/-- Exact local joint probability for two independent-bit words. -/
theorem iid_word_joint_probability {C x B d : ℕ} (hx : 1 ≤ x) (hd : d ≤ B)
    (hcut : x - 1 + (B+d) ≤ C) (u v : Fin B → F₂) :
    eventProbability (iidUniformPMF C) (fun omega =>
      Occurs (iidSequence C omega) x u ∧ Occurs (iidSequence C omega) (x+d) v) =
      if Compatible d u v then 1 / (2 : ℝ)^(B+d) else 0 := by
  simp_rw [occurs_pair_iff hx hd]
  by_cases hc : Compatible d u v
  · simp only [hc,true_and,if_true]
    exact iid_word_probability C x (B+d) hcut (mergedWord d hd u v)
  · simp [hc,eventProbability]

/-- The complete site-word field on an adequate finite iid cylinder. -/
def iidFieldIndicator (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (i : DictionaryIndex N L W) : IidSample (dyadicCutoff N L + 1) → Bool :=
  iidWordIndicator (dyadicCutoff N L + 1) i.1.val (L+1) i.2.val

def iidFieldLaw (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    (DictionaryIndex N L W → ℕ) → ℝ :=
  finiteFieldLaw (iidUniformPMF (dyadicCutoff N L + 1)) (indicatorField (iidFieldIndicator N L W))

theorem iidField_marginal (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (i : DictionaryIndex N L W) :
    marginal (iidUniformPMF (dyadicCutoff N L + 1)) (iidFieldIndicator N L W) i = (wordRate L : ℝ) := by
  rw [wordRate_coe]
  unfold marginal iidFieldIndicator
  simp only [iidWordIndicator_eq_true]
  apply iid_word_probability
  exact DictionaryFieldInfinite.dictionary_vertex_cutoff N L i.1

theorem iidField_rates_eq (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    fieldRates (iidUniformPMF (dyadicCutoff N L + 1)) (iidFieldIndicator N L W) =
      allWordRates N L W (dyadicBlock N) := by
  rw [allWordRates_full_eq]
  funext i
  apply NNReal.eq
  exact iidField_marginal N L W i

theorem hasSum_iidFieldLaw (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    HasSum (iidFieldLaw N L W) 1 := hasSum_finiteFieldLaw _ _

theorem iidFieldLaw_nonneg (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (k : DictionaryIndex N L W → ℕ) : 0 ≤ iidFieldLaw N L W k := finiteFieldLaw_nonneg _ _ k

end
end PaperC.V282.IidWordField
