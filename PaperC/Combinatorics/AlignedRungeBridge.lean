import PaperC.Algebra.RungeBound
import PaperC.Coding.AlignedComponentHamming
import PaperC.Combinatorics.AlignedExactFreeComponents

/-!
# From a short component word to the aligned Runge input

The short word supplied by the Section 8 component code selects whole graph
components.  This file expands that selection to its individual occurrences,
proves that no occurrence is duplicated, and turns exact-unit freeness into
distinctness of the translated Runge shifts.

The final theorem packages the finite hypotheses required by Lemma 3.1.  No
asymptotic estimate is hidden here.
-/

namespace PaperC
namespace AlignedRungeBridge

open scoped BigOperators
open Affine
open Affine.CanonicalRationalCode
open Affine.RationalChannelCode
open AlignedComponentCode
open AlignedExactFreeComponents
open ComponentProductParity
open LargePrimeComponents
open LargePrimeGraph
open LargePrimeOccurrences

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/--
Occurrences carried by the components selected by a binary word.  The sigma
type remembers the component, which makes product and cardinality formulas
literal finite sums.
-/
abbrev SelectedComponentVertex
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (word : Fin m → F₂) :=
  Σ i : {i // i ∈ HammingBound.wordSupport word},
    {v : Occurrence L //
      v ∈ componentVertices x y L (component i.1)}

/-- Forget the selected component and retain its occurrence. -/
def selectedOccurrence
    {m x y L : ℕ}
    {component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent}
    {word : Fin m → F₂} :
    SelectedComponentVertex component word → Occurrence L :=
  fun z ↦ z.2.1

/--
If the component enumeration is injective, the sigma presentation contains
each selected occurrence exactly once.
-/
theorem selectedOccurrence_injective
    {m x y L : ℕ}
    {component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent}
    (hcomponent : Function.Injective component)
    {word : Fin m → F₂} :
    Function.Injective
      (selectedOccurrence
        (component := component) (word := word)) := by
  rintro ⟨i, v⟩ ⟨j, w⟩ hvw
  have hcomponents : component i.1 = component j.1 := by
    have hvComponent :=
      (mem_componentVertices.mp v.2)
    have hwComponent :=
      (mem_componentVertices.mp w.2)
    rw [← hvComponent, ← hwComponent]
    exact congrArg
      (fun z ↦ (largePrimeGraph x y L).connectedComponentMk z)
      hvw
  have hij : i = j := by
    apply Subtype.ext
    exact hcomponent hcomponents
  subst j
  congr
  exact Subtype.ext hvw

/-- Cardinality of the expanded selection is the sum of component sizes. -/
theorem card_selectedComponentVertex
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (word : Fin m → F₂) :
    Fintype.card (SelectedComponentVertex component word) =
      ∑ i ∈ HammingBound.wordSupport word,
        (componentVertices x y L (component i)).card := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  change
    (∑ i : (HammingBound.wordSupport word),
      (componentVertices x y L (component i.1)).card) =
        ∑ i ∈ HammingBound.wordSupport word,
          (componentVertices x y L (component i)).card
  exact
    Finset.sum_coe_sort
      (HammingBound.wordSupport word)
      (fun i ↦ (componentVertices x y L (component i)).card)

/-- Product over the expanded selection is the product of component products. -/
theorem prod_selectedComponentVertex_labels
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (word : Fin m → F₂) :
    (∏ z : SelectedComponentVertex component word,
        Affine.twoStartCompleteVertexLabel x y L
          (selectedOccurrence z)) =
      ∏ i ∈ HammingBound.wordSupport word,
        componentVertexProduct x y L (component i) := by
  classical
  rw [Fintype.prod_sigma]
  simp only [selectedOccurrence, componentVertexProduct]
  simp_rw [Finset.prod_coe_sort]
  change
    (∏ i : (HammingBound.wordSupport word),
      ∏ v ∈ componentVertices x y L (component i.1),
        Affine.twoStartCompleteVertexLabel x y L v) =
      ∏ i ∈ HammingBound.wordSupport word,
        ∏ v ∈ componentVertices x y L (component i),
          Affine.twoStartCompleteVertexLabel x y L v
  exact
    Finset.prod_coe_sort
      (HammingBound.wordSupport word)
      (fun i ↦
        ∏ v ∈ componentVertices x y L (component i),
          Affine.twoStartCompleteVertexLabel x y L v)

/-- Total number of selected left occurrences, written componentwise. -/
noncomputable def selectedLeftCount
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (word : Fin m → F₂) : ℕ :=
  ∑ i ∈ HammingBound.wordSupport word,
    componentLeftCount x y L (component i)

/-- Total number of selected right occurrences, written componentwise. -/
noncomputable def selectedRightCount
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (word : Fin m → F₂) : ℕ :=
  ∑ i ∈ HammingBound.wordSupport word,
    componentRightCount x y L (component i)

/-- Left and right selected counts add up to the expanded cardinality. -/
theorem selectedLeftCount_add_rightCount
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (word : Fin m → F₂) :
    selectedLeftCount component word +
        selectedRightCount component word =
      Fintype.card (SelectedComponentVertex component word) := by
  classical
  rw [card_selectedComponentVertex]
  simp only [selectedLeftCount, selectedRightCount]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact componentLeftCount_add_rightCount x y L (component i)

/-- The affine shift used in the split Runge polynomial of Section 8. -/
def alignedShift
    {L : ℕ} (a b : ℕ) (h : ℤ) :
    Occurrence L → ℤ
  | Sum.inl v => (a : ℤ) * channelVertexOffset v
  | Sum.inr v => h + (b : ℤ) * channelVertexOffset v

/--
Exact-unit freeness makes the Runge shifts pairwise distinct, including
between the two boundary families.
-/
theorem alignedShift_selected_injective
    {m x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (hcomponent : Function.Injective component)
    (hexact :
      ∀ i, IsExactFreeComponent x y L a b h (component i))
    (word : Fin m → F₂) :
    Function.Injective
      (fun z : SelectedComponentVertex component word ↦
        alignedShift a b h (selectedOccurrence z)) := by
  intro z w hshift
  apply selectedOccurrence_injective hcomponent
  rcases z with ⟨i, ⟨vz, hvz⟩⟩
  rcases w with ⟨j, ⟨vw, hvw⟩⟩
  rcases vz with vz | vz <;> rcases vw with vw | vw
  · simp only [selectedOccurrence, alignedShift] at hshift ⊢
    have haZ : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
    have hoff :
        channelVertexOffset vz =
          channelVertexOffset vw :=
      mul_left_cancel₀ haZ hshift
    exact congrArg Sum.inl
      (ResidualCertificates.channelVertexOffset_injective hoff)
  · exfalso
    have hchannel :
        OnChannel a b h
          (channelVertexOffset vz,
            channelVertexOffset vw) := by
      unfold OnChannel
      simp only [selectedOccurrence, alignedShift] at hshift
      linarith
    have hcell :
        (vz, vw) ∈ rationalChannelUnits L a b h :=
      mem_rationalChannelUnits.mpr hchannel
    have hleft :=
      (hexact i.1) (vz, vw) hcell |>.1
    exact hleft (mem_componentVertices.mp hvz)
  · exfalso
    have hchannel :
        OnChannel a b h
          (channelVertexOffset vw,
            channelVertexOffset vz) := by
      unfold OnChannel
      simp only [selectedOccurrence, alignedShift] at hshift
      linarith
    have hcell :
        (vw, vz) ∈ rationalChannelUnits L a b h :=
      mem_rationalChannelUnits.mpr hchannel
    have hright :=
      (hexact i.1) (vw, vz) hcell |>.2
    exact hright (mem_componentVertices.mp hvz)
  · simp only [selectedOccurrence, alignedShift] at hshift ⊢
    have hbZ : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
    have hoff :
        channelVertexOffset vz =
          channelVertexOffset vw := by
      apply mul_left_cancel₀ hbZ
      linarith
    exact congrArg Sum.inr
      (ResidualCertificates.channelVertexOffset_injective hoff)

/-- Natural label after applying the left or right channel coefficient. -/
def scaledOccurrenceLabel
    {x y L : ℕ} (a b : ℕ) :
    Occurrence L → ℕ
  | Sum.inl v => a * Affine.startCompleteVertexLabel x L v
  | Sum.inr v => b * Affine.startCompleteVertexLabel y L v

/--
Finite product identity separating the two side coefficients from arbitrary
occurrence labels.
-/
private theorem prod_scaledOccurrenceLabel_aux
    {x y L : ℕ}
    (a b : ℕ) (s : Finset (Occurrence L)) :
    (∏ v ∈ s, scaledOccurrenceLabel (x := x) (y := y) a b v) =
      a ^ (s.filter IsLeftOccurrence).card *
        b ^ (s.filter IsRightOccurrence).card *
        ∏ v ∈ s, Affine.twoStartCompleteVertexLabel x y L v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [scaledOccurrenceLabel, IsLeftOccurrence, IsRightOccurrence]
  | @insert v s hv ih =>
      cases v with
      | inl v =>
          have hvIsLeft : IsLeftOccurrence (Sum.inl v) := trivial
          have hvNotRight : ¬IsRightOccurrence (Sum.inl v) := id
          have hvLeft :
              Sum.inl v ∉ s.filter IsLeftOccurrence := by
            intro hmem
            exact hv (Finset.mem_filter.mp hmem).1
          rw [Finset.prod_insert hv, ih]
          simp only [scaledOccurrenceLabel,
            Affine.twoStartCompleteVertexLabel,
            Finset.filter_insert, hvIsLeft, hvNotRight,
            if_true, if_false]
          rw [Finset.card_insert_of_notMem hvLeft, pow_succ]
          rw [Finset.prod_insert hv]
          ring
      | inr v =>
          have hvNotLeft : ¬IsLeftOccurrence (Sum.inr v) := id
          have hvIsRight : IsRightOccurrence (Sum.inr v) := trivial
          have hvRight :
              Sum.inr v ∉ s.filter IsRightOccurrence := by
            intro hmem
            exact hv (Finset.mem_filter.mp hmem).1
          rw [Finset.prod_insert hv, ih]
          simp only [scaledOccurrenceLabel,
            Affine.twoStartCompleteVertexLabel,
            Finset.filter_insert, hvNotLeft, hvIsRight,
            if_true, if_false]
          rw [Finset.card_insert_of_notMem hvRight, pow_succ]
          rw [Finset.prod_insert hv]
          ring

/-- Product identity for one connected component. -/
theorem prod_scaledOccurrenceLabel_component
    {x y L : ℕ} (a b : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    (∏ v ∈ componentVertices x y L C,
        scaledOccurrenceLabel (x := x) (y := y) a b v) =
      a ^ componentLeftCount x y L C *
        b ^ componentRightCount x y L C *
        componentVertexProduct x y L C := by
  simpa [componentLeftCount, componentRightCount,
    componentVertexProduct] using
    prod_scaledOccurrenceLabel_aux
      (x := x) (y := y) a b (componentVertices x y L C)

/-- Multiplicative collection of componentwise side factors. -/
private theorem prod_componentFactors_aux
    {ι : Type*}
    (s : Finset ι) (a b : ℕ)
    (left right product : ι → ℕ) :
    (∏ i ∈ s,
        a ^ left i * b ^ right i * product i) =
      a ^ (∑ i ∈ s, left i) *
        b ^ (∑ i ∈ s, right i) *
        ∏ i ∈ s, product i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi,
        ih, pow_add]
      ring

/--
The product of all scaled selected labels separates into the two selected
side counts and the product of the unscaled component labels.
-/
theorem prod_selected_scaledOccurrenceLabel
    {m x y L : ℕ}
    (a b : ℕ)
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (word : Fin m → F₂) :
    (∏ z : SelectedComponentVertex component word,
        scaledOccurrenceLabel (x := x) (y := y) a b
          (selectedOccurrence z)) =
      a ^ selectedLeftCount component word *
        b ^ selectedRightCount component word *
        ∏ i ∈ HammingBound.wordSupport word,
          componentVertexProduct x y L (component i) := by
  classical
  rw [Fintype.prod_sigma]
  simp only [selectedOccurrence]
  simp_rw [Finset.prod_coe_sort]
  calc
    (∏ i : (HammingBound.wordSupport word),
        ∏ v ∈ componentVertices x y L (component i.1),
          scaledOccurrenceLabel (x := x) (y := y) a b v) =
        ∏ i ∈ HammingBound.wordSupport word,
          ∏ v ∈ componentVertices x y L (component i),
            scaledOccurrenceLabel (x := x) (y := y) a b v :=
      Finset.prod_coe_sort
        (HammingBound.wordSupport word)
        (fun i ↦
          ∏ v ∈ componentVertices x y L (component i),
            scaledOccurrenceLabel (x := x) (y := y) a b v)
    _ =
        a ^ selectedLeftCount component word *
          b ^ selectedRightCount component word *
          ∏ i ∈ HammingBound.wordSupport word,
            componentVertexProduct x y L (component i) := by
      simp_rw [prod_scaledOccurrenceLabel_component]
      exact
        prod_componentFactors_aux
          (HammingBound.wordSupport word) a b
          (fun i ↦ componentLeftCount x y L (component i))
          (fun i ↦ componentRightCount x y L (component i))
          (fun i ↦ componentVertexProduct x y L (component i))

/--
At the base point `U = a*x`, each translated Runge factor is the
corresponding complete-boundary label multiplied by its side coefficient.
-/
theorem base_add_alignedShift_eq_scaledOccurrenceLabel
    {x y L a b : ℕ} {h : ℤ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (v : Occurrence L) :
    (((a * x : ℕ) : ℤ) + alignedShift a b h v) =
      (scaledOccurrenceLabel (x := x) (y := y) a b v : ℕ) := by
  cases v with
  | inl v =>
      simp only [alignedShift, scaledOccurrenceLabel, Nat.cast_mul]
      rw [Affine.RationalChannelCode.startCompleteVertexLabel_cast hx]
      ring
  | inr v =>
      simp only [alignedShift, scaledOccurrenceLabel, Nat.cast_mul]
      rw [Affine.RationalChannelCode.startCompleteVertexLabel_cast hy]
      rw [hheight]
      ring

/--
Even side counts and a square product of unscaled component labels make the
Runge value at `U=a*x` an integer square.
-/
theorem selected_base_product_square
    {m x y L a b : ℕ} {h : ℤ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (word : Fin m → F₂)
    (hleft : Even (selectedLeftCount component word))
    (hright : Even (selectedRightCount component word))
    (hsquare :
      ∃ q : ℕ,
        ∏ i ∈ HammingBound.wordSupport word,
            componentVertexProduct x y L (component i) =
          q ^ 2) :
    ∃ q : ℤ,
      (∏ z : SelectedComponentVertex component word,
          (((a * x : ℕ) : ℤ) +
            alignedShift a b h (selectedOccurrence z))) =
        q ^ 2 := by
  obtain ⟨leftHalf, hleftHalf⟩ := hleft
  obtain ⟨rightHalf, hrightHalf⟩ := hright
  obtain ⟨q, hq⟩ := hsquare
  have hleftEq :
      selectedLeftCount component word = 2 * leftHalf := by
    simpa [two_mul] using hleftHalf
  have hrightEq :
      selectedRightCount component word = 2 * rightHalf := by
    simpa [two_mul] using hrightHalf
  refine
    ⟨((a ^ leftHalf * b ^ rightHalf * q : ℕ) : ℤ), ?_⟩
  calc
    (∏ z : SelectedComponentVertex component word,
        (((a * x : ℕ) : ℤ) +
          alignedShift a b h (selectedOccurrence z))) =
        ∏ z : SelectedComponentVertex component word,
          ((scaledOccurrenceLabel (x := x) (y := y) a b
            (selectedOccurrence z) : ℕ) : ℤ) := by
      apply Finset.prod_congr rfl
      intro z hz
      exact
        base_add_alignedShift_eq_scaledOccurrenceLabel
          hx hy hheight (selectedOccurrence z)
    _ =
        ((∏ z : SelectedComponentVertex component word,
          scaledOccurrenceLabel (x := x) (y := y) a b
            (selectedOccurrence z) : ℕ) : ℤ) := by
      push_cast
      rfl
    _ =
        ((a ^ selectedLeftCount component word *
            b ^ selectedRightCount component word *
            ∏ i ∈ HammingBound.wordSupport word,
              componentVertexProduct x y L (component i) : ℕ) : ℤ) := by
      rw [prod_selected_scaledOccurrenceLabel]
    _ = (((a ^ leftHalf * b ^ rightHalf * q : ℕ) : ℤ) ^ 2) := by
      rw [hleftEq, hrightEq, hq]
      push_cast
      ring

/-- Even left and right counts make the expanded cardinality even. -/
theorem card_selectedComponentVertex_eq_two_mul
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (word : Fin m → F₂)
    (hleft : Even (selectedLeftCount component word))
    (hright : Even (selectedRightCount component word)) :
    ∃ k : ℕ,
      Fintype.card (SelectedComponentVertex component word) = 2 * k := by
  obtain ⟨leftHalf, hleftHalf⟩ := hleft
  obtain ⟨rightHalf, hrightHalf⟩ := hright
  refine ⟨leftHalf + rightHalf, ?_⟩
  rw [← selectedLeftCount_add_rightCount component word]
  omega

/--
A nonzero word selecting nontrivial components expands to at least two
vertices.
-/
theorem two_le_card_selectedComponentVertex
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (hnontrivial :
      ∀ i, 2 ≤ Fintype.card (component i).supp)
    (word : Fin m → F₂)
    (hword : word ≠ 0) :
    2 ≤ Fintype.card (SelectedComponentVertex component word) := by
  classical
  have hexists : ∃ i : Fin m, word i ≠ 0 := by
    by_contra hnot
    apply hword
    funext i
    by_contra hi
    exact hnot ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hexists
  have hiSupport : i ∈ HammingBound.wordSupport word := by
    simp [HammingBound.wordSupport, hi]
  rw [card_selectedComponentVertex]
  calc
    2 ≤ (componentVertices x y L (component i)).card := by
      rw [card_componentVertices]
      exact hnontrivial i
    _ ≤
        ∑ j ∈ HammingBound.wordSupport word,
          (componentVertices x y L (component j)).card :=
      Finset.single_le_sum
        (fun j _ ↦ Nat.zero_le
          (componentVertices x y L (component j)).card)
        hiSupport

/-- A word of weight `w` selecting `K`-vertex components expands to at most `K*w` vertices. -/
theorem card_selectedComponentVertex_le
    {m x y L K : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (hsmall :
      ∀ i, Fintype.card (component i).supp ≤ K)
    (word : Fin m → F₂) :
    Fintype.card (SelectedComponentVertex component word) ≤
      K * hammingNorm word := by
  classical
  rw [card_selectedComponentVertex]
  calc
    (∑ i ∈ HammingBound.wordSupport word,
        (componentVertices x y L (component i)).card) ≤
        ∑ _i ∈ HammingBound.wordSupport word, K := by
      apply Finset.sum_le_sum
      intro i hi
      rw [card_componentVertices]
      exact hsmall i
    _ = (HammingBound.wordSupport word).card * K := by
      simp
    _ = K * hammingNorm word := by
      rw [HammingBound.card_wordSupport]
      exact Nat.mul_comm _ _

/-- Elementary uniform bound for a complete-boundary offset. -/
theorem abs_channelVertexOffset_le
    {L : ℕ} (v : Fin (L + 1)) :
    |channelVertexOffset v| ≤ (L + 1 : ℕ) := by
  have hv := channelVertexOffset_mem_offsetInterval v
  rw [mem_offsetInterval] at hv
  rw [abs_le]
  constructor <;> omega

/--
If `a,b ≤ H` and `|h| ≤ 2H(L+1)`, every aligned shift is bounded by
`3H(L+1)`.
-/
theorem abs_alignedShift_le
    {L a b H : ℕ} {h : ℤ}
    (haH : a ≤ H) (hbH : b ≤ H)
    (hh :
      |h| ≤ ((2 * H * (L + 1) : ℕ) : ℤ))
    (v : Occurrence L) :
    |alignedShift a b h v| ≤
      ((3 * H * (L + 1) : ℕ) : ℤ) := by
  cases v with
  | inl v =>
      change
        |(a : ℤ) * channelVertexOffset v| ≤
          ((3 * H * (L + 1) : ℕ) : ℤ)
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg a)]
      have hoff := abs_channelVertexOffset_le v
      have haH' : (a : ℤ) ≤ H := by exact_mod_cast haH
      have hnonneg : (0 : ℤ) ≤ |channelVertexOffset v| := abs_nonneg _
      have hoff' :
          |channelVertexOffset v| ≤ ((L + 1 : ℕ) : ℤ) := by
        exact_mod_cast hoff
      calc
        (a : ℤ) * |channelVertexOffset v| ≤
            (H : ℤ) * |channelVertexOffset v| :=
          mul_le_mul_of_nonneg_right haH' hnonneg
        _ ≤ (H : ℤ) * (L + 1 : ℕ) :=
          mul_le_mul_of_nonneg_left hoff' (Int.natCast_nonneg H)
        _ ≤ ((3 * H * (L + 1) : ℕ) : ℤ) := by
          push_cast
          nlinarith
  | inr v =>
      have hoff := abs_channelVertexOffset_le v
      have hbH' : (b : ℤ) ≤ H := by exact_mod_cast hbH
      have hnonneg : (0 : ℤ) ≤ |channelVertexOffset v| := abs_nonneg _
      have hoff' :
          |channelVertexOffset v| ≤ ((L + 1 : ℕ) : ℤ) := by
        exact_mod_cast hoff
      calc
        |alignedShift a b h (Sum.inr v)| =
            |h + (b : ℤ) * channelVertexOffset v| := rfl
        _ ≤ |h| + |(b : ℤ) * channelVertexOffset v| := abs_add_le _ _
        _ = |h| + (b : ℤ) * |channelVertexOffset v| := by
          rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg b)]
        _ ≤
            ((2 * H * (L + 1) : ℕ) : ℤ) +
              (H : ℤ) * (L + 1 : ℕ) := by
          apply add_le_add hh
          calc
            (b : ℤ) * |channelVertexOffset v| ≤
                (H : ℤ) * |channelVertexOffset v| :=
              mul_le_mul_of_nonneg_right hbH' hnonneg
            _ ≤ (H : ℤ) * (L + 1 : ℕ) :=
              mul_le_mul_of_nonneg_left hoff' (Int.natCast_nonneg H)
        _ = ((3 * H * (L + 1) : ℕ) : ℤ) := by
          push_cast
          ring

/--
The defining inequality of a reduced candidate gives the height bound used
by the aligned Runge shifts.  This is the paper's estimate
`|b*y-a*x| < (a+b)(L+1) ≤ 2H(L+1)`, with the strict inequality weakened only
at the final integral interface.
-/
theorem candidate_pairChannelError_bound
    {x y L H : ℕ}
    (c : ReducedCandidate x y (L + 1) H) :
    |pairChannelError x y c.1.1 c.1.2| ≤
      ((2 * H * (L + 1) : ℕ) : ℤ) := by
  have hc :
      (c.1.1, c.1.2) ∈
        reducedChannelCandidates x y (L + 1) H :=
    c.2
  obtain ⟨_ha, _hb, haH, hbH, _hab, hchannel⟩ :=
    mem_reducedChannelCandidates.mp hc
  have habH : c.1.1 + c.1.2 ≤ 2 * H := by
    omega
  have hmul :
      (c.1.1 + c.1.2) * (L + 1) ≤
        2 * H * (L + 1) := by
    exact Nat.mul_le_mul_right (L + 1) habH
  exact
    (le_of_lt hchannel).trans (by
      exact_mod_cast hmul)

/--
Every translated root attached to a reduced height-`H` candidate lies in
the single interval of radius `3H(L+1)` used in Theorem 8.1.
-/
theorem candidate_abs_alignedShift_le
    {x y L H : ℕ}
    (c : ReducedCandidate x y (L + 1) H)
    (v : Occurrence L) :
    |alignedShift c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2) v| ≤
      ((3 * H * (L + 1) : ℕ) : ℤ) := by
  have hc :
      (c.1.1, c.1.2) ∈
        reducedChannelCandidates x y (L + 1) H :=
    c.2
  obtain ⟨_ha, _hb, haH, hbH, _hab, _hchannel⟩ :=
    mem_reducedChannelCandidates.mp hc
  exact
    abs_alignedShift_le haH hbH
      (candidate_pairChannelError_bound c) v

/--
Complete finite bridge from a short component-code word to the quantitative
Runge bound.

The selected `2k` roots are reindexed by `Fin (2*k)`.  Exact-unit freeness
gives distinctness, the two parity rows and the component-product rows give
the square value, and the component-size cutoff gives `k ≤ K*t`.
-/
theorem quantitative_runge_of_componentWord
    {m x y L a b K t R : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (hcomponent : Function.Injective component)
    (hexact :
      ∀ i, IsExactFreeComponent x y L a b h (component i))
    (hnontrivial :
      ∀ i, 2 ≤ Fintype.card (component i).supp)
    (hsmall :
      ∀ i, Fintype.card (component i).supp ≤ K)
    (word : Fin m → F₂)
    (hword0 : word ≠ 0)
    (hweight : hammingNorm word ≤ 2 * t)
    (hleft : Even (selectedLeftCount component word))
    (hright : Even (selectedRightCount component word))
    (hsquare :
      ∃ q : ℕ,
        ∏ i ∈ HammingBound.wordSupport word,
            componentVertexProduct x y L (component i) =
          q ^ 2)
    (hshiftBound :
      ∀ v : Occurrence L, |alignedShift a b h v| ≤ (R : ℤ))
    (hbase : 2 * R ≤ a * x) :
    ∃ k : ℕ,
      1 ≤ k ∧
      k ≤ K * t ∧
      a * x ≤ (128 * (2 * k) * R) ^ (4 * k) := by
  classical
  obtain ⟨k, hcard⟩ :=
    card_selectedComponentVertex_eq_two_mul
      component word hleft hright
  have hcardLower :
      2 ≤ Fintype.card (SelectedComponentVertex component word) :=
    two_le_card_selectedComponentVertex
      component hnontrivial word hword0
  have hk : 1 ≤ k := by omega
  have hcardUpper :
      Fintype.card (SelectedComponentVertex component word) ≤
        K * hammingNorm word :=
    card_selectedComponentVertex_le component hsmall word
  have htwo :
      2 * k ≤ 2 * (K * t) := by
    calc
      2 * k =
          Fintype.card (SelectedComponentVertex component word) :=
        hcard.symm
      _ ≤ K * hammingNorm word := hcardUpper
      _ ≤ K * (2 * t) :=
        Nat.mul_le_mul_left K hweight
      _ = 2 * (K * t) := by ring
  have hkKt : k ≤ K * t := by omega
  let e :
      Fin (2 * k) ≃ SelectedComponentVertex component word :=
    (Fintype.equivFinOfCardEq hcard).symm
  let γ : Fin (2 * k) → ℤ :=
    fun i ↦ alignedShift a b h (selectedOccurrence (e i))
  have hγInjective : Function.Injective γ :=
    (alignedShift_selected_injective
      ha hb component hcomponent hexact word).comp e.injective
  have hγBound : ∀ i, |γ i| ≤ (R : ℤ) := by
    intro i
    exact hshiftBound (selectedOccurrence (e i))
  obtain ⟨q, hq⟩ :=
    selected_base_product_square
      hx hy hheight component word hleft hright hsquare
  have hproduct :
      Finset.univ.prod
          (fun i : Fin (2 * k) ↦
            ((a * x : ℕ) : ℤ) + γ i) =
        q ^ 2 := by
    have hreindex :=
      e.prod_comp
        (fun z : SelectedComponentVertex component word ↦
          (((a * x : ℕ) : ℤ) +
            alignedShift a b h (selectedOccurrence z)))
    exact (by simpa [γ] using hreindex.trans hq)
  refine ⟨k, hk, hkKt, ?_⟩
  exact
    RungeBound.quantitative_runge_of_distinct
      hk hbase γ hγBound hγInjective q hproduct

end

end AlignedRungeBridge
end PaperC
