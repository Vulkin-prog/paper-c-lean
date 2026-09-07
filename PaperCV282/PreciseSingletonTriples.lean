import PaperCV282.PreciseSingletonTriplesParameters
import PaperCV282.PreciseSingletonHosts
import PaperCV282.MacroscopicGeometry

/-! # Literal triples in the sharp two-singleton bound

Both starts range over an arbitrary positive mask, without graph conditions,
separation or a bounded interval ratio. The square-class coefficient is
retained in the injection. Its height bound follows from the equation.
-/
namespace PaperC.V282.PreciseSingletonTriples

open Affine PropositionSixteenOne BoundedRatioTwoSingletonHosts SquarefreeSmoothCount
open PreciseSingletonTriplesParameters PreciseSingletonHosts MacroscopicGeometry
open BalasubramanianShoreyInput
open scoped BigOperators

noncomputable section

/-- All actual triples, for fixed offsets and an arbitrary mask of starts. -/
def triples (M L : ℕ) (i j : Fin (L+1)) (s : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact ((s.product s).product (squarefreeSmoothUpTo (L+1) ((M+L)^2))).filter fun t =>
    ∃ z : ℕ, startCompleteVertexLabel t.1.1 L i * startCompleteVertexLabel t.1.2 L j = t.2*z^2

/-- The offset labels are positive and have the same common height bound. -/
theorem label_bounds {M L x : ℕ} (hx : x ∈ Finset.Icc 2 M) (i : Fin (L+1)) :
    0 < startCompleteVertexLabel x L i ∧ startCompleteVertexLabel x L i ≤ M+L := by
  have hh := Finset.mem_Icc.mp hx
  have hi := i.isLt
  unfold startCompleteVertexLabel
  split_ifs <;> omega

/-- Membership has no independent bound on d: it follows from the displayed equation. -/
theorem mem_triples {M L : ℕ} (i j : Fin (L+1)) (s : Finset ℕ)
    (hs : s ⊆ Finset.Icc 2 M) (x y d : ℕ) :
    ((x,y),d) ∈ triples M L i j s ↔
      x ∈ s ∧ y ∈ s ∧ 0 < d ∧ Squarefree d ∧ IsSmoothAt (L+1) d ∧
        ∃ z : ℕ, startCompleteVertexLabel x L i * startCompleteVertexLabel y L j = d*z^2 := by
  classical
  constructor
  · intro ht
    have ht' := Finset.mem_filter.mp ht
    have hp := Finset.mem_product.mp ht'.1
    have hxy := Finset.mem_product.mp hp.1
    have hd := mem_squarefreeSmoothUpTo.mp hp.2
    exact ⟨hxy.1,hxy.2,hd.1,hd.2.2.1,hd.2.2.2,ht'.2⟩
  · rintro ⟨hx,hy,hd,hsq,hsm,⟨z,hz⟩⟩
    have hbX := label_bounds (hs hx) i
    have hbY := label_bounds (hs hy) j
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩, ?_⟩, ⟨z,hz⟩⟩
    exact mem_squarefreeSmoothUpTo.mpr
      ⟨hd,coefficient_le_square hbX.1 hbY.1 hbX.2 hbY.2 hz,hsq,hsm⟩

/-- The sigma coordinate retains d; the other coordinates are canonical. -/
def tripleParameter (L : ℕ) (i j : Fin (L+1)) (t : (ℕ × ℕ) × ℕ) :
    Σ _d : ℕ, SingletonParameterTuple :=
  ⟨t.2, canonicalTuple (startCompleteVertexLabel t.1.1 L i)
    (startCompleteVertexLabel t.1.2 L j) t.2⟩

/-- At a fixed offset a positive start is recovered from its label. -/
theorem start_eq_of_label_eq {L x y : ℕ} (i : Fin (L+1)) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : startCompleteVertexLabel x L i = startCompleteVertexLabel y L i) : x=y := by
  unfold startCompleteVertexLabel at h
  split_ifs at h <;> omega

/-- The exact finite triple count is controlled by the previously summed parameters. -/
theorem card_triples_le_parameterCount {M L : ℕ} (i j : Fin (L+1)) (s : Finset ℕ)
    (hs : s ⊆ Finset.Icc 2 M) :
    (triples M L i j s).card ≤ twoSingletonParameterCount M L 2 := by
  classical
  let T := (squarefreeSmoothUpTo (L+1) ((M+L)^2)).sigma (fun d => singletonParameterTuples d (M+L))
  have hmap : Set.MapsTo (tripleParameter L i j) (triples M L i j s) T := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    have hb := Finset.mem_product.mp ht'.1
    have hp := Finset.mem_product.mp hb.1
    have hd := mem_squarefreeSmoothUpTo.mp hb.2
    obtain ⟨z,hz⟩ := ht'.2
    have hX := label_bounds (hs hp.1) i
    have hY := label_bounds (hs hp.2) j
    exact Finset.mem_sigma.mpr ⟨hb.2,
      canonicalTuple_mem hX.1 hY.1 hX.2 hY.2 hd.1 hd.2.2.1 hz⟩
  have hinj : Set.InjOn (tripleParameter L i j) (triples M L i j s) := by
    rintro ⟨⟨x,y⟩,d⟩ ht ⟨⟨x',y'⟩,d'⟩ ht' he
    have hd : d=d' := congrArg Sigma.fst he
    subst d'
    have hh := (mem_triples i j s hs x y d).mp ht
    have hh' := (mem_triples i j s hs x' y' d).mp ht'
    obtain ⟨z,hz⟩ := hh.2.2.2.2.2
    obtain ⟨z',hz'⟩ := hh'.2.2.2.2.2
    have hX := label_bounds (hs hh.1) i
    have hY := label_bounds (hs hh.2.1) j
    have hX' := label_bounds (hs hh'.1) i
    have hY' := label_bounds (hs hh'.2.1) j
    have heparam : canonicalTuple (startCompleteVertexLabel x L i)
        (startCompleteVertexLabel y L j) d = canonicalTuple (startCompleteVertexLabel x' L i)
        (startCompleteVertexLabel y' L j) d := eq_of_heq (Sigma.mk.inj_iff.mp he |>.2)
    have hp := canonicalTuple_injective hX.1 hY.1 hX'.1 hY'.1 hh.2.2.1 hh.2.2.2.1 hz hz' heparam
    have hxx := start_eq_of_label_eq i (by have := (Finset.mem_Icc.mp (hs hh.1)).1; omega)
      (by have := (Finset.mem_Icc.mp (hs hh'.1)).1; omega) hp.1
    have hyy := start_eq_of_label_eq j (by have := (Finset.mem_Icc.mp (hs hh.2.1)).1; omega)
      (by have := (Finset.mem_Icc.mp (hs hh'.2.1)).1; omega) hp.2
    subst x'; subst y'; rfl
  have hc := Finset.card_le_card_of_injOn (tripleParameter L i j) hmap hinj
  simpa only [T, Finset.card_sigma, twoSingletonParameterCount, boundedRatioCutoff] using hc

/-- Article Lemma 3.17: sharp bound on the genuine triples in U_(M,delta). -/
theorem lemma_three_seventeen (betaMin betaMax : ℝ)
    (hmin : 0 < betaMin) (hmax : 0 ≤ betaMax) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ betaMax * Real.log M →
      ∀ (i j : Fin (L+1)) (delta : ℝ), 0 < delta →
      ((triples M L i j (macroscopicStarts M delta)).card : ℝ) ≤
        (M : ℝ) * Real.exp (singletonConstant betaMin *
          (Real.sqrt (L+1 : ℝ) / Real.log (L+1 : ℝ))) := by
  obtain ⟨Mzero,hbound⟩ := parameterCount_le_sharp_eventually betaMin betaMax hmin hmax
  refine ⟨max Mzero 2, ?_⟩
  intro M hM L hlo hhi i j delta hdelta
  exact (show ((triples M L i j (macroscopicStarts M delta)).card : ℝ) ≤
      (twoSingletonParameterCount M L 2 : ℝ) by
    exact_mod_cast card_triples_le_parameterCount i j (macroscopicStarts M delta)
      (macroscopicStarts_subset_Icc ((le_max_right _ _).trans hM) hdelta)).trans
    (hbound M ((le_max_left _ _).trans hM) L hlo hhi 2)

end
end PaperC.V282.PreciseSingletonTriples
