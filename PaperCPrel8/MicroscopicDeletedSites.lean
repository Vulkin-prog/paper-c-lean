import PaperCPrel8.MicroscopicDiscardBounds
import PaperCPrel8.MicroscopicGoodField

/-! # Actual microscopic deletion geometry

The paper indexes left boundaries by `j`, but probabilities use starts `j+1`.
Both the short-prefix deletion and the failure of a maximal-support pivot are
kept explicit. The source first moment controls their union.
-/
namespace PaperC.Prel8.MicroscopicDeletedSites
open MeasureTheory PaperC.InfiniteRademacher
open PaperC.Prel8.MicroscopicGoodField PaperC.Prel8.OddPrimePivot
open PaperC.Prel8.MicroscopicDiscardBounds PaperC.Prel8.IndependentScalarTail
open PaperC.V282.LaishramUniformInput PaperC.V282.PostQuadraticLiterature
open PaperC.V282.PrimeEulerPNT
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Boundaries at which at least one maximal-support pivot is too small. -/
def badPivotSites (n L E Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun j => ∃ a : Fin (L+E+2), largestOddPrime (j+a.val) ≤ Y

/-- The literal complement of the retained set, still in left-boundary coordinates. -/
def deletedSites (M n L E Y : ℕ) : Finset ℕ :=
  Finset.Icc 1 n \ goodSites M n L E Y

/-- Convert deleted left boundaries to the actual start coordinates. -/
def deletedStarts (M n L E Y : ℕ) : Finset ℕ :=
  (deletedSites M n L E Y).image (fun j => j+1)

/-- A deleted boundary is either shallow or has a bad pivot, and conversely. -/
theorem mem_deletedSites (M n L E Y j : ℕ) :
    j ∈ deletedSites M n L E Y ↔ j ∈ Finset.Icc 1 n ∧
      (j+1 < ⌈Real.sqrt M⌉₊ ∨ j ∈ badPivotSites n L E Y) := by
  simp only [deletedSites, Finset.mem_sdiff, goodSites, badPivotSites, Finset.mem_filter]
  constructor
  · rintro ⟨hj,hn⟩
    refine ⟨hj, ?_⟩
    by_cases hc : ⌈Real.sqrt M⌉₊ ≤ j+1
    · right
      refine ⟨hj, ?_⟩
      have hp : ¬∀ a : Fin (L+E+2), Y < largestOddPrime (j+a.val) :=
        fun hp => hn ⟨hj,hc,hp⟩
      simpa only [not_forall, Nat.not_lt] using hp
    · exact Or.inl (by omega)
  · rintro ⟨hj, hc | ⟨_,a,ha⟩⟩
    · refine ⟨hj, ?_⟩
      rintro ⟨_,hb,_⟩
      omega
    · refine ⟨hj, ?_⟩
      rintro ⟨_,_,hp⟩
      have := hp a
      omega

/-- The shallow boundary count is bounded by the exact integer square-root cutoff. -/
theorem shallow_card_le (M n : ℕ) :
    ((Finset.Icc 1 n).filter (fun j => j+1 < ⌈Real.sqrt M⌉₊)).card ≤ ⌈Real.sqrt M⌉₊ := by
  calc
    _ ≤ (Finset.range ⌈Real.sqrt M⌉₊).card := Finset.card_le_card (by
      intro j hj
      have := (Finset.mem_filter.mp hj).2
      exact Finset.mem_range.mpr (by omega))
    _ = _ := Finset.card_range _

/-- Only the sizes of the two deleted sets occur; overlaps are counted at most twice. -/
theorem deleted_card_le (M n L E Y : ℕ) :
    (deletedSites M n L E Y).card ≤ ⌈Real.sqrt M⌉₊ + (badPivotSites n L E Y).card := by
  have hs : deletedSites M n L E Y ⊆
      ((Finset.Icc 1 n).filter fun j => j+1 < ⌈Real.sqrt M⌉₊) ∪ badPivotSites n L E Y := by
    intro j hj
    obtain ⟨hj,hd⟩ := (mem_deletedSites M n L E Y j).mp hj
    rcases hd with hd | hd
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj,hd⟩)
    · exact Finset.mem_union_right _ hd
  exact (Finset.card_le_card hs).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (shallow_card_le M n) _))

/-- The change from boundaries to starts loses no cardinality. -/
theorem deletedStarts_card (M n L E Y : ℕ) :
    (deletedStarts M n L E Y).card = (deletedSites M n L E Y).card := by
  exact Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)

/-- With `n <= M`, every discarded start belongs to the ambient first-moment interval. -/
theorem deletedStarts_ambient {M n L E Y : ℕ} (hn : n ≤ M) :
    ∀ x ∈ deletedStarts M n L E Y, 2 ≤ x ∧ x ≤ 2*M := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  have hj := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hj).1
  omega

/-- Actual deletion cost, uniform before `n`, the excess cutoff, the pivot cutoff and the event. -/
theorem actual_deleted_bound_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      ∀ n E Y : ℕ, n ≤ M → ∀ A : Set InfiniteSample, 0 < infiniteRademacherMeasure.real A →
      infiniteRademacherMeasure.real (A ∩ hitEvent L (deletedStarts M n L E Y)) /
          infiniteRademacherMeasure.real A ≤
        (((⌈Real.sqrt M⌉₊:ℝ)+(badPivotSites n L E Y).card)/(2:ℝ)^L +
          2*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M)))) /
            infiniteRademacherMeasure.real A := by
  obtain ⟨Mzero,h⟩ := conditional_deleted_bound_eventually betaMin betaMax hbetaMin hbeta hLS hShorey hPNT hNR
  refine ⟨Mzero, ?_⟩
  intro M hM L hlo hhi n E Y hn A hA
  apply (h M hM L hlo hhi _ (deletedStarts_ambient hn) A hA).trans
  apply div_le_div_of_nonneg_right _ hA.le
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [deletedStarts_card]
  exact_mod_cast deleted_card_le M n L E Y

end
end PaperC.Prel8.MicroscopicDeletedSites
