import PaperCPrel8.HardConditionalForcing
import PaperCV282.SignedExactMarks

/-! # Exact signed-run Palm forcing

The paper's left boundary `j` is the retained model's run start `j+1`.
Only the `L+e+2` raw values of the requested mark are forced. Forcing the
whole maximal support would condition on a stronger event and is not used.
-/
namespace PaperC.Prel8.SignedPalmForcing
open PaperC.Prel8.PrimeForcing PaperC.Prel8.PivotGeometry
open PaperC.Prel8.HardConditionalForcing PaperC.Prel8.OddPrimePivot
open PaperC.ConditionalStartProbability PaperC.V282.PrescribedValues
open PaperC.V282.SignedExactMarks PaperC.V282.ExactMarkedModel
open PaperC.IndependentThinning PaperC.ArratiaGoldsteinGordonInput
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The existing signed exact-run event is precisely the forced raw-value word. -/
theorem signedWord_iff {M j L e : ℕ} (hL : 1 ≤ L) (s : F₂) (ω : SampleSpace M) :
    valueSystem M (fun a : Fin (L+e+2) => j+a.val) ω = signedExactWord L e s ↔
      SignedExactMark (valueBit ω) (j+1) L e s := by
  rw [valueSystem_eq_iff]
  simpa [PaperC.V282.WordOverlap.Occurs, PaperC.V282.WindowValues.vertex] using
    (signedExactMark_iff_occurs (g := valueBit ω) (x := j+1) (by omega) hL s).symm

/-- The deterministic arithmetic forcing produces the requested sign and exact excess. -/
theorem signedForcing_hits {M j L e : ℕ} (hL : 1 ≤ L)
    (q : Fin (L+e+2) → PrimeUpTo M)
    (hq : ∀ a, valueSystem M (fun a : Fin (L+e+2) => j+a.val)
      (Pi.single (q a) 1) = Pi.single a 1) (s : F₂) (ω : SampleSpace M) :
    SignedExactMark (valueBit (forceWord (fun a : Fin (L+e+2) => j+a.val)
      q (signedExactWord L e s) ω)) (j+1) L e s :=
  (signedWord_iff hL s _).mp (forceWord_hits _ q hq _ ω)

/-- Exact signed marginal under every small-prime event, with the actual geometric rate. -/
theorem actual_signed_small_probability {M Y j L e : ℕ}
    (hj : 0 < j) (hL : 1 ≤ L) (hM : j+(L+e+2) ≤ M+1)
    (hY : 1 ≤ Y) (hBY : L+e+2 ≤ Y)
    (hgood : ∀ a : Fin (L+e+2), Y < largestOddPrime (j+a.val))
    (s : F₂) (A : SmallSample M Y → Prop) :
    eventProbability (FinitePMF.uniform (SampleSpace M))
      (fun ω => A (restrictSmall M Y ω) ∧ SignedExactMark (valueBit ω) (j+1) L e s) =
    eventProbability (FinitePMF.uniform (SampleSpace M)) (fun ω => A (restrictSmall M Y ω)) *
      (signedMarkRate L e : ℝ) := by
  let q := cylinderPivot hj hM (fun a => hY.trans_lt (hgood a))
  have hq := cylinderPivot_basis hj hM (fun a => hY.trans_lt (hgood a))
    (fun a => hBY.trans (hgood a).le)
  have h := word_small_event_probability (fun a : Fin (L+e+2) => j+a.val)
    q hq hgood (signedExactWord L e s) A
  simpa only [signedWord_iff hL, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    Nat.cast_pow, Nat.cast_ofNat, signedMarkRate_coe, one_div] using h

/-- Source-facing finite conditional law for a signed exact mark, with no assumed Palm law. -/
theorem actual_signed_hard_conditional {M Y j L e : ℕ}
    (hj : 0 < j) (hL : 1 ≤ L) (hM : j+(L+e+2) ≤ M+1)
    (hY : 1 ≤ Y) (hBY : L+e+2 ≤ Y)
    (hgood : ∀ a : Fin (L+e+2), Y < largestOddPrime (j+a.val))
    (s : F₂) (A : SmallSample M Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace M))
      (fun ω => A (restrictSmall M Y ω))) (f : SampleSpace M → ℝ) :
    let q := cylinderPivot hj hM (fun a => hY.trans_lt (hgood a))
    finitePMFExpectation (FinitePMF.uniform (SampleSpace M))
      (fun ω => if A (restrictSmall M Y ω) then
        f (forceWord (fun a : Fin (L+e+2) => j+a.val) q (signedExactWord L e s) ω) else 0) /
      eventProbability (FinitePMF.uniform (SampleSpace M)) (fun ω => A (restrictSmall M Y ω)) =
    finitePMFExpectation (FinitePMF.uniform (SampleSpace M))
      (fun ω => if A (restrictSmall M Y ω) ∧ SignedExactMark (valueBit ω) (j+1) L e s then f ω else 0) /
      eventProbability (FinitePMF.uniform (SampleSpace M))
        (fun ω => A (restrictSmall M Y ω) ∧ SignedExactMark (valueBit ω) (j+1) L e s) := by
  have h := actual_window_hard_conditional hj hM hY hBY hgood (signedExactWord L e s) A hA f
  simpa only [signedWord_iff hL] using h

end
end PaperC.Prel8.SignedPalmForcing
