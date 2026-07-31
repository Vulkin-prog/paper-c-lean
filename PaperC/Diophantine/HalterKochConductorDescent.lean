import PaperC.Diophantine.GeneralizedPell
import Mathlib.Data.Fintype.EquivFin

/-!
# Source-shaped conductor descent for the Halter--Koch input

The registered interface `QuadraticOrderConductorFiberBoundStatement`
uses four colours as a convenient downstream counting device.  The
quadratic-order argument behind it is sharper:

* for squarefree `D`, the conductor (equivalently, the index of
  `ℤ[√D]` in the maximal order) is `2` when `D ≡ 1 (mod 4)` and `1`
  otherwise;
* at conductor at most two, the quotient of maximal-order units by
  order units has at most three elements;
* inside a fixed extended-principal-ideal fibre, order-principal ideals
  are exactly the cosets of that unit quotient.

The present repository does not yet contain the order embedding
`ℤ[√D] → O_K` needed to instantiate those three facts from Mathlib
objects.  `HalterKochConductorDescentData` therefore records precisely this
source boundary, with the unit quotient kept as an abstract finite type.
The theorem at the end proves, in Lean, that this sharper three-coset
statement implies the existing four-colour bridge.  The only cardinality
slack is the explicit injection `Fin 3 → Fin 4`.

No new `AUDIT_BRIDGE` is introduced here: this file factors and explains
the already registered Halter--Koch boundary.
-/

namespace PaperC
namespace PellInput

open scoped NumberField

noncomputable section

/--
Source-shaped data for the conductor-two descent.

`UnitQuotient` represents `O_Kˣ / ℤ[√D]ˣ`.  The last field says
literally that, after fixing the extended ideal, its generators modulo
equality of principal ideals in `ℤ[√D]` are the unit-quotient cosets.
-/
structure HalterKochConductorDescentData (D : ℕ) (M : ℤ) where
  K : Type
  [fieldK : Field K]
  [numberFieldK : NumberField K]
  [quadraticK : Algebra.IsQuadraticExtension ℚ K]
  idealOf :
    ℤ × ℤ →
      {I : Ideal (𝓞 K) //
        I ∣ Ideal.span ({(M : 𝓞 K)} : Set (𝓞 K))}
  /-- The conductor, equal here to the index `[O_K : ℤ[√D]]`. -/
  conductorIndex : ℕ
  /-- The standard integral-basis computation for squarefree `D`. -/
  conductorIndex_eq :
    conductorIndex = if D % 4 = 1 then 2 else 1
  /-- The finite quotient `O_Kˣ / ℤ[√D]ˣ`. -/
  UnitQuotient : Type
  [fintypeUnitQuotient : Fintype UnitQuotient]
  /-- Halter--Koch's unit-index bound at conductor at most two. -/
  unitQuotient_card_le_three :
    conductorIndex ≤ 2 → Fintype.card UnitQuotient ≤ 3
  /-- The unit coset of a generator, relative to its extended ideal fibre. -/
  generatorUnitCoset : ℤ × ℤ → UnitQuotient
  /--
  In one extended-ideal fibre, equality of order-principal ideals is
  exactly equality of unit-quotient cosets.
  -/
  principalIdeal_eq_iff_unitCoset_eq_of_same_extension :
    ∀ s t : ℤ × ℤ,
      s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M →
      t.1 ^ 2 - (D : ℤ) * t.2 ^ 2 = M →
      idealOf s = idealOf t →
      (Ideal.span
          ({toZsqrtd D s} : Set (ℤ√(D : ℤ))) =
        Ideal.span
          ({toZsqrtd D t} : Set (ℤ√(D : ℤ))) ↔
        generatorUnitCoset s = generatorUnitCoset t)

/--
The source-facing Halter--Koch statement used by the derivation below.
It has exactly the same arithmetic domain as the registered conductor
bridge, but exposes the conductor and unit-quotient mechanisms separately.
-/
def HalterKochConductorDescentStatement : Prop :=
  ∀ (D : ℕ) (M : ℤ),
    0 < D →
    Squarefree D →
    ¬ IsSquare (D : ℚ) →
    M ≠ 0 →
    Nonempty (HalterKochConductorDescentData D M)

/-- The conductor/index formula implies the bound used by the unit theorem. -/
private theorem conductorIndex_le_two
    {D : ℕ} {M : ℤ}
    (data : HalterKochConductorDescentData D M) :
    data.conductorIndex ≤ 2 := by
  rw [data.conductorIndex_eq]
  split <;> omega

/--
Canonical injection implementing the sole padding in the old interface:
the three unit cosets occupy the first three of four conductor colours.
-/
def padThreeConductorColours : Fin 3 → Fin 4 :=
  Fin.castLE (by omega)

private theorem padThreeConductorColours_injective :
    Function.Injective padThreeConductorColours :=
  Fin.castLE_injective (by omega)

/--
Encode an abstract unit quotient of cardinality at most three by `Fin 3`.
The unused colours, when the quotient has cardinality one or two, are
harmless and make the construction uniform.
-/
private def unitQuotientColourThree
    {D : ℕ} {M : ℤ}
    (data : HalterKochConductorDescentData D M) :
    data.UnitQuotient → Fin 3 := by
  letI : Fintype data.UnitQuotient := data.fintypeUnitQuotient
  exact fun q ↦
    Fin.castLE
      (data.unitQuotient_card_le_three
        (conductorIndex_le_two data))
      (Fintype.equivFin data.UnitQuotient q)

private theorem unitQuotientColourThree_injective
    {D : ℕ} {M : ℤ}
    (data : HalterKochConductorDescentData D M) :
    Function.Injective (unitQuotientColourThree data) := by
  letI : Fintype data.UnitQuotient := data.fintypeUnitQuotient
  intro q₁ q₂ hq
  apply (Fintype.equivFin data.UnitQuotient).injective
  exact
    (Fin.castLE_injective
      (data.unitQuotient_card_le_three
        (conductorIndex_le_two data))) hq

/--
Formal derivation of the registered four-colour statement from the
source-shaped conductor/index, unit-quotient and generator-coset facts.
-/
theorem quadraticOrderConductorFiberBound_of_halterKochConductorDescent
    (hHK : HalterKochConductorDescentStatement) :
    QuadraticOrderConductorFiberBoundStatement := by
  intro D M hDpos hDsquarefree hDnonsquare hM
  obtain ⟨data⟩ := hHK D M hDpos hDsquarefree hDnonsquare hM
  letI : Field data.K := data.fieldK
  letI : NumberField data.K := data.numberFieldK
  letI : Algebra.IsQuadraticExtension ℚ data.K := data.quadraticK
  letI : Fintype data.UnitQuotient := data.fintypeUnitQuotient
  let colourThree : ℤ × ℤ → Fin 3 :=
    fun s ↦ unitQuotientColourThree data (data.generatorUnitCoset s)
  let colourFour : ℤ × ℤ → Fin 4 :=
    fun s ↦ padThreeConductorColours (colourThree s)
  refine ⟨{
    K := data.K
    idealOf := data.idealOf
    conductorColour := colourFour
    same_principalIdeal_of_same_extension := ?_
  }⟩
  intro s t hs ht hcolour hideal
  have hcolourThree : colourThree s = colourThree t :=
    padThreeConductorColours_injective hcolour
  have hcoset :
      data.generatorUnitCoset s = data.generatorUnitCoset t := by
    exact
      unitQuotientColourThree_injective data hcolourThree
  exact
    (data.principalIdeal_eq_iff_unitCoset_eq_of_same_extension
      s t hs ht hideal).2 hcoset

end

end PellInput
end PaperC
