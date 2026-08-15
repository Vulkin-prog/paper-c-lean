import PaperC.Diophantine.GeneralizedPell
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic

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

## Why the maximal-order shortcut is not a local replacement in this encoding

The manuscript's maximal-order proof is mathematically sound: one may send
`α = X + Y√D` directly to the principal ideal `(α)` of `O_K`, count all
ideal divisors of `(M)` there, and allow every unit of `O_K` when counting the
generators of a fixed ideal.  Enlarging the acting unit group can only enlarge
the resulting upper bound, so the *paper proof* does not intrinsically need a
descent to `ℤ[√D]`.

The current Lean proof, however, splits that argument at a different boundary.
`QuadraticIdealDivisors.quadraticIdealDivisorTauSq` performs the maximal-order
ideal count, but the quantitative generator count is
`card_samePrincipalIdeal_solutionFiber`.  Its input is equality of principal
ideals in the concrete ring `Zsqrtd`, and
`same_principalIdeal_gives_pell_unit` turns precisely that equality into a
`Pell.Solution₁`.  The subsequent uniform bound uses the integral `x,y`
coordinates of this Pell unit in `pellUnit_y_natAbs_le`, followed by the
explicit geometric growth theorem `two_pow_le_y_pow_succ`.  Equality after
extension to `O_K` gives only a quotient in `(O_K)ˣ`; it does **not** supply a
`Pell.Solution₁`, since a maximal-order unit need not preserve `ℤ[√D]`
when `D ≡ 1 (mod 4)`.

Mathlib 4.32.2 contains the abstract Dirichlet unit theorem (in particular
`NumberField.Units.exist_unique_eq_mul_prod`, `fundSystem`, and the unit
lattice), but it does not provide the replacement needed here as one packaged
result: a concrete integral-basis description of `O_{ℚ(√D)}` connected to
`Zsqrtd`, together with a **uniform quantitative** height-box count for the
maximal-order unit orbit.  The available lattice result
`unitLattice_inter_ball_finite` proves finiteness, not the explicit logarithmic
bound uniform in the varying squarefree `D` required by Lemma 9.2.  A direct
maximal-order implementation would therefore have to construct the quadratic
field and both real embeddings, prove the coordinate/embedding height
comparison, specialize Dirichlet rank to one, bound torsion, and prove a
uniform positive lower bound for the fundamental logarithm before replacing
the complete orbit-counting block above.  That is a substantive refactor, not
a proof of the present bridge from existing Mathlib lemmas.

The historical `HalterKochConductorDescentData` record below retains that
source-shaped factorisation.  It is no longer needed to close the registered
interface, however.  The second half of this module constructs the quadratic
field, the order embedding and the extended ideals directly.  Its key
elementary observation is `2 O_K ⊆ ℤ[√D]`, proved from the concrete trace
and norm in `QuadraticAlgebra ℚ D 0`.  Reduction of relative units in the
four-element ring `O_K / 2 O_K` then realizes the historical `Fin 4`
interface and makes equality descend to principal ideals in `ℤ[√D]`.

No new `AUDIT_BRIDGE` is introduced here: the final theorem discharges the
already registered Halter--Koch compatibility interface internally.
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

/-!
## Internal construction by reduction modulo two

The construction below proves the registered four-colour interface without
assuming the source-shaped record above.  For `K = ℚ(√D)`, trace and norm show
that twice every algebraic integer belongs to `ℤ[√D]`.  The quotient
`O_K / 2 O_K` has four elements because `K` is quadratic.  Relative generators
of the same extended ideal are coloured by their residue in this quotient.
Equal colours make their quotient congruent to one modulo two; applying the
same twice-integral result to that unit and its inverse lifts it to an actual
unit of `ℤ[√D]`, which is exactly the required descent.
-/

namespace QuadraticOrderConductor

open scoped QuadraticAlgebra

private abbrev QD (D : ℕ) :=
  QuadraticAlgebra ℚ (D : ℚ) 0

section

variable (D : ℕ)
variable [Fact (∀ r : ℚ, r ^ 2 ≠ (D : ℚ) + 0 * r)]

local instance : NumberField (QD D) :=
  NumberField.of_module_finite ℚ (QD D)

local instance : Algebra.IsQuadraticExtension ℚ (QD D) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two _ _

private theorem omega_sq :
    (⟨0, 1⟩ : QD D) ^ 2 = (D : QD D) := by
  ext <;> simp [pow_two]

private theorem omega_integral :
    IsIntegral ℤ (⟨0, 1⟩ : QD D) := by
  apply IsIntegral.of_pow (n := 2) (by omega)
  rw [omega_sq]
  exact isIntegral_natCast D

private def sqrtDO : NumberField.RingOfIntegers (QD D) :=
  ⟨⟨0, 1⟩, omega_integral D⟩

private theorem sqrtDO_sq :
    (sqrtDO D) * (sqrtDO D) =
      (D : NumberField.RingOfIntegers (QD D)) := by
  apply NumberField.RingOfIntegers.ext
  change (⟨0, 1⟩ : QD D) * ⟨0, 1⟩ = (D : QD D)
  simpa only [pow_two] using omega_sq D

private def embedOrder :
    ℤ√(D : ℤ) →+* NumberField.RingOfIntegers (QD D) :=
  Zsqrtd.lift ⟨sqrtDO D, sqrtDO_sq D⟩

private theorem trace_eq (x : QD D) :
    Algebra.trace ℚ (QD D) x = 2 * x.re := by
  let b := QuadraticAlgebra.basis (D : ℚ) 0
  have hb0 : b 0 = (1 : QD D) := by
    apply b.repr.injective
    ext i
    fin_cases i <;> simp [b, QuadraticAlgebra.basis_repr_apply]
  have hb1 : b 1 = (⟨0, 1⟩ : QD D) := by
    apply b.repr.injective
    ext i
    fin_cases i <;> simp [b, QuadraticAlgebra.basis_repr_apply]
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two]
  simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    b, QuadraticAlgebra.basis_repr_apply, hb0, hb1]
  ring

private theorem norm_eq (x : QD D) :
    Algebra.norm ℚ x = x.re ^ 2 - (D : ℚ) * x.im ^ 2 := by
  rw [Algebra.norm_apply]
  change LinearMap.det
      (DistribSMul.toLinearMap ℚ (QD D) x) = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
  simp [QuadraticAlgebra.norm_def]
  ring

private abbrev OK := NumberField.RingOfIntegers (QD D)

omit [Fact (∀ r : ℚ, r ^ 2 ≠ (D : ℚ) + 0 * r)] in
private theorem rat_eq_int_of_squarefree_mul_sq_eq_int
    (hDpos : 0 < D) (hDsquarefree : Squarefree D)
    (q : ℚ) (z : ℤ) (hz : (z : ℚ) = (D : ℚ) * q ^ 2) :
    ∃ b : ℤ, (b : ℚ) = q := by
  have hz0 : 0 ≤ z := by
    exact_mod_cast (show (0 : ℚ) ≤ z by rw [hz]; positivity)
  let n : ℕ := z.natAbs
  have hnz : (n : ℤ) = z := Int.natAbs_of_nonneg hz0
  have hnq : (n : ℚ) = (D : ℚ) * q ^ 2 := by
    rw [← hz]
    exact_mod_cast hnz
  have hsquareQ : IsSquare ((D * n : ℕ) : ℚ) := by
    refine ⟨(D : ℚ) * q, ?_⟩
    rw [Nat.cast_mul, hnq]
    ring
  have hsquareNat : IsSquare (D * n) :=
    Rat.isSquare_natCast_iff.mp hsquareQ
  obtain ⟨k, hk⟩ := hsquareNat
  have hDdvdKsq : D ∣ k ^ 2 := by
    refine ⟨n, ?_⟩
    simpa only [pow_two] using hk.symm
  have hDdvdK : D ∣ k :=
    (hDsquarefree.dvd_pow_iff_dvd (by decide)).mp hDdvdKsq
  obtain ⟨l, rfl⟩ := hDdvdK
  have hn : n = D * l ^ 2 := by
    have hk' : D * n = D * (D * l ^ 2) := by
      simpa only [pow_two] using (hk.trans (by ring))
    exact Nat.eq_of_mul_eq_mul_left hDpos hk'
  have hq : q ^ 2 = (l : ℚ) ^ 2 := by
    rw [hn] at hnq
    push_cast at hnq
    apply mul_left_cancel₀ (show (D : ℚ) ≠ 0 by positivity)
    simpa only [mul_assoc] using hnq.symm
  rcases eq_or_eq_neg_of_sq_eq_sq q (l : ℚ) hq with h | h
  · exact ⟨l, h.symm⟩
  · exact ⟨-(l : ℤ), by exact_mod_cast h.symm⟩

private theorem two_mul_mem_order
    (hDpos : 0 < D) (hDsquarefree : Squarefree D)
    (z : OK D) :
    ∃ a : ℤ√(D : ℤ), embedOrder D a = (2 : OK D) * z := by
  have htraceInt :
      IsIntegral ℤ (Algebra.trace ℚ (QD D) (z : QD D)) :=
    Algebra.isIntegral_trace z.property
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp htraceInt
  have ha' : (a : ℚ) = 2 * (z : QD D).re := by
    simpa [trace_eq D] using ha
  have hnormInt :
      IsIntegral ℤ (Algebra.norm ℚ (z : QD D)) :=
    Algebra.isIntegral_norm ℚ z.property
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnormInt
  have hc' : (c : ℚ) =
      (z : QD D).re ^ 2 - (D : ℚ) * (z : QD D).im ^ 2 := by
    simpa [norm_eq D] using hc
  let w : ℤ := a ^ 2 - 4 * c
  have hw : (w : ℚ) = (D : ℚ) * (2 * (z : QD D).im) ^ 2 := by
    dsimp [w]
    push_cast
    rw [ha', hc']
    ring
  obtain ⟨b, hb⟩ :=
    rat_eq_int_of_squarefree_mul_sq_eq_int D hDpos hDsquarefree
      (2 * (z : QD D).im) w hw
  refine ⟨⟨a, b⟩, ?_⟩
  apply NumberField.RingOfIntegers.ext
  apply QuadraticAlgebra.ext
  · simpa [embedOrder, Zsqrtd.lift_apply_apply, sqrtDO, map_ofNat] using ha'
  · simpa [embedOrder, Zsqrtd.lift_apply_apply, sqrtDO, map_ofNat] using hb

private def alphaO (s : ℤ × ℤ) : OK D :=
  embedOrder D (toZsqrtd D s)

private def betaO (s : ℤ × ℤ) : OK D :=
  embedOrder D (star (toZsqrtd D s))

private theorem alphaO_mul_betaO {M : ℤ} {s : ℤ × ℤ}
    (hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M) :
    alphaO D s * betaO D s = (M : OK D) := by
  rw [alphaO, betaO, ← map_mul, ← Zsqrtd.norm_eq_mul_conj,
    generalizedPellEquation_iff_norm.mp hs]
  exact map_intCast (embedOrder D) M

private def idealOf (M : ℤ) (s : ℤ × ℤ) :
    {I : Ideal (OK D) //
      I ∣ Ideal.span ({(M : OK D)} : Set (OK D))} := by
  by_cases hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M
  · refine ⟨Ideal.span ({alphaO D s} : Set (OK D)), ?_⟩
    refine ⟨Ideal.span ({betaO D s} : Set (OK D)), ?_⟩
    rw [Ideal.span_singleton_mul_span_singleton, alphaO_mul_betaO D hs]
  · refine ⟨⊤, ?_⟩
    refine ⟨Ideal.span ({(M : OK D)} : Set (OK D)), ?_⟩
    simp

private theorem embedOrder_injective :
    Function.Injective (embedOrder D) := by
  apply Zsqrtd.lift_injective
  intro n hn
  apply (Fact.out : ∀ r : ℚ, r ^ 2 ≠ (D : ℚ) + 0 * r) (n : ℚ)
  norm_num [pow_two]
  exact_mod_cast hn.symm

private def twoIdeal : Ideal (OK D) :=
  Ideal.span {((2 : ℕ) : OK D)}

private theorem twoIdeal_ne_bot : twoIdeal D ≠ ⊥ := by
  apply mt Ideal.span_singleton_eq_bot.mp
  norm_num

private theorem twoQuotient_natCard :
    Nat.card (OK D ⧸ twoIdeal D) = 4 := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [twoIdeal, Ideal.absNorm_span_natCast,
    NumberField.RingOfIntegers.rank]
  rw [Algebra.IsQuadraticExtension.finrank_eq_two]
  norm_num

noncomputable local instance twoQuotientFintype :
    Fintype (OK D ⧸ twoIdeal D) := by
  letI : Finite (OK D ⧸ twoIdeal D) :=
    Ring.HasFiniteQuotients.finiteQuotient (twoIdeal_ne_bot D)
  exact Fintype.ofFinite _

private theorem twoQuotient_card :
    Fintype.card (OK D ⧸ twoIdeal D) = 4 := by
  rw [← Nat.card_eq_fintype_card]
  exact twoQuotient_natCard D

private noncomputable def residueEquivFinFour :
    (OK D ⧸ twoIdeal D) ≃ Fin 4 :=
  (Fintype.equivFin _).trans (finCongr (twoQuotient_card D))

private theorem mem_twoIdeal_iff (x : OK D) :
    x ∈ twoIdeal D ↔ ∃ y : OK D, (2 : OK D) * y = x := by
  rw [twoIdeal, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa [mul_comm] using hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa [mul_comm] using hy⟩

private theorem mem_embedOrder_of_sub_one_mem_twoIdeal
    (x : OK D) (hx : x - 1 ∈ twoIdeal D)
    (hDpos : 0 < D) (hDsquarefree : Squarefree D) :
    ∃ a : ℤ√(D : ℤ), embedOrder D a = x := by
  obtain ⟨y, hy⟩ := (mem_twoIdeal_iff D (x - 1)).mp hx
  obtain ⟨a, ha⟩ := two_mul_mem_order D hDpos hDsquarefree y
  refine ⟨a + 1, ?_⟩
  rw [map_add, map_one, ha, hy]
  exact sub_add_cancel x 1

private theorem unit_mem_embedOrder_of_mod_two_eq_one
    (u : (OK D)ˣ)
    (hu : Ideal.Quotient.mk (twoIdeal D) (u : OK D) = 1)
    (hDpos : 0 < D) (hDsquarefree : Squarefree D) :
    ∃ v : (ℤ√(D : ℤ))ˣ, Units.map (embedOrder D) v = u := by
  have huMem : (u : OK D) - 1 ∈ twoIdeal D := by
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (u : OK D) 1).mp (by simpa using hu)
  obtain ⟨a, ha⟩ := mem_embedOrder_of_sub_one_mem_twoIdeal D
    (u : OK D) huMem hDpos hDsquarefree
  have huInv :
      Ideal.Quotient.mk (twoIdeal D) ((u⁻¹ : (OK D)ˣ) : OK D) = 1 := by
    let qhom : OK D →+* (OK D ⧸ twoIdeal D) :=
      Ideal.Quotient.mk (twoIdeal D)
    have huUnits : Units.map qhom.toMonoidHom u = 1 := by
      apply Units.ext
      exact hu
    have huInvUnits : Units.map qhom.toMonoidHom (u⁻¹) = 1 := by
      simpa using congrArg Inv.inv huUnits
    exact congrArg Units.val huInvUnits
  have huInvMem : ((u⁻¹ : (OK D)ˣ) : OK D) - 1 ∈ twoIdeal D := by
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      ((u⁻¹ : (OK D)ˣ) : OK D) 1).mp (by simpa using huInv)
  obtain ⟨b, hb⟩ := mem_embedOrder_of_sub_one_mem_twoIdeal D
    ((u⁻¹ : (OK D)ˣ) : OK D) huInvMem hDpos hDsquarefree
  have hab : a * b = 1 := by
    apply embedOrder_injective D
    rw [map_mul, ha, hb]
    simp
  have hba : b * a = 1 := by rw [mul_comm, hab]
  let v : (ℤ√(D : ℤ))ˣ := ⟨a, b, hab, hba⟩
  refine ⟨v, ?_⟩
  apply Units.ext
  exact ha

private def Solution (M : ℤ) :=
  {s : ℤ × ℤ // s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M}

private def solutionIdeal (M : ℤ) (s : Solution D M) : Ideal (OK D) :=
  Ideal.span ({alphaO D s.1} : Set (OK D))

private def solutionIdealSetoid (M : ℤ) : Setoid (Solution D M) where
  r s t := solutionIdeal D M s = solutionIdeal D M t
  iseqv := ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

private noncomputable def solutionRepresentative
    (M : ℤ) (s : Solution D M) : Solution D M :=
  Quotient.out (Quotient.mk (solutionIdealSetoid D M) s)

private theorem solutionRepresentative_ideal
    (M : ℤ) (s : Solution D M) :
    solutionIdeal D M (solutionRepresentative D M s) =
      solutionIdeal D M s := by
  exact Quotient.exact (Quotient.out_eq
    (Quotient.mk (solutionIdealSetoid D M) s))

private noncomputable def relativeUnit
    (M : ℤ) (s : Solution D M) : (OK D)ˣ :=
  Classical.choose
    (Ideal.span_singleton_eq_span_singleton.mp
      (solutionRepresentative_ideal D M s))

private theorem relativeUnit_spec (M : ℤ) (s : Solution D M) :
    alphaO D (solutionRepresentative D M s).1 *
        (relativeUnit D M s : OK D) = alphaO D s.1 := by
  exact Classical.choose_spec
    (Ideal.span_singleton_eq_span_singleton.mp
      (solutionRepresentative_ideal D M s))

private noncomputable def solutionColour
    (M : ℤ) (s : Solution D M) : Fin 4 :=
  residueEquivFinFour D
    (Ideal.Quotient.mk (twoIdeal D) (relativeUnit D M s : OK D))

private noncomputable def conductorColour
    (M : ℤ) (s : ℤ × ℤ) : Fin 4 :=
  if hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M then
    solutionColour D M ⟨s, hs⟩
  else 0

private theorem same_principalIdeal_of_same_extension
    (M : ℤ) (hDpos : 0 < D) (hDsquarefree : Squarefree D)
    (s t : ℤ × ℤ)
    (hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M)
    (ht : t.1 ^ 2 - (D : ℤ) * t.2 ^ 2 = M)
    (hcolour : conductorColour D M s = conductorColour D M t)
    (hideal : idealOf D M s = idealOf D M t) :
    Ideal.span ({toZsqrtd D s} : Set (ℤ√(D : ℤ))) =
      Ideal.span ({toZsqrtd D t} : Set (ℤ√(D : ℤ))) := by
  let ss : Solution D M := ⟨s, hs⟩
  let tt : Solution D M := ⟨t, ht⟩
  have hideal' : solutionIdeal D M ss = solutionIdeal D M tt := by
    have h := congrArg Subtype.val hideal
    simpa [ss, tt, idealOf, solutionIdeal, hs, ht] using h
  have hclass :
      Quotient.mk (solutionIdealSetoid D M) ss =
        Quotient.mk (solutionIdealSetoid D M) tt :=
    Quotient.sound hideal'
  have hrep :
      solutionRepresentative D M ss = solutionRepresentative D M tt := by
    exact congrArg Quotient.out hclass
  have hcolour' : solutionColour D M ss = solutionColour D M tt := by
    simpa [conductorColour, hs, ht, ss, tt] using hcolour
  have hresidue :
      Ideal.Quotient.mk (twoIdeal D) (relativeUnit D M ss : OK D) =
        Ideal.Quotient.mk (twoIdeal D) (relativeUnit D M tt : OK D) := by
    exact (residueEquivFinFour D).injective hcolour'
  let us : (OK D)ˣ := relativeUnit D M ss
  let ut : (OK D)ˣ := relativeUnit D M tt
  let w : (OK D)ˣ := us⁻¹ * ut
  have hwmod : Ideal.Quotient.mk (twoIdeal D) (w : OK D) = 1 := by
    let rho : OK D →+* (OK D ⧸ twoIdeal D) :=
      Ideal.Quotient.mk (twoIdeal D)
    have hUnits :
        Units.map rho.toMonoidHom us = Units.map rho.toMonoidHom ut := by
      apply Units.ext
      exact hresidue
    have hwUnits : Units.map rho.toMonoidHom w = 1 := by
      dsimp [w]
      simp only [map_mul, map_inv]
      calc
        (Units.map rho.toMonoidHom us)⁻¹ * Units.map rho.toMonoidHom ut =
            (Units.map rho.toMonoidHom ut)⁻¹ *
              Units.map rho.toMonoidHom ut :=
          congrArg (fun x ↦ x⁻¹ * Units.map rho.toMonoidHom ut) hUnits
        _ = 1 := by simp
    exact congrArg Units.val hwUnits
  obtain ⟨v, hv⟩ :=
    unit_mem_embedOrder_of_mod_two_eq_one D w hwmod
      hDpos hDsquarefree
  have hwRel : alphaO D s * (w : OK D) = alphaO D t := by
    calc
      alphaO D s * (w : OK D) =
          (alphaO D (solutionRepresentative D M ss).1 * (us : OK D)) *
            ((us⁻¹ : (OK D)ˣ) : OK D) * (ut : OK D) := by
              rw [relativeUnit_spec D M ss]
              simp [w, ss, us, ut, mul_assoc]
      _ = alphaO D (solutionRepresentative D M ss).1 * (ut : OK D) := by
            simp [mul_assoc]
      _ = alphaO D (solutionRepresentative D M tt).1 * (ut : OK D) := by
            rw [hrep]
      _ = alphaO D t := relativeUnit_spec D M tt
  have hvVal : embedOrder D (v : ℤ√(D : ℤ)) = (w : OK D) := by
    exact congrArg Units.val hv
  have horderRel :
      toZsqrtd D s * (v : ℤ√(D : ℤ)) = toZsqrtd D t := by
    apply embedOrder_injective D
    rw [map_mul, hvVal]
    exact hwRel
  apply le_antisymm
  · rw [Ideal.span_singleton_le_span_singleton]
    refine ⟨(v⁻¹ : (ℤ√(D : ℤ))ˣ), ?_⟩
    calc
      toZsqrtd D s =
          (toZsqrtd D s * (v : ℤ√(D : ℤ))) *
            ((v⁻¹ : (ℤ√(D : ℤ))ˣ) : ℤ√(D : ℤ)) := by
              simp [mul_assoc]
      _ = toZsqrtd D t *
            ((v⁻¹ : (ℤ√(D : ℤ))ˣ) : ℤ√(D : ℤ)) := by
              rw [horderRel]
  · rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨v, horderRel.symm⟩

private noncomputable def conductorData
    (M : ℤ) (hDpos : 0 < D) (hDsquarefree : Squarefree D) :
    QuadraticOrderConductorData D M where
  K := QD D
  idealOf := idealOf D M
  conductorColour := conductorColour D M
  same_principalIdeal_of_same_extension :=
    same_principalIdeal_of_same_extension D M hDpos hDsquarefree

end

/--
The quadratic-order conductor fibre bound, constructed entirely in Lean.

The proof uses the four residue classes of `O_K / 2 O_K`; it therefore proves
the historical `Fin 4` interface directly and does not assume the stronger
source-shaped three-unit-coset record.
-/
private theorem quadraticOrderConductorFiberBoundInternal :
    QuadraticOrderConductorFiberBoundStatement := by
  intro D M hDpos hDsquarefree hDnonsquare _hM
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (D : ℚ) + 0 * r) := ⟨by
    intro r hr
    apply hDnonsquare
    refine ⟨r, ?_⟩
    simpa [pow_two] using hr.symm⟩
  exact ⟨conductorData D M hDpos hDsquarefree⟩

end QuadraticOrderConductor

/-- Public discharge theorem for the registered Halter--Koch interface. -/
theorem quadraticOrderConductorFiberBound :
    QuadraticOrderConductorFiberBoundStatement :=
  QuadraticOrderConductor.quadraticOrderConductorFiberBoundInternal

end

end PellInput
end PaperC
