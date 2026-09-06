import PaperCV282.MassPushforward
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Exact reindexing from excess marks to moving integer levels

All labels, including position and sign, are retained. This is a bijection
of finite configurations and therefore preserves half-L1 total variation
exactly. It introduces no approximation or probabilistic input.
-/
namespace PaperC.V282.MovingMarkedLevels

open FiniteFieldTotalVariation MassPushforward MeasureTheory

noncomputable section

/-- The retained levels start at minus the depth. -/
def MovingLevel (d : ℕ) := {r : ℤ // -(d : ℤ) ≤ r}

instance instCountableMovingLevel (d : ℕ) : Countable (MovingLevel d) :=
  inferInstanceAs (Countable {r : ℤ // -(d : ℤ) ≤ r})

/-- An excess e represents the integer level e-d. -/
def levelEquiv (d : ℕ) : ℕ ≃ MovingLevel d where
  toFun e := ⟨(e : ℤ)-d, by omega⟩
  invFun r := (r.val+d).toNat
  left_inv e := by simp
  right_inv r := by
    apply Subtype.ext
    have hr := r.property
    dsimp
    rw [Int.toNat_of_nonneg (by omega)]
    omega

theorem levelEquiv_val (d e : ℕ) : ((levelEquiv d e).val : ℤ) = (e : ℤ)-d := rfl

theorem levelEquiv_symm_val (d : ℕ) (r : MovingLevel d) :
    ((levelEquiv d).symm r : ℤ) = r.val+d := by
  exact Int.toNat_of_nonneg (by have := r.property; omega)

/-- The physical run length is unchanged by moving-level notation. -/
theorem runLength_eq (b d e : ℕ) (hd : d ≤ b) :
    ((b-d+e : ℕ) : ℤ) = (b : ℤ)+(levelEquiv d e).val := by
  rw [levelEquiv_val]
  omega

/-- Retain both the position and the sign while changing the excess coordinate. -/
def labelledLevelEquiv (α σ : Type*) (d : ℕ) :
    α × (ℕ × σ) ≃ α × (MovingLevel d × σ) :=
  Equiv.prodCongr (Equiv.refl α) (Equiv.prodCongr (levelEquiv d) (Equiv.refl σ))

/-- Reindex a finite configuration without aggregating any coordinate. -/
def configurationEquiv (α σ : Type*) (d : ℕ) :
    (α × (ℕ × σ) →₀ ℕ) ≃ (α × (MovingLevel d × σ) →₀ ℕ) :=
  Finsupp.equivCongrLeft (labelledLevelEquiv α σ d)

theorem configurationEquiv_apply (α σ : Type*) (d : ℕ)
    (c : α × (ℕ × σ) →₀ ℕ) (x : α) (e : ℕ) (s : σ) :
    configurationEquiv α σ d c (x,levelEquiv d e,s) = c (x,e,s) := by
  simp [configurationEquiv, Finsupp.equivCongrLeft_apply,
    Finsupp.equivMapDomain_apply, labelledLevelEquiv]

/-- A bijective statistic has a singleton fibre, with exactly the original mass. -/
theorem pushforwardMass_equiv {α β : Type*} (e : α ≃ β) (p : α → ℝ) (b : β) :
    pushforwardMass e p b = p (e.symm b) := by
  classical
  rw [pushforwardMass_eq_restricted]
  simp only [e.apply_eq_iff_eq_symm_apply]
  simp

/-- Exact total-variation invariance needs no normalization assumptions. -/
theorem massTotalVariation_equiv {α β : Type*} (e : α ≃ β) (p q : α → ℝ) :
    massTotalVariation (pushforwardMass e p) (pushforwardMass e q) =
      massTotalVariation p q := by
  simp only [massTotalVariation, pushforwardMass_equiv]
  congr 1
  exact e.symm.tsum_eq (fun a => |p a-q a|)

theorem configuration_totalVariation_eq (α σ : Type*) (d : ℕ)
    (p q : (α × (ℕ × σ) →₀ ℕ) → ℝ) :
    massTotalVariation (pushforwardMass (configurationEquiv α σ d) p)
      (pushforwardMass (configurationEquiv α σ d) q) = massTotalVariation p q :=
  massTotalVariation_equiv _ p q

/-- Injective maps preserve singleton masses on their image. -/
theorem pushforwardMass_injective_apply {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (p : α → ℝ) (a : α) :
    pushforwardMass f p (f a) = p a := by
  classical
  rw [pushforwardMass_eq_restricted]
  simp only [hf.eq_iff]
  simp

theorem pushforwardMass_zero_off_range {α β : Type*} (f : α → β) (p : α → ℝ)
    {b : β} (hb : b ∉ Set.range f) : pushforwardMass f p b = 0 := by
  classical
  rw [pushforwardMass_eq_restricted]
  have he : ∀ a, f a ≠ b := fun a h => hb ⟨a,h⟩
  simp [he]

/-- In particular, viewing a supported path as a full function loses no TV. -/
theorem massTotalVariation_injective {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (p q : α → ℝ) :
    massTotalVariation (pushforwardMass f p) (pushforwardMass f q) =
      massTotalVariation p q := by
  unfold massTotalVariation
  congr 1
  have hs : Function.support (fun b => |pushforwardMass f p b-pushforwardMass f q b|) ⊆
      Set.range f := by
    intro b hb
    by_contra h
    have hp := pushforwardMass_zero_off_range f p h
    have hq := pushforwardMass_zero_off_range f q h
    simp [Function.mem_support,hp,hq] at hb
  have h := hf.tsum_eq hs
  simpa only [pushforwardMass_injective_apply f hf] using h.symm

/-- Countable configurations give a measurable bijection for any discrete sigma-algebras. -/
theorem measurable_configurationEquiv (α σ : Type*) [Countable α] [Countable σ]
    (d : ℕ) [MeasurableSpace (α × (ℕ × σ) →₀ ℕ)]
    [MeasurableSingletonClass (α × (ℕ × σ) →₀ ℕ)]
    [MeasurableSpace (α × (MovingLevel d × σ) →₀ ℕ)] :
    Measurable (configurationEquiv α σ d) := by
  exact measurable_of_countable _

theorem measurable_configurationEquiv_symm (α σ : Type*) [Countable α] [Countable σ]
    (d : ℕ) [MeasurableSpace (α × (MovingLevel d × σ) →₀ ℕ)]
    [MeasurableSingletonClass (α × (MovingLevel d × σ) →₀ ℕ)]
    [MeasurableSpace (α × (ℕ × σ) →₀ ℕ)] :
    Measurable (configurationEquiv α σ d).symm := by
  exact measurable_of_countable _

end
end PaperC.V282.MovingMarkedLevels
