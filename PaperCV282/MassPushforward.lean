import PaperCV282.FiniteFieldTotalVariation
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Deterministic images of discrete probability laws

The source and target types need not be finite. In particular, the source can
be the full count space of a finite Poisson field. Every deterministic statistic
and coordinate restriction contracts the half-L1 total variation used here.
-/

namespace PaperC.V282.MassPushforward

open FiniteFieldTotalVariation ArratiaGoldsteinGordonInput

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The mass of a fibre of a deterministic map. -/
def pushforwardMass {α β : Type*} (f : α → β) (p : α → ℝ) (b : β) : ℝ :=
  ∑' a : f ⁻¹' {b}, p a

theorem pushforwardMass_nonneg {α β : Type*} (f : α → β) {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (b : β) : 0 ≤ pushforwardMass f p b :=
  tsum_nonneg fun a => hp a

theorem hasSum_pushforwardMass {α β : Type*} (f : α → β) {p : α → ℝ}
    {c : ℝ} (hp : HasSum p c) : HasSum (pushforwardMass f p) c :=
  hp.tsum_fiberwise f

/-- Summing masses over the fibre is the same as restricting by its indicator. -/
theorem pushforwardMass_eq_restricted {α β : Type*} (f : α → β) (p : α → ℝ)
    (b : β) : pushforwardMass f p b = ∑' a, if f a = b then p a else 0 := by
  classical
  rw [pushforwardMass, tsum_subtype]
  rfl

/-- Deterministic postprocessing cannot increase discrete total variation. -/
theorem massTotalVariation_pushforward_le {α β : Type*} (f : α → β)
    {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ a, 0 ≤ p a) (hq0 : ∀ a, 0 ≤ q a) :
    massTotalVariation (pushforwardMass f p) (pushforwardMass f q) ≤
      massTotalVariation p q := by
  have habs := summable_abs_sub_of_nonneg hp.summable hq.summable hp0 hq0
  have hfabs := habs.hasSum.tsum_fiberwise f
  have hsum := (summable_abs_sub_of_nonneg
    (hasSum_pushforwardMass f hp).summable (hasSum_pushforwardMass f hq).summable
    (pushforwardMass_nonneg f hp0) (pushforwardMass_nonneg f hq0)).tsum_le_tsum
    (fun b => show |pushforwardMass f p b - pushforwardMass f q b| ≤
        ∑' a : f ⁻¹' {b}, |p a - q a| from by
      have hpf : Summable (fun a : f ⁻¹' {b} => p a) := hp.summable.subtype _
      have hqf : Summable (fun a : f ⁻¹' {b} => q a) := hq.summable.subtype _
      rw [pushforwardMass, pushforwardMass, ← hpf.tsum_sub hqf]
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hpf.sub hqf).norm) hfabs.summable
  rw [hfabs.tsum_eq] at hsum
  exact mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2⁻¹)

/-- The image of a true finite-source law is the law of the composed statistic. -/
theorem pushforwardMass_finiteFieldLaw {Ω α β : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → α) (f : α → β) :
    pushforwardMass f (finiteFieldLaw μ Z) = finiteFieldLaw μ (fun ω => f (Z ω)) := by
  classical
  funext b
  rw [pushforwardMass_eq_restricted]
  have h := restricted_finiteFieldLaw_eq_eventProbability μ Z {a | f a = b}
  convert h using 1
  · congr 1
  · unfold eventProbability finiteFieldLaw
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxb : f (Z x) = b <;> simp [hxb]

/-- A bound for a full field also bounds any deterministic statistic of it. -/
theorem finiteFieldLaw_statistic_bound {Ω α β : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → α) (f : α → β) {q : α → ℝ}
    (hq : HasSum q 1) (hq0 : ∀ a, 0 ≤ q a) {r : ℝ}
    (h : massTotalVariation (finiteFieldLaw μ Z) q ≤ r) :
    massTotalVariation (finiteFieldLaw μ (fun ω => f (Z ω)))
      (pushforwardMass f q) ≤ r := by
  rw [← pushforwardMass_finiteFieldLaw]
  exact (massTotalVariation_pushforward_le f (hasSum_finiteFieldLaw μ Z) hq
    (finiteFieldLaw_nonneg μ Z) hq0).trans h

end

end PaperC.V282.MassPushforward
