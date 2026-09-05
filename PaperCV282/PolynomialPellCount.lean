import PaperC.Diophantine.HalterKochConductorDescent
import PaperCV282.DivisorSubpolynomial

/-!
# Unconditional Pell counting in polynomial-height boxes

The internally proved conductor comparison and unit-orbit count give a
finite divisor envelope. Elementary divisor subpolynomiality then gives
`M^epsilon`, uniformly in every coefficient and solution height in a
fixed polynomial box. No explicit Nicolas--Robin estimate is assumed;
the sharper `exp(O(log M / log log M))` rate is not asserted here.
-/

namespace PaperC.V282.PolynomialPellCount

open PellInput DivisorSubpolynomial LogarithmicWordPowers

noncomputable section

/-- The conductor comparison and squarefree reduction give an unconditional finite envelope. -/
theorem generalizedPellBox_atMost_divisor_orbit
    {D H : ℕ} {m : ℤ} (hDpos : 0 < D)
    (hD : ¬ IsSquare (D : ℚ)) (hm : m ≠ 0) :
    HasAtMostSolutionsReal (generalizedPellBox D m H)
      (((4 * m.natAbs.divisors.card ^ 2) * pellUnitOrbitEnvelope (D * H) : ℕ) : ℝ) := by
  obtain ⟨a, b, ha, hb, hasq, hdecomp, hanonsq⟩ := exists_squarefree_reduction hDpos hD
  exact hasAtMostSolutionsReal_of_squarefree_reduction ha hb hdecomp
    (squarefreeGeneralizedPellBox_atMost_of_conductorComparison
      quadraticOrderConductorFiberBound ha hasq hanonsq hm)

/-- The nonsquare-ratio condition is exactly what the generalized Pell substitution needs. -/
theorem product_not_isSquare_of_ratio_not_isSquare
    {A C : ℕ} (hC : 0 < C) (hratio : ¬ IsSquare ((A : ℚ) / (C : ℚ))) :
    ¬ IsSquare ((A * C : ℕ) : ℚ) := by
  rintro ⟨q, hq⟩
  apply hratio
  refine ⟨q / (C : ℚ), ?_⟩
  have hCne : (C : ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  have hq' : (A : ℚ) * (C : ℚ) = q * q := by
    simpa only [Nat.cast_mul, pow_two] using hq
  calc
    (A : ℚ) / (C : ℚ) = ((A : ℚ) * C) / ((C : ℚ) * C) := by field_simp
    _ = (q * q) / ((C : ℚ) * C) := by rw [hq']
    _ = (q / (C : ℚ)) * (q / (C : ℚ)) := by field_simp

/-- Scaling the first coordinate preserves distinct integral solutions. -/
theorem originalToGeneralized_injective {A : ℕ} (hA : 0 < A) :
    Function.Injective (fun s : ℤ × ℤ => ((A : ℤ) * s.1, s.2)) := by
  intro u v huv
  have hfirst : (A : ℤ) * u.1 = (A : ℤ) * v.1 := congrArg Prod.fst huv
  have hsecond := congrArg (fun z : ℤ × ℤ => z.2) huv
  change u.2 = v.2 at hsecond
  have hAne : (A : ℤ) ≠ 0 := by exact_mod_cast hA.ne'
  exact Prod.ext (mul_left_cancel₀ hAne hfirst) hsecond

/-- Exact equation transfer, with the enlarged height displayed explicitly. -/
theorem original_maps_to_generalized
    {A C H : ℕ} {e : ℤ} {s : ℤ × ℤ} (hA : 0 < A)
    (hs : pellBox A C e H s) :
    generalizedPellBox (A * C) ((A : ℤ) * e) (A * H) ((A : ℤ) * s.1, s.2) := by
  obtain ⟨heq, hx, hy⟩ := hs
  refine ⟨?_, ?_, hy.trans (Nat.le_mul_of_pos_left H hA)⟩
  · change ((A : ℤ) * s.1) ^ 2 - ((A * C : ℕ) : ℤ) * s.2 ^ 2 = (A : ℤ) * e
    calc
      _ = (A : ℤ) * ((A : ℤ) * s.1 ^ 2 - (C : ℤ) * s.2 ^ 2) := by push_cast; ring
      _ = _ := by rw [heq]
  · simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul_left A hx

/-- Finite original-Pell counting; squarefreeness of the two coefficients is unnecessary. -/
theorem pellBox_atMost_divisor_orbit
    {A C H : ℕ} {e : ℤ} (hA : 0 < A) (hC : 0 < C)
    (hratio : ¬ IsSquare ((A : ℚ) / (C : ℚ))) (he : e ≠ 0) :
    HasAtMostSolutionsReal (pellBox A C e H)
      (((4 * ((A : ℤ) * e).natAbs.divisors.card ^ 2) *
        pellUnitOrbitEnvelope ((A * C) * (A * H)) : ℕ) : ℝ) := by
  classical
  have hAe : (A : ℤ) * e ≠ 0 := mul_ne_zero (by exact_mod_cast hA.ne') he
  have hcount := generalizedPellBox_atMost_divisor_orbit (H := A * H)
    (Nat.mul_pos hA hC) (product_not_isSquare_of_ratio_not_isSquare hC hratio) hAe
  intro s hs
  have hi : ∀ t ∈ s.image (fun u : ℤ × ℤ => ((A : ℤ) * u.1, u.2)),
      generalizedPellBox (A * C) ((A : ℤ) * e) (A * H) t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact original_maps_to_generalized hA (hs u hu)
  simpa only [Finset.card_image_of_injective _ (originalToGeneralized_injective hA)]
    using hcount _ hi

/-- The logarithmic unit-orbit factor, including the fixed factor four, is uniformly subpolynomial. -/
theorem four_mul_pellUnitOrbitEnvelope_le_rpow_eventually
    (K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ H : ℕ, H ≤ M ^ K →
      4 * (pellUnitOrbitEnvelope H : ℝ) ≤ (M : ℝ) ^ epsilon := by
  let C : ℝ := ((2 * K + 1 : ℕ) : ℝ) / Real.log 2 + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨Mpoly, hpoly⟩ := polynomial_factor_le_rpow_eventually C hC 24 1 epsilon hepsilon
  refine ⟨max Mpoly (max 2 (⌈Real.exp 1⌉₊ + 1)), ?_⟩
  intro M hM H hH
  have htail : max 2 (⌈Real.exp 1⌉₊ + 1) ≤ M := (le_max_right _ _).trans hM
  have hMtwo : 2 ≤ M := (le_max_left _ _).trans htail
  have hexp : Real.exp 1 ≤ (M : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈Real.exp 1⌉₊ ≤ M by have := (le_max_right _ _).trans htail; omega))
  have hlogOne : 1 ≤ Real.log M := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have harg : 2 * H ^ 2 ≤ M ^ (2 * K + 1) := by
    calc
      _ ≤ M * (M ^ K) ^ 2 := Nat.mul_le_mul hMtwo (Nat.pow_le_pow_left hH _)
      _ = _ := by rw [← pow_mul, Nat.mul_comm K 2, pow_succ'];
  have hlog : (Nat.log 2 (2 * H ^ 2) : ℝ) ≤
      (((2 * K + 1 : ℕ) : ℝ) / Real.log 2) * Real.log M := by
    by_cases hHzero : H = 0
    · subst H
      simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, Nat.log_zero_right, Nat.cast_zero]
      positivity
    · exact binary_log_le_polynomial_log (by positivity) harg
  have hceiling : ((Nat.log 2 (2 * H ^ 2) + 1 : ℕ) : ℝ) ≤ C * Real.log M := by
    dsimp [C]
    push_cast at hlog
    push_cast
    nlinarith only [hlog, hlogOne]
  have hbound := hpoly M ((le_max_left _ _).trans hM) (Nat.log 2 (2 * H ^ 2)) hceiling
  have hbound' : (24 : ℝ) * (Nat.log 2 (2 * H ^ 2) + 1 : ℝ) ≤ (M : ℝ) ^ epsilon := by
    simpa only [pow_one, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ 24 * (Nat.log 2 (2 * H ^ 2) + 1 : ℝ))] using hbound
  apply le_trans _ hbound'
  unfold pellUnitOrbitEnvelope
  push_cast
  nlinarith only [show (0 : ℝ) ≤ Nat.log 2 (2 * H ^ 2) by positivity]

/-- Generalized Pell solutions are uniformly at most every fixed positive power of the ambient scale. -/
theorem generalizedPellBox_atMost_rpow_eventually
    (K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ D H : ℕ, ∀ m : ℤ,
      0 < D → ¬ IsSquare (D : ℚ) → m ≠ 0 →
      D ≤ M ^ K → H ≤ M ^ K → m.natAbs ≤ M ^ K →
      HasAtMostSolutionsReal (generalizedPellBox D m H) ((M : ℝ) ^ epsilon) := by
  obtain ⟨Md, hd⟩ := card_divisors_le_rpow_eventually K (epsilon / 4) (by positivity)
  obtain ⟨Mo, ho⟩ := four_mul_pellUnitOrbitEnvelope_le_rpow_eventually (2 * K)
    (epsilon / 2) (by positivity)
  refine ⟨max Md (max Mo 1), ?_⟩
  intro M hM D H m hDpos hD hm hDM hHM hmM
  have htail : max Mo 1 ≤ M := (le_max_right _ _).trans hM
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by have := (le_max_right _ _).trans htail; omega)
  have hdiv := hd M ((le_max_left _ _).trans hM) m.natAbs hmM
  have hheight : D * H ≤ M ^ (2 * K) := by
    calc
      _ ≤ M ^ K * M ^ K := Nat.mul_le_mul hDM hHM
      _ = _ := by rw [← pow_add]; congr 1; omega
  have horbit := ho M ((le_max_left _ _).trans htail) (D * H) hheight
  have henvelope :
      (((4 * m.natAbs.divisors.card ^ 2) * pellUnitOrbitEnvelope (D * H) : ℕ) : ℝ)
        ≤ (M : ℝ) ^ epsilon := by
    push_cast
    calc
      _ = (m.natAbs.divisors.card : ℝ) ^ 2 * (4 * (pellUnitOrbitEnvelope (D * H) : ℝ)) := by ring
      _ ≤ ((M : ℝ) ^ (epsilon / 4)) ^ 2 * (M : ℝ) ^ (epsilon / 2) := by gcongr
      _ = (M : ℝ) ^ epsilon := by
        rw [pow_two, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
        congr 1
        ring
  intro s hs
  exact (generalizedPellBox_atMost_divisor_orbit hDpos hD hm s hs).trans henvelope

/-- The original two-coefficient Pell equation has the same unconditional polynomial-height consequence. -/
theorem pellBox_atMost_rpow_eventually
    (K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ A C H : ℕ, ∀ e : ℤ,
      0 < A → 0 < C → ¬ IsSquare ((A : ℚ) / (C : ℚ)) → e ≠ 0 →
      A ≤ M ^ K → C ≤ M ^ K → H ≤ M ^ K → e.natAbs ≤ M ^ K →
      HasAtMostSolutionsReal (pellBox A C e H) ((M : ℝ) ^ epsilon) := by
  classical
  obtain ⟨Mzero, hcount⟩ := generalizedPellBox_atMost_rpow_eventually (2 * K) epsilon hepsilon
  refine ⟨Mzero, ?_⟩
  intro M hM A C H e hA hC hratio he hAM hCM hHM heM
  have hmul : ∀ a b : ℕ, a ≤ M ^ K → b ≤ M ^ K → a * b ≤ M ^ (2 * K) := by
    intro a b ha hb
    calc
      _ ≤ M ^ K * M ^ K := Nat.mul_le_mul ha hb
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hAe : (A : ℤ) * e ≠ 0 := mul_ne_zero (by exact_mod_cast hA.ne') he
  have heheight : ((A : ℤ) * e).natAbs ≤ M ^ (2 * K) := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hmul A e.natAbs hAM heM
  have hgeneral := hcount M hM (A * C) (A * H) ((A : ℤ) * e)
    (Nat.mul_pos hA hC) (product_not_isSquare_of_ratio_not_isSquare hC hratio) hAe
    (hmul A C hAM hCM) (hmul A H hAM hHM) heheight
  intro s hs
  have hi : ∀ t ∈ s.image (fun u : ℤ × ℤ => ((A : ℤ) * u.1, u.2)),
      generalizedPellBox (A * C) ((A : ℤ) * e) (A * H) t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact original_maps_to_generalized hA (hs u hu)
  simpa only [Finset.card_image_of_injective _ (originalToGeneralized_injective hA)]
    using hgeneral _ hi

end
end PaperC.V282.PolynomialPellCount
