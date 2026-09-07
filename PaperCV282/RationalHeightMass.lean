import PaperCV282.IntervalRationalMass

/-!
# Separate interval masses at canonical rational heights

The two sums use the selected historical canonical channel and its exact
weight `2^sigma - 1`. They are restricted to height two and height at
least three, respectively. Separation forces every omitted height to
have zero weight, so the two masses sum to the full rational mass.
-/

namespace PaperC.V282.RationalHeightMass

open Affine Affine.CanonicalRationalCode BoundedRatioGeometry RationalMassFinite
open scoped BigOperators

noncomputable section

/-- The actual canonical rational mass restricted to height two. -/
def rationalHeightTwoMass (N M A L : ℕ) : ℕ :=
  ∑ pair ∈ (separatedBoundedRatioPairs N M L).filter
      (fun pair => canonicalPairHeight A L pair.1 pair.2 = 2),
    (2 ^ canonicalPairSigma A L pair.1 pair.2 - 1)

/-- The actual canonical rational mass restricted to heights at least three. -/
def rationalHeightAtLeastThreeMass (N M A L : ℕ) : ℕ :=
  ∑ pair ∈ (separatedBoundedRatioPairs N M L).filter
      (fun pair => 3 ≤ canonicalPairHeight A L pair.1 pair.2),
    (2 ^ canonicalPairSigma A L pair.1 pair.2 - 1)

/-- A separated pair cannot have a positive canonical weight at height below two. -/
theorem canonicalPairSigma_eq_zero_of_height_lt_two
    {N M A L x y : ℕ}
    (hpair : (x, y) ∈ separatedBoundedRatioPairs N M L)
    (hheight : canonicalPairHeight A L x y < 2) :
    canonicalPairSigma A L x y = 0 := by
  by_contra hsigma
  have hmCanonical : 2 ≤ canonicalMultiplicity A L x y :=
    two_le_canonicalMultiplicity_of_sigma_pos (Nat.pos_of_ne_zero hsigma)
  obtain ⟨c, hchoice, hm⟩ :=
    exists_canonical_candidate_of_two_le_multiplicity hmCanonical
  rw [canonicalPairHeight_eq_of_choice hchoice] at hheight
  have hqPos : 0 < Nat.max c.1.1 c.1.2 :=
    (candidate_fst_pos c).trans_le (Nat.le_max_left _ _)
  have hqOne : Nat.max c.1.1 c.1.2 = 1 := by omega
  have hcells : 2 ≤ (channelCells L c.1.1 c.1.2
      (pairChannelError x y c.1.1 c.1.2)).card := by
    simpa [candidateMultiplicity] using hm
  have hnear := height_one_primitive_channel_forces_unit_and_nearby
    (candidate_fst_pos c) (candidate_snd_pos c) (candidate_coprime c)
    hqOne (h := pairChannelError x y c.1.1 c.1.2) rfl hcells
  have hsep := (mem_separatedBoundedRatioPairs.mp hpair).2.2
  omega

/-- Height-two weights are supported on the volumetric height-two cover. -/
theorem canonicalPairWeight_le_height_two_cover
    {N M A L x y : ℕ}
    (hpair : (x, y) ∈ separatedBoundedRatioPairs N M L)
    (hheight : canonicalPairHeight A L x y = 2) :
    2 ^ canonicalPairSigma A L x y - 1 ≤
      if (x, y) ∈ boundedHeightTwoPairCover N M L then 2 ^ (L / 2) else 0 := by
  by_cases hsigma : canonicalPairSigma A L x y = 0
  · simp [hsigma]
  have hmCanonical : 2 ≤ canonicalMultiplicity A L x y :=
    two_le_canonicalMultiplicity_of_sigma_pos (Nat.pos_of_ne_zero hsigma)
  obtain ⟨c, hchoice, hm⟩ :=
    exists_canonical_candidate_of_two_le_multiplicity hmCanonical
  have hmax : Nat.max c.1.1 c.1.2 = 2 := by
    simpa only [canonicalPairHeight_eq_of_choice hchoice] using hheight
  have hmem := pair_mem_boundedHeightTwoPairCover_of_choice hpair hm hmax
  rw [if_pos hmem]
  simpa only [hmax] using
    (canonicalPairWeight_le_pow_div_of_choice (base := 2) (by omega) hchoice)

/-- Weights of height at least three are supported on the large-height cover. -/
theorem canonicalPairWeight_le_height_three_cover
    {N M A L x y : ℕ}
    (hpair : (x, y) ∈ separatedBoundedRatioPairs N M L)
    (hheight : 3 ≤ canonicalPairHeight A L x y) :
    2 ^ canonicalPairSigma A L x y - 1 ≤
      if (x, y) ∈ boundedLargeChannelPairCover N M L then 2 ^ (L / 3) else 0 := by
  by_cases hsigma : canonicalPairSigma A L x y = 0
  · simp [hsigma]
  have hmCanonical : 2 ≤ canonicalMultiplicity A L x y :=
    two_le_canonicalMultiplicity_of_sigma_pos (Nat.pos_of_ne_zero hsigma)
  obtain ⟨c, hchoice, hm⟩ :=
    exists_canonical_candidate_of_two_le_multiplicity hmCanonical
  have hmax : 3 ≤ Nat.max c.1.1 c.1.2 := by
    simpa only [canonicalPairHeight_eq_of_choice hchoice] using hheight
  have hmaxL : Nat.max c.1.1 c.1.2 ≤ L :=
    candidate_max_le_length_of_two_units c hm
  have hmem := pair_mem_boundedLargeChannelPairCover_of_choice hpair hm hmax hmaxL
  rw [if_pos hmem]
  exact (canonicalPairWeight_le_pow_div_of_choice (base := 2) (by omega) hchoice).trans
    (Nat.pow_le_pow_right (by omega) (Nat.div_le_div_left hmax (by omega)))

/-- A finite sum of a constant supported on a cover is bounded by its cardinality. -/
theorem sum_cover_weight_le_card_mul
    {T : Type*} [DecidableEq T] (s t : Finset T) (w : ℕ) :
    (∑ x ∈ s, if x ∈ t then w else 0) ≤ t.card * w := by
  have hsubset : s.filter (fun x => x ∈ t) ⊆ t := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  calc
    _ = ∑ x ∈ s.filter (fun x => x ∈ t), w := by rw [Finset.sum_filter]
    _ = (s.filter (fun x => x ∈ t)).card * w := by simp
    _ ≤ t.card * w := Nat.mul_le_mul_right w (Finset.card_le_card hsubset)

/-- Separate volumetric bound for the true height-two mass. -/
theorem rationalHeightTwoMass_le_interval_profile
    {N M A L : ℕ} (hM : 1 ≤ M) (hNM : N ≤ M) (_hA : 1 ≤ A) :
    rationalHeightTwoMass N M A L ≤ 6 * M * (L + 1) * 2 ^ (L / 2) := by
  have hsum : rationalHeightTwoMass N M A L ≤
      (boundedHeightTwoPairCover N M L).card * 2 ^ (L / 2) := by
    unfold rationalHeightTwoMass
    refine (Finset.sum_le_sum fun pair hpair => ?_).trans
      (sum_cover_weight_le_card_mul _ (boundedHeightTwoPairCover N M L) (2 ^ (L / 2)))
    exact canonicalPairWeight_le_height_two_cover
      (Finset.mem_filter.mp hpair).1 (Finset.mem_filter.mp hpair).2
  have hwidth : 1 + (M - N) / 2 ≤ M :=
    IntervalRationalMass.one_add_width_div_le hM (by omega)
  have hcard : (boundedHeightTwoPairCover N M L).card ≤ 6 * M * (L + 1) := by
    calc
      _ ≤ 2 * ((3 * L + 1) * (1 + (M - N) / 2)) :=
        card_boundedHeightTwoPairCover_le hNM
      _ ≤ 2 * ((3 * (L + 1)) * M) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul (by omega) hwidth)
      _ = 6 * M * (L + 1) := by ring
  exact hsum.trans (Nat.mul_le_mul_right _ hcard)

/-- Separate volumetric bound for the true mass at heights at least three. -/
theorem rationalHeightAtLeastThreeMass_le_interval_profile
    {N M A L : ℕ} (hM : 1 ≤ M) (hNM : N ≤ M) (_hA : 1 ≤ A) :
    rationalHeightAtLeastThreeMass N M A L ≤
      4 * M * (L + 1) ^ 4 * 2 ^ (L / 3) := by
  have hsum : rationalHeightAtLeastThreeMass N M A L ≤
      (boundedLargeChannelPairCover N M L).card * 2 ^ (L / 3) := by
    unfold rationalHeightAtLeastThreeMass
    refine (Finset.sum_le_sum fun pair hpair => ?_).trans
      (sum_cover_weight_le_card_mul _ (boundedLargeChannelPairCover N M L) (2 ^ (L / 3)))
    exact canonicalPairWeight_le_height_three_cover
      (Finset.mem_filter.mp hpair).1 (Finset.mem_filter.mp hpair).2
  have hwidth : 1 + (M - N) / 3 ≤ M :=
    IntervalRationalMass.one_add_width_div_le hM (by omega)
  have hL : L ≤ L + 1 := by omega
  have hquad : (2 * L) * L + 1 ≤ 2 * (L + 1) ^ 2 := by nlinarith
  have hcard : (boundedLargeChannelPairCover N M L).card ≤ 4 * M * (L + 1) ^ 4 := by
    calc
      _ ≤ L * (2 * L) * ((2 * L) * L + 1) * (1 + (M - N) / 3) :=
        card_boundedLargeChannelPairCover_le hNM
      _ ≤ (L + 1) * (2 * (L + 1)) * (2 * (L + 1) ^ 2) * M :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul hL (Nat.mul_le_mul_left 2 hL)) hquad)
          hwidth
      _ = 4 * M * (L + 1) ^ 4 := by ring
  exact hsum.trans (Nat.mul_le_mul_right _ hcard)

/-- Exact decomposition: no positive weight is lost at heights zero or one. -/
theorem boundedRationalMass_eq_height_masses (N M A L : ℕ) :
    boundedRationalMass N M A L 2 =
      rationalHeightTwoMass N M A L + rationalHeightAtLeastThreeMass N M A L := by
  unfold boundedRationalMass rationalHeightTwoMass rationalHeightAtLeastThreeMass
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair hpair
  by_cases htwo : canonicalPairHeight A L pair.1 pair.2 = 2
  · have hthree : ¬ 3 ≤ canonicalPairHeight A L pair.1 pair.2 := by omega
    simp only [if_pos htwo, if_neg hthree, Nat.add_zero]
  · by_cases hthree : 3 ≤ canonicalPairHeight A L pair.1 pair.2
    · simp only [if_neg htwo, if_pos hthree, Nat.zero_add]
    · have hlow : canonicalPairHeight A L pair.1 pair.2 < 2 := by omega
      have hzero := canonicalPairSigma_eq_zero_of_height_lt_two hpair hlow
      simp [htwo, hthree, hzero]

end
end PaperC.V282.RationalHeightMass
