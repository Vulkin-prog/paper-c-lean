import PaperC.Arithmetic.ChannelStartPairs
import PaperC.Combinatorics.ResidualMasses
import PaperC.Combinatorics.CanonicalResidualAmbientCertificate
import PaperC.Combinatorics.CertificateLemmaSevenOne

set_option maxHeartbeats 2400000

/-!
# The one-dimensional CRT cover on a fixed positive rational channel

This file supplies the concrete covering step in the `σ > 0` part of
Proposition 7.3.  After fixing a canonical channel `(a,b,h)` and a residual
certificate size `r`, the relevant separated pairs form a finite population.
Projection to the left start is injective, and every projected start belongs
to the one-dimensional CRT solution set of its canonical residual
certificate in the common ambient cell family of that channel.
-/

namespace PaperC
namespace PositiveSigmaFixedChannelCover

open Finset
open scoped BigOperators
open Affine
open Affine.CanonicalRationalCode
open CanonicalResidualComponents
open ResidualComponentCounts
open ResidualMasses
open RationalMassFinite

noncomputable section

/--
Proof-carrying assertion that a separated pair has the fixed canonical
channel `(a,b,h)` and exactly `r` canonical residual components.
-/
structure FixedChannelWitness
    (A L a b : ℕ) (h : ℤ) (r : ℕ)
    (pair : ℕ × ℕ) where
  candidate_mem :
    (a, b) ∈
      reducedChannelCandidates
        pair.1 pair.2 (L + 1) ((L + 1) ^ A)
  choice :
    canonicalReducedCandidate?
        pair.1 pair.2 (L + 1) ((L + 1) ^ A) =
      some ⟨(a, b), candidate_mem⟩
  error_eq :
    pairChannelError pair.1 pair.2 a b = h
  count_eq :
    canonicalResidualComponentCount A pair.1 pair.2 L = r

/-- The bundled reduced candidate carried by a fixed-channel witness. -/
abbrev FixedChannelWitness.candidate
    {A L a b : ℕ} {h : ℤ} {r : ℕ} {pair : ℕ × ℕ}
    (w : FixedChannelWitness A L a b h r pair) :
    ReducedCandidate pair.1 pair.2 (L + 1) ((L + 1) ^ A) :=
  ⟨(a, b), w.candidate_mem⟩

/--
The active `P# ≤ N`, `σ>0` population on one fixed canonical channel and
with one fixed residual-certificate size.
-/
noncomputable def fixedChannelPairs
    (N A L a b : ℕ) (h : ℤ) (r : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact
    (positiveSigmaSmallProductPairs N A L hN).filter fun pair ↦
      Nonempty (FixedChannelWitness A L a b h r pair.1)

@[simp]
theorem mem_fixedChannelPairs
    {N A L a b r : ℕ} {h : ℤ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ fixedChannelPairs N A L a b h r hN ↔
      pair ∈ positiveSigmaSmallProductPairs N A L hN ∧
        Nonempty (FixedChannelWitness A L a b h r pair.1) := by
  simp [fixedChannelPairs]

/-- Left starts of the fixed-channel population. -/
noncomputable def fixedChannelFirstCoordinates
    (N A L a b : ℕ) (h : ℤ) (r : ℕ) (hN : 2 ≤ N) :
    Finset ℕ :=
  (fixedChannelPairs N A L a b h r hN).image
    (fun pair ↦ pair.1.1)

/-- A member of the fixed-channel population lies on the stated channel. -/
theorem pair_mem_channelStartPairs_of_mem_fixedChannelPairs
    {N A L a b r : ℕ} {h : ℤ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ fixedChannelPairs N A L a b h r hN) :
    pair.1 ∈ channelStartPairs N a b h := by
  have hsep := mem_separatedDyadicPairs.mp pair.2
  obtain ⟨w⟩ := (mem_fixedChannelPairs.mp hpair).2
  rw [mem_channelStartPairs]
  refine ⟨hsep.1, hsep.2.1, ?_⟩
  exact w.error_eq

/--
On the fixed population, the systematic exponent is the dimension of the
fixed rational channel.
-/
theorem pairSigma_eq_channelSigma_of_mem_fixedChannelPairs
    {N A L a b r : ℕ} {h : ℤ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ fixedChannelPairs N A L a b h r hN) :
    pairSigma A pair = channelSigma L a b h := by
  obtain ⟨w⟩ := (mem_fixedChannelPairs.mp hpair).2
  unfold pairSigma
  have hsigma :=
    RationalMassFinite.canonicalPairSigma_eq_channelSigma_of_choice
      (L := L) w.choice
  simpa [w.error_eq] using hsigma

/--
Every member of the positive-`σ` population belongs to a fixed-channel
population, for the canonical candidate and its actual value of `c#`.
This is the finite completeness statement needed before summing over
channels and certificate sizes.
-/
theorem exists_fixedChannelPairs_of_mem_positiveSigmaSmallProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ positiveSigmaSmallProductPairs N A L hN) :
    ∃ c :
        ReducedCandidate pair.1.1 pair.1.2
          (L + 1) ((L + 1) ^ A),
      canonicalReducedCandidate?
          pair.1.1 pair.1.2 (L + 1) ((L + 1) ^ A) =
        some c ∧
      2 ≤ candidateMultiplicity L c ∧
      pair ∈
        fixedChannelPairs N A L c.1.1 c.1.2
          (pairChannelError pair.1.1 pair.1.2 c.1.1 c.1.2)
          (canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L) hN := by
  have hsigma :=
    (mem_positiveSigmaSmallProductPairs.mp hpair).2
  have hmCanonical :
      2 ≤ canonicalMultiplicity A L pair.1.1 pair.1.2 :=
    RationalMassFinite.two_le_canonicalMultiplicity_of_sigma_pos
      hsigma
  obtain ⟨c, hchoice, hm⟩ :=
    exists_canonical_candidate_of_two_le_multiplicity hmCanonical
  refine ⟨c, hchoice, hm, ?_⟩
  rw [mem_fixedChannelPairs]
  refine ⟨hpair, ⟨?_⟩⟩
  exact
    { candidate_mem := c.2
      choice := hchoice
      error_eq := rfl
      count_eq := rfl }

/-- On a positive channel, the left-start projection is injective. -/
theorem fst_injOn_fixedChannelPairs
    {N A L a b r : ℕ} {h : ℤ} {hN : 2 ≤ N}
    (hb : 0 < b) :
    Set.InjOn (fun pair : SeparatedDyadicPair N L ↦ pair.1.1)
      (↑(fixedChannelPairs N A L a b h r hN) :
        Set (SeparatedDyadicPair N L)) := by
  intro pair₁ hpair₁ pair₂ hpair₂ hfst
  apply Subtype.ext
  apply
    fst_injOn_channelStartPairs hb
      (pair_mem_channelStartPairs_of_mem_fixedChannelPairs hpair₁)
      (pair_mem_channelStartPairs_of_mem_fixedChannelPairs hpair₂)
      hfst

/-- Projection to the left start preserves the population cardinality. -/
theorem card_fixedChannelFirstCoordinates
    {N A L a b r : ℕ} {h : ℤ} (hN : 2 ≤ N)
    (hb : 0 < b) :
    (fixedChannelFirstCoordinates N A L a b h r hN).card =
      (fixedChannelPairs N A L a b h r hN).card := by
  unfold fixedChannelFirstCoordinates
  exact Finset.card_image_of_injOn (fst_injOn_fixedChannelPairs hb)

private theorem exists_pair_of_mem_fixedChannelFirstCoordinates
    {N A L a b r : ℕ} {h : ℤ} {hN : 2 ≤ N}
    {x : ℕ}
    (hx : x ∈ fixedChannelFirstCoordinates N A L a b h r hN) :
    ∃ pair : SeparatedDyadicPair N L,
      pair ∈ fixedChannelPairs N A L a b h r hN ∧ pair.1.1 = x := by
  simpa [fixedChannelFirstCoordinates] using
    (Finset.mem_image.mp hx)

/-- The unique fixed-channel pair above a projected left start. -/
noncomputable def pairOfFirstCoordinate
    {N A L a b r : ℕ} {h : ℤ} {hN : 2 ≤ N}
    (x : ℕ)
    (hx : x ∈ fixedChannelFirstCoordinates N A L a b h r hN) :
    SeparatedDyadicPair N L :=
  Classical.choose (exists_pair_of_mem_fixedChannelFirstCoordinates hx)

theorem pairOfFirstCoordinate_mem
    {N A L a b r : ℕ} {h : ℤ} {hN : 2 ≤ N}
    (x : ℕ)
    (hx : x ∈ fixedChannelFirstCoordinates N A L a b h r hN) :
    pairOfFirstCoordinate x hx ∈
      fixedChannelPairs N A L a b h r hN :=
  (Classical.choose_spec
    (exists_pair_of_mem_fixedChannelFirstCoordinates hx)).1

theorem pairOfFirstCoordinate_fst
    {N A L a b r : ℕ} {h : ℤ} {hN : 2 ≤ N}
    (x : ℕ)
    (hx : x ∈ fixedChannelFirstCoordinates N A L a b h r hN) :
    (pairOfFirstCoordinate x hx).1.1 = x :=
  (Classical.choose_spec
    (exists_pair_of_mem_fixedChannelFirstCoordinates hx)).2

/-- The fixed-channel witness selected for a projected start. -/
noncomputable def witnessOfFirstCoordinate
    {N A L a b r : ℕ} {h : ℤ} {hN : 2 ≤ N}
    (x : ℕ)
    (hx : x ∈ fixedChannelFirstCoordinates N A L a b h r hN) :
    FixedChannelWitness A L a b h r (pairOfFirstCoordinate x hx).1 :=
  Classical.choice
    ((mem_fixedChannelPairs.mp
      (pairOfFirstCoordinate_mem x hx)).2)

/-- A certificate assignment together with the two facts required by the cover. -/
structure AmbientAssignmentPackage
    (L a b : ℕ) (h : ℤ) (r N x : ℕ) where
  certificate :
    CRT.UnorderedCertificate
      (Finset.univ :
        Finset (CanonicalResidualAmbientCell L a b h)) r
  admissible :
    CRT.CertificateAdmissible
      canonicalResidualAmbientCellModulus N certificate
  solution :
    x ∈
      CRT.certificateSolutions
        canonicalResidualAmbientLeftResidue
        canonicalResidualAmbientCellModulus
        N (2 * N) certificate

/--
The canonical residual certificate of a projected start, transported
together with admissibility and solution membership into the fixed ambient
channel family.
-/
noncomputable def ambientAssignmentPackageOfFirstCoordinate
    {N A L a b r : ℕ} {h : ℤ} {hN : 2 ≤ N}
    (hm : 2 ≤ channelUnitCount L a b h)
    (x : ℕ)
    (hx : x ∈ fixedChannelFirstCoordinates N A L a b h r hN) :
    AmbientAssignmentPackage L a b h r N x := by
  let pair := pairOfFirstCoordinate x hx
  let w := witnessOfFirstCoordinate x hx
  have hxy := pair_coordinates_two_le hN pair
  have herr :
      pairChannelError pair.1.1 pair.1.2 a b = h := by
    simpa only [pair] using w.error_eq
  have hmc :
      2 ≤ channelUnitCount L w.candidate.1.1 w.candidate.1.2
        (pairChannelError pair.1.1 pair.1.2
          w.candidate.1.1 w.candidate.1.2) := by
    simpa only [herr] using hm
  let cert :=
    canonicalResidualAmbientCertificate
      (A := A) (L := L)
      hxy.1 hxy.2 w.candidate w.choice hmc
  have hsmall :=
    (mem_activeSmallProductPairs.mp
      (mem_positiveSigmaSmallProductPairs.mp
        (mem_fixedChannelPairs.mp
          (pairOfFirstCoordinate_mem x hx)).1).1).1
  have hadmissible :
      CRT.CertificateAdmissible
        canonicalResidualAmbientCellModulus N cert := by
    exact
      (canonicalResidualAmbientCertificate_admissible_iff
        (A := A) (L := L) (N := N)
        hxy.1 hxy.2 w.candidate w.choice hmc).2 hsmall
  have hsolution :
      x ∈
        CRT.certificateSolutions
          canonicalResidualAmbientLeftResidue
          canonicalResidualAmbientCellModulus
          N (2 * N) cert := by
    unfold CRT.certificateSolutions
    rw [Finset.mem_filter]
    constructor
    · have hsep := mem_separatedDyadicPairs.mp pair.2
      have hxI := hsep.1
      rw [pairOfFirstCoordinate_fst x hx] at hxI
      simpa [dyadicBlock] using hxI
    · simpa only [cert, pair, pairOfFirstCoordinate_fst x hx] using
        (canonicalResidual_left_satisfies_ambientCertificate
          (A := A) (L := L)
          hxy.1 hxy.2 w.candidate w.choice hmc)
  let package :
      AmbientAssignmentPackage L a b
        (pairChannelError pair.1.1 pair.1.2 a b)
        (canonicalResidualComponentCount A pair.1.1 pair.1.2 L)
        N x :=
    { certificate := cert
      admissible := hadmissible
      solution := hsolution }
  rw [herr, w.count_eq] at package
  exact package

/-- The certificate field of the transported assignment package. -/
noncomputable def ambientCertificateOfFirstCoordinate
    {N A L a b r : ℕ} {h : ℤ} {hN : 2 ≤ N}
    (hm : 2 ≤ channelUnitCount L a b h)
    (x : ℕ)
    (hx : x ∈ fixedChannelFirstCoordinates N A L a b h r hN) :
    CRT.UnorderedCertificate
      (Finset.univ :
        Finset (CanonicalResidualAmbientCell L a b h)) r :=
  (ambientAssignmentPackageOfFirstCoordinate hm x hx).certificate

/--
The fixed-channel projected population is covered by the one-dimensional
ambient certificate mass.
-/
theorem four_pow_mul_card_fixedChannelPairs_le_solutionMass
    {N A L a b r : ℕ} {h : ℤ} (hN : 2 ≤ N)
    (hb : 0 < b)
    (hm : 2 ≤ channelUnitCount L a b h) :
    (4 : ℚ) ^ r *
        ((fixedChannelPairs N A L a b h r hN).card : ℚ) ≤
      CRT.admissibleCertificateSolutionMass
        (Finset.univ :
          Finset (CanonicalResidualAmbientCell L a b h))
        r canonicalResidualAmbientLeftResidue
        canonicalResidualAmbientCellModulus
        N (2 * N) N 4 := by
  rw [← card_fixedChannelFirstCoordinates hN hb]
  apply
    CRT.pow_mul_card_population_le_admissibleCertificateSolutionMass'
      (fixedChannelFirstCoordinates N A L a b h r hN)
      (ambientCertificateOfFirstCoordinate hm)
      canonicalResidualAmbientLeftResidue
      canonicalResidualAmbientCellModulus
      N (2 * N) N 4 (by norm_num)
  · intro x hx
    exact
      (ambientAssignmentPackageOfFirstCoordinate hm x hx).admissible
  · intro x hx
    exact
      (ambientAssignmentPackageOfFirstCoordinate hm x hx).solution

/--
The same cover followed by the one-dimensional fixed-size estimate of
Lemma 7.1.
-/
theorem four_pow_mul_card_fixedChannelPairs_le_lemmaSevenOne
    {N A L a b r : ℕ} {h : ℤ} (hN : 2 ≤ N)
    (hb : 0 < b)
    (hm : 2 ≤ channelUnitCount L a b h) :
    (4 : ℚ) ^ r *
        ((fixedChannelPairs N A L a b h r hN).card : ℚ) ≤
      (((1 + 1) * N : ℕ) : ℚ) *
        ((4 * ∑ p : CanonicalResidualAmbientPrime L a b,
            ((canonicalResidualAmbientCells L a b h p).card : ℚ) /
              (canonicalResidualAmbientPrimeModulus p : ℚ)) ^ r /
          r.factorial) := by
  exact
    (four_pow_mul_card_fixedChannelPairs_le_solutionMass hN hb hm).trans
      (CRT.labeledCell_admissibleCertificateSolutionMass_le
        (canonicalResidualAmbientCells L a b h) r
        canonicalResidualAmbientLeftResidue
        canonicalResidualAmbientPrimeModulus
        canonicalResidualAmbientPrimeModulus_prime
        N (2 * N) 1 N (by omega) (by omega)
        4 (by norm_num))

end

end PositiveSigmaFixedChannelCover
end PaperC
