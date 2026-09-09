# Lean 4.33.1 migration

**Status: local validation complete, 9 September 2026.** The maintainer authorized this
migration in a separate worktree based on commit
[`9286f4a954ac128ba3d5edd1c1d25203f45c099f`](https://github.com/Vulkin-prog/paper-c-lean/commit/9286f4a954ac128ba3d5edd1c1d25203f45c099f).
The complete build of all 23 libraries has passed (9,895 jobs), as have
the three kernel audits: PaperC (4,074 declarations), V11 (seven) and V282
(6,094). The strict local comparison also passed for all 80 selected
declarations across ten configurations and their reachable dependencies.
The [validation receipt](../migration_evidence/lean-4.33.1/validation.json)
records these results and their source identities. Official Comparator/NanoDa
qualification and Palomar admission are not established for this snapshot.
Historical qualification records remain bound to their original 4.32.0 sources.

## Pins

| Component | Official version | Commit |
|---|---|---|
| Lean | [`leanprover/lean4:v4.33.1`](https://github.com/leanprover/lean4/releases/tag/v4.33.1) | `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |
| Mathlib | [`v4.33.1`](https://github.com/leanprover-community/mathlib4/releases/tag/v4.33.1) | `0df444a360eaa60ab8c11dca51a86af692955474` |

Mathlib v4.33.1 differs from v4.33.0
(`db584cd6d46c92f209a44c0f1c829460d327499d`) only in its Lean toolchain
file. This does not make its Git provenance or its compiled objects
interchangeable with the earlier tag. The complete dependency lock was resolved and checked under the chosen
target; its identity is recorded in the validation receipt.

The baseline used Lean `v4.32.0` at
`8c9756b28d64dab099da31a4c09229a9e6a2ef35` and Mathlib `v4.32.0` at
`81a5d257c8e410db227a6665ed08f64fea08e997`. Its receipts remain evidence
only for their recorded sources and tools. The manuscript PDFs, source
archives, historical identifiers and original qualification records are
preserved. Migration does not discharge the seven explicit literature
propositions or create a final V3 publication identifier.

## Validation status at this source snapshot

| Check | Observed status |
|---|---|
| Full build, all 23 libraries | PASS, 9,895 jobs (`lean4331-full-build-15.log`). |
| PaperC kernel audit | PASS, 4,074 expected declarations. |
| V11 kernel audit | PASS, seven expected declarations. |
| V282 kernel audit | PASS, 6,094 expected declarations. |
| Strict interfaces and dependency closures, 80 selected declarations | PASS locally, ten configurations; this does not invoke official Comparator/NanoDa. |
| Official metadata contract and canonical import-closure preflight | PASS locally for five V3 families, 69 names and 8,690 imports; this is not provenance admission. |
| Full project acceptance by Comparator and NanoDa | Not established. |
| Palomar admission and rendering | Not established; external constraints below still apply. |

The three audit counts are separate scopes, not a deduplicated total. Their
allowed axiom lists are restricted to `propext`, `Classical.choice` and
`Quot.sound`. The seven mathematical literature inputs remain explicit
hypotheses; these audits do not prove those inputs. These are local results
for the migrated source snapshot, not a new registry qualification.

## Reproducing local validation

Run the following only after the exact target toolchain and dependencies
are available. Use the migration worktree and a 4.33.1-specific runtime and
cache; do not reuse a wrapper that selects the old worktree or compiler.
Local Lean operations are serialized and monitored on the Ubuntu partition,
with a 10 GiB starting threshold and a 5 GiB free-space reserve.

The default `lake build` covers only `PaperC`. The complete build surface
contains 23 libraries:

```sh
lake build PaperC PaperCV11 PaperCV282 \
  Challenge Solution ChallengeTransfer SolutionTransfer \
  ChallengeTheoremOneTwo SolutionTheoremOneTwo \
  ChallengeTheoremOneFour SolutionTheoremOneFour \
  ChallengeTheoremSixteenTwo SolutionTheoremSixteenTwo \
  ChallengeV3CriticalField SolutionV3CriticalField \
  ChallengeV3Patterns SolutionV3Patterns \
  ChallengeV3Limits SolutionV3Limits \
  ChallengeV3Boundary SolutionV3Boundary \
  ChallengeV3Crossover SolutionV3Crossover
```

After reconciling the pins, checking the source inventories, and regenerating
the audit products when required, preserve three separate kernel transcripts:

```sh
lake env lean AuditCheck.lean > core-audit-4331.log 2>&1
lake env lean PaperCV11/Audit.lean > v11-audit-4331.log 2>&1
lake env lean PaperCV282/Audit.lean > v282-audit-4331.log 2>&1
node scripts/verify_audit.mjs --input core-audit-4331.log
python3 scripts/check_v282_audit.py --log v282-audit-4331.log
```

The audit counts are 4,074, 7 and 6,094 respectively, not a deduplicated
total. All three transcripts have passed under Lean 4.33.1 at the current
source snapshot, with the exact expected names and permitted foundational
dependencies. For reproducibility, check those names and dependencies;
for V11, the seven-name check is specified in its
[workflow](../.github/workflows/v11-development.yml). The only foundational
axioms admitted are `propext`, `Classical.choice` and `Quot.sound`.
Intentional placeholders belong only to selected Challenge declarations,
not to Solution proofs or the mathematical development.

The source checks and their regression tests are separate gates:

```sh
node scripts/generate_audit.mjs --check-source-digest
node scripts/generate_audit.mjs --check-pdfs
node scripts/generate_audit.mjs --check-literature-certificates
node scripts/test_audit_root_guards.mjs
node scripts/check_comparator_sources.mjs
python3 scripts/check_v282_audit.py --check-source
python3 scripts/check_v3prel_sources.py
python3 -m unittest discover -s scripts -p test_v282_audit.py
python3 -m unittest discover -s scripts -p test_check_v3prel_candidates.py
python3 -m unittest discover -s scripts -p test_v3prel_sources.py
```

The historical baseline binds 382 `PaperC` files to fileset SHA-256
`3505665c32c33ddc5508994964f8623911ae83720b814f2fe4b7573bccba4137`.
Compatibility repairs change 20 of those files. The active migration
contract now binds the same 382-file scope to SHA-256
`081fb4c78b76d0cfc5da9fd505ff8226b051269d6ebdc5e2bdc4ee207a8b4d69`.
The separate `historical_baseline` object preserves the old digest, source
commit and 4.32.0 tools, and explicitly denies automatic transfer of its
qualification. The regenerated `AuditCheck.lean` changes only the digest
comment; its 4,074 audited names are unchanged. The current core contract
and its guards have passed. The complete downstream build, all three audits
and the strict interface check also passed on the frozen Lean snapshot;
future source changes require corresponding fresh checks.

## Compatibility repairs: current inventory

The current diff contains **51 adapted mathematical modules: 20 in
`PaperC` and 31 in `PaperCV282`**. The changed candidate Solution and
generated audit file are listed separately below. Targeted builds have
passed for these adaptations, followed by a successful complete build of
all 23 libraries (9,895 jobs), all three audits and the strict local
interface comparison. Existing warnings remain; this is not a claim of a
warning-free build.

| Module | Adaptation |
|---|---|
| [PaperC/Affine/Normalization](../PaperC/Affine/Normalization.lean) | Reduce finite-filter membership explicitly before identifying the relation kernel. |
| [PaperC/Affine/RelationalPrimeAssignment](../PaperC/Affine/RelationalPrimeAssignment.lean) | Unfold the single-coordinate function explicitly in the private parity proof. |
| [PaperC/Affine/StartDefectRank](../PaperC/Affine/StartDefectRank.lean) | Use the same explicit single-coordinate evaluation for the start relation. |
| [PaperC/Affine/TouchingDefectRank](../PaperC/Affine/TouchingDefectRank.lean) | Use explicit single-coordinate evaluation and eliminate the impossible unequal-to-itself branch. |
| [PaperC/Arithmetic/LowZonePrimePivots](../PaperC/Arithmetic/LowZonePrimePivots.lean) | Expose the natural-number index before rewriting; repair the same private-coordinate proof. |
| [PaperC/Asymptotics/BoundedRatioTerminalClosure](../PaperC/Asymptotics/BoundedRatioTerminalClosure.lean) | Keep the boundary-label predicate folded while rearranging the finite union. |
| [PaperC/Asymptotics/TheoremSixteenTwo](../PaperC/Asymptotics/TheoremSixteenTwo.lean) | Close the remaining subtype-coordinate equality explicitly. |
| [PaperC/Coding/AlignedComponentCode](../PaperC/Coding/AlignedComponentCode.lean) | Reduce filtered membership before distinguishing occurrence constructors. |
| [PaperC/Combinatorics/LargePrimeOccurrences](../PaperC/Combinatorics/LargePrimeOccurrences.lean) | Reduce the occurrence filter with explicit membership lemmas. |
| [PaperC/Combinatorics/SectionElevenPartition](../PaperC/Combinatorics/SectionElevenPartition.lean) | Scope the compatibility option to the generated Fintype instance; see the dedicated review below. |
| [PaperC/Combinatorics/TreeBoundary](../PaperC/Combinatorics/TreeBoundary.lean) | Expose edge-list membership and reduce the parity branch before subtype simplification. |
| [PaperC/Diophantine/HalterKochConductorDescent](../PaperC/Diophantine/HalterKochConductorDescent.lean) | Express the ring-of-integers equality in the quadratic field before taking its two coordinates. |
| [PaperC/LinearAlgebra/CanonicalSmallRows](../PaperC/LinearAlgebra/CanonicalSmallRows.lean) | Expose the same pointwise boundary-column sum before filtering it. |
| [PaperC/LinearAlgebra/PrivatePivots](../PaperC/LinearAlgebra/PrivatePivots.lean) | Remove a reflexivity step after rewriting already closes the goal. |
| [PaperC/Probability/ConditionalDependencyGraph](../PaperC/Probability/ConditionalDependencyGraph.lean) | Close subtype identities explicitly and reduce finite-filter membership in the joint fiber count. |
| [PaperC/Probability/ConditionalStartProbability](../PaperC/Probability/ConditionalStartProbability.lean) | Close pointwise linearity and subtype identities explicitly; evaluate the same single-coordinate assignment. |
| [PaperC/Probability/DefectFirstMoment](../PaperC/Probability/DefectFirstMoment.lean) | Establish the solution-cardinality identity explicitly and reuse it before normalization. |
| [PaperC/Probability/FiniteCylinderCountTransport](../PaperC/Probability/FiniteCylinderCountTransport.lean) | Close the subtype-coordinate equality after simplification. |
| [PaperC/Probability/IndependentThinning](../PaperC/Probability/IndependentThinning.lean) | Fix local decisions for existing universal predicates and unpack the outside-index subtype. |
| [PaperC/Probability/TouchingProbability](../PaperC/Probability/TouchingProbability.lean) | Reuse the explicit solution-cardinality identity before the final probability normalization. |
| [PaperCV282/AffineBorderPrimeClock](../PaperCV282/AffineBorderPrimeClock.lean) | Expose the prime-counting coordinate before applying the nth-prime identity. |
| [PaperCV282/AffineCrossoverLocationSource](../PaperCV282/AffineCrossoverLocationSource.lean) | Prove the same affine-conditioned probability law before coercion, using a proof-local probability instance. |
| [PaperCV282/AggregateCoordinateIdentities](../PaperCV282/AggregateCoordinateIdentities.lean) | Express the sum over the inverse site equivalence directly. |
| [PaperCV282/AllStartFieldTransfer](../PaperCV282/AllStartFieldTransfer.lean) | Prove the retained nonnegative rate equality before coercing it to the reals. |
| [PaperCV282/BulkMarkedSource](../PaperCV282/BulkMarkedSource.lean) | Expose the pointwise signed mark before identifying the finite projection. |
| [PaperCV282/BulkMarkedTypes](../PaperCV282/BulkMarkedTypes.lean) | Close the unchanged embedding-range identity by reflexivity. |
| [PaperCV282/BulkMicroscopicRecord](../PaperCV282/BulkMicroscopicRecord.lean) | Remove case splitting after simplification already closes the identity. |
| [PaperCV282/ConditionalFieldTransfer](../PaperCV282/ConditionalFieldTransfer.lean) | Remove a reflexivity step after simplification already closes the goal. |
| [PaperCV282/CrossoverLocationGrid](../PaperCV282/CrossoverLocationGrid.lean) | Name the same inverse grid index explicitly before the fiber calculation. |
| [PaperCV282/CrossoverLocationTransfer](../PaperCV282/CrossoverLocationTransfer.lean) | Prove the probability-measure identity before coercion, with its probability instance local to the proof. |
| [PaperCV282/D4ClosureLaplaceSource](../PaperCV282/D4ClosureLaplaceSource.lean) | Expose the integer shifted level before the arithmetic step. |
| [PaperCV282/DictionaryFieldDeletion](../PaperCV282/DictionaryFieldDeletion.lean) | Reduce finite-filter membership before the definitional event identity. |
| [PaperCV282/ExactMarkedModel](../PaperCV282/ExactMarkedModel.lean) | Reduce the Boolean decision before identifying the exact-length event. |
| [PaperCV282/IndependentDefectParameters](../PaperCV282/IndependentDefectParameters.lean) | Build finite-filter membership directly from the existing monotonicity theorem. |
| [PaperCV282/InfiniteMaskedScalarTransfer](../PaperCV282/InfiniteMaskedScalarTransfer.lean) | Transport the count predicate explicitly before simplifying its conditional indicator. |
| [PaperCV282/MacroAggregateFilling](../PaperCV282/MacroAggregateFilling.lean) | Rewrite the signed aggregate rate before reducing real coercions. |
| [PaperCV282/MacroAggregatePaths](../PaperCV282/MacroAggregatePaths.lean) | Expose the same shifted spatial coordinates before the source/filter identity. |
| [PaperCV282/MacroAggregateTruncation](../PaperCV282/MacroAggregateTruncation.lean) | Evaluate the finite rate sum before taking real coercions. |
| [PaperCV282/MacroTransportUnsigned](../PaperCV282/MacroTransportUnsigned.lean) | Identify each signed site rate explicitly before summing over signs. |
| [PaperCV282/MaskedScalarCoupling](../PaperCV282/MaskedScalarCoupling.lean) | Keep the same count predicate explicit on each branch of the indicator. |
| [PaperCV282/MicroscopicPrivatePrimes](../PaperCV282/MicroscopicPrivatePrimes.lean) | Expose the valuation coordinate and its codomain before evaluating the private column. |
| [PaperCV282/MovingMarkedSource](../PaperCV282/MovingMarkedSource.lean) | Expose the shifted excess and source index before simplification. |
| [PaperCV282/PoissonResolvedPast](../PaperCV282/PoissonResolvedPast.lean) | Expose the natural-number shift and filter condition before arithmetic. |
| [PaperCV282/PrefixLongestGeometry](../PaperCV282/PrefixLongestGeometry.lean) | Remove a reflexivity step after the prefix-event identity is already proved. |
| [PaperCV282/PrimeClockEvents](../PaperCV282/PrimeClockEvents.lean) | Expose the measurable predicate, then use an explicit event/intersection equality. |
| [PaperCV282/RarePrefixGeometry](../PaperCV282/RarePrefixGeometry.lean) | Apply the least-index identity with the original membership predicate explicit. |
| [PaperCV282/SpatialMarkedPoissonIdentification](../PaperCV282/SpatialMarkedPoissonIdentification.lean) | Expose the same site pair before applying the inverse-equivalence identity. |
| [PaperCV282/SpatialMarkedSource](../PaperCV282/SpatialMarkedSource.lean) | Expose the same signed source coefficient before using the site identity. |
| [PaperCV282/SpatialMarkedTypes](../PaperCV282/SpatialMarkedTypes.lean) | Expose the same site pair before proving the finite embedding range. |
| [PaperCV282/UnsignedMarkedRelations](../PaperCV282/UnsignedMarkedRelations.lean) | Apply the known negative predicate explicitly to the conditional indicator. |
| [PaperCV282/WindowValues](../PaperCV282/WindowValues.lean) | Apply the single-coordinate lemmas with the original coordinate instance explicit. |

| Other changed Lean file | Scope |
|---|---|
| [SolutionV3Patterns](../SolutionV3Patterns.lean) | Only the body of `constant_window_distance_eq`: apply the already known positive/negative predicate explicitly. No shared interface definition or theorem statement changes. |
| [AuditCheck](../AuditCheck.lean) | Regenerated source-digest comment only; the 4,074 audited names are unchanged. |

The strict local check establishes exact structural equality of the
elaborated interfaces of **80 selected declarations** (69 V3 and 11
historical) and their reachable constant dependencies, across ten pairs.
It checked that all **1,171 Lean sources and 20 selected compiled modules**
were unchanged before and after the run. The Challenge files and selected
theorem lists are unchanged. This check imports the compiled environments;
it does not run the official Comparator export parser/kernel or NanoDa.

The inspected changes preserve theorem statements, mathematical hypotheses,
probability laws, events, coordinate maps and the seven literature inputs.
Some edits occur in proof fields of structured definitions: linearity for
`extendSmall` and `extendLarge`, and the right-inverse proof of
`startCoordinateSplit`. Their computational fields are unchanged. The
predicate-decision instances in `IndependentThinning` and the probability
instances in `CrossoverLocationTransfer.firstStartLaw_eq` and
`AffineCrossoverLocationSource.firstStartLaw_eq` are local to their proofs.
They use, respectively, the existing positive-hit theorem and the existing
positive intersection hypothesis. Neither changes the public statement. New digests and
kernel results must accompany each migrated source snapshot. Historical
receipts cannot be relabelled as evidence for these files.

### One local derivation exception

`SectionElevenPartition` retains the same seven `ResidualSector` constructors
and their order. `DecidableEq` and `Repr` are derived as before; only the
standalone `Fintype` derivation uses:

```lean
set_option backward.isDefEq.respectTransparency.types false in
deriving instance Fintype for ResidualSector
```

The option applies to that command and its generated auxiliary declarations,
not to the inductive definition, later theorems or the whole project. It lets
Mathlib's enumeration derivation elaborate its generated completeness proof
across the List-to-Multiset coercion. There is no project-wide compatibility
flag.

The independent `lean4331-residual-sector-review.json` compared the 4.32.0
and 4.33.1 outputs for **46 generated declarations**. Names, displayed types
and recorded axiom dependencies were byte-identical, including `enumList`,
its completeness/nodup lemmas and `instFintypeResidualSector`. This is a
specific derivation check; it does not assert that proof terms or compiled
objects from the two compilers are identical, or that the whole project
has passed. The standalone transcripts have SHA-256
`bb3b956fe6bb0d6a7cd06b67cb3b5d3500caf80c88ea71859ed2603c88d7183b`.

## Candidate verification and external constraints

All five V3 families have passed the local strict check: 69 selected
declarations, distributed 13/9/29/7/11. The four historical entries select
ten declarations, with a separate eleventh declaration for the historical
finite-to-infinite transfer. Their ten Challenge/Solution pairs build and
all 80 interfaces pass locally. This does not establish official Comparator
or NanoDa acceptance of the exported project.

The candidate preflight has checked the official metadata contract from
the pinned, verified contract checkout, together with the canonical import
closure: five V3 families, 69 names and 8,690 imports. It does not establish
acceptance under the separate Mathlib ancestry rule. Full replays additionally require an exporter
compatible with the exact project Lean, Comparator, NanoDa and the real
sandbox wrapper. Their scripts can fetch dependencies and build tools; they
are not offline checks. Record exact tool commits, protected configurations,
preflight/postflight hashes and logs for the final frozen source. A local
replay does not issue a registry identifier or establish rendering success.

The canonical exporter source at
[`15f6055e299ad5b89345e533cc2192f4cc00f659`](https://github.com/leanprover/lean4export/tree/15f6055e299ad5b89345e533cc2192f4cc00f659)
declares Lean 4.33.0. It has been compiled locally with the exact project
Lean 4.33.1, as allowed by Palomar's merged
[PR #122](https://github.com/PalomarRegistry/PalomarSubmission/pull/122).
A real two-theorem export passed its metadata and selected-name checks;
this is a technical tool check, not acceptance of the project's candidates
by Comparator or NanoDa. The runners check the effective project compiler
and select Comparator's own pinned build toolchain separately through elan.
They preserve the provenance guard and the real sandbox requirements.

The assessment of **9 September 2026** identified two separate external
issues:

- **Mathlib provenance:** Palomar
  [PR #128](https://github.com/PalomarRegistry/PalomarSubmission/pull/128)
  was still open. The observed canonical rule required ancestry from
  `master`; the official Mathlib v4.33.1 commit is a patch branch outside
  that ancestry. The current local ancestry guard mirrors this rule. A
  successful proof build does not remove that rejection. Any later rule
  change, or decision to use a different Mathlib pin, requires its own
  explicit evidence.
- **Rendering:** Palomar
  [issue #134](https://github.com/PalomarRegistry/PalomarSubmission/issues/134)
  concerns loss of definitional equalities when preparing the display
  module. The compiler migration has not been shown to fix it. Proof
  checking, registry admission and rendering remain distinct outcomes.

The resulting status must therefore be stated separately: local proof
compilation and technical export checks are migration evidence; admission
under Palomar's provenance policy, full candidate verification and successful
rendering each require their own observed result. Neither the unchanged
4.32.0 registrations nor a local 4.33.1 test provides that result automatically.

## Completion record

The [local validation record](../migration_evidence/lean-4.33.1/validation.json)
preserves the successful full build, all three audit scopes, the strict
interface check and the exact source identities. Its
[source snapshot](../migration_evidence/lean-4.33.1/lean-sources.json) and
[strict-check receipt](../migration_evidence/lean-4.33.1/strict-boundary.json)
are retained alongside it. The external qualification record remains pending.
A future official replay must identify its submitted commit, tool revisions,
provenance decision and kernel results independently. Failed attempts and
historical receipts retain their original pins and are not relabelled as
successful 4.33.1 evidence.
