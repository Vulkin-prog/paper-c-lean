# Publication and Palomar release plan

This plan records the author's publication sequence of 20 September 2026.
The [current manuscript package](../manuscripts/paper-c/README.md) and
[source alignment](MANUSCRIPT_ALIGNMENT.md) are integrated. The seven explicit
literature propositions remain assumptions for this release.

## 1. Prepare the public repository and submission dossiers

Prepare the expanded Palomar selection around the five existing mathematical
families and the two recommended additional families:

1. Critical Poisson field and small-prime conditioning, including the
   information-adapted cutoff.
2. Dictionaries, exact marks and clusters, including typical and affine dictionaries.
3. Threshold staircase and Poisson–Gaussian limits.
4. Boundary, prefix laws and longest runs.
5. Microscopic–bulk crossover.
6. Microscopic signed field, dyadic restrictions and empirical count laws.
7. Regular configurations, Palm laws and the absolute-cumulant obstruction.

The [submission guide](PALOMAR_SUBMISSIONS.md) now records the exact 89-declaration
selection, its seven Challenge/Solution interfaces and metadata. Verify the
immutable commit to be submitted; the prepared grouping is not an issued registry entry. Keep established
configuration paths stable where they already identify a registered family.
Record actual identifiers and registration status rather than assuming a failed
or pending attempt produced an entry.

Present the paper, its abstract, mathematical scope, explicit hypotheses, build
instructions and registration links in the README. Remove the working-version
narrative from that front page. Keep immutable evidence and provenance available
in supporting documentation; do not rewrite their original scope.

Use structured person records for the author's metadata:

```yaml
authors:
  - name: "Brice Pouly"
    github: "Vulkin-prog"
    orcid: "0009-0008-8491-2467"
```

The ORCID is recorded in the author's supplied manuscript sources. The current
[Palomar validator](https://github.com/PalomarRegistry/PalomarSubmission/blob/3561d237dcc4b28482558ad28a64d767d7cc8615/scripts/submission_contract.py#L458)
accepts this format. Put bibliographic identifiers in `sources`, not in the
public mathematical abstract; do not repeat authorship and DOI information
already represented by structured metadata.

## 2. Author submits to Palomar

When the dossiers and repository are ready, the author performs the submissions.
The repository then records the actual issued identifiers and versions.
Local qualification is distinct from Palomar's own verification and review.

## 3. Author publishes the paper

The author adds the Palomar references to the article and companion, then
publishes the paper on Zenodo. No future version DOI is inferred from a concept
DOI. Publication on another platform is recorded only when confirmed.

## 4. Integrate the published edition

The author supplies the published article, companion, editable sources and the
Zenodo DOI of paper V3. Verify the files, compare them against the current
manuscript, and update the public package, formal correspondence, README and
submission metadata. Review any mathematical edits before retaining a coverage
claim. Keep the article DOI distinct from the formalization DOI.

## 5. Author submits the Palomar version updates

After validation at the new immutable commit, the author makes the planned v2
submissions with the published paper references. Use the actual existing entry
identifiers and appropriate next version for any already-versioned record;
an unregistered attempt does not become a version update.

No submission, merge, publication or external identifier is created by this
plan. Work stays on the Ubuntu partition, with disk checks before large builds.
