# Final V3 publication and the next Palomar versions

This plan records the author's decisions of 7–8 September 2026. The current
sources are the supplied V3PREL article and companion. The final V3 files and
their published version identifiers are not yet available.

The documentation preparation presents the current sources and existing
publication records accurately. It does not turn V3PREL into the final V3,
issue a Palomar identifier, or qualify a new proof snapshot.

## Final article and companion

When the final sources and published PDFs are available:

- archive them separately from the preserved V3PREL payload, recording exact
  file identities and the public links to both documents;
- compare the final statements with V3PREL and update the source-to-Lean
  correspondence, numbering and any affected proofs;
- replace the README's explicitly labelled V3PREL abstract with the final
  article's abstract, reproduced faithfully;
- verify the DOI of each published version on Zenodo and Cambridge Open
  Engage, distinguishing those identifiers from the paper's concept DOI and
  the separate formalization DOI.

## Five metadata files

Update the existing `formalization.yaml` in each of
`palomar/v3prel/critical_field/`, `patterns/`, `limits/`, `boundary/` and
`crossover/` when the final sources are available.

The public description should explain the mathematical content, scope and
required literature assumptions. Do not duplicate the author, bibliographic
title or DOI already displayed in the structured fields. Keep the author in
`project.authors` and the publication details in `sources`; inspect the
registry preview for unnecessary repetition.

Use the final article title and version in the relevant project/source
fields, update source paths, hashes and theorem locations, and retain the
precise limits of each selected family. New verification and review outcomes
must identify their actual commit; historical evidence is not a result for a
changed snapshot.

## README and historical material

The README introduces the paper, its abstract, the current formalization
scope, the five Palomar families and a short reproduction path. It links to
the detailed development and the archived historical README.

Keep the historical source files, proof interfaces, registry identifiers,
hashes and qualification evidence in place. Moving their narrative out of the
front page does not erase or update their original claims. In particular,
old release documentation must not be presented as a guide to the final V3
without checking and updating its scope.

## Version updates in Palomar

Once the first five entries have actually been registered, submit each
updated family using **its existing identifier**, its Comparator path and
the new immutable commit. This requests the next version of each of the
five entries. A failed attempt that never produced a registered identifier
remains a new submission with the existing-ID field blank. See the
[Palomar form](https://submit.palomar-registry.org/).

Keep the repository, project directory and configuration paths stable for
these updates. The `v3prel` path names may remain as stable identifiers even
after the source metadata describes the final paper; renaming them merely
for appearance can disrupt the correspondence with the existing entries.

The final paper can cite the stable registry identifiers. Record the exact
registered versions and commits in the repository once issued. Run the
appropriate source, metadata and proof checks before publishing the new
snapshot; Palomar then performs its own verification of that commit.

## Information needed to complete this plan

- Final article and companion sources, PDFs and accompanying files.
- Public links and exact version DOIs on Zenodo and Cambridge Open Engage.
- The five issued Palomar identifiers and any findings from their reviews.

Lean and mathlib remain pinned to 4.32.0. Local work continues on the Ubuntu
partition, with available disk space checked before substantial builds.
