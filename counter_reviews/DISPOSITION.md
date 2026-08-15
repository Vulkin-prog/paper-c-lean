# Disposition of the historical agent counter-reviews

This table records the disposition of the two immutable reports archived in
this directory. It is a remediation ledger, not a retroactive change to their
verdicts and not an approval of the current pull request or release candidate.
Later reviews and the release-qualification gates take precedence over this
snapshot.

Status vocabulary:

- **resolved**: the requested change is present in the manuscript or Lean
  repository;
- **partially resolved**: a concrete remediation exists, but a release or
  independent-review condition remains;
- **open**: the requested publication action has not occurred;
- **historical observation**: no patch was requested, or the statement records
  the reviewer's assessment rather than a defect.

## Mathematical counter-review

Source: [`2026-08-13-mathematical-counter-review.md`](2026-08-13-mathematical-counter-review.md).

| Finding or requested change | Disposition | Evidence and remaining boundary |
|---|---|---|
| The dyadic core, Runge/Hamming argument, rational/residual split, terminal Pell closure and Chen--Stein assembly appeared mathematically coherent. | **historical observation** | Preserved as the reviewer's assessment; it is not converted into a peer-review endorsement. |
| The Lean claim was not independently usable because only a PDF had been supplied and no source tree, lockfile, build or audit was available. | **partially resolved** | The public repository now contains the full Lean tree, `lean-toolchain`, `lake-manifest.json`, root builds, exhaustive audit, source digests and Comparator protocols. Final version-specific release qualification and publication remain separate gates. |
| The seven imported literature statements needed an inspectable proposition/source/consumer map. | **resolved at repository level** | `formalization.yaml`, `audit_config.json`, the generated `AXIOM_AUDIT.md`, and `literature_certificates/` expose the registered proposition, source locator, status and consumers. The current inventory is thirteen registered bridges: seven discharged and six open. Human source review of the six open bridges is still welcome and is not supplied by the kernel audit. |
| The scope of mechanization had to distinguish manuscript mathematics, conditional Lean deductions and standard non-mechanized reformulations. | **resolved** | The public boundary documents and manuscript formalization section distinguish ordinary Lean premises from kernel axioms and list the remaining encoding gaps. Comparator proves the declared implications; it does not validate the literature sources. |
| The previously unnamed marked-process regime `r_e + 1 < d <= Q` needed an explicit disjoint-support argument. | **resolved** | Both v09 TeX sources now state that the union has diameter at most `2Q < Y_Q`, hence shares no prime coordinate above `Y_Q` and creates no dependency edge. The frozen English and French PDFs contain that correction. |
| Proposition 9.11 had to state or consume the preceding `D^# >= 3` elimination explicitly. | **resolved** | The terminal-reduction proof now begins by invoking the preceding many-defects proposition and states that the remaining proof is under `D^# <= 2`. |
| The bounded-ratio Proposition 16.1 and Appendix 17 needed a more auditable transport of hosts, the volumetric `2:1` channel, CRT sectors and terminal constants. | **partially resolved** | The manuscript now isolates those four sites, gives the modified exponents and constant order, and the Lean development exposes bounded-ratio endpoints. This removes the specific drafting omission; targeted human mathematical review of the global theorem is still outstanding. |
| The exponential terminal rate needed constants fixed before `N`. | **resolved** | The manuscript now isolates a terminal-host constants lemma, fixes `C_term` and `N_term`, then chooses `K > 2 C_term / log 2`. |
| "Maximal stretch" needed an almost-sure finiteness qualification. | **resolved** | The v09 definition introduces the maximal stretch only on `J_{x,L}=1` and points to the preceding almost-sure finiteness lemma. |
| The Laishram--Shorey specialization and other terminology needed more exact wording. | **resolved** | The v09 text cites Corollary 1 and equation (10), records `delta(k) >= 0`, and no longer describes the published corollary as having the disputed finite-exception form. |
| Publish and freeze an exact Lean archive linked to the manuscript. | **partially resolved** | Exact source/PDF hashes and a Q-to-R evidence protocol exist. A final tag, release assets, post-publication asset verification and version DOI are still open release actions. |

## Repository and release audit

Source: [`2026-08-13-repository-release-audit.md`](2026-08-13-repository-release-audit.md).

| Finding or requested change | Disposition | Evidence and remaining boundary |
|---|---|---|
| The Halter--Koch conductor-fibre premise was open and the cited pages had not been converted into the stronger source-shaped record. | **resolved by a different route** | `PaperC.PellInput.quadraticOrderConductorFiberBound` proves the registered `Fin 4` proposition directly by reduction modulo two. The old source-shaped record remains uninstantiated; no claim of formalizing Halter--Koch is made. See [`docs/HK_INTERFACE_ADJUDICATION.md`](../docs/HK_INTERFACE_ADJUDICATION.md). |
| The exact PR head had a red Comparator job. | **partially resolved** | Later exact source and packaging candidates obtained green kernel/build/audit and ordinary Comparator runs. Every successor source/evidence pair must obtain its own exact green runs; an earlier success is not inherited. |
| The new PDFs were not bound to hardened Comparator evidence. | **partially resolved** | Hardened, non-root, no-fallback local evidence and a Q-to-R release binding were produced for an exact pair. Any source candidate changed in response to a later review requires fresh evidence and a new binding. |
| A merge alone would not create a qualified public version. | **open** | No disposition table can replace the remaining tag, strict qualification, release assets, downloaded-asset verification and version DOI. |
| The repository description overclaimed the state and would become numerically stale after merge. | **open post-merge metadata action** | The description still describes default-branch `main` (4,070 declarations and seven open bridges). After the final qualified merge it should be updated to the verified counts and should call the PDFs byte-hashed external manuscript artifacts. |
| The phrase "independent counter-reviews" could be mistaken for human or GitHub approval. | **resolved** | [`README.md`](README.md) classifies both texts as agent-generated, records unavailable author/model/prompt fields, and explicitly denies GitHub-approval or independent-human-review status. |
| PDF QA and visual claims needed reproducible evidence. | **partially resolved** | The Lean repository checks structure, embedded fonts, links, metadata, text extraction, private paths and exact hashes. The authoring sources, build scripts and visual QA record live in the companion manuscript repository; this repository intentionally freezes the resulting PDF bytes. See [`docs/PDF_ARTIFACT_BOUNDARY.md`](../docs/PDF_ARTIFACT_BOUNDARY.md). A new independent typographical review is not implied. |
| Merge strategy must preserve the exact evidence commit and release identity. | **open release procedure** | The final release must use a history-preserving merge/fast-forward policy, run qualification on the exact evidence commit and tag that exact object. Squash or rebase must not be used for the qualified Q/R pair. |

## Conditions deliberately left open

The following are not papered over by documentary remediation:

1. six literature bridges remain `external/open` for the global endpoint;
2. a targeted human review of the modulo-two proof and the open literature
   translations has not been recorded;
3. a successor source/evidence pair must be qualified from its own exact
   bytes;
4. publication assets and their downloaded copies must be checked before the
   release blocker can be closed.
