# Lean formalization of Paper C

This repository accompanies the manuscript:

> *A critical Poisson law in a dyadic block — Starting points of long constant
> stretches of an extended Rademacher random completely multiplicative
> function*, Brice Pouly.

Public paper records: [Cambridge Open Engage DOI
`10.33774/coe-2026-z3l74`](https://doi.org/10.33774/coe-2026-z3l74) and
[Zenodo paper concept DOI
`10.5281/zenodo.21736676`](https://doi.org/10.5281/zenodo.21736676).

Public formalization: [`github.com/Vulkin-prog/paper-c-lean`](https://github.com/Vulkin-prog/paper-c-lean)
and [Zenodo formalization concept DOI
`10.5281/zenodo.21735481`](https://doi.org/10.5281/zenodo.21735481).

Target manuscript: `paper_C_complete_v09_en.pdf` (77 physical pages; 935831
bytes), SHA-256
`c99ac22eaa0bb59032fc2d683c03d19826f9e9bf27920433df4fae9b49e14cb1`.

Synchronized French manuscript: `paper_C_complete_v09.pdf` (79 pages; 946847
bytes), SHA-256
`11d67677fbf9ba52a462b6df2d03a9affed71c670a27a2d525519af66358af44`.

> **Release-candidate status (2026-08-13).** PR #5 and branch
> `agent/v0481-publication-metadata` are not a qualified `v0.48.1` release.
> The Halter--Koch compatibility interface is now discharged internally by a
> Lean construction using reduction modulo (2); it is no longer a premise of
> the canonical endpoints. This changes both the Lean core and the main
> Comparator surface, so the published v0.48.0 hardened evidence does not bind
> this source snapshot. The snapshot records
> `source_snapshot_comparator_state: definitions_and_digests_only`; any
> certifying outcome is authoritative only under
> `release_evidence/v0.48.1/` in a validated unique-child packaging commit.
> Its metadata therefore remains true whether or not that later layer exists.
> See
> [`docs/HK_INTERFACE_ADJUDICATION.md`](docs/HK_INTERFACE_ADJUDICATION.md) and
> [`RELEASE_QUALIFICATION.md`](RELEASE_QUALIFICATION.md). The two supplied
> audits are published as **agent counter-reviews**, not human peer review, in
> [`counter_reviews/`](counter_reviews/).

## Status

This repository is a **formal proof of the canonical endpoints, conditional
on six explicitly registered external propositions that remain open**. The
Halter--Koch bridge remains registered with external provenance but now has
`status: discharged`; it is not one of those six premises. Complete
unconditional kernel certification would additionally require the six open
propositions themselves to be formalized. The repository deliberately
distinguishes:

1. the objects and lemmas actually proved by Lean;
2. the arithmetic, probabilistic, and Diophantine obligations that remain to
   be formalized;
3. external results that cannot honestly be replaced by axioms when the goal
   is certification.

The Paper C Lean core and the two Solution files contain no
`sorry` and introduce no mathematical axiom beyond `propext`, `Quot.sound`,
and `Classical.choice`. `Challenge.lean` and `ChallengeTransfer.lean` each
contain exactly one source-level `by sorry`, on their named final Comparator
theorem. This count is per source file: `ChallengeTransfer` imports
`Challenge`, so its transitive environment also contains the first Challenge
placeholder. The generated proof-side `sorry_count` excludes these two
intentional Comparator placeholders and is zero. The command

```bash
rg -n '(^|[[:space:]])(sorry|axiom|admit|native_decide|unsafe|partial)([[:space:]]|$)' --glob '*.lean' PaperC.lean PaperC
```

must therefore return no matches. This certifies only the modules present, not
the complete 77-page target manuscript or its synchronized 79-page French
source.

## External semantic audit boundary

Version `0.48.0` introduced the project-independent semantic boundary. The
v0.48.1 candidate changes its main theorem from four ordinary premises to
three after the internal conductor discharge. `Challenge.lean` imports only
Mathlib modules.
`ChallengeTransfer.lean` imports exactly `Challenge`, and therefore depends
transitively only on the first Challenge and Mathlib, never on `PaperC`. The
matching Solution files do not import either Challenge module.

| Comparator target | Trusted statement | Solution-side interface and proof | Scope |
|---|---|---|---|
| `comparator/theorem_one_one.json` | `Challenge.lean` | `Solution.lean` | The quantitative finite-cylinder form of Theorem 1.1 |
| `comparator/theorem_one_one_transfer.json` | `ChallengeTransfer.lean` | `SolutionTransfer.lean` | Exact identity of the infinite-product and finite-cylinder laws |

`Challenge.lean` imports only `Mathlib`.  It defines the finite uniform
Rademacher cylinder, the associated completely multiplicative sign function,
the dyadic start count and its law, the Poisson law, and total variation with
the explicit half-`ℓ¹` normalization.  Its theorem
`paper_c_theorem_one_one_finite_cylinder` is the rate on printed/PDF page 3 of
the frozen English manuscript.  The challenge declarations live in the fresh
`PaperCAudit` namespace.  `Solution.lean` itself reproduces that complete
declarative interface, with the same names, types, and bodies, without
importing the Challenge.  It additionally imports `PaperC` and closes that
exact statement with
`PaperC.CorollaryThirteenTen.theorem_one_one_uniformBigO_canonical`.
The Arratia--Goldstein--Gordon finite-probability record is not definitionally
identical to its core counterpart, so `Solution.lean` contains an explicit,
proved record translation. The historical conductor declaration remains in
the audit namespace for traceability but is not a theorem argument.
`SolutionTransfer.lean` likewise reproduces the declarations
specific to the infinite-model interface without importing
`ChallengeTransfer.lean`, then applies the frozen exact law identity.  The
two pairs are intentionally loaded in separate environments because their
global names coincide.

Theorem 1.1 is stated unconditionally in the manuscript. The main Comparator
theorem is instead an implication from the three fully stated propositions
below. Comparator checks that `Solution` proves that implication; it does not
check that the cited primary sources imply the three propositions, and it does
not by itself check fidelity to the manuscript. The separate infinite-to-
finite law identity is unconditional and exact.

The finite-cylinder theorem takes exactly three ordinary, fully stated
literature-facing hypotheses:

| Literature input | Audit bridge | Role in the paper |
|---|---|---|
| Arratia--Goldstein--Gordon, Theorem 1 | `AGG89-T1-finite-dependency-b3-zero` | Finite Chen--Stein bound with `b₃ = 0` |
| Evertse--Silverman, Theorem 1(b) | `ES86-T1b-Q-split-n2` | Uniform count for the split quadratic equation used in Lemma 9.1 |
| Nicolas--Robin, Theorem 1 | `NR83-T1-divisor-log-bound` | Direct logarithmic divisor bound used in Lemma 9.2 |

These are theorem arguments, not Lean axioms.  The explicit Comparator
allowlist in both JSON files is exactly `propext`, `Quot.sound`, and
`Classical.choice`.

The presentation differences from the manuscript are deliberate and recorded
inside the challenge:

- the main challenge uses the finite cylinder of primes at most `2*N+L`, while
  the manuscript starts from the infinite product; the second Comparator pair
  is required for exact transfer of the law;
- `UniformBigOOn` expands `O_C` as one nonnegative constant and one threshold,
  followed by all `N` beyond that threshold and all admissible `L`; the
  threshold is uniform in `L` and may depend on `C`;
- the critical window is exactly
  `|L - log N / log 2| ≤ C`, so the admissible window itself depends on `C`;
- total variation is written as one half of the discrete `ℓ¹` distance,
  equivalent to the supremum-over-events convention used in the paper;
- the interface proves the harmless strengthening `C ≥ 0`; the manuscript
  states `C > 0`.

The global longest-run theorem is intentionally outside this Comparator
surface. It consumes the other three open literature bridges---the prime
number theorem, Laishram--Shorey, and Balasubramanian--Shorey---and will need a
separate audit target.

**Recorded hardened status.** Both Paper C Comparator targets passed the
hardened local procedure at Paper C commit
`27c91f8bdd5c3f4eeda4183eb3bfd7453a14ba07`. The runs used real landrun under
`systemd-run --user --pty`, a non-root account, zero inherited, effective,
permitted, and ambient capabilities, and `NoNewPrivileges`. Comparator built
each Challenge/Solution pair in a separate clean checkout; the Lean default
kernel accepted both solutions with exit status 0.

The public release bundle is
`paper-c-hardened-public-27c91f8.tar.zst`, published in the
[v0.48.0 release](https://github.com/Vulkin-prog/paper-c-lean/releases/tag/v0.48.0).
It is 49,765 bytes, with SHA-256
`7279ed99e6b1a98b6458fe1f8d95dd1f68af445646ee6a23d0044c7bee94ce50`.
It retains the exact summary (SHA-256
`b1d956eeee5451a64dbbdab495fe2f56f22b7ee06e2d65624394b3fee5ca41fb`),
both result records, all 12 source-snapshot files, and the raw checksum
inventory. Its Comparator-fileset digest is
`646e3ba055daf0509ba70237f4e87c59e18fa697b4698a4647ef5f04435757a5`.
`REDACTION_MANIFEST.json` (SHA-256
`01c3619d80786999a323c8b2073c4e674bf97af46f179b7e1434af53f3b6f29b`)
binds all 17 retained and 13 omitted source members by SHA-256.

The private source archive `paper-c-hardened-27c91f8.tar.zst` is 98,049
bytes, with SHA-256
`a4f5469e7c57236dc22f480297591d322eeda0f9d3cf9b7b0a7ff55cb4f6ae89`.
It remains local and is not published because the omitted host logs and raw
transcripts contain a username, hostname, local groups, HOME/PATH, and
temporary paths. The raw main and transfer transcript SHA-256 values remain
cryptographically recorded as
`fed5cf1fd82037c98c1b3f4c713189958ac92b5ceb58982e0e1093f31ce7599e`
and
`13703cb6794c4102b6d172e6632fddb1df75d6d47dfa32e46f63030adea33076`.
The public bundle therefore preserves the certified result bindings but does
not permit independent line-by-line inspection of the full host trace. The
generator validates the privacy-minimized repository records and their
configuration and fileset bindings; it deliberately does not fetch or
revalidate the GitHub release asset.

This is a Lean-kernel-only result. Both configurations have
`enable_nanoda: false`; Nanoda was not run, and no dual-kernel result is
claimed. The evidence certifies the historical Comparator inputs at commit
`27c91f8bdd5c...`. The final v0.48.0 metadata layer leaves its six-file
Comparator fileset and both manuscript PDFs byte-identical to that certified
commit. The current v0.48.1 candidate changes the Lean core and removes the
Halter--Koch argument from the main Challenge/Solution theorem, in addition to
replacing the manuscript PDFs and associated documentation. The source
snapshot itself carries no post-freeze execution verdict. A qualified release
is established only by evidence in the validated packaging commit that binds
the new three-premise Comparator surface, the final PDF bytes, and the exact
source commit. The published v0.48.0 evidence remains valid only for its
historical inputs and manuscript hashes; it neither binds nor qualifies the
v0.48.1 snapshot. The
earlier fake-landrun transcripts remain historical unsandboxed compatibility
tests only; they are not the release certificate.
The audited Paper C commit is distinct from the pinned Comparator source
commit `51491237b1d2f96cca203af9c34bced6fe38e0d8` and from GitHub event SHAs
formerly used in hosted-artifact names.

For the final evidence, each `result-*.json` records the Challenge and
Solution SHA-256 values, the exact theorem list and permitted-axiom list, the
two manuscript SHA-256 values, and the five pinned tool commits. The aggregate
summary repeats the shared tool and manuscript identities.

### Source-audit qualifications

The documentary files under `literature_certificates/` comprise three active
source certificates for the three open premises of Theorem 1.1 and one
historical Halter--Koch closure note. All four participate in the documentary
fileset digest, but only the first three count as active literature
certificates for Theorem 1.1. They are neither Lean proofs nor independent
human review. For
Arratia--Goldstein--Gordon, the notation is on p. 10 and the theorem and
total-variation bound are on p. 11; the Challenge inequality is a conservative
consequence under the half-`ℓ¹` convention. The Evertse--Silverman report
spells out the `K=L=Q`, split-polynomial specialization. For
Nicolas--Robin, the printed function is normalized by `log 2`: bounding the
normalized maximum by `2` gives the Lean coefficient `2 log 2`. The historical
Halter--Koch report records why the former source-shaped route had an open gap;
the current kernel discharge does not rely on filling that source-to-record
derivation. Instead Lean proves the compatibility proposition directly by the
modulo-two construction. Accordingly `HK13-QO-conductor-fibres` is
`external/discharged`, while the three literature premises of the main
Comparator remain `external/open`. None of the documentary reviews is human
certification.

One narrower compatibility probe has actually run: Comparator's own upstream
self-test suite completed under the pinned sources with the official
fake-landrun shim.  Its transcript is
`comparator/transcripts/toolchain_compatibility_unsandboxed.txt`, SHA-256
`2ee3dcde7fee2dc4a31b1cc4395ea9f5d31f2b2526741f6f18f6463991c25cd5`.
This earlier transcript is an unsandboxed test of the tool combination only;
unlike the two project smoke-test transcripts above, it did not load either
Paper C configuration.

`formalization.yaml` uses the official v0.3 format.  It and
`audit_manifest.json` are generated deterministically from the schema-5
`audit_config.json`, which is the sole editorial source for manuscript-item
mapping, bridge consumption, conditionality, and Comparator coverage.  The
generated metadata records the proof-side `sorry_count` separately from the
two intentional challenge placeholders and records the present review level
as agent-reviewed, not independent peer review. It distinguishes the timeless
source-snapshot state from the release-evidence location and required
packaging commit; it never turns presence or absence of later evidence into a
source-tree run status. The item list itself remains an editorial inventory
requiring human review; it cannot be inferred completely from Lean or the
PDFs.

The v0.48.0 historical core fileset was exactly `PaperC.lean` plus the 381
files under `PaperC/`. Its v0.47.0 SHA-256 was
`f6020b0bae9b8c6f22ab6ed0b6c3024a22e0a697ddb5578bb65c5e1f2a56c999`;
the v0.48.0 Comparator-fileset SHA-256 was
`646e3ba055daf0509ba70237f4e87c59e18fa697b4698a4647ef5f04435757a5`.
The additive rc2 literature-certificate fileset had its own SHA-256,
`6e4b3e86107bc68911778830c50e66139c6c6d56b037d8143a235d2a8cbd2996`;
it was not part of either frozen Lean fileset. Version v0.48.1 replaces the two
manuscript PDFs and changes both the Lean core and main Comparator interface to
incorporate the internal conductor proof. Its regenerated digests and audit
counts are authoritative only after the source set is stabilized. None of the
v0.48.0 frozen hashes can qualify this new core.

Project version `0.47.0` closed the root-module gap in the indivisible
manuscript--sources--audit triplet. `PaperC.lean`, the library target built by
Lake, now participates in source discovery, the digest, declaration and bridge
inventory, and the generated kernel audit. Both hashed PDFs are included
in the repository and are hashed from their actual bytes before any build.
Before the present conductor closure, the mathematical Lean content had been
unchanged from v045, which added the exact
exponential wrapper for Corollary 11.3, source-law wrappers for Theorems 1.1
and 16.2, the recentered global Poisson endpoint, the uniform masked rate,
and the finite-prefix law. The v0.48.1 candidate now adds a direct construction
of the quadratic field, order embedding, ideal data, and residue colouring
modulo (2). The registered Halter--Koch bridge is therefore discharged, and
the global open-external boundary falls from seven interfaces to six. The
project otherwise carries v044 forward, whose
only project-wide change before that was the Lean/mathlib migration from
`v4.19.0` to `v4.32.2`. It retains
the closure of the internal §14 chain, the v041 legacy cleanup, and the
standalone canonical endpoint for Theorem 1.4, connected directly to the
quantitative mother mass. The dyadic Riemann sums, spatially and markedly
thinned parameters, marked dependency graph, its two Chen–Stein terms, exact
cylinder--source-law transfers, and detruncation have all been assembled.
Under the three explicit literature inputs Arratia--Goldstein--Gordon,
Evertse--Silverman, and Nicolas--Robin, Lean proves the limits of
the Laplace functionals
\[
 \mathbb E e^{-\int g\,d\Xi_{N,L}}
 \longrightarrow
 \exp\!\left(-\lambda\int_1^2(1-e^{-g(t)})\,dt\right)
\]
and, for every fixed cutoff containing the discrete support of the marks,
\[
 \mathbb E e^{-\int g\,d\widehat\Xi_{N,L}}
 \longrightarrow
 \exp\!\left(-\lambda\int_1^2
   \sum_{e\ge0}2^{-(e+1)}(1-e^{-g(t,e)})\,dt\right).
\]
Here the marked left-hand side is literal as well: the
`FullMarkedLaplaceTransfer` module defines the complete source functional by
summing over all finite excesses. As soon as \(g(t,e)=0\) for \(e>E\), Lean
proves its pointwise equality, and then equality in expectation, with the
truncated functional to which the finite Chen–Stein argument applies. The
public endpoint therefore quantifies directly over
`infiniteFullMarkedLaplaceExpectation`, not over a truncated surrogate. The
probability of a mark \(>E\) has `limsup` at most
\(\lambda2^{-(E+1)}\), yielding the final uniform tightness. These complete
functionals constitute the formal characterization of the two PPPs. Since
mathlib does not yet provide a standard space of point measures with the vague
topology, the repository does not introduce an artificial topological object
merely to restate this conclusion.

Lemma 14.5, almost-sure uniqueness of the excess,
\(J_{x,L}=\sum_eK_{x,e}\), Lemma 14.8, and the v0.39 cylinder transfers remain
the basis of this closure. The maximum law in Corollary 14.9 is also concluded
canonically. For the finite vector of counts, the source/retained laws and
their coupling are exact. `PrimeEncodedCountVector` injects the vector into
the positive integers through prime powers; `PrimeEncodedCountLaplace`
identifies exactly the pushed-forward source law and its transforms with the
constant tests \(s\log p_e\). `PoissonVectorMass` performs the same computation
for the product--Poisson target, and `DirichletAtomConvergence` turns
convergence of all these transforms into convergence of each atom. Thus the
theorem `corollary_fourteen_eight_counts` closes the count vector under the
three canonical literature inputs alone, with no retained-law premise and no
new bridge.

Lean milestone `0.38.0` discharged the internal generalized-Pell interface of
Lemma 9.2. The new `PaperC.Diophantine.GeneralizedPell` module formalizes the
translation into principal ideals, the quotient of two generators in the same
fiber as a Pell unit, exponential unit growth, logarithmic control by height,
finite orbit counting, and reduction to the squarefree kernel. The factor
\(\tau(|M|)^2\) is not assumed:
`QuadraticIdealDivisors` proves it in Lean by unique factorization of ideals
and quadratic decomposition theory. The former bridge
`PCv07c-L9.2-generalized-Pell` now has `status: discharged`.

The historical Halter--Koch boundary remains registered for provenance, but
its compatibility proposition is now discharged without using the cited book.
`HalterKochConductorDescent` constructs
\(K=\mathbb Q(\sqrt D)\), embeds \(\mathbb Z[\sqrt D]\) into \(O_K\), and
assigns the extended principal ideal on solutions, with a total harmless
default off the equation. Concrete trace and norm calculations prove
\(2O_K\subseteq\mathbb Z[\sqrt D]\). Since \(O_K/2O_K\) has four elements,
the residue of a relative unit supplies the historical `Fin 4` colour. Equal
residues make the quotient unit congruent to one modulo (2); lifting both it
and its inverse produces a unit of \(\mathbb Z[\sqrt D]\), which descends the
principal-ideal equality. The earlier source-shaped `Fin 3 → Fin 4` adapter is
retained for compatibility but is not used by this proof. Consequently
`HK13-QO-conductor-fibres` has `kind: external` and `status: discharged`.

Version 0.39 narrows the bibliographic boundary further:
`PaperC.Diophantine.PellDivisorEnvelope` starts from Nicolas--Robin's direct
logarithmic inequality for the divisor function. Lean then proves the
polynomial-height substitution, treatment of small arguments, squaring of the
divisor factor, and absorption of the logarithmic unit count. The former
specialized envelope `NicolasRobinPellEnvelopeStatement` remains as the
discharged `NR83-T1-divisor-bound` wrapper; canonical endpoints now take
`NR83-T1-divisor-log-bound`.

The dyadic mother-mass chain identifies exactly
\[
  R_2(N,L)=R_{2,\kappa}(N,2N,L),
\]
preserves on this specialization the rates \(3/2\), \(7/4\), \(31/16\), and
\(5/3\) of the power-saving sectors, and then transports the exponential gain
from the dense nonterminal branch. Summing the seven sectors now gives the
canonical statement printed as Corollary 11.3,
\[
  R_2(N,L)=O_C\!\left(N^2
    \exp\!\left(-c_R\frac{\sqrt{\log N}}{\log\log N}\right)\right),
  \qquad c_R>0.
\]
In particular it gives
\[
  R_2(N,L)=O_C\!\left(
    \frac{N^2}{(\log\log N)^2}\right)
\]
under Evertse--Silverman and Nicolas--Robin.

The canonical entries
`corollary_thirteen_ten_uniformBigO_canonical` and
`theorem_one_one_uniformBigO_canonical` have the exact bridge list AGG,
Evertse--Silverman, and Nicolas--Robin, all of kind `external/open`. The
Halter--Koch compatibility bridge is `external/discharged` and no longer a
theorem argument. Thus no `internal/open` bridge propagates to canonical
Theorem 1.1.
Version 041 removes the old signatures taking Pell or its specialized
envelope directly, along with the four interfaces C11.3, P9.9, P9.11, and
T10.1 and their public consumers. The v0.48.1 candidate further removes the
now-discharged conductor argument from the canonical signatures.

This version also retains the bridge-free closure of Lemmas 17.14–17.16 and
the \(\alpha=3/16\) instance of 17.17, as well as the canonical terminal
population
\[
  T_K=\{s+\widetilde k\le
    \lfloor K\sqrt B/\log B\rfloor\}
\]
It now closes the three deep sectors of Proposition 16.1 under only the
already registered open external inputs: Evertse--Silverman and
Nicolas–Robin.

The arithmetic equivalence of Lemma 9.10 is now proved in its exact source
scope. When
`canonicalReducedCandidate? x y (L + 1) ((L + 1) ^ A) = none`, the canonical
rational code is zero, and the corrected coordinates of
cardinality \(D^\#+c^\#\) parametrize the full solution space for the large
primes. Under \(L+1\le M\), \(x+L\le M\), and \(y+L\le M\), Lean maps the
boundary of each complete relation into the kernel of the concrete matrix
formed by the small-prime rows and the two block parities. Injectivity and
surjectivity of this map are proved, yielding the linear
relations--kernel equivalence and, because the rational code is zero, the
residual-quotient--kernel equivalence. The audited 9.10 interface is retained
with `status: discharged`.

For 17.26, Lean covers the literal active population by the bases \(x-1\) of
windows containing two defects and by finite component shapes, then
disintegrates each fixed fiber by its smooth squarefree coefficient. Degree
one satisfies the \(N^{1/2+o(1)}\) envelope. Degree two injects into Pell when
its normalized coefficient is at least two, and into signed divisor pairs of
\(\Delta^2\) when that coefficient is one. Degree at least three injects into
Evertse--Silverman. The factorial factors controlling \(\omega(n)\), divisor
sums, and the Evertse--Silverman sum are now proved uniformly
\(N^{o(1)}\); degrees, bases, and shapes are then aggregated. Lean thereby
obtains
\[
  N^{3/2+o_{C,\kappa_0}(1)}
    =o_{C,\kappa_0}(N^2)
\]
with no dedicated interface for 17.26.

For 17.28, Lean follows the manuscript's literal dichotomy. When
\(3c^\#\le2B\), a direct count of hosts with a component of size at most ten
is assembled from the mobile fibers of degrees \(2\) and at least three,
under Pell and Evertse--Silverman. When \(2B<3c^\#\), a component of size two
exists. Lean formalizes the two-singleton parametrization, harmonic sum, and
Euler product, and then establishes the global count
\[
  N\exp\!\left(C_{\rm term}\frac{\sqrt B}{\log B}\right).
\]
The global union over shapes uses the safe upper bound \(9B^4\), rather than
the refined \(B^2\) factor from the source proof; this polynomial loss is
absorbed into \(C_{\rm term}\) and does not change the rate. After extracting
\(2^{R_K(B)+1}\), the formalized choice
\[
  K=\frac{2C_{\rm term}+1}{\log2}
\]
yields \(2C_{\rm term}<K\log2\) and the required little-oh, with no dedicated
interface for 17.28.

For 17.30, Lean closes the incidence of first starts and uniform summation of
partner fibers under Pell, replaces the small-subset count by the Chebyshev
envelope, and then proves \(\#T_K\le N^{3/4+o(1)}\) and
\(\sum_{T_K}(2^\tau-1)\le N^{7/4+o(1)}=o(N^2)\). The transfer between the rank
population and the intrinsic population applies the nonaligned theorem of
9.10 directly, with no arithmetic hypothesis supplied by the caller. The
canonical APIs of Proposition 16.1 and Theorem 16.2 therefore construct this
sector themselves from Pell.

The three historical interfaces 17.26, 17.28, and 17.30 remain registered for
the two direct generic assemblies and for traceability, with status
`discharged`; the historical interface of 9.10 now has the same status. The
canonical API consumes none of them. Canonical Proposition 16.1 takes only
Evertse--Silverman and the two literature corollaries that reconstruct Pell.
Version 041 removes the six intermediate sector adapters and the variants
receiving Pell directly; only canonical endpoints and direct generic
assemblies are retained. The v047 toolchain remains frozen at Lean/mathlib
`v4.32.2`. This migration changes neither canonical signatures nor audit
registry entries.

For Theorem 16.2, under the source hypothesis \(C>0\), Lean defines the global
count \(Z_M\) on a common finite cylinder, proves the truncation coupling,
Poisson recentering, and the iterated passage first in \(j_0\) and then in
\(M\). It obtains
\[
 d_{\rm TV}(\mathcal L(Z_M),\operatorname{Pois}(\Lambda_M))\to0,\qquad
 \Lambda_M=(1+o_C(1))M2^{-L},
\]
as well as \(\mathbb P(Z_M=0)=e^{-\Lambda_M}+o_C(1)\), under the registered
inputs of Proposition 15.5 and the bounded-ratio passage.
`TheoremSixteenTwoRecentered` now completes the Poisson coupling step and
exposes the printed form
\[
 d_{\rm TV}(\mathcal L(Z_M),\operatorname{Pois}(M2^{-L}))\to0,
 \qquad
 \mathbb P(Z_M=0)=e^{-M2^{-L}}+o_C(1).
\]
`TheoremSixteenTwoInfiniteModel` defines the literal count on the infinite
Rademacher product space and proves exact equality with the finite-cylinder
law before transporting the canonical theorem. Likewise,
`infiniteDyadicStartCount`, its exact law identity, and
`theorem_one_one_infinite_model` place Theorem 1.1 directly on the source law.
`CorollaryPrefixLaw` defines the finite-prefix observable literally,
including the exceptional start at (x=1), and proves the exact deterministic
identity
\[
  \{W_{M,L}=0\}=\{R_M<L\}.
\]
The source-law transfer identifies its infinite-product law with a common
finite cylinder. `PrefixBoundaryProbability` proves that the left-boundary
event has exact mass (2^{-\pi(L)}). `PrefixOverflowCoupling` identifies the
right-overflow contribution with the masked first moment at
(N'=M-L+2), transports the critical window, and proves that the boundary
plus overflow coupling cost is uniformly (o_C(1)). Finally,
`CorollaryPrefixLawCanonical` combines this coupling with the recentered
Theorem 16.2 and exposes Corollary 16.4 directly on
`infinitePrefixStartCount`:
\[
 d_{\rm TV}(\mathcal L(W_{M,L}),\operatorname{Pois}(M2^{-L}))=o_C(1),
 \qquad
 \mathbb P(R_M<L)=e^{-M2^{-L}}+o_C(1).
\]
Marginal and law
invariance under cylinder enlargement is a proved finite equivalence. The
bounded-ratio modules now certify the cardinality and mass of bad starts, the
little-oh estimates for \(b_1\) and the mean of \(b_2\), the mixture of
conditional laws, the good/complete coupling, the retained mean, and its
rounding error. `BoundedRatioPoissonAssembly` assembles these results under
AGG and Proposition 16.1, after which `TheoremSixteenTwo` transfers them
exactly to the retained count and closes the iterated passage. The former
aggregate internal interface `BoundedRangePoissonApproximation` is removed.

Generic public Theorem 16.2 retains the three sector interfaces for an
arbitrary terminal classifier. Its principal canonical variant no longer
takes a threshold \(K\), a terminal family, or a Section 17 estimate. Its only
unformalized premises are PNT, Laishram--Shorey,
Balasubramanian--Shorey, AGG, Evertse--Silverman, and Nicolas--Robin, all
`external/open`. The conductor comparison used inside Pell is constructed in
Lean. It adds neither probabilistic assembly debt nor any open internal bridge.
The §14 PPP convergences are now certified by their Laplace
functionals and, for marks, by uniform tightness. Publication metrics are
reproduced in
[`REPRODUCIBILITY.md`](REPRODUCIBILITY.md).

## Licensing

The Lean source code is licensed under the Apache License 2.0; see
[`LICENSE`](LICENSE). The English and French manuscript PDFs included in this
repository are licensed under the Creative Commons Attribution 4.0
International license (CC BY 4.0).

## Archive contract

Starting with version 0.19, every published archive has a single
`paper_c_lean/` root. Project files sit immediately beneath that root. This
contract is stable for subsequent versions: neither a flat archive nor a
double `paper_c_lean/paper_c_lean/` nesting. The archive for this release is
`paper_c_lean_v0481.zip`. It includes both hashed PDFs at the project root,
so every fingerprint check is executable offline from a fresh extraction.
Validate the generated metadata in the extracted archive with the generator's
read-only check, not with `git diff`:

```bash
zip_check_dir="$(mktemp -d)"
unzip -q paper_c_lean_v0481.zip -d "$zip_check_dir"
(cd "$zip_check_dir/paper_c_lean" && \
  node scripts/check_comparator_sources.mjs && \
  node scripts/generate_audit.mjs --check)
```

The archive intentionally contains no `.git` directory, so a Git cleanliness
test is neither available nor required for this extraction check.

## Certified modules

- `PaperC.Arithmetic.ParityVector`: vector of prime valuations modulo two and
  compatibility with multiplication.
- `PaperC.Arithmetic.CRT`: a certificate of pairwise coprime congruences
  defines a unique class modulo the product, with a certified interface
  between `Nat.ModEq` and integer congruences.
- `PaperC.Arithmetic.IntervalCongruence`: exact upper bounds for the number of
  representatives of a class in an interval and in a product of two
  intervals, used by replacements R3--R5.
- `PaperC.Arithmetic.CertificateCount`: composition of CRT uniqueness and
  interval counting, directly giving the upper bound
  "length / product of moduli \(+1\)" for a finite certificate, as well as its
  two-variable rectangular form. Under \(P\le N\), and for intervals of
  length at most \(C_0N\), Lean also absorbs the terminal term and obtains
  \((C_0+1)N/P\), and respectively its square.
- `PaperC.Arithmetic.StartResidue`: canonical residue class of a start offset
  and the exact equivalence
  \(x\equiv r_{p,v}\pmod p\iff
  p\mid\operatorname{label}(x,v)\), connecting arithmetic cells to the natural
  CRT.
- `PaperC.Arithmetic.ChannelGeometry`: integer geometry of a channel,
  primitive direction of the difference of two cells, and bounds
  \(a,b\le L\).
- `PaperC.Arithmetic.ChannelUniqueness`: exact determinant argument yielding
  uniqueness of two reduced rational codes in a sufficiently narrow channel
  (the arithmetic core of Lemma 5.2).
- `PaperC.Arithmetic.ChannelCount`: injective projections of channel cells and
  an exact upper bound by the largest primitive step, namely the geometric
  factor \(1+B/\max(a,b)\) of Lemma 7.2.
- `PaperC.Arithmetic.ResidualChannelCells`, `ResidualChannelCount`,
  `ResidualChannelSupport`, `ResidualPrimeMass`,
  `DyadicPrimeReciprocalSums`, and `ResidualChannelLemmaSevenTwo`: exact
  definition of \(\Delta=h+bj-ai\), the residual cells
  \(p\mid\Delta\ne0\), their finite prime support, and their fibers by value
  of \(\Delta\). Lean proves
  \[
  E_p\le
  \left(1+\frac{8qB}{p}\right)\left(1+\frac Bq\right),
  \qquad p<4qB,
  \]
  and then, by dyadic shells and the already certified Chebyshev bound,
  \[
  \sum_p\frac{E_p}{p}\le
  \frac{896B}{\lfloor\log_2B\rfloor}.
  \]
  The chosen support is proved complete: enlarging the prime cutoff adds only
  zero terms. This certifies Lemma 7.2 in an effective finite formulation,
  under the paper's explicit hypotheses \(m\ge2\), \(2\le q\le L\), and
  \(B=L+1\ge4\).
- `PaperC.Affine.StartBoundaryRange`, `RelationBoundaryIff`, and
  `RationalChannelCode`: the complete boundary is exactly the hyperplane of
  even vectors; the prime equations characterize the relations exactly; even
  subsets of the units of a channel give an injective code of dimension
  \(m-1\), with nonzero criterion \(m\ge2\) and affine character
  \(1_{\{i=-1\}}+1_{\{j=-1\}}\). This certifies Lemma 5.1.
- `PaperC.Arithmetic.CanonicalChannel`,
  `PaperC.Asymptotics.CanonicalChannelWindow`,
  `PaperC.Affine.CanonicalRationalCode`, and
  `PaperC.Asymptotics.CanonicalRationalCodeWindow`: finite selection of the
  canonical reduced ratio, uniform uniqueness by determinant, construction
  of \(S_{\rm rat}\), \(\sigma,\tau\), the exact \(m_{\rm ex}\le1\) branch,
  and coverage of every nonzero code. This certifies Lemma 5.2.
- `PaperC.Arithmetic.ChannelEnumeration`,
  `ChannelMultiplicityBounds`, `ChannelStartPairs`,
  `SeparatedSmallChannels`, `HeightTwoPairCount`,
  `WeightedChannelMass`, and `RationalMassFinite`, together with the
  asymptotic modules `CriticalChannelPowers`, `RationalPowers`,
  `CriticalRationalMassEnvelopes`, `CriticalRationalMass`, and
  `WeightedChannelMassCritical`: finite counts of ratios, heights, units, and
  pairs of starts, treatment of the boundary case \(q=2\), followed by the
  uniform proofs \(N^{4/3+o_C(1)}\), \(N^{5/3+o_C(1)}\), and
  \(N^{1+o_C(1)}\). They certify Proposition 5.4 and Lemma 5.5.
- `PaperC.Combinatorics.LargePrimeOccurrences`,
  `LargePrimeGraph`, `PinnedGraphResolution`, and
  `LargePrimeGraphResolution`: construction of the large-prime graph, exact
  identification of its equations with \(W_{>B}(x,y)\), and then a canonical
  linear equivalence with one free coordinate per unpinned component. Lean
  proves \(\dim W_{>B}=D+c\), identifies \(D\) with the literal number of
  defective vertices, and obtains \(D+2c\le2(L+1)\). This certifies Lemma 6.1
  in full.
- `PaperC.Arithmetic.ComponentSquareClass` and
  `PaperC.Combinatorics.LargePrimeComponents`: on every unpinned component of
  two separated positive starts, the parities at primes \(p>L+1\) vanish and
  the product of the labels is \(d z^2\), where \(d>0\) is squarefree and all
  its prime divisors are \(\le L+1\). The representative \(d\) and positive
  root are canonical and unique. This certifies the square-class conclusion
  of Lemma 6.2.
- `PaperC.Arithmetic.ExactUnitLargeKernel` and
  `PaperC.Combinatorics.ExactUnitIsolation`: for an exact unit whose primitive
  coefficients lie below the cutoff, both occurrences have the same large
  odd kernel. If this kernel is one, both are defective; otherwise they are
  adjacent and alone form an unpinned component of cardinality two. Moreover,
  two distinct units in the same positive channel have disjoint pairs of
  occurrences and determine distinct components; in the nondefective branch,
  these remain unpinned and of cardinality two. This certifies Lemma 6.3 in
  full under its explicit positivity, coprimality, height, and cutoff
  hypotheses.
- `PaperC.LinearAlgebra.QuotientParity`,
  `CanonicalResidualQuotient`,
  `PaperC.Combinatorics.LargePrimeRelationBoundary`,
  `ResidualComponentCounts`, and `DefectiveVertexIntervalBound`: literal
  interpretation of \(\tau\) as the dimension of
  \(R(x,y)/S_{\rm rat}\), injection of the relation boundary into
  \(W_{>B}\), loss of one dimension through left-block parity, partition
  \(m=d+n\), exact definitions of \(D^\#\) and \(c^\#\), and then
  \[
  \tau\le D^\#+c^\#,\qquad D^\#+2c^\#\le2B.
  \]
  The defective vertices inject into the two sets of interval defects;
  Proposition 3.2 then gives, with uniform quantifiers in the critical window,
  \(D^\#\ll_C B/\log B\). This certifies Lemma 6.4 in the finite model under
  the paper's explicit geometric hypotheses.
- `PaperC.Combinatorics.ResidualCertificates`,
  `OneUnitResidualExceptions`, `CanonicalResidualComponents`,
  `CanonicalResidualPrimeProduct`, and
  `CanonicalResidualCRTCertificate`: concrete construction of
  \(C_{\rm res}\), proof that \(\lvert C_{\rm res}\rvert=c^\#\), selection of
  the smallest prime and then the lexicographically least cell in each
  component, and a canonical family of cardinality \(c^\#\). Lean verifies
  that the left offsets are distinct, as are the right offsets; that the
  primes \(p_s>B\) are distinct; that they divide \(x+i_s\) and \(y+j_s\);
  and that \(h+bj_s-ai_s\ne0\) when \(m\ge2\). When \(m=1\), every exception
  belongs to the family of components meeting both occurrences of the unique
  unit, whose cardinality is at most two. This certifies Lemma 6.5. The
  canonical product \(P^\#\) is also defined, is positive, has exactly
  \(c^\#\) factors, and carries a formal \(P^\#\le N\) / \(P^\#>N\)
  dichotomy. The associated complete certificate has this product, is
  admissible exactly in the first branch, and both starts satisfy all its
  congruences.
- `PaperC.Affine.System`: finite affine systems over \(\mathbf F_2\),
  compatibility, fibers, and exact counting by the kernel.
- `PaperC.Affine.Probability` and `PaperC.Affine.Fourier`: exact uniform
  probability of a fiber and the division-free Fourier identity of Lemma 2.1.
- `PaperC.Affine.Normalization`: relation character, parameters
  \(\eta,\rho\), exact normalization of the signed sum, and the inequality
  \(\lvert\eta2^\rho-1\rvert\le 2^\rho-1\) from Lemma 2.1.
- `PaperC.Combinatorics.TreeBoundary`: boundary of a finite edge set,
  additivity under symmetric difference, existence on a connected graph, and
  an existence--uniqueness bijection between edge subsets of a tree and even
  vertex subsets (Lemma 2.2).
- `PaperC.Combinatorics.CertificateSummation`,
  `CertificateCRTInstantiation`, `CertificateCellFamilies`, and
  `CertificateLemmaSevenOne`, together with
  `PaperC.Analysis.ExponentialSeriesMajorant`: passage from ordered to
  unordered certificates, distinct primes and hence coprimality, condition
  \(P\le N\), weighted 1D/2D CRT counts, exact \(1/r!\) factor, grouping of
  cells giving \(u\sum_pE_p/p\) and \(uM\sum_p1/p^2\), summation over all
  possible sizes, and an upper bound by the exponential series. This certifies
  Lemma 7.1 in its exact finite formulation.
- `PaperC.Combinatorics.ResidualMasses`,
  `PropositionSevenThreeSigmaZeroCover`,
  `PositiveSigmaFixedChannelCover`, `PositiveSigmaFixedChannelBound`,
  `PositiveSigmaGlobalGrouping`, and `PositiveSigmaKeyMassBound`, together
  with the asymptotic modules `CorrectedDefectEnvelope`,
  `SigmaZeroQuadraticCritical`, `ResidualCertificateMassCritical`,
  `PositiveSigmaQuadraticCritical`, `QuadraticAndInterpolationClosure`, and
  `PropositionSevenThreeCritical`: literal definition of the masses
  \(Q_{\rm res}\) and \(R_{\rm res}\) in the \(P^\#\le N\) sector, exact
  partition according to \(\sigma=0\) or \(\sigma>0\), two-dimensional CRT
  coverage of the exceptional branch, and then grouping of the systematic
  branch without double counting by the finite keys \((q,a,b,h,r)\). The
  explicit envelopes respectively use
  \(\exp(112B/\lfloor\log_2B\rfloor)\) and
  \(\exp(3584B/\lfloor\log_2B\rfloor)\), together with the finite maximum of
  the corrected defect. Lean deduces, uniformly in the critical window,
  \[
  Q_{\rm res}\le N^{2+o_C(1)},\qquad
  R_{\rm res}\le N^{7/4+o_C(1)},
  \]
  with the second bound obtained by finite interpolation (6.6). This fully
  certifies Proposition 7.3 under its explicit hypotheses.
- The modules `SmallHeightLargeProductPairs`,
  `SmallHeightResidualPrimeSupport`, `SmallHeightResidualComponentEnvelope`,
  `SmallHeightTauEnvelope`, and `SmallHeightLargeProductMassBound`, together
  with the asymptotic modules `SmallHeightComponentEnvelopeCritical`,
  `SmallHeightTauEnvelopeCritical`, `SmallHeightSigmaZeroCritical`,
  `SmallHeightPositiveSigmaCritical`, and `PropositionSevenFourCritical`
  formalize the canonical small-height \(P^\#>N\) sector
  \(q\le\sqrt{\log(L+1)}\). Lean constructs a finite envelope for the number
  of residual components, separates the \(\sigma=0\) and \(\sigma>0\)
  branches exactly, and then proves, for \(C\ge0\) and \(A\ge1\), uniformly
  in the critical window,
  \[
  Q_{\rm res}^{\rm small\ height}\le N^{5/3+o_C(1)},\qquad
  R_{\rm res}^{\rm small\ height}\le N^{19/12+o_C(1)}.
  \]
  The second upper bound implies in particular
  \(R_{\rm res}^{\rm small\ height}=o_C(N^2)\). This certifies
  Proposition 7.4 under its explicit hypotheses, without asserting an
  asymptotic equivalence or certifying the main theorem.
- `PaperC.Combinatorics.SmallComponentExtraction`,
  `AlignedExactFreeComponents`, `ComponentProductParity`,
  `AlignedRungeBridge`, `AlignedCoreExclusion`,
  `AlignedDeepCoreExtraction`, and the coding modules
  `TwoParityColumnCode`, `AlignedComponentCode`,
  `AlignedComponentHamming` certify the finite core of Theorem 8.1. Lean
  removes at most two components meeting the exact units, extracts a family
  of small components, constructs the matrix \(\Phi\) with its two block
  parities, finds a short word, deduces a square product and distinct roots,
  and then applies Runge. For the deep core of the already certified
  partition, \(B\ge32\) and \(3B<16c^\#\) explicitly yield at least \(B/16\)
  exact-free components of size at most \(43\). The integer radius
  \[
  t(B)=\left\lceil
    \frac{64B}{\lfloor\log_2B\rfloor
      \lfloor\log_2\lfloor\log_2B\rfloor\rfloor}
  \right\rceil
  \]
  uniformly satisfies the Hamming budget. Lean also closes \(2R\le ax\) and
  the entire range of Runge inequalities \(1\le k\le43t(B)\), and finally
  proves that no aligned core with \(3B<16c^\#\) and height \(H\le B^A\)
  remains for sufficiently large \(N\) in
  \(\lvert L-\log_2N\rvert\le C\).
- `PaperC.Diophantine.EvertseSilvermanInput` formalizes the exact interface of
  Lemma 9.1 without turning the cited result into a global declaration. The
  external bridge is an explicit hypothesis on the abscissae \(X\) for which
  \(Z^2=e\prod_r(X+h_r)\) has a solution \(Z\ne0\), with upper bound
  \(7^{4+9|S|}\). Lean proves that there are at most two ordinates for each
  abscissa, thus recovering the factor two in (9.2); proves separately that
  there are at most \(d\) solutions with \(Z=0\); and then uses the injection
  \((X,Y)\mapsto(X,eY)\) to obtain the corresponding upper bound for
  \(\prod_r(X+h_r)=eY^2\). This implication is certified; the
  Evertse--Silverman theorem itself remains to be imported or formalized.
- `PaperC.Diophantine.PellInput` and
  `PaperC.Diophantine.PellRealExponent` formalize the reductions of Lemmas 9.2
  and 17.19 for every exponent
  \(K_0\in\mathbb R_{>0}\). `GeneralizedPell`,
  `QuadraticIdealDivisors`, and `PellDivisorEnvelope` discharge the internal
  bridge: ideals, unit orbits, heights, and the divisor envelope are rebuilt
  in Lean from the Nicolas--Robin input and the internal modulo-two conductor
  construction. Lean
  also proves the injection \((z,w)\mapsto(Az,w)\), the identity with
  \(X^2-ACw^2=Ae\), nonsquareness of \(AC\), all height bounds, and exact
  cardinality transfer. Lean passes to \(J=\lceil K_0\rceil\), then chooses
  \(H=\lfloor N^{K_0}\rfloor\) to obtain exactly the source predicate
  \(|z|,|w|\le N^{K_0}\). This adaptation adds no Diophantine hypothesis.
- `PaperC.Diophantine.ComponentNormalization` and
  `SingletonProductParametrization` certify the arithmetic cores of Lemmas
  9.3--9.5. Lean constructs the canonical squarefree factor of \(PQ=dz^2\),
  proves its uniqueness and the bound \(e\le dP\), treats degree one exactly,
  injectively reduces degree two to Pell and degree at least three to the
  Evertse--Silverman interface, and then establishes the canonical
  parametrization \(X=ecu^2,\ Y=(d/e)cv^2\), its converse, its uniqueness,
  and bounds for its parameters. `BoundedRatioManyDefectsDegreeTwoSum`,
  `BoundedRatioManyDefectsEvertseSum`, and
  `BoundedRatioManyDefectsDegreeAssembly` now assemble the asymptotic sums of
  9.4--9.5 under Evertse--Silverman and the discharged Pell bridge; only the
  literature inputs remain open.
- `PaperC.Combinatorics.DeepCoreSmallComponent` and
  `PaperC.Diophantine.MultipleDefects` certify the finite reductions of Lemmas
  9.6--9.8: extraction of a bounded-size component under a density hypothesis,
  injection of two defects into a Pell equation, exact cardinality transfer,
  and factorization of the same-class branch.
  `BoundedRatioNonterminalHostCounts`,
  `BoundedRatioNonterminalRealHosts`, and
  `BoundedRatioNonterminalAssembly` close the connection to host populations
  and the sums over smooth parameters under the same inputs.
- `PaperC.Asymptotics.PropositionNineNine` defines the exact deep-core
  population with \(\sigma=0\) and \(D^\#\ge3\), proves finite weight and mass
  envelopes, and removes zero-mass pairs. Each active host carries a canonical
  component with support between 2 and 10 and belongs to one of the two
  oriented branches with two concrete defects. Version 041 removes the former
  host-count interface and its asymptotic endpoint: the canonical mother-mass
  route uses direct bounded-ratio counts instead. The arbitrary fixed-shape
  API of 9.9 is no longer claimed as a public endpoint.
- `PaperC.LinearAlgebra.NonalignedCoreRank`,
  `PaperC.LinearAlgebra.CanonicalExactRank`,
  `PaperC.LinearAlgebra.CanonicalSmallRows`,
  `PaperC.Combinatorics.TerminalComponentCount`, and
  `PaperC.Arithmetic.TerminalMatching` formalize the cores of Lemmas
  9.10--9.12. Lean constructs the canonical families of cardinalities
  \(D^\#\) and \(c^\#\), and then the actual small-row matrix with
  \(\pi(L+1)+2\) rows: primes \(p\le L+1\) and two block parities. Under
  \(L+1\le M\), the columns injectively synthesize concrete large-prime
  solutions, and their kernel is characterized exactly by the unique
  boundaries of relations. In the nonaligned source branch
  `canonicalReducedCandidate? = none`, Lean proves that coordinate synthesis
  is surjective onto the full large-prime space. Under the coverage conditions
  \(x+L\le M\) and \(y+L\le M\), the complete boundaries then give a linear
  equivalence between relations and the concrete kernel. Since the rational
  code is zero, this equivalence descends to the residual quotient and proves,
  with no bridge, \(\tau+\widetilde k=D^\#+c^\#\). The combinatorial count
  gives at least \(B-3s\) components of size two; their kernels are
  nontrivial, equal within a component, coprime across components, and their
  product divides an explicitly bounded nonzero determinant.
- `PaperC.Arithmetic.TerminalKernelCount`,
  `PaperC.Combinatorics.CanonicalTerminalPopulation`,
  `PaperC.Combinatorics.TerminalClosureCounting`, and
  `PaperC.Diophantine.TerminalPartnerPell` certify the finite steps of
  Proposition 9.11 and the terminal closure of Theorem 10.1. For
  \(s=B-c^\#\), the canonical residual family has at least \(B-3s\)
  components of size two. A finite proxy for \(T_K\), parametrized by the
  function representing \(\widetilde k\) and by an integer budget, is
  connected to first-start and partner fibers; Lean proves \(\tau\le B+2\)
  and \(\mathrm{mass}(T_K)\le\#T_K\,4\,2^B\). This is supplemented by
  uniqueness of the factor above the threshold, double counting, injective
  reduction of partners to Pell, and
  \[
  \#A_{B,T}(X)\le
  2\sqrt X\sqrt T\prod_{p\le B}(1+p^{-1/2})
  \le2\sqrt X\sqrt T\,e^{2\sqrt B}.
  \]
  Partner counting is conditional on the two external inputs that reconstruct
  Pell. The asymptotic upper bounds for first coordinates and fibers, as well
  as the canonical assembly, are now closed. The former generic T10.1 wrapper
  is removed in v041.
- `PaperC.Combinatorics.SectionElevenPartition` and
  `CanonicalSectionElevenPartition` formalize the six ordered tests of Lemma
  11.1. The seven sectors cover all separated pairs, are pairwise disjoint,
  and determine a unique sector. The first three coincide exactly with the
  already certified populations of Section 7, and the union of the last four
  is exactly the deep core. The second module instantiates the terminal test
  with the integer-budget proxy and identifies Sector 7 exactly with its
  canonically nonaligned part; identification of the rank function and budget
  with the manuscript's asymptotic threshold remains explicit.
- `PaperC.Asymptotics.PropositionElevenTwo` retains the finite core of
  Proposition 11.2. Lean proves the identity
  \(2^{\sigma+\tau}-1=(2^\sigma-1)+2^\sigma(2^\tau-1)\), the associated
  finite sums, and disintegration into the seven sectors. Sectors 1–5 are
  connected to Propositions 7.3–7.5, Theorem 8.1, and Proposition 9.9.
  Version 041 removes the former public assembly parametrized by
  `smallRowRank` and `rankBudget`, along with its three internal interfaces.
  The uniform conclusion used by canonical endpoints is now supplied
  exclusively by the quantitative bounded-ratio mother mass.
- `PaperC.Asymptotics.PropositionElevenThree` retains the computation for the
  five elementary sectors and the assembly computation at the literal scale
  of Corollary 11.3,
  \[
    R_2(N,L)\ll_C N^2
      \exp\!\left(-c\frac{\sqrt{\log N}}{\log\log N}\right).
  \]
  The former public conclusions consuming the abstract rate for the sixth
  sector, the 9.9 host count, and the 10.1 terminal mass are removed.
  `DyadicKappaQuantitative` supplies the canonical conclusion directly.
- `PaperC.Probability.SectionTwelveMoments` retains the exact core of the §12
  moment deduction in the finite cylinder. Off-diagonal pairs are partitioned
  into strict overlap, contact, and separation; Lean proves the exact
  identities for the second factorial moment,
  \[
  \mathbb E[(Z)_2]-(N)_2\,2^{-2L}=o_C(1),\qquad
  \mathbb E[(Z)_2]-\lambda_N^2=o_C(1),
  \]
  and the variance from a supplied homogeneous estimate. The three former
  public endpoints receiving the 9.9, 9.11, and 10.1 interfaces remain
  removed. Version 042 adds
  `PaperC.SectionTwelveMoments.theorem_one_four_canonical`, which connects
  this core directly to the quantitative mother mass and simultaneously
  concludes the first-moment rate, the little-oh for the second factorial
  moment, \(R_2(N,L)=o_C(N^2)\), and the little-oh for the variance. Its only
  external hypotheses are Evertse--Silverman and Nicolas--Robin.
- `PaperC.Analysis.TerminalPrimeCutoff`,
  `PrimeReciprocalSqrtSum`, `PaperC.Probability.BadStartCount`, and
  `TerminalBadStartBound`, followed by `BadStartMass`, formalize the cores of
  Lemmas 13.3–13.4. The threshold is literally
  \(Y=\lfloor B^2\log B\rfloor\), with \(B\le Y\le B^3\) for \(B\ge2\).
  Lean injects the incidences of bad starts and retains the exact Euler
  product. A dyadic decomposition based only on the certified Chebyshev bound
  gives, for \(H\ge16\),
  \[
  \sum_{p\le H}p^{-1/2}\le
  2\sqrt{\operatorname{rootCutoff}(H)}
  +\frac{56\sqrt{2H}}{\lfloor\log_2H\rfloor/2},
  \qquad \operatorname{rootCutoff}(H)^2\le H.
  \]
  For \(N\ge1\) and \(B\ge16\), this estimate gives, without a bridge, the
  explicit envelope at the terminal threshold
  \[
  \#D_Y\le2L\sqrt{2N+L}\,
  \exp\!\left(
    2\sqrt{\sqrt{B^2\log B}}+
    168\sqrt2\,\frac B{\sqrt{\log B}}\right).
  \]
  The modules `TerminalBadStartsCritical` and `BadStartMassCritical` close
  both connections: the terminal exponential is uniformly subpolynomial, so
  \(\#D_Y=N^{1/2+o_C(1)}\), \(\#D_Y=o_C(N)\), and
  \(2^{-L}\#D_Y=o_C(1)\). Moreover, `terminalDefectWeightMass` is bounded
  exactly by the defect mass of Proposition 3.2. Lean thus concludes
  \(\sum_{x\in D_Y}\mathbb P(J_{x,L}=1)=o_C(1)\), with no bridge.
- `PaperC.Probability.LargePrimeDependencyGraph` and
  `PaperC.Analysis.DependencyEdgeBound`, followed by
  `PaperC.Asymptotics.DependencyEdgesCritical`, construct the supports
  \(\Pi_x(Y)\), the simple graph of good starts, and its coverage by a shared
  prime. They give
  \[
  E_Y\le(L+1)^2\sum_{\substack{Y<p\le3N\\p\ {\rm prime}}}(N/p+1)^2
  \]
  and then the fully explicit upper bound
  \[
  (L+1)^2\left(
    \frac{28N^2}{Y\lfloor\log_2Y\rfloor}
    +\frac{6N^2}{Y}+3N\right).
  \]
  At the literal cutoff \(Y=\lfloor(L+1)^2\log(L+1)\rfloor\), Lean reduces it
  to \(E_Y\le37N^2/m\) as soon as \(m\le\log(L+1)\), and then proves
  \(E_Y=o_C(N^2)\) uniformly in the critical window, with no bridge. Thus the
  asymptotic conclusion (13.6) is certified; the more precise manuscript
  formula containing \(NB^2\log\log N\) is not reproduced, because the
  coarser intermediate upper bound suffices for the little-oh.
- `PaperC.Probability.ConditionalDependencyGraph` and
  `ConditionalAGGInstantiation` close Lemma 13.5 and its connection to the
  AGG interface in the finite cylinder. Lean proves that each conditioned
  event depends only on \(\Pi_x(Y)\), and then its factorization against the
  joint event of an arbitrary family of good non-neighbors. The uniform law
  of the remaining coordinates is a `FinitePMF`; its marginal is exactly
  \(2^{-L}\). For every start, every outside set, and every Boolean assignment
  on that set—not merely the pattern in which all events hold—Lean proves the
  factorization required by `HasExactDependencyGraph`. Applying the external
  AGG bridge to the concrete cylinder is therefore a direct Lean theorem.
- `PaperC.Probability.ArratiaGoldsteinGordonInput` registers Theorem 13.7 as
  an `external` bridge. It defines a finite family of indicators, closed
  neighborhoods, exact independence outside a neighborhood, \(b_1,b_2\), the
  law of the sum, and total variation distance to the Poisson law. The
  consequence \(d_{\rm TV}\le2(b_1+b_2)\) is never postulated: it must be
  supplied explicitly as the cited hypothesis.
- `PaperC.Probability.SteinChenTerms` and
  `PaperC.Asymptotics.SteinChenCritical` formalize Lemma 13.8. The first term
  unconditionally satisfies \(b_1=o_C(1)\). The second is decomposed into
  overlap, contact, and separation; its finite upper bound and
  \(\mathbb E b_2=o_C(1)\) are proved under the conclusion of Proposition
  11.2, supplied as an explicit premise.
  `PaperC.Probability.ConditionalAGGAverage` proves the exact decomposition
  `SampleSpace ≃ SmallSample × LargeSample`, followed by the uniform total
  law. The conditional means of \(b_1\) and \(b_2\) are thereby identified
  exactly with the finite terms of 13.8, with no new bridge.
  `PaperC.Probability.SectionThirteenFiniteBound` adds the standalone total
  variation calculation: symmetry, triangle inequality, convexity of a
  uniform mixture, and a coupling inequality between finite natural-valued
  laws. Together, these modules give the explicit finite upper bound in
  Corollary 13.9 from the bad starts and Chen–Stein terms. Version 041 removes
  the former endpoint that reconstructed this premise from the three internal
  interfaces of 11.2.
  `PaperC.Probability.SectionThirteenCouplings` then identifies the averaged
  law with the law of the good count on the complete cylinder, couples it to
  the count of all starts, and proves directly
  \(d_{\rm TV}(\mathrm{Pois}(r),\mathrm{Pois}(s))\le|r-s|\). The parameter
  difference is exactly \(\#D_Y2^{-L}\). The canonical quantitative route
  directly assembles the stronger conclusion of Corollary 13.10:
  \[
    d_{\rm TV}\!\left(\mathcal L(Z_{N,L}),
      \mathrm{Pois}(N2^{-L})\right)=o_C(1).
  \]
  The former standalone qualitative endpoints of Corollary 13.9 and the
  abstract sector transfer of 11.3 are removed; the finite lemmas and
  canonical connections remain available. In particular, Lean proves
  \[
    e^{-c\sqrt{\log N}/\log\log N}
      =O_c((\log\log N)^{-2})
  \]
  It also establishes this rate for the normalized cardinality of bad starts,
  the weighted contribution of terminal defects, and their full probability
  mass. `PaperC.Asymptotics.DyadicKappaTransport` identifies the mother mass
  with the \(M=2N\) specialization of \(R_{2,\kappa}\).
  `BoundedRatioElementaryQuantitative`, `BoundedRatioDenseQuantitative`, and
  `DyadicKappaQuantitative` preserve the sector rates, assemble the moderate
  and dense branches of the sixth sector, and sum the seven masses.
  `PaperC.Asymptotics.CorollaryThirteenTen` then specializes the harmonic edge
  bound at the terminal cutoff, proves its critical rate, quantitatively
  reconstructs \(b_1\) and \(\mathbb E b_2\), applies AGG, and assembles the
  final total variation triangle. Lean thereby obtains
  \[
    d_{\rm TV}\!\left(\mathcal L(Z_{N,L}),
      \operatorname{Pois}(N2^{-L})\right)
      =O((\log\log N)^{-2})
  \]
  uniformly in \(\lvert L-\log_2N\rvert\le C\). The canonical entry depends
  only on AGG, Evertse--Silverman, and Nicolas--Robin. The former
  sector inputs and direct Pell inputs are removed. The finer intermediate
  formula of 13.6 is not claimed: the coarser harmonic bound suffices for the
  final rate.
- `PaperC.Probability.MaskedFirstMoment` and
  `PaperC.Asymptotics.MaskedFirstMomentCritical`, together with
  `PaperC.Asymptotics.LogLogRunWindow`, close the first moment of Proposition
  14.1 uniformly for all deterministic masks in the literal window
  \(\lvert L-\log_2N\rvert\le C_\star\log\log N\). The resulting envelope is
  \(N^{-1/2+o(1)}\), and hence uniformly \(o(1)\), with no bridge.
- `PaperC.Probability.MaskedSteinChen`,
  `PaperC.Asymptotics.MaskedPoissonCritical`, and
  `PaperC.Asymptotics.MaskedPoissonCanonical` close Proposition 14.2 modulo
  the literature alone. The original graph remains an exact dependency graph
  after deterministic cancellation of indicators outside the mask; its
  \(b_1,b_2\) terms are bounded by their complete versions. Lean identifies
  the averaged conditional law with the law of the masked count on the
  complete cylinder, couples this count after removing \(D_Y\), controls the
  parameter loss exactly, and then proves, uniformly for every
  \(A_N\subseteq I_N\),
  \[
    d_{\rm TV}\!\left(\mathcal L(Z_{N,L}(A_N)),
      \operatorname{Pois}(|A_N|2^{-L})\right)=o_C(1).
  \]
  The canonical endpoint takes exactly AGG, Evertse--Silverman, and
  Nicolas--Robin. The former internal interfaces of
  Proposition 11.2 and their public wrappers are removed in v041; the
  canonical signature is unchanged.
- `PaperC.Asymptotics.MaskedPoissonRate` closes Remark 14.3 at its printed
  quantitative strength. The induced-subgraph \(b_1,b_2\) sums are dominated
  term by term before the small-prime expectation, while the coupling and
  parameter displacement are absorbed by the two positive full-block
  corrections. Hence the preceding display is uniformly
  \(O_C((\log\log N)^{-2})\) over all masks.
- `PaperC.Probability.SpatialThinningFinite`,
  `IndependentThinning`, `LaplaceVoidClosure`, and
  `PoissonLaplaceFunctional` construct the product law of the auxiliary
  Bernoulli variables and prove the finite identity
  \[
    \mathbb P(W_g=0\mid(J_x)_x)
      =\exp\!\left(-\sum_{x:J_x=1}g_x\right),
  \]
  together with the bounds on the thinned terms and the AGG error
  \(4(b_1+b_2)\). `SpatialRiemannSums`,
  `SpatialMarkedParameters`, `ConditionalExpectationAverage`,
  `InfiniteLaplaceTransfer`, and `SpatialLaplaceCritical` connect this
  identity to the literal Riemann sum and to expectation under the true
  source law. The final theorem is the Laplace functional of
  \(\operatorname{PPP}(\lambda\,dt)\).
- `PaperC.Model.InfiniteRademacher` constructs the infinite product law of the
  prime signs and proves Lemma 14.5 without a bridge. A constant tail would
  force all sufficiently late prime bits to zero, a null event because its
  cylinders of length \(N\) have mass \(2^{-N}\). `InfiniteCylinderTransfer`
  proves that every finite projection is exactly the preceding uniform law
  and that multiplicative values coincide on integers covered by the cutoff.
- `PaperC.Probability.InfiniteExactLengthProbabilityTransfer` specializes
  this image law to exact-length events. It proves their measurability,
  identifies them with the preimage of the finite event when the cutoff covers
  \(x+q-1\), and then transforms their infinite measure exactly into a
  rational uniform probability. The same identity is established for the full
  double sum over starts removed in Lemma 14.8.
- `ExactLengthDecomposition` and `InfiniteExactLengthDecomposition` give,
  almost surely, a unique excess \(e\) on the start event for every \(x\ge2\)
  and \(L\ge1\). The cardinal form is \(1\) on that event and \(0\) outside
  it. They also prove \(e>E\Rightarrow J_{x,L+E+1}=1\), the inclusion used in
  mark detruncation.
- `PaperC.Probability.MixedLengthAffine` certifies Lemma 14.6 in the finite
  cylinder. The exact-length events \(q_e=L+e+1\) and \(q_f=L+f+1\) form a
  unique mixed affine fiber whose probability is exactly
  \(2^{-q_e-q_f}\eta_{e,f}2^{\rho_{e,f}}\). When \(e,f\le E\), zero extension
  of the row coefficients injects the mixed-relation space into that of the
  two systems of length \(Q=L+E+1\), and Lean deduces
  \(\rho_{e,f}\le\rho_Q\), with no bridge.
- `PaperC.Probability.ExactLengthConditionalRank` formalizes the finite core
  of Lemma 14.8 after the small primes have been fixed. The exact systems on
  `LargeSample` satisfy the identities \(\eta2^\rho/2^m\). A realization of
  the rows by edges, private pivots, and control of the cycle space gives the
  exact marginal \(2^{-q}\) in the forest case and, when the local cyclomatic
  number is at most one,
  \[
    \mathbb P(K_{x,q}K_{y,r}=1\mid\mathcal F_Y)
      \le 2^{1-q-r}.
  \]
  The simultaneous arithmetic instantiation of these structural hypotheses is
  carried out downstream by the marked Chen–Stein modules, with no added
  bridge.
- `PaperC.Probability.ExactLengthBadStartMass` and
  `PaperC.Asymptotics.ExactLengthBadStartMassCritical` close Lemma 14.8. The
  removed mass is separated between already defective supports and full-rank
  systems, summed over \(0\le e\le E\), and then normalized at the common
  length \(Q=L+E+1\). Direct counting on non-root vertices costs a factor
  \(2\) relative to the constant displayed in the paper, without changing the
  uniform conclusion \(o_{C,E}(1)\).
  `lemma_fourteen_seven_finiteCylinder` is the intermediate step for the
  rational probabilities on the cylinder; `lemma_fourteen_seven` replaces
  each term exactly by \(\mathbb P_\infty(K_{x,e}=1)\) and therefore concerns
  the infinite source law.
- `PaperC.Probability.MarkedLocalGeometry` proves directly that two distinct
  marks at the same start and two strictly overlapping starts have zero joint
  mass. Support intersections at offsets \(L+e\) and \(L+e+1\) are computed
  exactly, preparing the local Chen–Stein contributions.
- `MarkedConditionalDependencyGraph`, `TwoStartLocalRank`,
  `MarkedSteinChenTerms`, and `MarkedSteinChenSplitBound` close the marked
  calculation. Local pairs inject into a population \(O_E(N(L+E))\), and
  their joint rank is bounded by \(E+1\). Separated pairs inject into common
  edges, and their rank defect is bounded by the homogeneous mass at
  \(Q=L+E+1\). `MarkedSteinChenCritical` transports the canonical \(κ\) bounds
  and obtains \(b_1,b_2=o_{C,E}(1)\) with no internal bridge.
- `MarkedLaplaceFiniteClosure` compares the complete and retained functionals
  exactly using the mass in Lemma 14.8 and controls the parameter correction.
  `MarkedLaplaceCritical` combines these estimates with the Riemann limits for
  each fixed cutoff. `PaperC.Probability.FullMarkedLaplaceTransfer`
  separately defines the literally complete source functional, whose inner
  sum ranges over all excesses \(e\in\mathbb N_0\), and proves that a test
  vanishing above \(E\) gives exactly the truncated functional, pointwise and
  after integration. `MarkedDetruncationCritical` then establishes
  \[
    \limsup_N\mathbb P(\text{a mark}>E)
      \le\lambda2^{-(E+1)}
  \]
  and uniform tightness as \(E\to\infty\). Finally,
  `CorollaryFourteenEightMaximum` proves
  \(\mathbb P(M_{N,L}\le m)\to
  \exp(-\lambda2^{-(m+1)})\) through the canonical route.
- `PrimeEncodedCountVector`, `PrimeEncodedCountLaplace`,
  `PoissonVectorMass`, and `DirichletAtomConvergence` close the other part of
  Corollary 14.9. Prime-power encoding is injective; the inverse transforms of
  the source law are exactly the marked functionals at tests \(s\log p_e\),
  those of the target are the product of the Poisson transforms, and Dirichlet
  inversion yields convergence of each vector atom. The canonical endpoint
  takes only AGG, Evertse--Silverman, and Nicolas--Robin.
- `PaperC.Asymptotics.SectionFourteenClosure` supplies the two public
  endpoints `theorem_one_two_ii_laplace` and
  `theorem_one_two_iii_laplace_and_tightness`. The latter quantifies over a
  positive continuous test structure carrying its witness of finite support
  in marks, literally concerns `infiniteFullMarkedLaplaceExpectation`, uses
  the complete/truncated equality from `FullMarkedLaplaceTransfer`, identifies
  the finite target sum with the full series on \(\mathbb N_0\), and then
  combines Laplace convergence with uniform tightness.
- `PaperC.Arithmetic.LowZonePrimePivots` and
  `PaperC.Asymptotics.LowZoneCritical` certify the finite core of Lemma 15.1:
  intermediate-prime supports, linear independence, rank, the identity
  \(r(x)=\pi(L)-\pi(\sqrt{x+L})\), and the summed bound. The \(o(1)\)
  conclusion no longer requires an internal bridge: Lean deduces the integer
  gap from \(x\le L^{2-\varepsilon}\) and itself establishes decay of the
  envelope. The sole `external` bridge is now the source statement
  \(\pi(t)\log t/t\to1\) of the prime number theorem; Lean derives from it the
  uniform lower bound \(3\log_2L\le\pi(L)-\pi(\sqrt{x+L})\) throughout the
  manuscript's zone.
- `PaperC.Arithmetic.LaishramShoreyInput`,
  `PolynomialZoneLargePrimes`, and
  `PaperC.Asymptotics.PolynomialZoneCritical`, followed by
  `PaperC.Asymptotics.PolynomialZoneSum`, conditionally close Lemma 15.2.
  Corollary 1 of Laishram–Shorey is an `external` bridge transcribed with its
  exact minimum and correction \(\delta(B)\). Lean removes the primes
  \(\le B\), attaches each remaining prime to a unique vertex, discards the
  superset of primes whose square divides a vertex—of cardinality at most
  three—and bounds by two the number of simple large primes per vertex. It
  thereby obtains the exact finite lower bound for non-\(B\)-defective
  vertices, specializes it to \(B=L+1,\ L+2<x\le2L^2\), and then transports
  it into the probability bound (15.1). The source PNT also formally gives the
  rank lower bound \(c_3B/\log B\), with \(c_3=1/32\). Lean then sums all
  probabilities over the literal band \(L+2<x\le2L^2\) and proves that this
  mass tends to zero under the two external bridges LS04 and PNT.
- `PaperC.Arithmetic.SquarefreeSmoothCount`,
  `PaperC.Asymptotics.SquarefreeSmoothCritical`,
  `PaperC.Asymptotics.HighZoneTwoDefects`, and
  `PaperC.Asymptotics.LemmaFifteenThree` conditionally close Lemma 15.3.
  Squarefree \(B\)-smooth kernels inject into subsets of the primes \(\le B\),
  giving the exact upper bound \(2^{\pi(B)}\), and then its
  \(\exp(O(B/\log B))\) scale under PNT. Lean also assembles the finite count
  over two kernels and two offsets, constructs the canonical kernels of the
  defective vertices, excludes the case of two equal kernels in the high
  zone, and effectively covers every two-defect window by the corresponding
  finite union. Under the Pell interface, now discharged by its two literature
  inputs, the cardinality is bounded by
  \[
    \#\mathcal D_B(3N)^2 B^2
      \exp\!\bigl(c\log(3N)/\log\log(3N)\bigr).
  \]
  Lean then combines these factors and uniformly compares
  \(\log(3N)/\log\log(3N)\) with the critical scale of the upper parameter
  \(M\). It obtains exactly, with a constant and threshold independent of the
  subblock,
  \[
    \#\{x\in[N,2N):m_x\ge2\}
      \le \exp(KL/\log L),
    \qquad 2L^2\le N\le M,
  \]
  when \(\lvert L-\log_2M\rvert\le C\). The only registered bridges are PNT
  and the literature inputs for generalized Pell (`external`).
- `PaperC.Arithmetic.BalasubramanianShoreyInput` registers Theorem 1 of
  Balasubramanian–Shorey as an `external` bridge, with the equations, density
  conditions, and primary source. The `BalasubramanianShoreyMaximum` module
  then proves the canonical decomposition of the product of defective
  vertices, smoothness of the remaining factor, and the literal conclusion of
  Lemma 15.4:
  \[
    m_x\le B-g_B,\qquad g_B=B-\mu_B(\theta_0),
  \]
  for sufficiently large \(B\) and \(x>B^2+2\), under this external bridge.
- `PaperC.Asymptotics.PropositionFifteenFive`,
  `PropositionFifteenFiveDecay`, `PropositionFifteenFiveClosure`, and
  `PropositionFifteenFivePartition` conditionally close Proposition 15.5.
  Lean defines the literal mass of starts \(2\le x<M/2^{j_0}\), covers the
  zone \(x\le2L^2\) with Lemmas 15.1–15.2, inserts Lemmas 15.3–15.4
  simultaneously into each upper block, and proves
  \[
    L\,e^{KL/\log L}\,2^{1-g_L}\longrightarrow0.
  \]
  The finite geometric sum explicitly gives \(O(2^{-j_0})\), and the predicate
  `DeepTruncationDoubleLimit` encodes the order \(j_0\to\infty\), followed by
  \(M\to\infty\). The finite partition starts at \(2L^2+1\), covers the high
  zone exactly by adjacent blocks up to the cutoff \(M/2^{j_0}\), treats the
  last block by its integer envelope, and uses at most \(2L\) blocks. The
  public theorem
  `PropositionFifteenFivePartition.proposition_fifteen_five` thus assembles
  the global bound \(O_C(2^{-j_0})+o_M(1)\) and the exact double limit under
  PNT, Laishram--Shorey, and Balasubramanian--Shorey (`external`) and
  generalized Pell (`internal`), with no residual-partition hypothesis.
- `PaperC.Combinatorics.BoundedRatioGeometry` and
  `PaperC.Asymptotics.BoundedRatioRationalMass` certify the new setting of
  Lemma 17.5. For \(U(N,M)=[N,M)\), Lean proves the exact cardinality of the
  interval and upper bounds for classes and channels, separates the volumetric
  channel \(q=2\) from heights \(q\ge3\), and then obtains the uniform bound
  \(16(\kappa_0+1)(L+1)^4N2^{\lfloor L/2\rfloor}\). Its asymptotic conversion
  bounds the systematic mass, with no bridge, by
  \(N^{3/2+o_{C,\kappa_0}(1)}=o_{C,\kappa_0}(N^2)\). The purely geometric sum
  of Lemma 17.6 is unchanged, and its already certified subpolynomial linear
  bound is re-exported.
- `PaperC.Combinatorics.BoundedRatioRelationalHosts`,
  `BoundedRatioResidualMasses`,
  `PaperC.Asymptotics.BoundedRatioRelationalHostsCritical`,
  `BoundedRatioCorrectedDefectEnvelope`, and `BoundedRatioSectorClosure`
  supply the common foundation for Sectors 17.14–17.16. Host counting is
  performed directly on \([N,M)\), at the exact cutoff \(M+L\), with no
  dyadic coverage. The linear and quadratic masses are connected by
  Cauchy–Schwarz, while uniform maxima of the corrected defect and envelopes
  independent of \(M\) are transported into the critical window.
- `PaperC.Asymptotics.BoundedRatioSmallProductSector`,
  `BoundedRatioSmallHeightSector`,
  `BoundedRatioShallowCoreSigmaCritical`, and
  `BoundedRatioShallowCoreSector` respectively close Lemmas 17.14–17.16. The
  first two sectors give \(Q_{\rm res}\le N^{2+o(1)}\) and
  \(R_{\rm res}\le N^{7/4+o(1)}\). The third gives
  \(Q_{\rm res}\le N^{19/8+o(1)}\) and
  \(R_{\rm res}\le N^{31/16+o(1)}\). All three quadratic little-oh estimates
  are Lean theorems with no bridge hypothesis.
- `PaperC.Asymptotics.PropositionSixteenOne` defines the literal quantity
  \(R_{2,\kappa}(N,L)\), proves the weight identities, and constructs, for
  every supplied terminal family, the seven ordered fibers of Partition
  17.31. The `BoundedRatioSectorAligned` module transports aligned exclusion
  to the sole common lower bound \(N\), closing the \(\alpha=3/16\) instance
  of Lemma 17.17 without a bridge, even across two subblocks.
  `PropositionSixteenOneCore` separates this core from the public wrapper to
  avoid import cycles. The generic theorem assembles Proposition 16.1 under
  the three `internal` interfaces of deep Sectors (5)–(7). The canonical
  theorem now constructs Sectors (5) and (6) from Evertse--Silverman and Pell,
  chooses the terminal threshold of (6) itself, and then constructs (7) from
  Pell and the source-exact Lean theorem for 9.10. It therefore no longer
  takes any Section 17 sector interface or 9.10 arithmetic hypothesis.
- `PaperC.Combinatorics.BoundedRatioCanonicalTerminalPopulation`,
  `BoundedRatioIntrinsicTerminalPopulation`,
  `PaperC.Asymptotics.BoundedRatioComponentNormalization`,
  `BoundedRatioComponentHosts`, `BoundedRatioTwoDefectStarts`,
  `BoundedRatioDistinctKernelTwoDefects`, `BoundedRatioManyDefectsReduction`,
  `BoundedRatioTerminalClosure`, and `BoundedRatioTerminalFibers` fix the
  terminal population, normalize the components, and isolate the finite
  invariants of Sectors 17.26–17.30.
- `PaperC.Asymptotics.BoundedRatioManyDefectsFibers` covers the literal active
  hosts by fibers with a window base containing two defects and a fixed shape.
  `BoundedRatioManyDefectsFixedFibers` then disintegrates these fibers by
  squarefree coefficient: degree one is closed, degree two is reduced to Pell
  or signed divisors, and degree at least three is reduced to
  Evertse--Silverman, with automatic polynomial heights.
  `BoundedRatioManyDefectsDegreeTwoSum` and
  `BoundedRatioManyDefectsEvertseSum` close the two explicit subpolynomial
  sums; the former relies in particular on the factorial bounds from
  `PrimeFactorsFactorialBound`. `BoundedRatioManyDefectsRealFibers`,
  `BoundedRatioManyDefectsDegreeAssembly`, and
  `BoundedRatioManyDefectsAssembly` then aggregate degrees, bases, and shapes,
  and close 17.26 in full under only the ES and Pell bridges.
- `PaperC.Asymptotics.BoundedRatioNonterminalClosure` closes the 17.28 weight
  calculation. `BoundedRatioNonterminalCardinality` replaces the global
  criterion left in v033 with the exact source dichotomy and closes both
  branches under the direct host counts of sizes ten and two.
  `BoundedRatioNonterminalHostCounts` and
  `BoundedRatioNonterminalRealHosts` disintegrate the shapes exactly according
  to the mobile or two-singleton branch. `BoundedRatioTwoSingletonHosts`
  proves the arithmetic injection, harmonic sum, and Euler product;
  `BoundedRatioTwoSingletonCritical` absorbs the safe global factor \(9B^4\)
  and supplies
  \(N\exp(C_{\rm term}\sqrt B/\log B)\).
  `BoundedRatioNonterminalMobileAssembly` constructs the moderate branch
  under ES and Pell, and `BoundedRatioNonterminalAssembly` chooses
  \(K=(2C_{\rm term}+1)/\log2\) to close 17.28 in full.
- `PaperC.Asymptotics.BoundedRatioTerminalPartnerClosure` constructs the rank
  partner fibers. `BoundedRatioTerminalSummation` uniformly sums first starts
  under Pell, proves the exponents \(3/4\) and \(7/4\), and then transports
  the conclusion exactly to the intrinsic population through the nonaligned
  theorem of 9.10, with no supplied premise. This last sector is therefore no
  longer a dedicated debt of the canonical API.
- `PaperC.Asymptotics.BoundedRatioSteinChen`,
  `BoundedRatioBadStarts`, `BoundedRatioWeightedDefect`, and
  `BoundedRatioSteinChenRates` construct the good and bad starts in
  \([N,M)\), their exact conditional graph, and their uniform cylinder. Lean
  proves the marginal \(2^{-L}\), the conditional parameter and its exact
  correction, and then the uniform bounds
  \(\#D_Y=N^{1/2+o_{C,\kappa_0}(1)}\) and
  \(\sum_{x\in D_Y}\mathbb P(J_x)=o_{C,\kappa_0}(1)\). It also establishes
  \(b_1=o_{C,\kappa_0}(1)\), as well as its specialization to
  \([M/2^j,M)\) for every fixed \(j\).
- `PaperC.Probability.FiniteCylinderCountTransport`,
  `PaperC.Asymptotics.BoundedRatioSteinChenSecondTerm`, and
  `BoundedRatioSteinChenSecondTermCritical` prove exact law transfer between
  cutoffs, the finite total law, the overlap/contact/separation partition of
  the second term, and \(\mathbb E b_2=o_{C,\kappa_0}(1)\). The separated
  branch is bounded by \(R_{2,\kappa}\), the contact branch has the exact
  joint marginal, and edge counting satisfies
  \(E_{Y,U}=o_{C,\kappa_0}(N^2)\).
- `PaperC.Asymptotics.BoundedRatioPoissonAssembly`,
  `BoundedRatioFixedJBadStarts`,
  `PaperC.Probability.BoundedRatioRetainedTransport`, and
  `PaperC.Asymptotics.TheoremSixteenTwo` assemble AGG, the conditional
  mixture, the good/complete coupling, parameter displacement, the mean, and
  exact rounding at the boundary \(M/2^j\). The necessary transport lemmas are
  also integrated into `TheoremSixteenTwo` to avoid an import cycle. They
  close Lemmas 17.34–17.37 and the connection to the retained count with no
  additional internal bridge.
- `PaperC.Asymptotics.TheoremSixteenTwo` constructs on a single cylinder the
  global and retained counts, their laws, their expectations, and their
  Poisson parameters. The coupling estimates, TV triangle, recentering, order
  of limits, asymptotic equivalent of \(\Lambda_M\), and void probability are
  proved in Lean. Marginal compatibility between the global cylinder and each
  local cylinder is now obtained by a product decomposition of the prime
  coordinates, with no hypothesis. The public theorem directly assembles
  Proposition 15.5 and Proposition 16.1, quantified for every \(C'>0\) and
  every \(\kappa_0\ge2\), with a terminal family allowed to depend on these
  parameters; the edge estimate is likewise supplied for every \(C'>0\). The
  direct generic assembly exposes the three `discharged` sector interfaces;
  the three intermediate adapters that supplied them in stages are removed in
  v041. The canonical API constructs the three deep sectors: it no longer
  exposes \(K\), a terminal family, or any Section 17 hypothesis. Only AGG,
  PNT, Laishram--Shorey, Balasubramanian--Shorey, Evertse--Silverman,
  and Nicolas--Robin remain visible. The arithmetic interface of
  9.10 and the aggregate fixed-ratio interface have disappeared from this
  canonical route.
- `PaperC.LinearAlgebra.PrivatePivots` and
  `PaperC.Probability.ConditionalStartProbability` certify Lemma 13.1 and
  Corollary 13.2 in the finite cylinder. Lean splits the coordinates
  \(p\le Y\) and \(p>Y\) exactly, translates the system after arbitrary
  fixation of the small primes, and then uses private pivots to prove
  surjectivity of the large part outside \(D_Y\). Each conditioned fiber
  satisfies
  \[
  \#\mathrm{solutions}\,2^L=\#\mathrm{large\ assignments},
  \]
  and therefore has probability exactly \(2^{-L}\). This equality represents
  conditioning by the uniform law on the remaining cylinder, without relying
  on a measure-theoretic API.
- `PaperC.Combinatorics.GraphCycleRank` and
  `PaperC.Combinatorics.CycleSpaceDimension`: dependencies between edge
  vectors are cyclic, the dimension of the cycle space is bounded by the safe
  truncated form \(|E|-(|V|-|C|)\), and the rank bound of Lemma 14.7 follows
  under an explicit root-connectivity hypothesis.
- `PaperC.Coding.HammingBound`: exact volume of binary balls, disjointness at
  minimum distance, and the Hamming bound, including the codimension form used
  in Section 3 under the actual hypothesis \(\dim C\ge n-r\), together with
  the two inequalities
  \(2^{n-r}\sum_{j\le t}\binom nj\le2^n\) and
  \(\sum_{j\le t}\binom nj\le2^r\) from (3.5).
- `PaperC.Coding.DefectCodeRank`, `DefectCodeRunge`,
  `DefectCodeRepresentation`, `DefectCodeDistance`,
  `DefectCodeProposition`, `RungeDefectApplication`,
  `HammingDefectBound`, and `DefectCodeHamming`: exact rank--nullity for the
  augmented defect matrix, even weight, deduction of complete prime-coordinate
  coverage from \(f=s a^2\), square product, reindexing of a nonzero word into
  \(d=2k\ge2\) Runge data, minimum distance, complete connection to (3.5), and
  the finite bound \(m<2t\,2^{(r+1)/t+1}\). The single terminal comparison
  \((128(2t)R)^{4t}<U\) excludes all short words.
- `PaperC.Arithmetic.PrimesUpTo`, `PrimeCountBridge`, and
  `ChebyshevPrimeCount`: canonical increasing enumeration of primes \(p\le H\),
  identification with the arithmetic finset, and the elementary bound
  \(\lfloor\log_2H\rfloor\pi(H)\le7H\), with no prime number theorem.
- `PaperC.Arithmetic.DefectCounting`, `WeightedDefectCounting`, and
  `DefectivePredicate`: for \(n>0\), equivalence between \(K_H(n)=1\) and a
  representation \(n=s a^2\) with prime support \(\le H\), followed by coarse
  and weighted counts, including
  \[
  \#\mathcal D_H^+(X)\le
  \sqrt X\prod_{p\le H}(1+p^{-1/2}).
  \]
- `PaperC.Analysis.RungeLogarithmicGrowth`, `ReciprocalSqrtSum`,
  `SmoothEulerProduct`, `DefectGlobalBound`, and `WeightedDefectMass`, together
  with `PaperC.Coding.CanonicalDefectCode`, `IntervalDefectBound`, and
  `PaperC.Combinatorics.IntervalDefectAggregation`: integer radius through a
  logarithmic floor, concrete connection of the code to the defects of an
  interval, Euler product \(\le e^{2\sqrt H}\), double counting of intervals,
  and the assembled uniform finite upper bound preceding (3.4).
- `PaperC.Analysis.CriticalWindowParameters`, `CriticalWindowScale`,
  `DefectPointwiseRate`, `CriticalWeightedDefect`, and
  `CriticalPointwiseIntervals`: complete closure of Proposition 3.2. The
  radius and its budget are uniformly valid under
  \(c_1\log N\le H\le c_2\log N\); every admissible interval has
  \(O_{c_1,c_2}(\log N/\log\log N)\) defects; and the mass in (3.4) satisfies
  the quantified formulation of \(N^{1/2+o(1)}\).
- `PaperC.Asymptotics.ExpSqrtLog`, `CappedRadiusDyadic`, `HalfPower`, and
  `LinearPower`: uniform envelopes for \(e^{C\sqrt{\log N}}\), \(H+1\), the
  dyadic Hamming factor, and their products; kernel-checked definitions of
  \(N^{1/2+o(1)}\), \(N^{-1/2+o(1)}\), and \(N^{1+o(1)}\).
- `PaperC.Combinatorics.RungeCoefficients` and
  `PaperC.Analysis.RungePowerSeries`: formal binomial expansion of
  \(\prod_\nu(1+\gamma_\nu X)^{1/2}\), exact identification of its
  coefficient \(c_m\) with the sum over weak compositions, integrality of
  \(2^dc_m\) for \(2m\le d\), the upper bound
  \(\lvert c_m\rvert\le(8R)^d\) in the useful range, and the formal identity
  \(F(X)^2=\prod_\nu(1+\gamma_\nu X)\).
- The modules `RungeAnalyticProduct`, `RungeTailEstimate`, `RungeScaling`,
  `RungeEstimate`, `RungeTruncationBounds`, `RungeQPolynomial`,
  `RungeEquality`, `RungeNonEquality`, and `RungeBound`, together with the
  preceding coefficient, translation, and dyadic-separation modules,
  **certify Lemma 3.1 in full**. Lean verifies convergence of the series
  product, the positive branch, (3.3), the dyadic and polynomial branches,
  \(\deg Q\le k-1\), the height of \(Q\), and then
  \[
  U\le(128\,dR)^{2d}\qquad(d=2k\ge2).
  \]
  The manuscript's existential absolute constant is therefore instantiated as
  \(C_0=128\).
- `PaperC.Runs.Starts`: exact additive definition of a start and
  incompatibility of two overlapping starts (Lemma 3.4(i)).
- `PaperC.Affine.TouchingSystem`, `TouchingDefectRank`,
  `PaperC.Combinatorics.TouchingPairs`, `PaperC.Analysis.TouchingMass`,
  `TouchingWindow`, and `CriticalTouchingPairs`: affine system of two starts
  at distance \(L\), injective boundary of their joint tree with \(2L\) edges,
  a bound on the rank defect by the defects in \([x,x+2L]\), counting of both
  orientations, and a complete proof of Lemma 3.4(ii) under
  \(\lvert L-\log_2N\rvert\le C\):
  \[
  \sum_{\substack{x,y\in I_N\\|x-y|=L}}
    (2^{\rho(x,y)}-1)\le N^{1+o_C(1)}
  \]
  in the quantified uniform sense.
- `PaperC.Model.FiniteRademacher`: finite cylindrical model of the random
  completely multiplicative function and dyadic counting variable.
- `PaperC.Affine.StartSystem`: identification of a start with the affine
  system of Section 2.
- `PaperC.Probability.StartProbability`: exact connection between the
  cylindrical probability of a start and the count of its affine fiber.
- `PaperC.Probability.TouchingProbability`: exact cylindrical probability of
  two touching starts, normalization \(\eta2^\rho/2^{2L}\), and absolute
  bound by \((2^m-1)/2^{2L}\) under \(\rho\le m\).
- `PaperC.Probability.FactorialMoment` and
  `PaperC.Probability.FiniteExpectation`: algebraic identity for the second
  factorial moment, followed by an exact proof of
  \(\mathbb E Z_{N,L}=\sum_x\mathbb P(J_{x,L})\) in the finite cylinder.
- `PaperC.Affine.StartDefectRank`,
  `PaperC.Probability.DefectFirstMoment`, `CriticalFirstMoment`, and
  `CriticalRunWindow`: injection of start-tree relations into defective
  vertices, the finite first-moment formula, followed by a proof of Corollary
  3.3 in its literal window \(\lvert L-\log_2N\rvert\le C\), with error
  \(N^{-1/2+o_C(1)}\).
- `PaperC.Probability.FinitePMF`: finite core of total variation.
- `PaperC.Asymptotics.Uniform`: explicit quantifiers for uniform asymptotic
  notation.
- `PaperC.Affine.TwoStartSystem`,
  `PaperC.Affine.RelationalPrimeAssignment`,
  `PaperC.Arithmetic.LargeOddKernel`,
  `PaperC.Combinatorics.LargeKernelAssignments`, and
  `PaperC.Combinatorics.RelationalHosts`: affine system of two starts,
  canonical selection of a nonzero occurrence, unique assignment of each
  prime \(p>L+1\) with odd valuation to an occurrence in the opposite block,
  and then CRT grouping of starts by assignment. Lean obtains exactly
  \[
  H_2(N,L)\le
  8(L+1)N\sum_{1\le n\le3N}
  \frac{(L+1)^{\omega(K_{L+1}(n))}}{K_{L+1}(n)}.
  \]
- `PaperC.Arithmetic.LargeKernelWeightedCounting`,
  `PaperC.Analysis.ReciprocalThreeHalvesTail`,
  `PaperC.Analysis.LargeEulerProduct`,
  `PaperC.Analysis.RelationalHostBound`, and
  `PaperC.Asymptotics.ThreeHalvesPower`,
  `PaperC.Asymptotics.RelationalHostsThreeHalves`: canonical decomposition
  \(n=a^2ur\), upper bounds for the two Euler products without the prime
  number theorem, and closure of the finite bound
  \[
  H_2(N,L)\le
  8(L+1)N\sqrt{3N}\,e^{4\sqrt{L+1}}.
  \]
  Under \(L+1\le C\log N\), this upper bound gives the quantified uniform
  formulation \(H_2(N,L)\le N^{3/2+o_C(1)}\), which Lean then transports to
  the literal window \(\lvert L-\log_2N\rvert\le C\), certifying Lemma 4.2.
- `PaperC.Analysis.RelationalInterpolation`: finite Cauchy--Schwarz on an
  arbitrary subset of relational hosts, with separate upper bounds for their
  cardinality and the sum of squares. The exponent calculation in (4.3) is
  also verified explicitly: \(N^{3/2+\varepsilon}\) and
  \(N^{5/2-\delta+\varepsilon}\) give
  \(N^{2-\delta/2+\varepsilon}\). Its eventual uniform version certifies
  Lemma 4.3.

The detailed correspondence table between the manuscript and Lean is in
[`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md). Logical-dependency
checking is performed by [`AuditCheck.lean`](AuditCheck.lean), whose exhaustive
and stable list is also provided in
[`audit_manifest.json`](audit_manifest.json). The human-readable report
remains recorded in [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md).

`#print axioms` does not detect ordinary hypotheses passed as arguments. Here,
"unconditional" means only "depends on no registered bridge." The registry
distinguishes:

- `external`: a published result verifiable against its source, such as
  Evertse--Silverman;
- `internal`: an argument originating in the manuscript's proof, such as
  generalized Pell or an assembly connection;
- `open`: a bridge still required by at least one relevant canonical API;
- `discharged`: a retained and verifiable historical interface whose
  conclusion has now been reconstructed in Lean from further-upstream inputs.

Thus `kind` describes provenance, while only `status: open` signals remaining
debt. The inventory, status, and theorem-by-theorem propagation of each bridge
appear in `audit_manifest.json` and `AXIOM_AUDIT.md`. The manifest also carries
the two edition digests—`target_pdf` for the English submission edition and
`source_pdf_fr` for the synchronized French source—together with the sourced
transcription of each statement.

## Why the probabilistic model is finite first

For a window contained in \([1,M]\), all events under consideration depend
only on the signs of primes \(p\le M\). The repository therefore works first
on the finite space

\[
\Omega_M=\{0,1\}^{\{p\le M:p\ {\rm prime}\}},
\]

equipped with the uniform law. Extensionally, this representation is the
cylindrical restriction of the infinite product, but it avoids introducing
infinite products and conditional expectation before they are needed.

The cutoff `dyadicCutoff N L = 2*N + L` covers all windows whose start belongs
to `dyadicBlock N`. The generic function `startProbability N L x` remains
defined outside this block, but there it denotes only the probability in this
truncated cylinder; no identification with the infinite model is claimed
outside the covered zone.

## Building

The project pins Lean `v4.32.2` and mathlib `v4.32.2`. The `lean-toolchain`
file, `lakefile.toml`, and the Lake manifest lock this toolchain for v0.48.1;
the pins are unchanged from v0.48.0.
The v0.48.1 conductor construction changes the audited Lean source digest,
public declaration inventory, conditionality map, and main Comparator
signature. Exact counts and hashes must therefore be taken from the regenerated
`audit_manifest.json`, `AXIOM_AUDIT.md`, and release binding after the source
commit is frozen; the v0.48.0 totals are historical and must not be reused to
qualify this candidate.

The exact source pins used by the v0.48.0 compatibility work are:

| Component | Version or commit |
|---|---|
| Lean | `v4.32.2`, commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c` |
| Mathlib | `v4.32.2`, commit `905b95818eb32af7874a58b427f50c1711a5e96c` |
| Comparator | `51491237b1d2f96cca203af9c34bced6fe38e0d8` |
| lean4export | `af5aa64bb914c3c2c781f378088dbd38acf4f804` |
| landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |
| formalization.yaml v0.3 template | `fab03cbbed1a5857de17af32de30421a734c77c6` |

There is no official Comparator/lean4export `v4.32.2` tag.  The exact commits
above therefore replace a nonexistent version tag.  In particular, the
Comparator binary and the standalone lean4export binary must both be built
from their pinned sources with the Paper C Lean `v4.32.2` toolchain; do not
silently build Comparator with the newer toolchain named by its source
checkout.  These are source
pins, not evidence of a hardened execution; the actual smoke-test and
publication status is stated above.

### Ordinary build and generated metadata

Fetch the Mathlib cache once when needed.  The ordinary development and CI
job may compile both sides explicitly:

```bash
lake exe cache get
node scripts/generate_audit.mjs --check-pdfs
node scripts/generate_audit.mjs --check-source-digest
node scripts/generate_audit.mjs --check-literature-certificates
rg -n '(^|[[:space:]])(sorry|axiom|admit|native_decide|unsafe|partial)([[:space:]]|$)' --glob '*.lean' PaperC.lean PaperC
node scripts/check_comparator_sources.mjs
node scripts/test_audit_root_guards.mjs
lake build PaperC
lake env lean Challenge.lean
lake env lean ChallengeTransfer.lean
lake env lean Solution.lean
lake env lean SolutionTransfer.lean
node scripts/generate_audit.mjs --check
mkdir -p ci-logs
lake env lean AuditCheck.lean 2>&1 | tee ci-logs/AuditCheck.log
node scripts/verify_audit.mjs --input ci-logs/AuditCheck.log
node scripts/generate_audit.mjs --check
```

When this sequence is run in a tracked checkout, the following additional
check confirms that regeneration introduced no tracked change:

```bash
git diff --exit-code -- AuditCheck.lean audit_manifest.json formalization.yaml AXIOM_AUDIT.md
```

Do not run that Git command when validating an extracted release ZIP: an
archive has no repository history.  In that case the preceding
`node scripts/generate_audit.mjs --check` is the authoritative deterministic
comparison against the generated files shipped in the archive.

The PDF check hashes the actual bytes of both repository PDFs and fails if
either file is absent or differs from `audit_config.json`. The source-digest
check covers the exact native-filesystem set recorded as
`core_source_fileset: ["PaperC.lean", "PaperC/**/*.lean"]`, independently of
the Comparator fileset. The literature-certificate check independently binds
the three active source certificates and the historical Halter--Koch closure
note, distinguishes open obligations from that discharged boundary, and
records the aggregate digest of all four documentary files. The hygiene scan,
`check_comparator_sources.mjs`, and isolated root
guards then establish the core token policy, the
Challenge/Solution structural boundary, and that changing `PaperC.lean`
invalidates the digest
and that adding a public theorem there adds both an inventory record and its
generated `#print axioms` command.  The interface checks require Mathlib-only
imports and exactly one final placeholder in each Challenge, reject every
forbidden token in both Solution files and any solution-side support module,
and compile the four modules separately.  Only then are the shipped generated
artifacts checked and the exhaustive audit executed. `AuditCheck.lean` imports
`PaperC`, so the root module itself is
loaded; the single logged run executes `#print axioms` for every public theorem
or lemma and for the two historical public proof-carrying constructions.
`verify_audit.mjs` reads its preserved log, requires one output for every
manifest target, and rejects anything outside the foundational allowlist. The
final `--check` hashes both PDFs again and verifies that `AuditCheck.lean`,
`audit_manifest.json`, `formalization.yaml`, and the generated registry in
`AXIOM_AUDIT.md` are exactly current.  Schema-5 `audit_config.json` is the sole
input for the editorial item map; generation checks names, declaring files,
bridge identifiers, conditionality, the theorem names listed by each
Comparator configuration, and the immutable source-snapshot/packaging-evidence
boundary. The public workflow implementing this sequence is
`.github/workflows/reproducibility.yml`; it archives `AuditCheck.log` as a CI
artifact. The generator's source enumeration is independent of `rg`; the
workflow nevertheless installs `ripgrep` explicitly before the separate
root-inclusive hygiene scan.

The workflow's two-entry Comparator matrix runs in separate clean checkouts.
On the current hosted runner, pushes and pull requests use the explicitly
non-certifying smoke test when real landrun, a usable user systemd manager, or
an approved transport for Comparator's prescribed `--pty` wrapper is absent.
After an actual hosted run attached both Comparator targets without producing
their first startup marker, the workflow conservatively treats captured
non-TTY stdio as insufficient evidence that this transport is usable.  This
is a fail-closed CI policy, not a claim that `systemd-run --pty` intrinsically
requires pre-existing terminal file descriptors.  A manual
`workflow_dispatch` with `require_hardened: true` disables the fallback and is
therefore expected to fail on the current hosted transport; the release gate
remains the hardened local procedure below.  Each Comparator execution step
is capped at 60 minutes, and each successful matrix entry assembles one atomic
transcript and one `result-*.json`.  The script
`scripts/assemble_comparator_evidence.mjs` rejects stale hashes, dirty
checkouts, pre-existing `.olean` files, root execution, `LD_PRELOAD`, missing
Lean-kernel acceptance markers, or an inaccurate sandbox/nanoda claim.

This ordinary build is not a Comparator certificate.  In particular, it
compiles the solution wrappers in the same working tree and is therefore
incompatible with Comparator's clean-checkout trust assumption.

### Building the pinned Comparator tools

The following one-time setup uses independent tool checkouts.  It requires
Git, Elan/Lake, Go 1.24 or later, and a Linux host for real landrun.  The
Comparator and lean4export are both built with Paper C's exact `v4.32.2`
toolchain.  Comparator's source checkout names `v4.33.0-rc1`, but that is not
the compatibility combination tested for this release.

```bash
PAPER_C_TOOLS="$(realpath ../paper-c-v048-tools)"
mkdir -p "$PAPER_C_TOOLS/bin"

git clone https://github.com/leanprover/comparator.git "$PAPER_C_TOOLS/comparator"
git -C "$PAPER_C_TOOLS/comparator" checkout 51491237b1d2f96cca203af9c34bced6fe38e0d8
(cd "$PAPER_C_TOOLS/comparator" && \
  ELAN_TOOLCHAIN=leanprover/lean4:v4.32.2 lake build comparator)

git clone https://github.com/leanprover/lean4export.git "$PAPER_C_TOOLS/lean4export-4.32.2"
git -C "$PAPER_C_TOOLS/lean4export-4.32.2" checkout af5aa64bb914c3c2c781f378088dbd38acf4f804
(cd "$PAPER_C_TOOLS/lean4export-4.32.2" && \
  ELAN_TOOLCHAIN=leanprover/lean4:v4.32.2 lake build lean4export)

git clone https://github.com/Zouuup/landrun.git "$PAPER_C_TOOLS/landrun"
git -C "$PAPER_C_TOOLS/landrun" checkout 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
(cd "$PAPER_C_TOOLS/landrun" && \
  go build -trimpath -o "$PAPER_C_TOOLS/bin/landrun" cmd/landrun/main.go)

git clone https://github.com/mathlib-initiative/formalization.yaml.git \
  "$PAPER_C_TOOLS/formalization-yaml"
git -C "$PAPER_C_TOOLS/formalization-yaml" checkout fab03cbbed1a5857de17af32de30421a734c77c6
```

For each Paper C Comparator run intended as publication evidence, save the
exact identities and machine-dependent binary hashes in the same transcript
as the command output.  The hardened recipe below does this atomically.  The
following commands list the required tool fields for an exploratory run:

```bash
git -C "$PAPER_C_TOOLS/comparator" rev-parse HEAD
git -C "$PAPER_C_TOOLS/lean4export-4.32.2" rev-parse HEAD
git -C "$PAPER_C_TOOLS/landrun" rev-parse HEAD
git -C "$PAPER_C_TOOLS/formalization-yaml" rev-parse HEAD
lean --version
lake env lean --version
sha256sum \
  "$PAPER_C_TOOLS/comparator/.lake/build/bin/comparator" \
  "$PAPER_C_TOOLS/comparator/scripts/fake-landrun.sh" \
  "$PAPER_C_TOOLS/lean4export-4.32.2/.lake/build/bin/lean4export" \
  "$PAPER_C_TOOLS/bin/landrun"
```

This requirement is specific to the two project runs.  It is not a blanket
claim that every historical transcript in `comparator/transcripts/` contains
all of these fields: in particular, the earlier upstream compatibility probe
is a narrower tool-suite log and is not publication evidence for Paper C.

### Unsandboxed development smoke test

Comparator's own `scripts/fake-landrun.sh` is useful for compatibility
development on a disposable checkout.  It deliberately performs no sandboxing.
This command is therefore an **unsandboxed Comparator semantic smoke test**,
never the hardened publication evidence:

```bash
PAPER_C_TOOLS="$(realpath ../paper-c-v048-tools)"
COMPARATOR_LANDRUN="$(realpath "$PAPER_C_TOOLS/comparator/scripts/fake-landrun.sh")" \
COMPARATOR_LEAN4EXPORT="$(realpath "$PAPER_C_TOOLS/lean4export-4.32.2/.lake/build/bin/lean4export")" \
lake env "$(realpath "$PAPER_C_TOOLS/comparator/.lake/build/bin/comparator")" \
  comparator/theorem_one_one.json
```

The transfer smoke test substitutes
`comparator/theorem_one_one_transfer.json`.  Both commands have actually
completed in separate clean checkouts with Lean default-kernel acceptance and
exit status 0.  They were run as `root` with fake-landrun and an `LD_PRELOAD`
compatibility shim, so they show only toolchain and semantic compatibility;
they do not establish sandbox isolation or non-privileged execution.  The
recorded transcripts are
`comparator/transcripts/theorem_one_one_unsandboxed.txt` and
`comparator/transcripts/theorem_one_one_transfer_unsandboxed.txt`; their
historical SHA-256 values are recorded in the rc1 changelog entry.

### Hardened local Comparator procedure

The supported reference hosts are stock Ubuntu 24.04 LTS and 26.04 LTS on
`x86_64` or `arm64`.  Ubuntu 22.04's stock kernel and Node.js are too old for
this release gate.  The runner requires Linux 6.2 or newer so that Landlock
can mediate truncation as well as file creation, and Node.js 18 or newer.

Install the Ubuntu prerequisites once:

```bash
sudo apt update
sudo apt install --yes \
  bash bsdutils build-essential ca-certificates coreutils curl \
  dbus-user-session findutils git grep nodejs sed systemd tar util-linux zstd
```

Install the official per-user Elan distribution if `$HOME/.elan/bin/elan`
does not already exist, then load it in the current shell:

```bash
curl --proto '=https' --tlsv1.2 -sSf \
  https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
source "$HOME/.elan/env"
```

After installing `dbus-user-session`, log out and back in if
`systemctl --user show-environment` cannot contact the user manager.  Do not
run the verifier with `sudo`.  Go does not need to be installed: the runner
downloads Go 1.24.13 for the current architecture and checks its official
SHA-256 before use.  The pinned Lean toolchain may already be installed: the
runner uses Elan's idempotent `run --install` interface, which reuses it when
present and installs it only when absent.  A separate invocation then parses
the single-line Lean version record and requires the exact pinned commit
before continuing.

Update to the exact commit to be certified and require a completely clean
checkout, including no untracked files.  Run the preflight first, then the
full verifier from an interactive terminal.  The outer stock `setpriv` wrapper
removes the `CAP_WAKE_ALARM` capability that `pam_systemd` may place in the
calling Ubuntu session; the clean `PATH` prevents user-installed commands from
shadowing the audited Ubuntu and Elan binaries:

```bash
git status --short
unset LD_LIBRARY_PATH
PATH="/usr/bin:/bin:$HOME/.elan/bin" \
  /usr/bin/setpriv --inh-caps=-all --ambient-caps=-all --no-new-privs -- \
  ./scripts/run_hardened_comparator.sh --preflight-only
PATH="/usr/bin:/bin:$HOME/.elan/bin" \
  /usr/bin/setpriv --inh-caps=-all --ambient-caps=-all --no-new-privs -- \
  ./scripts/run_hardened_comparator.sh
```

The first command must print nothing.  A `tmux` terminal is acceptable, but a
pipe, `nohup`, an IDE task runner, a container, and redirected standard file
descriptors are rejected.  The full run builds the three pinned tools, creates
one fresh Paper C checkout immediately before each target, fetches only the
trusted dependency cache, and runs both targets through the pinned real
landrun inside the Comparator README's `systemd-run --user --pty` wrapper.
Before each target it tests that real landrun refuses file creation,
truncation, removal, and rename under the exact read-only-root policy.
Ubuntu 26.04 may implement `/usr/bin/sha256sum`, `touch`, and `truncate` as
root-owned links into its stock Rust coreutils provider and `rm` or `mv` as
links to GNU-prefixed binaries.  The runner accepts those provider layouts
only through the fixed `/usr/bin` invocation paths, validates the resolved
targets as root-owned and non-writable by group/others, and records them in
the evidence.  Their canonical parent directories receive the same ownership
and write-permission checks.  Since `systemd --user` is an independent manager
and may retain `CAP_WAKE_ALARM` even after the calling shell is cleaned, the
runner also audits and fingerprints `/usr/bin/setpriv` and invokes it inside
each of the four transient payloads.  The systemd `NoNewPrivileges=yes`
property remains mandatory.  The launcher and every transient Comparator unit
must report zero inheritable/permitted/effective/ambient capabilities and
`NoNewPrivs=1`; the evidence validator requires both transient markers and the
recorded inner capability-drop method.  A failed initial systemd probe prints
a bounded diagnostic transcript before stopping.

Systemd 259 decorates the first interactive PTY payload byte with an OSC window
title by default.  The runner rejects inherited
`SYSTEMD_ADJUST_TERMINAL_TITLE` values in both the caller and user-manager
environments, sets the documented value `0` before every PTY `systemd-run`, and
records that setting in hardened evidence.  Security markers therefore remain
exact lines; the verifier does not weaken them by stripping arbitrary terminal
control sequences.  The inexpensive preflight now verifies this exact-line
property before any tool download or build.

Raw PTY marker checks operate directly on the transcript file and accept only
an exact record with one optional terminal CR.  They deliberately use neither a
permissive terminal-control filter nor an early-exit `grep -q` pipeline: with
`pipefail`, the latter can turn a valid early match in a long transcript into a
producer `SIGPIPE` failure.

The Comparator phase may be quiet for a while: its raw pseudo-terminal stream
is written to evidence files instead of being replayed to the invoking
terminal.  This prevents an untrusted Solution from injecting terminal control
sequences.  Failures preserve the diagnostic directory and never create a
`SUCCESS` marker.  Only after both result JSON files pass
`scripts/assemble_comparator_evidence.mjs` validation does the runner create:

- an evidence directory ending in the certified commit and UTC timestamp;
- a sibling private raw `.tar.zst` bundle that **must not be uploaded**;
- a sibling checksum for that private raw bundle.

Publication requires the separate, omission-only derivation and independent
verification described in `scripts/PUBLIC_COMPARATOR_ARCHIVE.md`. Only its
`paper-c-hardened-public-<full-commit>.tar.zst` output is a publication asset.

Preserved `*.partial` directories and temporary work trees are forensic
diagnostics only: do not rename, promote, or reuse them.  Evidence production
after any failure requires a complete new run from a clean committed `HEAD`.

The final summary is a sandboxed, non-root Comparator result accepted by the
Lean default kernel.  It is deliberately not described as a dual-kernel
result: both configurations keep `enable_nanoda: false`.  The trusted
computing base still includes the recorded Ubuntu/systemd binaries, pinned
Comparator/lean4export/landrun sources, Lean, and the downloaded Mathlib OLean
cache.  The operational probes document the tested restrictions; they are not
a general certification of every host-security property.

<details>
<summary>Obsolete manual sketch retained for historical comparison</summary>

Do not use the following inline sketch for release evidence.  It predates the
atomic two-target runner, its complete negative-control suite, safe PTY
capture, and machine-readable final validation.

```bash
PAPER_C_TOOLS="$(realpath ../paper-c-v048-tools)"
export COMPARATOR_BIN="$(realpath "$PAPER_C_TOOLS/comparator/.lake/build/bin/comparator")"
export COMPARATOR_LANDRUN="$(realpath "$PAPER_C_TOOLS/bin/landrun")"
export COMPARATOR_LEAN4EXPORT="$(realpath "$PAPER_C_TOOLS/lean4export-4.32.2/.lake/build/bin/lean4export")"
CONFIG=comparator/theorem_one_one.json
LOG="$(cd .. && pwd)/comparator-theorem-one-one-hardened.log"

(
  set -o pipefail
  {
    set -eu
    trap 'final_status=$?; echo "exit_code=$final_status"' EXIT
    echo "timestamp_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "mode=hardened-procedure-candidate"
    echo "uid=$(id -u)"
    test "$(id -u)" -ne 0
    echo "repository_commit=$(git rev-parse HEAD)"
    tracked_dirty="$(git status --porcelain --untracked-files=no)"
    if [ -n "$tracked_dirty" ]; then
      echo 'tracked_dirty=FAILED'
      printf '%s\n' "$tracked_dirty"
      exit 88
    fi
    echo 'tracked_dirty_count=0'
    echo "lean_toolchain=$(tr -d '\r\n' < lean-toolchain)"
    echo "mathlib_version=$(git -C .lake/packages/mathlib describe --tags --exact-match)"
    echo "mathlib_commit=$(git -C .lake/packages/mathlib rev-parse HEAD)"
    echo "config=$CONFIG"
    sha256sum "$CONFIG"
    lake env lean --version
    "$COMPARATOR_LANDRUN" --version
    systemd-run --version | sed -n '1p'
    echo "comparator_commit=$(git -C "$PAPER_C_TOOLS/comparator" rev-parse HEAD)"
    echo "lean4export_commit=$(git -C "$PAPER_C_TOOLS/lean4export-4.32.2" rev-parse HEAD)"
    echo "landrun_commit=$(git -C "$PAPER_C_TOOLS/landrun" rev-parse HEAD)"
    sha256sum \
      "$COMPARATOR_BIN" \
      "$COMPARATOR_LEAN4EXPORT" \
      "$COMPARATOR_LANDRUN"

    project_oleans="$(find . -path './.lake/packages' -prune -o \
      -type f -name '*.olean' -print)"
    if [ -n "$project_oleans" ]; then
      echo 'preexisting_project_oleans=FAILED'
      printf '%s\n' "$project_oleans"
      exit 89
    fi
    echo 'preexisting_project_olean_count=0'

    write_probe="$(pwd)/.landrun-write-must-fail"
    rm -f "$write_probe"
    echo 'landrun_negative_control=running'
    if "$COMPARATOR_LANDRUN" \
      --best-effort --ro / --rw /dev -ldd -add-exec -- \
      /usr/bin/touch "$write_probe"; then
      echo 'landrun_negative_control=FAILED_write_returned_success'
      exit 90
    elif [ -e "$write_probe" ]; then
      echo 'landrun_negative_control=FAILED_file_was_created'
      exit 91
    fi
    echo 'landrun_negative_control=passed_write_refused'

    RUN=(
      systemd-run '--property=RestrictAddressFamilies=~AF_UNIX' --user --pty
      -E "PATH=$PATH"
      -E "COMPARATOR_BIN=$COMPARATOR_BIN"
      -E "COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN"
      -E "COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT"
      -E "CONFIG=$CONFIG"
      --working-directory="$(pwd)" --
      bash -c 'lake env "$COMPARATOR_BIN" "$CONFIG"'
    )
    printf 'command='
    printf ' %q' "${RUN[@]}"
    printf '\n'
    set +e
    "${RUN[@]}"
    status=$?
    set -e
    exit "$status"
  } 2>&1 | tee "$LOG"
  exit "${PIPESTATUS[0]}"
)
```

</details>

The automated runner always executes the main finite-cylinder and independent
infinite-to-finite transfer configurations. Do not infer transfer coverage
from the main result alone. A hardened reference run succeeded for the
v0.48.0 configurations at Paper C commit `27c91f8bdd5c...`. The v0.48.1
snapshot changes the main configuration to three premises, so that historical
run is not evidence for it. The runner remains the reproduction procedure;
the result for v0.48.1 is read only from a validated packaging layer bound to
the exact source snapshot, never from a temporal claim in source metadata.

The axiom audit does not detect ordinary hypotheses. Their inventory is the
bridge registry in `audit_manifest.json` and `AXIOM_AUDIT.md`: each entry has
`kind: external | internal` and `status: open | discharged`, and each
conditional public theorem is marked with the exact list and kind of bridges
it takes as direct premises. In v0.48.0, the interfaces for 9.10, 9.2, 17.26,
17.28, and 17.30, as well as the former Nicolas--Robin envelope, have
`status: discharged`. `kind: internal` describes provenance and therefore does
not by itself mean that debt remains open. All five `internal` interfaces are
`discharged`; all seven `open` entries are `external`. The v0.48.0 manifest's
declaration, audit-target, and conditionality counts are reproduced in
`REPRODUCIBILITY.md`.

The generator parser also covers the format in which `theorem` or `lemma`
appears alone on one line and the name begins on the next. This correction
reinstates six declarations, including three historical ones, that the former
parser did not inventory.

## What still blocks complete certification

External results are isolated from internal debt. Eight external interfaces
are registered: six remain open. The historical Halter--Koch interface and the
former specialized Nicolas--Robin envelope are retained as discharged
compatibility interfaces.

- Evertse–Silverman (Lemma 9.1), whose exact conditional interface is
  formalized;
- Arratia–Goldstein–Gordon / Chen–Stein (Theorem 13.7), now represented by an
  exact finite interface;
- the prime number theorem, in its source form \(\pi(t)\log t/t\to1\), used in
  Lemma 15.1;
- Corollary 1 of Laishram–Shorey, used in Lemma 15.2;
- Theorem 1 of Balasubramanian–Shorey, used in Lemma 15.4;
- the Nicolas–Robin theorem on the divisor function, in the direct logarithmic
  form used by `PellDivisorEnvelope`;

The two discharged external compatibility interfaces are:

- `HK13-QO-conductor-fibres`, now proved internally by the quadratic-field,
  modulo-two residue construction;
- the former Nicolas--Robin eventual specialization to polynomially bounded
  parameters in 9.2, discharged by `PellDivisorEnvelope`.

The five `internal` interfaces correspond to Pell, 9.10, 17.26, 17.28, and
17.30; all are `discharged` and retained for traceability. The former P9.9,
P9.11, T10.1, and C11.3 interfaces were removed with their generic public
endpoints. Thus no `internal/open` bridge remains. The phrase "unconditional
modulo the literature" describes the boundary of the canonical endpoints
exactly: it consists solely of the six external results that remain open.

Lemma 17.26 now assembles its signed-divisor and Evertse--Silverman sums;
Lemma 17.28 assembles the mobile-host and two-singleton counts and chooses
\(K\) itself; Lemma 17.30 was already closed under Pell and now uses the Lean
theorem for 9.10 with no additional hypothesis. Canonical Theorems 16.1 and
16.2 therefore take no internal bridge. The marginal identity between two
finite cutoffs, the bad-start bounds, \(b_1\), \(b_2\), the mixture, coupling,
mean, and boundary rounding are also discharged. The former
`BoundedRangePoissonApproximation` interface is no longer registered. The
direct generic Theorem 16.2 retains the three `discharged` sector premises,
but its intermediate adapters have been removed. Its principal canonical
variant no longer receives a threshold \(K\), a terminal family, or a Section
17 premise.

The quantitative Runge lemma, Proposition 3.2, Corollary 3.3, both parts of
Lemma 3.4, Lemmas 4.2--4.3, Lemmas 5.1--5.2 and 5.5, Proposition 5.4, and
Lemmas 6.1 and 6.4--6.5 are now fully certified in the finite model under their
explicit hypotheses. The square-class conclusion of Lemma 6.2 and Lemma 6.3,
including disjointness of occurrence pairs and distinction of components
associated with distinct units, are also certified. This includes uniform
closure of the critical-window thresholds, the quantifiers replacing
\(O_{c_1,c_2}\), \(N^{1/2+o(1)}\), and \(N^{-1/2+o_C(1)}\), and the ranks of
the start tree and double touching tree. Lemmas 7.1 and 7.2 and Propositions
7.3, 7.4, and 7.5 are now certified in their effective finite formulations,
with explicit constants. For Proposition 7.5, Lean retains the literal
population \(P^\#>N\), outside small height, with \(16c^\#\le3(L+1)\), and
then proves \(Q_{\rm res}\le N^{19/8+o_C(1)}\) and
\(R_{\rm res}\le N^{31/16+o_C(1)}=o_C(N^2)\). The exact partition of Sectors
7.3--7.5 and the remaining deep core is also certified. Outstanding work
notably includes generalizing the literal \(\alpha=3/16\) instance of Theorem
8.1 to an arbitrary positive parameter. The internal Pell proof is discharged;
only the Nicolas--Robin literature input remains explicit, while the conductor
comparison is proved in Lean.
The former arbitrary public routes through 9.9–11.3 and §12 were removed in
v041; their finite cores remain in the modules, while the canonical mother
mass is supplied by the \(κ\)-proofs. Lemmas 13.3–13.5, the terms in Lemma
13.8, and the complete Boolean connection to the AGG interface are now
certified. The qualitative conclusion of Corollary 13.9 follows from the
quantitative canonical endpoint, rather than from a second legacy public
route. Corollary 13.10 assembles the edge term at the terminal cutoff, the
quantitative Chen–Stein terms, and the total variation triangle to give the
uniform rate \(O((\log\log N)^{-2})\). This conclusion is the conditional
quantitative form of Theorem 1.1 in the finite cylinder. Its canonical entry
uses AGG, Evertse--Silverman, and the Nicolas--Robin logarithmic inequality.
The \(o_C(N^2)\) in 13.6 is certified at the literal cutoff.
Proposition 14.1 is closed in the manuscript's log-log window, and canonical
Proposition 14.2 now uses AGG and the quantitative \(κ\) mother mass, with no
internal bridge. The Laplace identities, their Riemann limits, the marked
Chen–Stein calculation, and §14 detruncation are assembled. Lemma 15.1 has
its complete finite core, and its conclusion now depends only on the external
PNT bridge: the former internal gap debt has been discharged.

Version 8 retains Corollary 11.3, which explicitly states the
quantitative version required for the rate in Corollary 13.10:

\[
R_2(N,L)\ll_C N^2
\exp\!\left(-c_R\frac{\sqrt{\log N}}{\log\log N}\right),
\qquad c_R=c_R(A,C)>0.
\]

Version 045 now exposes this formula itself as
`PaperC.DyadicKappaQuantitative.corollary_eleven_three_canonical`. The theorem
chooses \(c_R>0\), transports every polynomial-saving sector to the common
exponential scale, adds the nonterminal exponential sector, and specializes
the bounded-ratio mother mass back to the literal \(R_2\). The harmonic
consequence continues to feed `PaperC.Asymptotics.CorollaryThirteenTen`.

## Recommended next steps

1. Generalize the existing rational encoding to the literal statement of
   Theorem 8.1 for every real \(\alpha>0\).
2. If a stable mathlib API becomes available, transport the already proved
   Laplace characterizations to an equivalent formulation in vague convergence
   of point measures.
