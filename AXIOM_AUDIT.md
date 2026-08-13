# Audit logique

## Source canonique depuis la v019

L'audit machine canonique est désormais `AuditCheck.lean`. Il est engendré
directement depuis les déclarations publiques des sources, et non depuis les
listes Markdown :

```bash
node scripts/generate_audit.mjs --check
lake env lean AuditCheck.lean
```

`audit_manifest.json` contient la même liste triée de noms et son empreinte
des sources. Pour la v044, l’audit couvre chaque déclaration publique
`theorem`/`lemma` et deux constructions publiques porteuses de preuves ; les
comptes exacts sont inscrits par le générateur dans le manifeste. Les
déclarations privées ne sont pas des cibles séparées, mais leurs dépendances
sont visibles transitivement dans les résultats publics.

La cible courante du manifeste est l’édition anglaise v08 ; l’édition
française v08 synchronisée est enregistrée séparément sous `source_pdf_fr`.
Les citations attachées aux ponts conservent leur provenance historique v07c,
sans modifier les identifiants, natures ou statuts du registre.

L'audit utilise Lean `v4.32.2` sur le point d'entrée `PaperC.Main`. La liste
admise reste `[propext, Classical.choice, Quot.sound]`; toute apparition de
`sorryAx`, `Lean.ofReduceBool` ou d'un postulat mathématique propre au papier
invalide le jalon.


<!-- BEGIN GENERATED BRIDGE REGISTRY -->
## Registre des ponts

`#print axioms` ne détecte pas les hypothèses ordinaires passées en
arguments. Ici, « inconditionnel » signifie uniquement « ne prend
aucun pont enregistré comme prémisse utilisable ». Le présent registre est distinct
de la liste blanche fondationnelle.

Un pont `external` renvoie à une source publiée indépendante et peut être
contrôlé par citation. Un pont `internal` renvoie au manuscrit cible
lui-même. Cette nature décrit la provenance, et non l’état de la
formalisation.

Le statut `open` signale un pont qui reste à fournir comme entrée dans
l’API canonique ou dans une couche inférieure. Le statut `discharged`
signale qu’une construction Lean publique le décharge dans l’API canonique;
son interface peut rester exposée pour compatibilité historique. Ce statut
porte sur le projet dans son ensemble : un ancien théorème peut donc encore
prendre explicitement un pont `discharged` comme prémisse.

La couche de certificats bibliographiques rc2 est distincte de ces statuts
Lean. Elle documente une contre-expertise source→proposition faite par des
agents, sans constituer une preuve du noyau ni une revue humaine indépendante.
Pour les trois ponts ouverts de Theorem 1.1, cette couche est la qualification
documentaire courante et rend explicites les réserves conservées dans le cœur
audité. Le fichier HK13 distinct est une note historique de clôture, et non
un certificat actif ni une prémisse de cet endpoint.

Ponts enregistrés : 13. Théorèmes publics inconditionnels : 3913. Théorèmes publics conditionnels : 159.
Répartition des ponts par provenance : 8 external, 5 internal. Théorèmes conditionnels par nature de pont (un théorème mixte compterait dans chaque catégorie) : 121 external, 59 internal.
Répartition des ponts par statut : 6 open, 7 discharged. Théorèmes conditionnels par statut de pont (un théorème mixte compterait dans chaque catégorie) : 119 open, 62 discharged.

| Identifiant | Nature | Statut | Proposition Lean | Déchargé par | Documentation rc2 | Source primaire | Localisation |
|---|---|---|---|---|---|---|---|
| `ADGR07-PNT` | `external` | `open` | `PaperC.PrimeNumberTheoremInput.PrimeNumberTheoremStatement` | — | — | Jeremy Avigad, Kevin Donnelly, David Gray, Paul Raff, *A formally verified proof of the prime number theorem*, Abstract, p. 1 | Lemma 15.1 |
| `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement` | — | [`agent_checked_supports`](literature_certificates/AGG89-T1-finite-dependency-b3-zero.md) | Richard Arratia, Larry Goldstein, Louis Gordon, *Two moments suffice for Poisson approximations: the Chen–Stein method*, Theorem 1 and the total-variation convention, printed p. 11; definitions of b1, b2, and b3 begin on printed p. 10. | Theorem 13.7 |
| `BS93-Theorem-1` | `external` | `open` | `PaperC.BalasubramanianShoreyInput.BalasubramanianShoreyStatement` | — | — | R. Balasubramanian, T. N. Shorey, *Squares in products from a block of consecutive integers*, Theorem 1; equations (1), (4), and (5), pp. 213–214 | Lemma 15.4 |
| `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement` | — | [`agent_checked_supports`](literature_certificates/ES86-T1b-Q-split-n2.md) | J.-H. Evertse, J. H. Silverman, *Uniform bounds for the number of solutions to Y^n = f(X)*, Theorem 1(b), printed p. 238. | Lemma 9.1 |
| `HK13-QO-conductor-fibres` | `external` | `discharged` | `PaperC.PellInput.QuadraticOrderConductorFiberBoundStatement` | `PaperC.PellInput.quadraticOrderConductorFiberBound` | [`historical_closure_note`](literature_certificates/HK13-QO-conductor-fibres.md) | Franz Halter-Koch, *Quadratic Irrationals: An Introduction to Classical Number Theory*, Theorem 1.1.6(1)(b), pp. 4–5; Definition 5.1.6 and Theorem 5.1.7(1),(3), pp. 118–119; Theorem 5.2.3(1),(2), p. 125; Theorem 5.2.5(1), pp. 126–127 | Lemma 9.2 |
| `LS04-Corollary-1` | `external` | `open` | `PaperC.LaishramShoreyInput.LaishramShoreyStatement` | — | — | Shanta Laishram, T. N. Shorey, *Number of prime divisors in a product of consecutive integers*, Corollary 1, equation (10), p. 330; definition of δ(k), p. 328 | Lemma 15.2 |
| `NR83-T1-divisor-bound` | `external` | `discharged` | `PaperC.PellInput.NicolasRobinPellEnvelopeStatement` | `PaperC.PellInput.nicolasRobinPellEnvelope_of_divisorLogBound` | — | J.-L. Nicolas, G. Robin, *Majorations explicites pour le nombre de diviseurs de N*, definition of f and Théorème 1, p. 485 | Lemma 9.2 |
| `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC.PellInput.NicolasRobinDivisorLogBoundStatement` | — | [`agent_checked_supports`](literature_certificates/NR83-T1-divisor-log-bound.md) | J.-L. Nicolas, G. Robin, *Majorations explicites pour le nombre de diviseurs de N*, Theorem 1, printed p. 485. | Lemma 9.2 |
| `PCv07c-L17.26-bounded-ratio-many-defects` | `internal` | `discharged` | `PaperC.PropositionSixteenOne.ManyDefectsSectorStabilityStatement` | `PaperC.BoundedRatioManyDefectsAssembly.manyDefectsSectorStability`<br>`PaperC.PropositionSixteenOne.proposition_sixteen_one_canonical`<br>`PaperC.TheoremSixteenTwo.theorem_sixteen_two_canonical` | — | Brice Pouly, *Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue*, Lemmes 17.18–17.26, pp. 60–62 | Lemma 17.26 |
| `PCv07c-L17.28-bounded-ratio-nonterminal-sector` | `internal` | `discharged` | `PaperC.PropositionSixteenOne.NonterminalSectorStabilityStatement` | `PaperC.BoundedRatioNonterminalAssembly.exists_nonterminalSectorStability`<br>`PaperC.PropositionSixteenOne.proposition_sixteen_one_canonical`<br>`PaperC.TheoremSixteenTwo.theorem_sixteen_two_canonical` | — | Brice Pouly, *Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue*, Lemme 17.28, p. 63 | Lemma 17.28 |
| `PCv07c-L17.30-bounded-ratio-terminal-sector` | `internal` | `discharged` | `PaperC.PropositionSixteenOne.TerminalSectorStabilityStatement` | `PaperC.BoundedRatioTerminalSummation.intrinsicTerminalSectorStability`<br>`PaperC.PropositionSixteenOne.proposition_sixteen_one_canonical`<br>`PaperC.TheoremSixteenTwo.theorem_sixteen_two_canonical` | — | Brice Pouly, *Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue*, Lemme 17.30, pp. 63–64 | Lemma 17.30 |
| `PCv07c-L9.10-arithmetic-kernel-equivalence` | `internal` | `discharged` | `PaperC.CanonicalSmallRows.CanonicalArithmeticKernelStatement` | `PaperC.CanonicalSmallRows.canonicalArithmeticKernelStatement`<br>`PaperC.CanonicalSmallRows.residualTau_eq_corrected_add_components_sub_arithmeticRank_of_choice_none` | — | Brice Pouly, *Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue*, Lemme 9.10, démonstration, p. 32 | Lemma 9.10 |
| `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC.PellInput.GeneralizedPellPolynomialBoxStatement` | `PaperC.PellInput.generalizedPellPolynomialBox_of_quadraticOrder_nicolasRobin`<br>`PaperC.PellInput.generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound`<br>`PaperC.PellInput.generalizedPellPolynomialBox_of_divisorLogBound` | — | Brice Pouly, *Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue*, Lemme 9.2, démonstration, pp. 28–29 | Lemma 9.2 |

### Transcriptions sources à contrôler

#### `ADGR07-PNT`

- Source : Jeremy Avigad, Kevin Donnelly, David Gray, Paul Raff, *A formally verified proof of the prime number theorem*, Abstract, p. 1.
- Nature : `external`.
- Statut : `open`.
- Proposition Lean : `PaperC.PrimeNumberTheoremInput.PrimeNumberTheoremStatement`.
- Relation de formalisation courante : exact sequential real-valued form of the cited prime number theorem: (π(L) * log L) / L tends to 1. The uniform low-zone estimate and its exponential-decay consequence are proved in Lean from this statement.
- Contrôle source courant : `manual_primary_source_check_required`.

> the density of primes in the positive integers is asymptotic to 1/ln x.

#### `AGG89-T1-finite-dependency-b3-zero`

- Source : Richard Arratia, Larry Goldstein, Louis Gordon, *Two moments suffice for Poisson approximations: the Chen–Stein method*, Theorem 1 and the total-variation convention, printed p. 11; definitions of b1, b2, and b3 begin on printed p. 10.
- Localisation enregistrée dans le cœur gelé : Theorem 1, p. 10 (supplantée pour rc2).
- Nature : `external`.
- Statut : `open`.
- Proposition Lean : `PaperC.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement`.
- Relation de formalisation courante : Agent counter-audit supports the registered source-to-proposition implication, without a Lean formalization or independent human review. Registered relation: finite-family specialization of Theorem 1 to closed graph neighborhoods and exact independence outside each neighborhood, hence b₃ = 0; total variation is defined with the standard half-L¹ normalization.
- Contrôle source courant : `agent_checked_supports`.
- Wording de contrôle dans le cœur gelé : `manual_primary_source_check_required` (supplanté pour rc2).
- Qualification rc2 : `agent_checked_supports`; lecture primaire `full_text`; pas de revue humaine indépendante.
- Certificat rc2 : [`literature_certificates/AGG89-T1-finite-dependency-b3-zero.md`](literature_certificates/AGG89-T1-finite-dependency-b3-zero.md), SHA-256 `684886dc2d9b79d175f32d46434352d2ea7084a955340ab376ca2bf92eb70115`, 5007 octets.
- Limites rc2 : The source theorem is on printed page 11, not page 10; the Challenge bound is a conservative consequence under its half-l1 normalization. No independent human verification.
- Citation littérale : extrait (les formules structurées ci-dessous complètent la transcription).

> ≤ 2(b₁ + b₂ + b₃).

#### `BS93-Theorem-1`

- Source : R. Balasubramanian, T. N. Shorey, *Squares in products from a block of consecutive integers*, Theorem 1; equations (1), (4), and (5), pp. 213–214.
- Nature : `external`.
- Statut : `open`.
- Proposition Lean : `PaperC.BalasubramanianShoreyInput.BalasubramanianShoreyStatement`.
- Relation de formalisation courante : equivalent finset reformulation of the distinct offsets and their product; P⁺(b)≤k is expressed as every prime factor of b being at most k; the real absolute bound C₂ is replaced by its natural ceiling; published effectivity is not encoded.
- Contrôle source courant : `verified_equivalent_reformulation_against_primary_source_pdf`.
- Citation littérale : extrait (les formules structurées ci-dessous complètent la transcription).
- Note de vérification : Equation (1) is (m+d₁)⋯(m+dₜ)=by² with distinct 1≤dᵢ≤k, b,y positive and P⁺(b)≤k; (4) is m>k²; (5) is t≥μₖ(θ₀). The source setup has k≥t≥2. The natural C₂ is the ceiling of the published absolute real constant. The published effectivity of θ₀ and C₂ is not encoded as computable data.
- Formules affichées transcrites :
  - `conclusion` : `k≤C₂`
  - `condition_4` : `m>k²`
  - `condition_5` : `t≥μₖ(θ₀)`
  - `equation_1` : `(m+d₁)⋯(m+dₜ)=b y²`
  - `offset_setup` : `k≥t≥2, m≥0, y≥1, 1≤d₁<⋯<dₜ≤k, P⁺(b)≤k`

> Theorem 1. Let k ≥ 27. There exist effectively computable absolute constants θ₀ and C₂

#### `ES86-T1b-Q-split-n2`

- Source : J.-H. Evertse, J. H. Silverman, *Uniform bounds for the number of solutions to Y^n = f(X)*, Theorem 1(b), printed p. 238.
- Localisation enregistrée dans le cœur gelé : Theorem 1(b), p. 238 (supplantée pour rc2).
- Nature : `external`.
- Statut : `open`.
- Proposition Lean : `PaperC.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement`.
- Relation de formalisation courante : Agent counter-audit supports the registered source-to-proposition implication, without a Lean formalization or independent human review. Registered relation: specialization to K = L = ℚ, a split polynomial, n = 2, and the abscissa count before the elementary factor two.
- Contrôle source courant : `agent_checked_supports`.
- Wording de contrôle dans le cœur gelé : `manual_primary_source_check_required` (supplanté pour rc2).
- Qualification rc2 : `agent_checked_supports`; lecture primaire `full_text`; pas de revue humaine indépendante.
- Certificat rc2 : [`literature_certificates/ES86-T1b-Q-split-n2.md`](literature_certificates/ES86-T1b-Q-split-n2.md), SHA-256 `578b50f50915995429222f7d19dba8c7c7b7df5b44acd5143f47e19477898793`, 3370 octets.
- Limites rc2 : The K=L=Q specialization and bad-place set are documented, but not formalized from a Lean version of the source theorem. No independent human verification.

> Let d ≥ 3, and assume that L contains at least three zeros of f. Then #V(R_S,f,2) ≤ 7^{M(4m+9s)} · 4^{κ₂(L)}.

#### `HK13-QO-conductor-fibres`

- Source : Franz Halter-Koch, *Quadratic Irrationals: An Introduction to Classical Number Theory*, Theorem 1.1.6(1)(b), pp. 4–5; Definition 5.1.6 and Theorem 5.1.7(1),(3), pp. 118–119; Theorem 5.2.3(1),(2), p. 125; Theorem 5.2.5(1), pp. 126–127.
- Nature : `external`.
- Statut : `discharged`.
- Déchargé par : `PaperC.PellInput.quadraticOrderConductorFiberBound`.
- Proposition Lean : `PaperC.PellInput.QuadraticOrderConductorFiberBoundStatement`.
- Relation de formalisation courante : discharged historical compatibility interface: Lean constructs K = ℚ(√D), the order embedding ℤ[√D] → O_K, the extended principal ideals, and the descent directly. Trace and norm prove 2 O_K ⊆ ℤ[√D]; the four-element quotient O_K / 2 O_K supplies the historical Fin 4 colour, and equality of colours lifts the relative unit back to ℤ[√D]. No Halter–Koch theorem is used by the discharge proof. Lean separately proves the τ(|M|)² ideal-divisor bound and all unit-orbit, height, finite-cardinality, and squarefree-reduction consequences.
- Contrôle source courant : `manually checked against the cited theorem statements and proofs on 2026-07-31`.
- Note historique de clôture : [`literature_certificates/HK13-QO-conductor-fibres.md`](literature_certificates/HK13-QO-conductor-fibres.md), SHA-256 `68f0b85c7b42bd6c94cbf6ade22478bc07b2fef0686bc94adb28dbc3111c0971`, 2792 octets.
- Rôle courant : Historical source-to-record gap report retained for provenance and superseded by the direct modulo-two Lean construction. It is not an active source certificate or an endpoint premise.
- Citation littérale : extrait (les formules structurées ci-dessous complètent la transcription).
- Note de vérification : Theorem 5.1.7 identifies the order and its conductor; Theorem 5.2.3 gives unit-group index 3 in the half-integral conductor-two case and 1 otherwise; Theorem 5.2.5 describes all generators of a fixed principal ideal as unit multiples. The Lean colour type is Fin 4 only because Fin 3 is padded into it. Lean separately proves the τ(|M|)² count of maximal-order ideal divisors, unit growth, height counting, and squarefree reduction.
- Formules affichées transcrites :
  - `descent` : `J(s) = J(t) and c(s) = c(t) imply (s) = (t) in ℤ[√D]`
  - `lean_colour_padding` : `Fin 3 → Fin 4`
  - `maximal_order_divisor` : `J(x,y) divides (M) in the maximal quadratic order`
  - `norm_fibre` : `N(x + y√D) = x² - Dy² = M`
  - `order_conductor` : `ℤ[√D] has conductor 2 when D ≡ 1 (mod 4), and conductor 1 otherwise`
  - `unit_cosets` : `[O_Kˣ : ℤ[√D]ˣ] ≤ 3`

> O_{Δf²} = ℤ + f O_Δ and [O_Δ : O_{Δf²}] = f.

#### `LS04-Corollary-1`

- Source : Shanta Laishram, T. N. Shorey, *Number of prime divisors in a product of consecutive integers*, Corollary 1, equation (10), p. 330; definition of δ(k), p. 328.
- Nature : `external`.
- Statut : `open`.
- Proposition Lean : `PaperC.LaishramShoreyInput.LaishramShoreyStatement`.
- Relation de formalisation courante : exact natural-number transcription; primeFactors.card is ω, PrimesUpTo.count is π, and Nat division by 4 is the printed floor.
- Contrôle source courant : `verified_transcription_against_primary_source_pdf`.
- Note de vérification : The surrounding source fixes k ≥ 2 and defines Δ(n,k)=n(n+1)⋯(n+k−1). The four cases of δ(k) are transcribed in exceptionCorrection.

> Let n > k. Then ω(Δ) ≥ min(π(k) + ⌊3/4 π(k)⌋ − 1 + δ(k), π(2k) − 1).

#### `NR83-T1-divisor-bound`

- Source : J.-L. Nicolas, G. Robin, *Majorations explicites pour le nombre de diviseurs de N*, definition of f and Théorème 1, p. 485.
- Nature : `external`.
- Statut : `discharged`.
- Déchargé par : `PaperC.PellInput.nicolasRobinPellEnvelope_of_divisorLogBound`.
- Proposition Lean : `PaperC.PellInput.NicolasRobinPellEnvelopeStatement`.
- Relation de formalisation courante : discharged legacy envelope retained for compatibility: PellDivisorEnvelope derives it from NR83-T1-divisor-log-bound, proving in Lean the polynomial substitution, small-argument split, squaring of the divisor count, and absorption of the explicit logarithmic unit-orbit factor.
- Contrôle source courant : `manual_primary_source_check_required`.
- Citation littérale : extrait (les formules structurées ci-dessous complètent la transcription).
- Note de vérification : Theorem 1 gives the global maximum of f. This legacy specialized envelope is now derived in Lean from the separately registered source-shaped logarithmic inequality; the polynomial-height substitution, squaring, and logarithmic unit-factor absorption are kernel-checked.
- Formules affichées transcrites :
  - `divisor_function` : `d(n) = ∑_{d|n} 1`
  - `lean_corollary` : `4 d(m)² · (4 log₂(2H²)+6) ≤ exp(c log N / log log N) for m ≤ N^K and H ≤ N^(2K)`
  - `normalized_function` : `f(n) = log(d(n)) log(log n) / (log 2 log n)`

> Le maximum de f(n) est atteint en n = 6983776800, et l'on a : max f(n) = 1,5379.

#### `NR83-T1-divisor-log-bound`

- Source : J.-L. Nicolas, G. Robin, *Majorations explicites pour le nombre de diviseurs de N*, Theorem 1, printed p. 485.
- Localisation enregistrée dans le cœur gelé : definition of f and Théorème 1, p. 485 (supplantée pour rc2).
- Nature : `external`.
- Statut : `open`.
- Proposition Lean : `PaperC.PellInput.NicolasRobinDivisorLogBoundStatement`.
- Relation de formalisation courante : Agent counter-audit supports the registered source-to-proposition implication, without a Lean formalization or independent human review. Registered relation: source-shaped Nicolas–Robin input only: the direct logarithmic divisor inequality above n=64. Lean derives the former specialized Pell envelope, including polynomial substitution, all finite small-m cases, the squared divisor factor, and logarithmic height absorption.
- Contrôle source courant : `agent_checked_supports`.
- Wording de contrôle dans le cœur gelé : `manual_primary_source_check_required` (supplanté pour rc2).
- Qualification rc2 : `agent_checked_supports`; lecture primaire `full_text`; pas de revue humaine indépendante.
- Certificat rc2 : [`literature_certificates/NR83-T1-divisor-log-bound.md`](literature_certificates/NR83-T1-divisor-log-bound.md), SHA-256 `51ac933cbc7e41fce60cfe7a939c6c606bbb1fd0d3642bb6ed7fbfe02c163e73`, 3366 octets.
- Limites rc2 : The certificate uses the exact maximizer and an elementary strict bound below 2, rather than treating the printed decimal 1.5379 as exact. No independent human verification.
- Citation littérale : extrait (les formules structurées ci-dessous complètent la transcription).
- Note de vérification du cœur gelé (supplantée pour rc2) : The printed 1.5379 is rounded (the maximizing value is approximately 1.53793986), so Lean deliberately uses the safe exact majorant 2 rather than interpreting the four-decimal display as an exact rational bound. The proposition is restricted to n ≥ 64 so log(log n) is positive. PellDivisorEnvelope proves every later polynomial-height and unit-orbit consequence.
- Formules affichées transcrites :
  - `divisor_function` : `d(n) = ∑_{d|n} 1`
  - `lean_statement` : `log(d(n)) log(log n) ≤ 2 log(2) log(n), for n ≥ 64`
  - `normalized_function` : `f(n) = log(d(n)) log(log n) / (log 2 log n)`

> Le maximum de f(n) est atteint en n = 6983776800, et l'on a : max f(n) = 1,5379.

#### `PCv07c-L17.26-bounded-ratio-many-defects`

- Source : Brice Pouly, *Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue*, Lemmes 17.18–17.26, pp. 60–62.
- Nature : `internal`.
- Statut : `discharged`.
- Déchargé par : `PaperC.BoundedRatioManyDefectsAssembly.manyDefectsSectorStability`, `PaperC.PropositionSixteenOne.proposition_sixteen_one_canonical`, `PaperC.TheoremSixteenTwo.theorem_sixteen_two_canonical`.
- Proposition Lean : `PaperC.PropositionSixteenOne.ManyDefectsSectorStabilityStatement`.
- Relation de formalisation courante : discharged historical interface retained for compatibility: Lean covers every literal active host by a two-defect window base and a finite component shape, disintegrates each fixed fibre by a smooth squarefree coefficient, closes degree one with an N^(1/2+o(1)) envelope, closes degree two from generalized Pell or an exact signed-divisor factorization, and closes degree at least three from Evertse–Silverman together with an unconditional factorial bound for the number of prime factors. The signed-divisor and Evertse–Silverman sums are uniformly N^o(1), the degree-by-degree fixed-fibre assembly is complete, and the resulting N^(3/2+o(1)) estimate is transported to little-oh of N^2. Evertse–Silverman and generalized Pell remain explicit lower-level antecedents; there is no remaining Lemma 17.26-specific formalization debt.
- Contrôle source courant : `manual_primary_source_check_required`.

> Lemme 17.26 (Élimination des défauts multiples sur U). La masse linéaire des couples du coeur profond non aligné tels que D# ≥ 3 est N^{3/2+o_{C,κ₀}(1)}.

#### `PCv07c-L17.28-bounded-ratio-nonterminal-sector`

- Source : Brice Pouly, *Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue*, Lemme 17.28, p. 63.
- Nature : `internal`.
- Statut : `discharged`.
- Déchargé par : `PaperC.BoundedRatioNonterminalAssembly.exists_nonterminalSectorStability`, `PaperC.PropositionSixteenOne.proposition_sixteen_one_canonical`, `PaperC.TheoremSixteenTwo.theorem_sixteen_two_canonical`.
- Proposition Lean : `PaperC.PropositionSixteenOne.NonterminalSectorStabilityStatement`.
- Relation de formalisation courante : discharged historical interface retained for compatibility: Lean follows the manuscript split 3c# <= 2B versus 2B < 3c# exactly. In the first branch, the size-at-most-ten host population is reduced to fixed shapes and mobile fibres; the two-singleton shapes have an elementary N^(1+o(1)) envelope, degree two is closed from generalized Pell, and degree at least three is closed from Evertse–Silverman, giving N^(5/3+o(1)) mass. In the second branch, Lean extracts a size-two component, the exact factor 2^(R_K(B)+1), and an elementary Euler-product bound N exp(Cterm sqrt(B)/log B); it then chooses K with 2 Cterm < K log 2. The finite mass decomposition, floor handling, both host counts and both little-oh transports are complete. Evertse–Silverman and generalized Pell remain explicit lower-level antecedents; there is no remaining Lemma 17.28-specific formalization debt.
- Contrôle source courant : `manual_primary_source_check_required`.

> La masse du coeur profond non aligné à D# ≤ 2 — les couples à D# ≥ 3 étant éliminés par le lemme 17.26 — est o_{C,κ₀}(N²) en dehors de l’ensemble T_K.

#### `PCv07c-L17.30-bounded-ratio-terminal-sector`

- Source : Brice Pouly, *Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue*, Lemme 17.30, pp. 63–64.
- Nature : `internal`.
- Statut : `discharged`.
- Déchargé par : `PaperC.BoundedRatioTerminalSummation.intrinsicTerminalSectorStability`, `PaperC.PropositionSixteenOne.proposition_sixteen_one_canonical`, `PaperC.TheoremSixteenTwo.theorem_sixteen_two_canonical`.
- Proposition Lean : `PaperC.PropositionSixteenOne.TerminalSectorStabilityStatement`.
- Relation de formalisation courante : discharged historical generic terminal-sector interface retained for compatibility with arbitrary terminal classifiers; for the canonical intrinsic classifier, Lean proves the complete first-start and partner summation under generalized Pell, the uniform N^(3/4+o(1)) cardinal bound, the N^(7/4+o(1)) = o(N^2) mass bound, and the exact transport through the proved source-scoped Lemma 9.10 arithmetic equivalence. Consequently the principal canonical Proposition 16.1 and Theorem 16.2 replace this coarse premise by generalized Pell alone. Evertse–Silverman is not used in Lemma 17.30, and there is no remaining Lemma 17.30-specific formalization debt.
- Contrôle source courant : `manual_primary_source_check_required`.

> Lemme 17.30 (Fermeture terminale sur U). Avec T = (C_det(κ₀)NB)^{1/2}, la population terminale satisfait #T_K ≤ N^{3/4+o_{C,κ₀}(1)} et ∑_{(x,y)∈T_K}(2^{τ(x,y)}−1) ≤ N^{7/4+o_{C,κ₀}(1)}.

#### `PCv07c-L9.10-arithmetic-kernel-equivalence`

- Source : Brice Pouly, *Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue*, Lemme 9.10, démonstration, p. 32.
- Nature : `internal`.
- Statut : `discharged`.
- Déchargé par : `PaperC.CanonicalSmallRows.canonicalArithmeticKernelStatement`, `PaperC.CanonicalSmallRows.residualTau_eq_corrected_add_components_sub_arithmeticRank_of_choice_none`.
- Proposition Lean : `PaperC.CanonicalSmallRows.CanonicalArithmeticKernelStatement`.
- Relation de formalisation courante : source-exact nonaligned statement for Lemma 9.10: when no canonical rational channel exists and the finite cylinder covers both complete boundaries, the residual quotient is the kernel of the fixed prime-and-block matrix.
- Contrôle source courant : `manual_primary_source_check_required`.

> Le lemme 6.1 identifie l’espace des solutions des grands premiers à F_2^{D#+c#} dans la branche non alignée. Les seules équations qui restent sont les lignes de M̃.

#### `PCv07c-L9.2-generalized-Pell`

- Source : Brice Pouly, *Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue*, Lemme 9.2, démonstration, pp. 28–29.
- Nature : `internal`.
- Statut : `discharged`.
- Déchargé par : `PaperC.PellInput.generalizedPellPolynomialBox_of_quadraticOrder_nicolasRobin`, `PaperC.PellInput.generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound`, `PaperC.PellInput.generalizedPellPolynomialBox_of_divisorLogBound`.
- Proposition Lean : `PaperC.PellInput.GeneralizedPellPolynomialBoxStatement`.
- Relation de formalisation courante : legacy manuscript-facing interface, discharged in Lean by generalizedPellPolynomialBox_of_divisorLogBound. The quadratic-order conductor fibre bound is proved internally by PaperC.PellInput.quadraticOrderConductorFiberBound; its only open upstream assumption is the direct Nicolas--Robin logarithmic inequality NR83-T1-divisor-log-bound. The maximal-order ideal-divisor count, conductor descent, unit orbits, height control, finite counting, squarefree-kernel reduction, polynomial substitution and logarithmic-factor absorption are proved internally.
- Contrôle source courant : `manual_primary_source_check_required`.

> Ainsi le nombre de solutions est au plus O_{K₀}(τ(|M|)² log N). Comme |M| ≤ N^{O_{K₀}(1)}, la borne divisorielle standard donne (9.3).

### Conditionnalité de chaque théorème public

| Théorème | Conditionnalité | Ponts requis | Nature(s) | Statut(s) des ponts | Source |
|---|---|---|---|---|---|
| `PaperC.Affine.CanonicalRationalCode.candidate_coprime` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:51` |
| `PaperC.Affine.CanonicalRationalCode.candidate_fst_pos` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:39` |
| `PaperC.Affine.CanonicalRationalCode.candidate_max_le_length_of_two_units` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:170` |
| `PaperC.Affine.CanonicalRationalCode.candidate_snd_pos` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:45` |
| `PaperC.Affine.CanonicalRationalCode.canonicalRationalCode_eq_bot_of_multiplicity_le_one` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:281` |
| `PaperC.Affine.CanonicalRationalCode.canonicalRationalCode_eq_of_rationalCode_ne_bot` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:404` |
| `PaperC.Affine.CanonicalRationalCode.canonicalRationalCode_eq_of_two_units` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:331` |
| `PaperC.Affine.CanonicalRationalCode.canonicalReducedCandidate?_eq_none_iff` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:67` |
| `PaperC.Affine.CanonicalRationalCode.canonicalReducedCandidate?_eq_some_of_mem` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:97` |
| `PaperC.Affine.CanonicalRationalCode.canonicalReducedCandidate?_map_val` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:84` |
| `PaperC.Affine.CanonicalRationalCode.degenerate_canonical_channel` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:306` |
| `PaperC.Affine.CanonicalRationalCode.exists_canonical_candidate_of_two_le_multiplicity` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:149` |
| `PaperC.Affine.CanonicalRationalCode.rationalSigma_eq_canonicalMultiplicity_sub_one` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:215` |
| `PaperC.Affine.CanonicalRationalCode.rationalSigma_eq_card_sub_one_of_two_units` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:377` |
| `PaperC.Affine.CanonicalRationalCode.rationalSigma_le_relationRho` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:261` |
| `PaperC.Affine.CanonicalRationalCode.relationRho_eq_rationalSigma_add_residualTau` | inconditionnel | — | — | — | `PaperC/Affine/CanonicalRationalCode.lean:270` |
| `PaperC.Affine.RationalChannelCode.card_rationalChannelUnits_eq_channelCells` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:167` |
| `PaperC.Affine.RationalChannelCode.channelAffineCharacter_apply` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:1082` |
| `PaperC.Affine.RationalChannelCode.channelCellUnit_channelUnitCell` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:140` |
| `PaperC.Affine.RationalChannelCode.channelRelationCoefficients_injective` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:584` |
| `PaperC.Affine.RationalChannelCode.channelRelationCoefficients_mem_relationSpace` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:827` |
| `PaperC.Affine.RationalChannelCode.channelUnitCell_channelCellUnit` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:132` |
| `PaperC.Affine.RationalChannelCode.channelUnitCell_mem_channelCells` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:73` |
| `PaperC.Affine.RationalChannelCode.channelUnit_label_mul_eq` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:772` |
| `PaperC.Affine.RationalChannelCode.channelUnit_left_injective` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:513` |
| `PaperC.Affine.RationalChannelCode.channelUnit_right_injective` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:533` |
| `PaperC.Affine.RationalChannelCode.channelVertexOffset_eq_neg_one_iff` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:1091` |
| `PaperC.Affine.RationalChannelCode.channelVertexOffset_mem_offsetInterval` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:60` |
| `PaperC.Affine.RationalChannelCode.channelVertexOffset_offsetVertexOfMem` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:98` |
| `PaperC.Affine.RationalChannelCode.channelVertexOffset_startRootVertex` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:1104` |
| `PaperC.Affine.RationalChannelCode.coordinateSum_apply` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:200` |
| `PaperC.Affine.RationalChannelCode.coordinateSum_eq_selectedChannelUnits_card` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:225` |
| `PaperC.Affine.RationalChannelCode.coordinateSum_surjective` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:261` |
| `PaperC.Affine.RationalChannelCode.dotProduct_twoStartRhs_eq_boundary_roots` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:1051` |
| `PaperC.Affine.RationalChannelCode.dotProduct_twoStartSystem_eq_sum_completeBoundary` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:657` |
| `PaperC.Affine.RationalChannelCode.finrank_evenChannelSelection` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:287` |
| `PaperC.Affine.RationalChannelCode.finrank_evenChannelSelection_all` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:302` |
| `PaperC.Affine.RationalChannelCode.finrank_ker_coordinateSum` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:274` |
| `PaperC.Affine.RationalChannelCode.finrank_rationalCode` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:927` |
| `PaperC.Affine.RationalChannelCode.finrank_rationalCode_all` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:944` |
| `PaperC.Affine.RationalChannelCode.finrank_rationalCode_eq_channelCells_card_sub_one` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:986` |
| `PaperC.Affine.RationalChannelCode.leftUnitBoundary_apply` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:340` |
| `PaperC.Affine.RationalChannelCode.leftUnitBoundary_injective` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:553` |
| `PaperC.Affine.RationalChannelCode.leftUnitBoundary_root` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:1108` |
| `PaperC.Affine.RationalChannelCode.max_channelCoefficients_le_length` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:1012` |
| `PaperC.Affine.RationalChannelCode.mem_evenChannelSelection_iff_even_card` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:250` |
| `PaperC.Affine.RationalChannelCode.mem_rationalChannelUnits` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:51` |
| `PaperC.Affine.RationalChannelCode.offsetVertexOfMem_channelVertexOffset` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:107` |
| `PaperC.Affine.RationalChannelCode.rationalCode_ne_bot_iff_two_le_card` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:960` |
| `PaperC.Affine.RationalChannelCode.rationalCode_ne_bot_iff_two_le_channelCells_card` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:973` |
| `PaperC.Affine.RationalChannelCode.rationalRelationMap_coe` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:887` |
| `PaperC.Affine.RationalChannelCode.rationalRelationMap_injective` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:900` |
| `PaperC.Affine.RationalChannelCode.relationCharacter_rationalRelationMap` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:1158` |
| `PaperC.Affine.RationalChannelCode.rightUnitBoundary_apply` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:351` |
| `PaperC.Affine.RationalChannelCode.rightUnitBoundary_root` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:1131` |
| `PaperC.Affine.RationalChannelCode.startCompleteBoundary_liftEvenBoundary` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:395` |
| `PaperC.Affine.RationalChannelCode.startCompleteBoundary_root_eq_dot_startRhs` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:1036` |
| `PaperC.Affine.RationalChannelCode.startCompleteVertexLabel_cast` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:179` |
| `PaperC.Affine.RationalChannelCode.startCompleteVertexLabel_pos` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:791` |
| `PaperC.Affine.RationalChannelCode.startSystem_apply_eq_sum_incidence` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:601` |
| `PaperC.Affine.RationalChannelCode.startVertexSum_leftUnitBoundary` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:361` |
| `PaperC.Affine.RationalChannelCode.startVertexSum_rightUnitBoundary` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:375` |
| `PaperC.Affine.RationalChannelCode.sum_completeBoundary_channelRelationCoefficients` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:744` |
| `PaperC.Affine.RationalChannelCode.sum_startSystem_eq_sum_completeBoundary` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:617` |
| `PaperC.Affine.RationalChannelCode.twoStartCompleteBoundary_channelRelationCoefficients_inl` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:483` |
| `PaperC.Affine.RationalChannelCode.twoStartCompleteBoundary_channelRelationCoefficients_inr` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:497` |
| `PaperC.Affine.RationalChannelCode.valueBit_add_of_channelUnit` | inconditionnel | — | — | — | `PaperC/Affine/RationalChannelCode.lean:804` |
| `PaperC.Affine.RelationalPrimeAssignment.dvd_of_parityVec_ne_zero` | inconditionnel | — | — | — | `PaperC/Affine/RelationalPrimeAssignment.lean:155` |
| `PaperC.Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_left` | inconditionnel | — | — | — | `PaperC/Affine/RelationalPrimeAssignment.lean:336` |
| `PaperC.Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_right` | inconditionnel | — | — | — | `PaperC/Affine/RelationalPrimeAssignment.lean:370` |
| `PaperC.Affine.RelationalPrimeAssignment.existsUnique_opposite_of_left` | inconditionnel | — | — | — | `PaperC/Affine/RelationalPrimeAssignment.lean:210` |
| `PaperC.Affine.RelationalPrimeAssignment.existsUnique_opposite_of_right` | inconditionnel | — | — | — | `PaperC/Affine/RelationalPrimeAssignment.lean:270` |
| `PaperC.Affine.RelationalPrimeAssignment.parityVec_ne_zero_unique_in_start` | inconditionnel | — | — | — | `PaperC/Affine/RelationalPrimeAssignment.lean:167` |
| `PaperC.Affine.RelationalPrimeAssignment.relation_boundary_prime_equation` | inconditionnel | — | — | — | `PaperC/Affine/RelationalPrimeAssignment.lean:88` |
| `PaperC.Affine.RelationalPrimeAssignment.relation_prime_equation` | inconditionnel | — | — | — | `PaperC/Affine/RelationalPrimeAssignment.lean:52` |
| `PaperC.Affine.RelationalPrimeAssignment.startCompleteVertexLabel_dist_lt` | inconditionnel | — | — | — | `PaperC/Affine/RelationalPrimeAssignment.lean:123` |
| `PaperC.Affine.RelationalPrimeAssignment.startCompleteVertexLabel_injective` | inconditionnel | — | — | — | `PaperC/Affine/RelationalPrimeAssignment.lean:101` |
| `PaperC.Affine.StartDefectRank.card_startDefectIndices_le` | inconditionnel | — | — | — | `PaperC/Affine/StartDefectRank.lean:411` |
| `PaperC.Affine.StartDefectRank.relationRho_startSystem_le_card_defectsInInterval` | inconditionnel | — | — | — | `PaperC/Affine/StartDefectRank.lean:457` |
| `PaperC.Affine.StartDefectRank.startDefectRestriction_injective` | inconditionnel | — | — | — | `PaperC/Affine/StartDefectRank.lean:381` |
| `PaperC.Affine.StartDefectRank.startInteriorBoundary_apply_ne_zero` | inconditionnel | — | — | — | `PaperC/Affine/StartDefectRank.lean:63` |
| `PaperC.Affine.StartDefectRank.startInteriorBoundary_apply_zero` | inconditionnel | — | — | — | `PaperC/Affine/StartDefectRank.lean:58` |
| `PaperC.Affine.StartDefectRank.startInteriorBoundary_eq_zero_of_not_hDefective` | inconditionnel | — | — | — | `PaperC/Affine/StartDefectRank.lean:223` |
| `PaperC.Affine.StartDefectRank.startInteriorBoundary_injective` | inconditionnel | — | — | — | `PaperC/Affine/StartDefectRank.lean:69` |
| `PaperC.Affine.TouchingDefectRank.card_touchingDefectIndices_le` | inconditionnel | — | — | — | `PaperC/Affine/TouchingDefectRank.lean:867` |
| `PaperC.Affine.TouchingDefectRank.relationRho_touchingSystem_le_card_defectsInInterval` | inconditionnel | — | — | — | `PaperC/Affine/TouchingDefectRank.lean:942` |
| `PaperC.Affine.TouchingDefectRank.touchingDefectRestriction_injective` | inconditionnel | — | — | — | `PaperC/Affine/TouchingDefectRank.lean:833` |
| `PaperC.Affine.TouchingDefectRank.touchingInteriorBoundary_apply_eq_sum_incidence` | inconditionnel | — | — | — | `PaperC/Affine/TouchingDefectRank.lean:250` |
| `PaperC.Affine.TouchingDefectRank.touchingInteriorBoundary_eq_zero_of_not_hDefective` | inconditionnel | — | — | — | `PaperC/Affine/TouchingDefectRank.lean:681` |
| `PaperC.Affine.TouchingDefectRank.touchingInteriorBoundary_injective` | inconditionnel | — | — | — | `PaperC/Affine/TouchingDefectRank.lean:132` |
| `PaperC.Affine.TouchingDefectRank.touchingVertexLabel_injective` | inconditionnel | — | — | — | `PaperC/Affine/TouchingDefectRank.lean:36` |
| `PaperC.Affine.abs_eta_mul_two_pow_rho_sub_one_le` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:267` |
| `PaperC.Affine.add_eq_zero_iff_eq` | inconditionnel | — | — | — | `PaperC/Affine/StartSystem.lean:24` |
| `PaperC.Affine.affineFiber_fourier_identity` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:196` |
| `PaperC.Affine.affineFiber_normalized_card_identity` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:227` |
| `PaperC.Affine.binarySign_add` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:41` |
| `PaperC.Affine.binarySign_eq_one_iff` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:37` |
| `PaperC.Affine.binarySign_neg` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:47` |
| `PaperC.Affine.binarySign_sub` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:51` |
| `PaperC.Affine.binarySign_zero` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:33` |
| `PaperC.Affine.canonicalTwoStartBoundaryIndex_le` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:570` |
| `PaperC.Affine.canonicalTwoStartBoundaryIndex_mem` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:549` |
| `PaperC.Affine.canonicalTwoStartBoundaryOccurrence_ne_zero` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:557` |
| `PaperC.Affine.card_eq_two_pow_finrank` | inconditionnel | — | — | — | `PaperC/Affine/Probability.lean:38` |
| `PaperC.Affine.card_pi_f2` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:219` |
| `PaperC.Affine.card_solution_eq_card_ker` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:130` |
| `PaperC.Affine.card_solution_eq_ite` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:169` |
| `PaperC.Affine.card_solution_eq_pow_finrank` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:139` |
| `PaperC.Affine.card_solution_eq_pow_finrank_of_compatible` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:153` |
| `PaperC.Affine.card_solution_eq_zero_of_not_compatible` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:162` |
| `PaperC.Affine.card_solution_is_power_of_two` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:184` |
| `PaperC.Affine.compatible_iff_nonempty` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:56` |
| `PaperC.Affine.compatible_of_relationCharacter_eq_zero` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:174` |
| `PaperC.Affine.dotLinear_apply` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:109` |
| `PaperC.Affine.dotLinear_eq_zero_iff` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:114` |
| `PaperC.Affine.existsUnique_startCompleteBoundary_eq` | inconditionnel | — | — | — | `PaperC/Affine/StartBoundaryRange.lean:160` |
| `PaperC.Affine.exists_twoStartCompleteBoundary_ne_zero` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:465` |
| `PaperC.Affine.mem_relationSpace_twoStartSystem_iff_boundary_prime_equations` | inconditionnel | — | — | — | `PaperC/Affine/RelationBoundaryIff.lean:152` |
| `PaperC.Affine.mem_solutionSet_iff` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:46` |
| `PaperC.Affine.mem_startSolutionSet_iff` | inconditionnel | — | — | — | `PaperC/Affine/StartSystem.lean:96` |
| `PaperC.Affine.mem_startSolutionSet_iff_startAt` | inconditionnel | — | — | — | `PaperC/Affine/StartSystem.lean:110` |
| `PaperC.Affine.mem_twoStartBoundarySupport` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:514` |
| `PaperC.Affine.not_compatible_iff_isEmpty` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:66` |
| `PaperC.Affine.range_startCompleteBoundary_eq_ker_startVertexSum` | inconditionnel | — | — | — | `PaperC/Affine/StartBoundaryRange.lean:81` |
| `PaperC.Affine.relationCanonicalSelectedOccurrence_minimal` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:605` |
| `PaperC.Affine.relationCanonicalSelectedOccurrence_ne_zero` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:589` |
| `PaperC.Affine.relationCharacter_apply` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:50` |
| `PaperC.Affine.relationCharacter_eq_zero_iff_compatible` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:198` |
| `PaperC.Affine.relationCharacter_eq_zero_of_compatible` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:94` |
| `PaperC.Affine.relationEta_eq_one_iff` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:69` |
| `PaperC.Affine.relationEta_eq_one_iff_compatible` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:205` |
| `PaperC.Affine.relationEta_eq_zero_iff` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:75` |
| `PaperC.Affine.relationEta_eq_zero_iff_not_compatible` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:212` |
| `PaperC.Affine.relationEta_eq_zero_or_one` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:81` |
| `PaperC.Affine.relationFunctional_apply` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:152` |
| `PaperC.Affine.relationMap_apply` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:170` |
| `PaperC.Affine.relationRho_pos_of_character_ne_zero` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:254` |
| `PaperC.Affine.relationSignedSum_eq_eta_mul_two_pow_rho` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:153` |
| `PaperC.Affine.relationSignedSum_eq_ite` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:134` |
| `PaperC.Affine.relationSignedSum_eq_sum_relationCharacter` | inconditionnel | — | — | — | `PaperC/Affine/Normalization.lean:115` |
| `PaperC.Affine.relation_exists_selectedOccurrence` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:486` |
| `PaperC.Affine.relation_twoStartBoundarySupport_nonempty` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:523` |
| `PaperC.Affine.solutionEquivKer_apply_coe` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:93` |
| `PaperC.Affine.solutionEquivKer_symm_apply_coe` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:99` |
| `PaperC.Affine.solution_property` | inconditionnel | — | — | — | `PaperC/Affine/System.lean:51` |
| `PaperC.Affine.startBoundaryEquivEven_apply_coe` | inconditionnel | — | — | — | `PaperC/Affine/StartBoundaryRange.lean:149` |
| `PaperC.Affine.startBoundaryToEven_injective` | inconditionnel | — | — | — | `PaperC/Affine/StartBoundaryRange.lean:119` |
| `PaperC.Affine.startBoundaryToEven_surjective` | inconditionnel | — | — | — | `PaperC/Affine/StartBoundaryRange.lean:125` |
| `PaperC.Affine.startCompleteBoundary_apply` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:130` |
| `PaperC.Affine.startCompleteBoundary_injective` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:218` |
| `PaperC.Affine.startCompleteVertexLabel_base` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:260` |
| `PaperC.Affine.startCompleteVertexLabel_root` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:249` |
| `PaperC.Affine.startCompleteVertexLabel_tip` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:255` |
| `PaperC.Affine.startEdgeParity_eq_endpoint_sum` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:269` |
| `PaperC.Affine.startEdgeParity_eq_sum_incidence` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:282` |
| `PaperC.Affine.startRhs_apply` | inconditionnel | — | — | — | `PaperC/Affine/StartSystem.lean:60` |
| `PaperC.Affine.startSystem_apply` | inconditionnel | — | — | — | `PaperC/Affine/StartSystem.lean:46` |
| `PaperC.Affine.startSystem_eq_startRhs_iff` | inconditionnel | — | — | — | `PaperC/Affine/StartSystem.lean:68` |
| `PaperC.Affine.startSystem_eq_startRhs_iff_startAt` | inconditionnel | — | — | — | `PaperC/Affine/StartSystem.lean:104` |
| `PaperC.Affine.startVertexSum_apply` | inconditionnel | — | — | — | `PaperC/Affine/StartBoundaryRange.lean:33` |
| `PaperC.Affine.startVertexSum_startCompleteBoundary_eq_zero` | inconditionnel | — | — | — | `PaperC/Affine/StartBoundaryRange.lean:49` |
| `PaperC.Affine.startVertexSum_surjective` | inconditionnel | — | — | — | `PaperC/Affine/StartBoundaryRange.lean:70` |
| `PaperC.Affine.sum_binarySign_dotProduct` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:127` |
| `PaperC.Affine.sum_binarySign_linear` | inconditionnel | — | — | — | `PaperC/Affine/Fourier.lean:85` |
| `PaperC.Affine.sum_startEdgeParity_eq_sum_completeBoundary` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:298` |
| `PaperC.Affine.sum_startIncidenceColumn_eq_zero` | inconditionnel | — | — | — | `PaperC/Affine/StartBoundaryRange.lean:39` |
| `PaperC.Affine.sum_twoStartEdgeParity_eq_sum_completeBoundary` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:441` |
| `PaperC.Affine.touchingRhs_apply_inl` | inconditionnel | — | — | — | `PaperC/Affine/TouchingSystem.lean:48` |
| `PaperC.Affine.touchingRhs_apply_inr` | inconditionnel | — | — | — | `PaperC/Affine/TouchingSystem.lean:53` |
| `PaperC.Affine.touchingRoot_le_dyadicCutoff` | inconditionnel | — | — | — | `PaperC/Affine/TouchingSystem.lean:95` |
| `PaperC.Affine.touchingSystem_apply_inl` | inconditionnel | — | — | — | `PaperC/Affine/TouchingSystem.lean:34` |
| `PaperC.Affine.touchingSystem_apply_inr` | inconditionnel | — | — | — | `PaperC/Affine/TouchingSystem.lean:41` |
| `PaperC.Affine.touchingSystem_eq_touchingRhs_iff` | inconditionnel | — | — | — | `PaperC/Affine/TouchingSystem.lean:61` |
| `PaperC.Affine.touchingWindow_le_dyadicCutoff` | inconditionnel | — | — | — | `PaperC/Affine/TouchingSystem.lean:85` |
| `PaperC.Affine.twoStartCompleteBoundary_apply_inl` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:391` |
| `PaperC.Affine.twoStartCompleteBoundary_apply_inr` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:399` |
| `PaperC.Affine.twoStartCompleteBoundary_injective` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:407` |
| `PaperC.Affine.twoStartRhs_apply_inl` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:67` |
| `PaperC.Affine.twoStartRhs_apply_inr` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:72` |
| `PaperC.Affine.twoStartSystem_apply_inl` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:53` |
| `PaperC.Affine.twoStartSystem_apply_inr` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:60` |
| `PaperC.Affine.twoStartSystem_eq_twoStartRhs_iff` | inconditionnel | — | — | — | `PaperC/Affine/TwoStartSystem.lean:77` |
| `PaperC.Affine.uniformSolutionProbability_eq_ite` | inconditionnel | — | — | — | `PaperC/Affine/Probability.lean:48` |
| `PaperC.Affine.uniformSolutionProbability_of_compatible` | inconditionnel | — | — | — | `PaperC/Affine/Probability.lean:62` |
| `PaperC.Affine.uniformSolutionProbability_of_not_compatible` | inconditionnel | — | — | — | `PaperC/Affine/Probability.lean:70` |
| `PaperC.AlignedComponentCode.componentCode_finrank_ge` | inconditionnel | — | — | — | `PaperC/Coding/AlignedComponentCode.lean:113` |
| `PaperC.AlignedComponentCode.componentLeftCount_add_rightCount` | inconditionnel | — | — | — | `PaperC/Coding/AlignedComponentCode.lean:71` |
| `PaperC.AlignedComponentCode.kernelWord_componentProducts_square` | inconditionnel | — | — | — | `PaperC/Coding/AlignedComponentCode.lean:189` |
| `PaperC.AlignedComponentCode.kernelWord_leftCount_even` | inconditionnel | — | — | — | `PaperC/Coding/AlignedComponentCode.lean:126` |
| `PaperC.AlignedComponentCode.kernelWord_parity_package` | inconditionnel | — | — | — | `PaperC/Coding/AlignedComponentCode.lean:236` |
| `PaperC.AlignedComponentCode.kernelWord_rightCount_even` | inconditionnel | — | — | — | `PaperC/Coding/AlignedComponentCode.lean:156` |
| `PaperC.AlignedComponentHamming.exists_short_kernelWord_parity_package` | inconditionnel | — | — | — | `PaperC/Coding/AlignedComponentHamming.lean:27` |
| `PaperC.AlignedCoreExclusion.mem_smallExactFreeResidualComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedCoreExclusion.lean:57` |
| `PaperC.AlignedCoreExclusion.no_aligned_core_of_finite_conditions` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedCoreExclusion.lean:127` |
| `PaperC.AlignedCoreExclusion.no_candidate_aligned_core_of_finite_conditions` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedCoreExclusion.lean:231` |
| `PaperC.AlignedCoreExclusion.target_le_card_smallExactFreeResidualComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedCoreExclusion.lean:69` |
| `PaperC.AlignedCoreExclusion.target_le_card_smallExactFreeResidualComponents_of_candidate` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedCoreExclusion.lean:102` |
| `PaperC.AlignedDeepCoreExtraction.fixed_cutoff_counting_budget` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedDeepCoreExtraction.lean:36` |
| `PaperC.AlignedDeepCoreExtraction.no_dense_candidate_aligned_core_of_hamming_runge_conditions` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedDeepCoreExtraction.lean:176` |
| `PaperC.AlignedDeepCoreExtraction.no_dense_candidate_aligned_core_of_numerical_conditions` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedDeepCoreExtraction.lean:136` |
| `PaperC.AlignedDeepCoreExtraction.one_sixteenth_le_card_smallExactFreeResidualComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedDeepCoreExtraction.lean:86` |
| `PaperC.AlignedDeepCoreExtraction.one_sixteenth_le_card_smallExactFreeResidualComponents_of_candidate` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedDeepCoreExtraction.lean:108` |
| `PaperC.AlignedDeepCoreExtraction.prime_rows_le_one_sixteenth` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedDeepCoreExtraction.lean:64` |
| `PaperC.AlignedExactFreeComponents.card_residualComponents_le_card_exactFree_add_two` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedExactFreeComponents.lean:257` |
| `PaperC.AlignedExactFreeComponents.exactFreeResidualComponents_eq_of_two_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedExactFreeComponents.lean:186` |
| `PaperC.AlignedExactFreeComponents.isExactFreeComponent_of_channelUnitCount_eq_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedExactFreeComponents.lean:235` |
| `PaperC.AlignedExactFreeComponents.isExactFreeComponent_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedExactFreeComponents.lean:78` |
| `PaperC.AlignedExactFreeComponents.isExactFreeComponent_of_mem_residual_of_two_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedExactFreeComponents.lean:113` |
| `PaperC.AlignedExactFreeComponents.isNontrivialUnpinnedComponent_of_mem_exactFree` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedExactFreeComponents.lean:94` |
| `PaperC.AlignedExactFreeComponents.mem_exactFreeResidualComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedExactFreeComponents.lean:68` |
| `PaperC.AlignedExactFreeComponents.mem_oneUnitExceptionalComponents_of_not_exactFree` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedExactFreeComponents.lean:212` |
| `PaperC.AlignedExactFreeComponents.mem_residualComponents_of_mem_exactFree` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedExactFreeComponents.lean:86` |
| `PaperC.AlignedRungeBridge.abs_alignedShift_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:560` |
| `PaperC.AlignedRungeBridge.abs_channelVertexOffset_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:548` |
| `PaperC.AlignedRungeBridge.alignedShift_selected_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:188` |
| `PaperC.AlignedRungeBridge.base_add_alignedShift_eq_scaledOccurrenceLabel` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:388` |
| `PaperC.AlignedRungeBridge.candidate_abs_alignedShift_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:647` |
| `PaperC.AlignedRungeBridge.candidate_pairChannelError_bound` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:622` |
| `PaperC.AlignedRungeBridge.card_selectedComponentVertex` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:92` |
| `PaperC.AlignedRungeBridge.card_selectedComponentVertex_eq_two_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:470` |
| `PaperC.AlignedRungeBridge.card_selectedComponentVertex_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:522` |
| `PaperC.AlignedRungeBridge.prod_scaledOccurrenceLabel_component` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:307` |
| `PaperC.AlignedRungeBridge.prod_selectedComponentVertex_labels` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:114` |
| `PaperC.AlignedRungeBridge.prod_selected_scaledOccurrenceLabel` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:342` |
| `PaperC.AlignedRungeBridge.quantitative_runge_of_componentWord` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:672` |
| `PaperC.AlignedRungeBridge.selectedLeftCount_add_rightCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:161` |
| `PaperC.AlignedRungeBridge.selectedOccurrence_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:65` |
| `PaperC.AlignedRungeBridge.selected_base_product_square` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:410` |
| `PaperC.AlignedRungeBridge.two_le_card_selectedComponentVertex` | inconditionnel | — | — | — | `PaperC/Combinatorics/AlignedRungeBridge.lean:489` |
| `PaperC.AlignedRungeGrowth.rungeNumerics_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/AlignedRungeGrowth.lean:434` |
| `PaperC.AlignedRungeGrowth.rungeScale_lt_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/AlignedRungeGrowth.lean:218` |
| `PaperC.AlignedRungeGrowth.rungeScale_lt_of_log_budget` | inconditionnel | — | — | — | `PaperC/Asymptotics/AlignedRungeGrowth.lean:37` |
| `PaperC.AlignedRungeGrowth.six_mul_pow_lt_succ_pow_add_two` | inconditionnel | — | — | — | `PaperC/Asymptotics/AlignedRungeGrowth.lean:345` |
| `PaperC.AlignedRungeGrowth.translationRange_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/AlignedRungeGrowth.lean:368` |
| `PaperC.ArratiaGoldsteinGordonInput.bOne_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/ArratiaGoldsteinGordonInput.lean:200` |
| `PaperC.ArratiaGoldsteinGordonInput.bTwo_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/ArratiaGoldsteinGordonInput.lean:212` |
| `PaperC.ArratiaGoldsteinGordonInput.eventProbability_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/ArratiaGoldsteinGordonInput.lean:50` |
| `PaperC.ArratiaGoldsteinGordonInput.indicatorSumLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/ArratiaGoldsteinGordonInput.lean:238` |
| `PaperC.ArratiaGoldsteinGordonInput.jointMarginal_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/ArratiaGoldsteinGordonInput.lean:81` |
| `PaperC.ArratiaGoldsteinGordonInput.marginal_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/ArratiaGoldsteinGordonInput.lean:75` |
| `PaperC.ArratiaGoldsteinGordonInput.mem_closedNeighborhood` | inconditionnel | — | — | — | `PaperC/Probability/ArratiaGoldsteinGordonInput.lean:117` |
| `PaperC.ArratiaGoldsteinGordonInput.poissonParameter_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/ArratiaGoldsteinGordonInput.lean:94` |
| `PaperC.ArratiaGoldsteinGordonInput.self_mem_closedNeighborhood` | inconditionnel | — | — | — | `PaperC/Probability/ArratiaGoldsteinGordonInput.lean:126` |
| `PaperC.ArratiaGoldsteinGordonInput.totalVariationToPoisson_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/ArratiaGoldsteinGordonInput.lean:311` |
| `PaperC.BadStartCount.card_terminalBadStartIncidences_le` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:145` |
| `PaperC.BadStartCount.card_terminalBadStarts_cast_le_eulerProduct` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:199` |
| `PaperC.BadStartCount.card_terminalBadStarts_cast_le_exp` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:234` |
| `PaperC.BadStartCount.card_terminalBadStarts_cast_le_primeSensitive` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:550` |
| `PaperC.BadStartCount.card_terminalBadStarts_cast_le_primeSensitive_two_mul` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:576` |
| `PaperC.BadStartCount.card_terminalBadStarts_le` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:166` |
| `PaperC.BadStartCount.card_terminalBadStarts_le_incidences` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:98` |
| `PaperC.BadStartCount.image_fst_terminalBadStartIncidences` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:84` |
| `PaperC.BadStartCount.image_terminalBadIncidenceCode_subset` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:122` |
| `PaperC.BadStartCount.mem_terminalBadStartIncidences` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:75` |
| `PaperC.BadStartCount.mem_terminalBadStarts` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:61` |
| `PaperC.BadStartCount.mem_unitLargeKernelValues` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:45` |
| `PaperC.BadStartCount.terminalBadIncidenceCode_injective` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:110` |
| `PaperC.BadStartCount.unitLargeKernelValues_eq_bounded` | inconditionnel | — | — | — | `PaperC/Probability/BadStartCount.lean:180` |
| `PaperC.BadStartMass.hDefective_mono` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:52` |
| `PaperC.BadStartMass.largeOddKernel_eq_one_mono` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:60` |
| `PaperC.BadStartMass.mem_startDefectIndicesAt` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:45` |
| `PaperC.BadStartMass.relationRho_startSystem_eq_zero_of_not_bad` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:143` |
| `PaperC.BadStartMass.relationRho_startSystem_le_card_startDefectIndicesAt` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:98` |
| `PaperC.BadStartMass.startDefectIndicesAt_nonempty_iff` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:127` |
| `PaperC.BadStartMass.startDefectIndices_subset_at` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:83` |
| `PaperC.BadStartMass.startProbabilityMass_terminalBadStarts_le_two_cutoffs` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:341` |
| `PaperC.BadStartMass.startProbabilityMass_terminalBadStarts_le_weight` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:291` |
| `PaperC.BadStartMass.startProbability_eq_baseline_of_not_bad` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:168` |
| `PaperC.BadStartMass.startProbability_le_two_mul_defectWeight_div` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:248` |
| `PaperC.BadStartMass.startProbability_le_two_pow_defect_div` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:205` |
| `PaperC.BadStartMass.startProbability_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:194` |
| `PaperC.BadStartMass.terminalBadStarts_mono` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:68` |
| `PaperC.BadStartMass.two_pow_le_two_mul_two_pow_sub_one` | inconditionnel | — | — | — | `PaperC/Probability/BadStartMass.lean:234` |
| `PaperC.BadStartMassCritical.normalizedTerminalDefectContribution_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BadStartMassCritical.lean:187` |
| `PaperC.BadStartMassCritical.terminalBadStartProbabilityMass_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BadStartMassCritical.lean:249` |
| `PaperC.BadStartMassCritical.terminalBadStartProbabilityMass_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BadStartMassCritical.lean:297` |
| `PaperC.BadStartMassCritical.terminalDefectWeightMassNat_le_dyadicDefectMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/BadStartMassCritical.lean:51` |
| `PaperC.BadStartMassCritical.terminalDefectWeightMass_cast_le_dyadicDefectMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/BadStartMassCritical.lean:93` |
| `PaperC.BadStartMassCritical.terminalDefectWeightMass_eq_natCast` | inconditionnel | — | — | — | `PaperC/Asymptotics/BadStartMassCritical.lean:38` |
| `PaperC.BadStartMassCritical.terminalDefectWeightMass_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Asymptotics/BadStartMassCritical.lean:113` |
| `PaperC.BadStartMassCritical.terminalDefectWeightMass_uniformLittleOLinear` | inconditionnel | — | — | — | `PaperC/Asymptotics/BadStartMassCritical.lean:163` |
| `PaperC.BalasubramanianShoreyInput.gap_eq` | inconditionnel | — | — | — | `PaperC/Arithmetic/BalasubramanianShoreyInput.lean:36` |
| `PaperC.BalasubramanianShoreyInput.windowBound_of_balasubramanianShorey` | conditionnel | `BS93-Theorem-1` | `external` | `open` | `PaperC/Arithmetic/BalasubramanianShoreyInput.lean:120` |
| `PaperC.BalasubramanianShoreyMaximum.blockOddPart_isSmoothAt` | inconditionnel | — | — | — | `PaperC/Arithmetic/BalasubramanianShoreyMaximum.lean:107` |
| `PaperC.BalasubramanianShoreyMaximum.defectiveOffsets_card_lt_mu_eventually` | conditionnel | `BS93-Theorem-1` | `external` | `open` | `PaperC/Arithmetic/BalasubramanianShoreyMaximum.lean:312` |
| `PaperC.BalasubramanianShoreyMaximum.defectiveOffsets_denseSquareSubproduct` | inconditionnel | — | — | — | `PaperC/Arithmetic/BalasubramanianShoreyMaximum.lean:160` |
| `PaperC.BalasubramanianShoreyMaximum.defectiveProduct_decomposition` | inconditionnel | — | — | — | `PaperC/Arithmetic/BalasubramanianShoreyMaximum.lean:79` |
| `PaperC.BalasubramanianShoreyMaximum.defectiveWindow_card_le_complement_gap_eventually` | conditionnel | `BS93-Theorem-1` | `external` | `open` | `PaperC/Arithmetic/BalasubramanianShoreyMaximum.lean:352` |
| `PaperC.BalasubramanianShoreyMaximum.defectiveWindow_card_lt_mu_eventually` | conditionnel | `BS93-Theorem-1` | `external` | `open` | `PaperC/Arithmetic/BalasubramanianShoreyMaximum.lean:336` |
| `PaperC.BalasubramanianShoreyMaximum.eventually_two_le_mu` | inconditionnel | — | — | — | `PaperC/Arithmetic/BalasubramanianShoreyMaximum.lean:248` |
| `PaperC.BalasubramanianShoreyMaximum.mem_defectiveOffsets` | inconditionnel | — | — | — | `PaperC/Arithmetic/BalasubramanianShoreyMaximum.lean:49` |
| `PaperC.BalasubramanianShoreyMaximum.muRatio_tendsto_one` | inconditionnel | — | — | — | `PaperC/Arithmetic/BalasubramanianShoreyMaximum.lean:198` |
| `PaperC.BoundedRatioBadStarts.boundedTerminalBadStartCardEnvelope_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:303` |
| `PaperC.BoundedRatioBadStarts.boundedTerminalBadStartResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:283` |
| `PaperC.BoundedRatioBadStarts.boundedTerminalBadStarts_terminalCutoff_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:395` |
| `PaperC.BoundedRatioBadStarts.boundedTerminalBadStarts_terminalCutoff_uniformLittleO` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:489` |
| `PaperC.BoundedRatioBadStarts.boundedTerminalBadStarts_terminalCutoff_uniformLittleOLinear` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:432` |
| `PaperC.BoundedRatioBadStarts.card_boundedTerminalBadStartIncidences_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:116` |
| `PaperC.BoundedRatioBadStarts.card_boundedTerminalBadStarts_cast_le_eulerProduct` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:151` |
| `PaperC.BoundedRatioBadStarts.card_boundedTerminalBadStarts_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:135` |
| `PaperC.BoundedRatioBadStarts.card_boundedTerminalBadStarts_le_incidences` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:84` |
| `PaperC.BoundedRatioBadStarts.card_boundedTerminalBadStarts_terminalCutoff_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:319` |
| `PaperC.BoundedRatioBadStarts.card_boundedTerminalBadStarts_terminalPrimeCutoff_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:183` |
| `PaperC.BoundedRatioBadStarts.card_boundedTerminalBadStarts_terminalPrimeCutoff_le_readable` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:219` |
| `PaperC.BoundedRatioBadStarts.image_fst_boundedTerminalBadStartIncidences` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:70` |
| `PaperC.BoundedRatioBadStarts.image_terminalBadIncidenceCode_bounded_subset` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:95` |
| `PaperC.BoundedRatioBadStarts.mem_boundedTerminalBadStartIncidences` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:61` |
| `PaperC.BoundedRatioBadStarts.normalized_boundedTerminalBadStarts_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioBadStarts.lean:528` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.arithmeticKernelEquivalence_of_isCanonicallyNonaligned` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:157` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedIntrinsicTerminalSlack_eq_slack_add_canonicalRank` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:316` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedRankTerminalPredicate_iff_intrinsic` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:472` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedRankTerminalResidualMass_eq_sectorResidualMassNat` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:891` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedRankTerminalResidualMass_le_card_mul_weight` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:820` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedRatioSectorOf_eq_nonterminal_intrinsic_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:449` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedRatioSectorOf_eq_nonterminal_rank_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:409` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedRatioSectorOf_eq_terminal_intrinsic_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:429` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedRatioSectorOf_eq_terminal_rank_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:390` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedRatioSectorPairs_nonterminal_eq_intrinsicNonterminalPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:621` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedRatioSectorPairs_nonterminal_eq_rankNonterminalPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:595` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedRatioSectorPairs_terminal_eq_intrinsicTerminalPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:608` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedRatioSectorPairs_terminal_eq_rankTerminalPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:582` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.boundedTerminalSlack_le_intrinsic` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:221` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.bounded_terminal_component_count` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:942` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.canonicalResidualComponentCount_le_runLength` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:127` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.card_boundedRankTerminalPairs_eq_sum_partnerFibers` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:835` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.card_boundedRankTerminalPairs_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:873` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.card_boundedRankTerminalPairs_le_firstStarts_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:851` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.card_canonicalResidualComponents_eq_runLength_sub_slack` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:923` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.intrinsicBudget_iff_slack_add_rank_budget` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:335` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.intrinsicSlack_le_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:236` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.le_terminalRankBudget_iff_cast_le_scale` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:109` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.mem_boundedIntrinsicNonterminalPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:570` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.mem_boundedIntrinsicTerminalPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:558` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.mem_boundedRankNonterminalPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:547` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.mem_boundedRankTerminalPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:536` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.mem_rankNonterminalPairs_iff_mem_intrinsicNonterminalPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:647` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.mem_rankTerminalPairs_iff_mem_intrinsicTerminalPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:634` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.pairSigma_eq_zero_of_isCanonicallyNonaligned` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:682` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.pairSigma_eq_zero_of_mem_intrinsicNonterminal` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:733` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.pairTau_add_budget_succ_le_corrected_runLength` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:718` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.pairTau_add_canonicalRank_eq_corrected_add_components` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:285` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.pairTau_eq_corrected_add_components_sub_canonicalRank` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:258` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.pairTau_le_corrected_add_components` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:186` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.pairTau_le_runLength_add_two_of_mem_rankTerminal` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:694` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.residualWeight_eq_two_pow_sub_one_of_mem_rankTerminal` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:802` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.residualWeight_mul_two_pow_budget_succ_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:751` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.runLength_le_boundedRatioCutoff` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:141` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.terminalRankBudget_cast_le_scale` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:102` |
| `PaperC.BoundedRatioCanonicalTerminalPopulation.terminalRankScale_nonneg` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioCanonicalTerminalPopulation.lean:92` |
| `PaperC.BoundedRatioComponentHosts.boundedComponentHosts_subset_shapeUnion` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:1123` |
| `PaperC.BoundedRatioComponentHosts.card_boundedComponentHosts_le_of_shapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:1155` |
| `PaperC.BoundedRatioComponentHosts.card_boundedOffsetShapes_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:227` |
| `PaperC.BoundedRatioComponentHosts.card_componentLeftOffsets` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:87` |
| `PaperC.BoundedRatioComponentHosts.card_componentOffsets` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:159` |
| `PaperC.BoundedRatioComponentHosts.card_componentRightOffsets` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:110` |
| `PaperC.BoundedRatioComponentHosts.card_denseCanonicalCorePairs_le_of_shapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:1232` |
| `PaperC.BoundedRatioComponentHosts.card_smallSupports_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:209` |
| `PaperC.BoundedRatioComponentHosts.componentLeftProduct_eq_offsetProduct` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:505` |
| `PaperC.BoundedRatioComponentHosts.componentLeftShift_injective` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:542` |
| `PaperC.BoundedRatioComponentHosts.componentNormalizedEquation_atMost_of_evertseSilverman` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:645` |
| `PaperC.BoundedRatioComponentHosts.componentOffsetShape_mem` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:250` |
| `PaperC.BoundedRatioComponentHosts.componentOffsets_nonempty` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:133` |
| `PaperC.BoundedRatioComponentHosts.componentRightProduct_eq_offsetProduct` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:517` |
| `PaperC.BoundedRatioComponentHosts.componentRightShift_injective` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:548` |
| `PaperC.BoundedRatioComponentHosts.denseCanonicalCorePairs_subset_boundedComponentHosts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:1213` |
| `PaperC.BoundedRatioComponentHosts.exists_componentNormalizedSolution_with_height` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:598` |
| `PaperC.BoundedRatioComponentHosts.exists_componentRightFiber_with_height` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:900` |
| `PaperC.BoundedRatioComponentHosts.mem_boundedComponentHosts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:281` |
| `PaperC.BoundedRatioComponentHosts.mem_boundedComponentHostsOfShape` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:1105` |
| `PaperC.BoundedRatioComponentHosts.mem_boundedComponentHosts_of_rational_density` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:294` |
| `PaperC.BoundedRatioComponentHosts.mem_boundedOffsetShapes` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:185` |
| `PaperC.BoundedRatioComponentHosts.mem_componentLeftOffsets` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:69` |
| `PaperC.BoundedRatioComponentHosts.mem_componentRightOffsets` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:78` |
| `PaperC.BoundedRatioComponentHosts.mem_denseCanonicalCorePairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:1201` |
| `PaperC.BoundedRatioComponentHosts.normalizedOffsetDegreeTwo_atMost_of_pell` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:966` |
| `PaperC.BoundedRatioComponentHosts.normalizedOffsetDegreeTwo_polynomialBox_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:1011` |
| `PaperC.BoundedRatioComponentHosts.offsetProductNatFiber_degree_one_atMost` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:876` |
| `PaperC.BoundedRatioComponentHosts.offsetShiftOfCard_injective` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:695` |
| `PaperC.BoundedRatioComponentHosts.offsetShift_injective` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:354` |
| `PaperC.BoundedRatioComponentHosts.oneOffsetFiber_atMost_sqrt` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:825` |
| `PaperC.BoundedRatioComponentHosts.oneOffsetFiber_maps_to_oneShift` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:773` |
| `PaperC.BoundedRatioComponentHosts.oneOffsetToOneShift_injective_on` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:798` |
| `PaperC.BoundedRatioComponentHosts.reindexedOffsetNormalizedEquation_degree_two_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:941` |
| `PaperC.BoundedRatioComponentHosts.reindexedOffsetNormalizedEquation_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:730` |
| `PaperC.BoundedRatioComponentHosts.shiftedProduct_componentLeftShift` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:556` |
| `PaperC.BoundedRatioComponentHosts.shiftedProduct_componentRightShift` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:569` |
| `PaperC.BoundedRatioComponentHosts.shiftedProduct_offsetShift` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:365` |
| `PaperC.BoundedRatioComponentHosts.shiftedProduct_offsetShiftOfCard` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentHosts.lean:708` |
| `PaperC.BoundedRatioComponentNormalization.componentLeftProduct_le_cutoff_pow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:423` |
| `PaperC.BoundedRatioComponentNormalization.componentLeftProduct_le_cutoff_pow_card` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:345` |
| `PaperC.BoundedRatioComponentNormalization.componentLeftProduct_pos` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:249` |
| `PaperC.BoundedRatioComponentNormalization.componentProduct_labels_eq_componentVertexProduct` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:100` |
| `PaperC.BoundedRatioComponentNormalization.componentRightProduct_le_cutoff_pow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:437` |
| `PaperC.BoundedRatioComponentNormalization.componentRightProduct_le_cutoff_pow_card` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:367` |
| `PaperC.BoundedRatioComponentNormalization.componentRightProduct_pos` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:257` |
| `PaperC.BoundedRatioComponentNormalization.componentVertexProduct_eq_left_mul_right` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:86` |
| `PaperC.BoundedRatioComponentNormalization.componentVertexProduct_le_cutoff_pow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:451` |
| `PaperC.BoundedRatioComponentNormalization.componentVertexProduct_le_cutoff_pow_card` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:389` |
| `PaperC.BoundedRatioComponentNormalization.exists_component_square_class_equation` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:470` |
| `PaperC.BoundedRatioComponentNormalization.exists_left_and_right_vertices` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:122` |
| `PaperC.BoundedRatioComponentNormalization.exists_normalized_component_equation` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:506` |
| `PaperC.BoundedRatioComponentNormalization.exists_normalized_component_equation_with_height` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:549` |
| `PaperC.BoundedRatioComponentNormalization.leftOccurrenceFactor_le_cutoff` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:265` |
| `PaperC.BoundedRatioComponentNormalization.leftOccurrenceFactor_pos` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:223` |
| `PaperC.BoundedRatioComponentNormalization.left_mul_rightOccurrenceFactor` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:77` |
| `PaperC.BoundedRatioComponentNormalization.one_le_boundedRatioCutoff_of_pair` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:411` |
| `PaperC.BoundedRatioComponentNormalization.one_le_componentLeftCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:183` |
| `PaperC.BoundedRatioComponentNormalization.one_le_componentRightCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:202` |
| `PaperC.BoundedRatioComponentNormalization.rightOccurrenceFactor_le_cutoff` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:295` |
| `PaperC.BoundedRatioComponentNormalization.rightOccurrenceFactor_pos` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:236` |
| `PaperC.BoundedRatioComponentNormalization.twoStartCompleteVertexLabel_le_cutoff` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioComponentNormalization.lean:325` |
| `PaperC.BoundedRatioCorrectedDefectEnvelope.canonicalCorrectedDefectCount_le_max` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioCorrectedDefectEnvelope.lean:269` |
| `PaperC.BoundedRatioCorrectedDefectEnvelope.criticalWindow_transport_of_sq_bounds` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioCorrectedDefectEnvelope.lean:38` |
| `PaperC.BoundedRatioCorrectedDefectEnvelope.four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioCorrectedDefectEnvelope.lean:473` |
| `PaperC.BoundedRatioCorrectedDefectEnvelope.log_div_loglog_le_four_of_sq_bounds` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioCorrectedDefectEnvelope.lean:98` |
| `PaperC.BoundedRatioCorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioCorrectedDefectEnvelope.lean:299` |
| `PaperC.BoundedRatioCorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount_log_bound_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioCorrectedDefectEnvelope.lean:335` |
| `PaperC.BoundedRatioCorrectedDefectEnvelope.pointwise_all_intervals_of_sq_bounds` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioCorrectedDefectEnvelope.lean:189` |
| `PaperC.BoundedRatioDenseQuantitative.criticalSqrtCoefficient_pos` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioDenseQuantitative.lean:35` |
| `PaperC.BoundedRatioDenseQuantitative.denseQuantitativeConstant_pos` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioDenseQuantitative.lean:47` |
| `PaperC.BoundedRatioDenseQuantitative.exists_highDensityIntrinsicNonterminalMassEnvelope_quantitative` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioDenseQuantitative.lean:370` |
| `PaperC.BoundedRatioDenseQuantitative.highDensityIntrinsicNonterminalMassEnvelope_uniformBigO_quantitative` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioDenseQuantitative.lean:244` |
| `PaperC.BoundedRatioDenseQuantitative.sqrtLog_div_loglog_le_heightScale_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioDenseQuantitative.lean:65` |
| `PaperC.BoundedRatioDistinctKernelTwoDefects.card_squarefreeSmoothUpTo_le_smoothKernelChebyshevEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioDistinctKernelTwoDefects.lean:281` |
| `PaperC.BoundedRatioDistinctKernelTwoDefects.distinctKernelDefectBases_subset_distinctPaired` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioDistinctKernelTwoDefects.lean:82` |
| `PaperC.BoundedRatioDistinctKernelTwoDefects.distinctKernelDefectBases_uniformSubpolynomial` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioDistinctKernelTwoDefects.lean:615` |
| `PaperC.BoundedRatioDistinctKernelTwoDefects.distinctKernelTwoDefectResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioDistinctKernelTwoDefects.lean:423` |
| `PaperC.BoundedRatioDistinctKernelTwoDefects.expLogLogBound_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioDistinctKernelTwoDefects.lean:394` |
| `PaperC.BoundedRatioDistinctKernelTwoDefects.generalizedPell_implies_card_distinctKernelDefectBases_le_residual` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioDistinctKernelTwoDefects.lean:457` |
| `PaperC.BoundedRatioDistinctKernelTwoDefects.generalizedPell_implies_distinctKernelDefectBases_polynomial_bound` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioDistinctKernelTwoDefects.lean:183` |
| `PaperC.BoundedRatioDistinctKernelTwoDefects.mem_distinctKernelDefectBases` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioDistinctKernelTwoDefects.lean:63` |
| `PaperC.BoundedRatioDistinctKernelTwoDefects.smoothKernelChebyshevEnvelope_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioDistinctKernelTwoDefects.lean:375` |
| `PaperC.BoundedRatioElementaryQuantitative.alignedDeepCore_dyadic_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:326` |
| `PaperC.BoundedRatioElementaryQuantitative.alignedDeepCore_dyadic_uniformBigO_of_scale` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:294` |
| `PaperC.BoundedRatioElementaryQuantitative.alignedDeepCore_dyadic_uniformBigO_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:340` |
| `PaperC.BoundedRatioElementaryQuantitative.shallowCore_dyadic_uniformThirtyOneSixteenths` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:275` |
| `PaperC.BoundedRatioElementaryQuantitative.shallowCore_uniformThirtyOneSixteenthsInBoundedRatioWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:243` |
| `PaperC.BoundedRatioElementaryQuantitative.smallCanonicalHeight_dyadic_uniformSevenFourths` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:225` |
| `PaperC.BoundedRatioElementaryQuantitative.smallCanonicalHeight_uniformSevenFourthsInBoundedRatioWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:193` |
| `PaperC.BoundedRatioElementaryQuantitative.smallPrimeProduct_dyadic_uniformSevenFourths` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:169` |
| `PaperC.BoundedRatioElementaryQuantitative.systematicMass_dyadic_uniformThreeHalves` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:154` |
| `PaperC.BoundedRatioElementaryQuantitative.systematicMass_uniformThreeHalvesInBoundedRatioWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:124` |
| `PaperC.BoundedRatioElementaryQuantitative.terminal_dyadic_uniformSevenFourths` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:357` |
| `PaperC.BoundedRatioElementaryQuantitative.uniformRationalPowerInBoundedRatioWindow_dyadic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioElementaryQuantitative.lean:36` |
| `PaperC.BoundedRatioFixedJBadStarts.fixedJWindowConstant_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:36` |
| `PaperC.BoundedRatioFixedJBadStarts.fixedJ_boundedRatio_bounds` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:74` |
| `PaperC.BoundedRatioFixedJBadStarts.fixedJ_division_upper_bound` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:45` |
| `PaperC.BoundedRatioFixedJBadStarts.fixedJ_uniformLittleOOne_of_boundedRatio` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:184` |
| `PaperC.BoundedRatioFixedJBadStarts.inRunLengthWindow_div_twoPow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:95` |
| `PaperC.BoundedRatioFixedJBadStarts.retainedBadStartProbabilityMass_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:315` |
| `PaperC.BoundedRatioFixedJBadStarts.retainedFullStartMean_eq_goodParameter_add_badMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:333` |
| `PaperC.BoundedRatioFixedJBadStarts.retainedFullStartMean_eq_length_sub_badCard_add_badMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:350` |
| `PaperC.BoundedRatioFixedJBadStarts.retainedFullStartMean_sub_lengthParameter_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:379` |
| `PaperC.BoundedRatioFixedJBadStarts.retainedFullStartMean_sub_lengthParameter_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:408` |
| `PaperC.BoundedRatioFixedJBadStarts.retainedTerminalBadStarts_normalized_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:224` |
| `PaperC.BoundedRatioFixedJBadStarts.retainedTerminalDefectWeightMass_div_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:262` |
| `PaperC.BoundedRatioFixedJBadStarts.retainedTerminalDefectWeightMass_normalized_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioFixedJBadStarts.lean:243` |
| `PaperC.BoundedRatioGeometry.boundedCanonicalPairWeight_le_coverWeights` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:1056` |
| `PaperC.BoundedRatioGeometry.boundedChannelFirstCoordinates_subset_modClass` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:462` |
| `PaperC.BoundedRatioGeometry.boundedChannelSecondCoordinates_subset_modClass` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:498` |
| `PaperC.BoundedRatioGeometry.boundedChannelStartPairs_card_le_firstStep` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:534` |
| `PaperC.BoundedRatioGeometry.boundedChannelStartPairs_card_le_maxStep` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:597` |
| `PaperC.BoundedRatioGeometry.boundedChannelStartPairs_card_le_secondStep` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:564` |
| `PaperC.BoundedRatioGeometry.boundedDyadicCover_eq` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:178` |
| `PaperC.BoundedRatioGeometry.boundedHeightTwoMass_four_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:1390` |
| `PaperC.BoundedRatioGeometry.boundedHeightTwoMass_two_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:1382` |
| `PaperC.BoundedRatioGeometry.boundedRatioBlock_subset_dyadic_union` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:204` |
| `PaperC.BoundedRatioGeometry.boundedRatio_canonicalRationalCode_eq` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:669` |
| `PaperC.BoundedRatioGeometry.boundedRatio_channel_height_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:640` |
| `PaperC.BoundedRatioGeometry.boundedRatio_interpolation` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:704` |
| `PaperC.BoundedRatioGeometry.boundedRatio_rationalCode_finrank` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:618` |
| `PaperC.BoundedRatioGeometry.boundedRatio_reducedChannelCandidates_card_le_one` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:657` |
| `PaperC.BoundedRatioGeometry.boundedRatio_weightedChannelGeometry_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:1402` |
| `PaperC.BoundedRatioGeometry.boundedRationalMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:1162` |
| `PaperC.BoundedRatioGeometry.boundedRationalMass_two_le_common` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:1261` |
| `PaperC.BoundedRatioGeometry.card_boundedHeightTwoBackwardCover_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:772` |
| `PaperC.BoundedRatioGeometry.card_boundedHeightTwoForwardCover_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:745` |
| `PaperC.BoundedRatioGeometry.card_boundedHeightTwoPairCover_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:802` |
| `PaperC.BoundedRatioGeometry.card_boundedLargeChannelPairCoverAtHeight_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:930` |
| `PaperC.BoundedRatioGeometry.card_boundedLargeChannelPairCoverAtRatio_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:879` |
| `PaperC.BoundedRatioGeometry.card_boundedLargeChannelPairCover_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:967` |
| `PaperC.BoundedRatioGeometry.card_boundedRatioBlock` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:57` |
| `PaperC.BoundedRatioGeometry.card_boundedRatioBlock_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:62` |
| `PaperC.BoundedRatioGeometry.card_boundedRatioBlock_modClass_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:282` |
| `PaperC.BoundedRatioGeometry.card_boundedRatioBlock_modClass_cast_le_kappa` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:294` |
| `PaperC.BoundedRatioGeometry.card_boundedRatioBlock_modClass_le_one_add_div` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:227` |
| `PaperC.BoundedRatioGeometry.card_boundedRatioPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:80` |
| `PaperC.BoundedRatioGeometry.card_boundedRatioPairs_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:85` |
| `PaperC.BoundedRatioGeometry.card_separatedBoundedRatioPairs_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:106` |
| `PaperC.BoundedRatioGeometry.channelTranslationParameter_bounds` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:381` |
| `PaperC.BoundedRatioGeometry.channelTranslationParameter_unique` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:366` |
| `PaperC.BoundedRatioGeometry.exists_channelTranslationParameter` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:332` |
| `PaperC.BoundedRatioGeometry.exists_mem_dyadicShell` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:143` |
| `PaperC.BoundedRatioGeometry.fst_injOn_boundedChannelStartPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:415` |
| `PaperC.BoundedRatioGeometry.mem_boundedChannelStartPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:318` |
| `PaperC.BoundedRatioGeometry.mem_boundedDyadicShell` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:129` |
| `PaperC.BoundedRatioGeometry.mem_boundedRatioBlock` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:51` |
| `PaperC.BoundedRatioGeometry.mem_boundedRatioPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:73` |
| `PaperC.BoundedRatioGeometry.mem_dyadicShell` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:119` |
| `PaperC.BoundedRatioGeometry.mem_separatedBoundedRatioPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:98` |
| `PaperC.BoundedRatioGeometry.nontrivialChannelHeights_card_le_three_mul_add_one` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:733` |
| `PaperC.BoundedRatioGeometry.pair_mem_boundedHeightTwoPairCover_of_choice` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:823` |
| `PaperC.BoundedRatioGeometry.pair_mem_boundedLargeChannelPairCover_of_choice` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:1007` |
| `PaperC.BoundedRatioGeometry.self_le_two_pow` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:163` |
| `PaperC.BoundedRatioGeometry.snd_injOn_boundedChannelStartPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioGeometry.lean:438` |
| `PaperC.BoundedRatioIntrinsicTerminalPopulation.boundedIntrinsicTerminalResidualMass_eq_sectorResidualMassNat` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioIntrinsicTerminalPopulation.lean:150` |
| `PaperC.BoundedRatioIntrinsicTerminalPopulation.boundedIntrinsicTerminalResidualMass_le_card_mul_weight` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioIntrinsicTerminalPopulation.lean:79` |
| `PaperC.BoundedRatioIntrinsicTerminalPopulation.card_boundedIntrinsicTerminalPairs_eq_sum_partnerFibers` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioIntrinsicTerminalPopulation.lean:94` |
| `PaperC.BoundedRatioIntrinsicTerminalPopulation.card_boundedIntrinsicTerminalPairs_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioIntrinsicTerminalPopulation.lean:132` |
| `PaperC.BoundedRatioIntrinsicTerminalPopulation.card_boundedIntrinsicTerminalPairs_le_firstStarts_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioIntrinsicTerminalPopulation.lean:110` |
| `PaperC.BoundedRatioIntrinsicTerminalPopulation.pairTau_le_runLength_add_two_of_mem_intrinsicTerminal` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioIntrinsicTerminalPopulation.lean:43` |
| `PaperC.BoundedRatioIntrinsicTerminalPopulation.residualWeight_eq_two_pow_sub_one_of_mem_intrinsicTerminal` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioIntrinsicTerminalPopulation.lean:64` |
| `PaperC.BoundedRatioManyDefectsAssembly.manyDefectsSectorStability` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsAssembly.lean:111` |
| `PaperC.BoundedRatioManyDefectsAssembly.manyDefectsSector_rates` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsAssembly.lean:36` |
| `PaperC.BoundedRatioManyDefectsAssembly.manyDefectsSector_uniformLittleO` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsAssembly.lean:94` |
| `PaperC.BoundedRatioManyDefectsAssembly.manyDefectsSector_uniformThreeHalves` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsAssembly.lean:78` |
| `PaperC.BoundedRatioManyDefectsDegreeAssembly.degreeAssemblyEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeAssembly.lean:106` |
| `PaperC.BoundedRatioManyDefectsDegreeAssembly.degreeAssemblyEnvelope_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeAssembly.lean:143` |
| `PaperC.BoundedRatioManyDefectsDegreeAssembly.degreeOneFixedFiberEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeAssembly.lean:57` |
| `PaperC.BoundedRatioManyDefectsDegreeAssembly.manyDefectsSector_rates_of_degreeAssembly` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeAssembly.lean:194` |
| `PaperC.BoundedRatioManyDefectsDegreeAssembly.manyDefectsSector_uniformLittleO_of_degreeAssembly` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeAssembly.lean:721` |
| `PaperC.BoundedRatioManyDefectsDegreeAssembly.manyDefectsSector_uniformThreeHalves_of_degreeAssembly` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeAssembly.lean:674` |
| `PaperC.BoundedRatioManyDefectsDegreeAssembly.one_le_degreeOneFixedFiberEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeAssembly.lean:69` |
| `PaperC.BoundedRatioManyDefectsDegreeTwoSum.degreeTwoFixedFiberResidual_eventually_one_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeTwoSum.lean:307` |
| `PaperC.BoundedRatioManyDefectsDegreeTwoSum.degreeTwoFixedFiberResidual_one_le_of_large` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeTwoSum.lean:270` |
| `PaperC.BoundedRatioManyDefectsDegreeTwoSum.degreeTwoFixedFiberResidual_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeTwoSum.lean:197` |
| `PaperC.BoundedRatioManyDefectsDegreeTwoSum.degreeTwoFixedFiberResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeTwoSum.lean:169` |
| `PaperC.BoundedRatioManyDefectsDegreeTwoSum.degreeTwoSignedDivisorEnvelope_one_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeTwoSum.lean:51` |
| `PaperC.BoundedRatioManyDefectsDegreeTwoSum.degreeTwoSignedDivisorEnvelope_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeTwoSum.lean:137` |
| `PaperC.BoundedRatioManyDefectsDegreeTwoSum.generalizedPell_implies_card_left_degreeTwoFiber_le_residual` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeTwoSum.lean:368` |
| `PaperC.BoundedRatioManyDefectsDegreeTwoSum.generalizedPell_implies_card_right_degreeTwoFiber_le_residual` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeTwoSum.lean:528` |
| `PaperC.BoundedRatioManyDefectsDegreeTwoSum.signedDivisorCount_cast_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsDegreeTwoSum.lean:77` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.card_leftBaseShapeFiber_degree_at_least_three_le_common` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:937` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.card_leftBaseShapeFiber_degree_at_least_three_le_residual` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:719` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.card_rightBaseShapeFiber_degree_at_least_three_le_common` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:963` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.card_rightBaseShapeFiber_degree_at_least_three_le_residual` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:787` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.evertseBadHeightExponent_pos` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:56` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.evertseCommonFixedFiberResidual_eventually_one_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:181` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.evertseCommonFixedFiberResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:1103` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.evertseFixedFiberResidual_le_common` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:874` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.evertsePolynomialHeightEnvelope_terminalLabelCutoff_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:991` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.explicitBound_le_evertsePolynomialHeightEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:85` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.leftEvertseBadInteger_le_cutoffPow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:611` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.one_le_evertseCommonFixedFiberResidual` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:168` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.one_le_evertseFixedFiberResidual` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:129` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.one_le_evertsePolynomialHeightEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:71` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.pairDifferenceProduct_offsetShift_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:294` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.pairDifferenceProduct_offsetShift_le_cutoffPow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:340` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.rightEvertseBadInteger_le_cutoffPow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:664` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.two_pow_smallPrimesUpTo_cast_le_smoothKernelChebyshevEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:195` |
| `PaperC.BoundedRatioManyDefectsEvertseSum.two_pow_smallPrimesUpTo_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsEvertseSum.lean:1073` |
| `PaperC.BoundedRatioManyDefectsFibers.card_activeManyDefects_le_explicit_of_distinctBaseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:686` |
| `PaperC.BoundedRatioManyDefectsFibers.card_leftBaseShapeFiber_le_width` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:223` |
| `PaperC.BoundedRatioManyDefectsFibers.card_leftTwoDefectActiveHosts_le_of_baseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:438` |
| `PaperC.BoundedRatioManyDefectsFibers.card_rightBaseShapeFiber_le_width` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:279` |
| `PaperC.BoundedRatioManyDefectsFibers.card_rightTwoDefectActiveHosts_le_of_baseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:489` |
| `PaperC.BoundedRatioManyDefectsFibers.componentShapeEnvelope_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:774` |
| `PaperC.BoundedRatioManyDefectsFibers.leftTwoDefectActiveHosts_subset_baseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:350` |
| `PaperC.BoundedRatioManyDefectsFibers.manyDefectsSectorStability_of_baseShapeFiberEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:1001` |
| `PaperC.BoundedRatioManyDefectsFibers.manyDefectsSector_uniformLittleO_of_baseShapeFiberEnvelope` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:840` |
| `PaperC.BoundedRatioManyDefectsFibers.mem_leftBaseShapeFiber` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:192` |
| `PaperC.BoundedRatioManyDefectsFibers.mem_rightBaseShapeFiber` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:205` |
| `PaperC.BoundedRatioManyDefectsFibers.mem_twoDefectBaseCover` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:59` |
| `PaperC.BoundedRatioManyDefectsFibers.orientedHostCover_card_le_explicit_of_distinctBaseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:613` |
| `PaperC.BoundedRatioManyDefectsFibers.orientedHostCover_card_le_of_baseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:543` |
| `PaperC.BoundedRatioManyDefectsFibers.orientedHostCover_card_le_of_distinctBaseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:577` |
| `PaperC.BoundedRatioManyDefectsFibers.orientedHostCover_card_le_trivial_width` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:662` |
| `PaperC.BoundedRatioManyDefectsFibers.rightTwoDefectActiveHosts_subset_baseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:393` |
| `PaperC.BoundedRatioManyDefectsFibers.sectorResidualMassNat_le_explicit_of_distinctBaseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:716` |
| `PaperC.BoundedRatioManyDefectsFibers.shiftedBase_mem_twoDefectBaseCover_of_two_defects` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:86` |
| `PaperC.BoundedRatioManyDefectsFibers.twoDefectBaseCover_eq_distinctKernel` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:154` |
| `PaperC.BoundedRatioManyDefectsFibers.twoDefect_highZone_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:799` |
| `PaperC.BoundedRatioManyDefectsFibers.uniformSubpolynomialOn_pow_fixed` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFibers.lean:752` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_divisorsAntidiagonal_eq_card_divisors` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1221` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_int_divisorsAntidiag_natCast` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1212` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_int_divisorsAntidiag_natCast_eq_two_mul_divisors` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1248` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftBaseShapeFiber_degree_at_least_three` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:2119` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftBaseShapeFiber_degree_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:660` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftBaseShapeFiber_degree_one_cast_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:786` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftBaseShapeFiber_degree_two_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1570` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftBaseShapeFiber_degree_two_of_pell_boxes` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1480` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftBaseShapeFiber_degree_two_polynomial_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1909` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftBaseShapeFiber_le_of_fixedSquareClassCounts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:506` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftBaseShapeFiber_le_sum_fixedSquareClassCounts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:580` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftFixedSquareClassFiber_degree_at_least_three` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:2070` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftFixedSquareClassFiber_degree_two_of_pell` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1405` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftFixedSquareClassFiber_degree_two_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1445` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_leftFixedSquareClassFiber_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:438` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightBaseShapeFiber_degree_at_least_three` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:2150` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightBaseShapeFiber_degree_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:686` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightBaseShapeFiber_degree_one_cast_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:829` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightBaseShapeFiber_degree_two_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1630` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightBaseShapeFiber_degree_two_of_pell_boxes` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1523` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightBaseShapeFiber_degree_two_polynomial_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1969` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightBaseShapeFiber_le_of_fixedSquareClassCounts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:541` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightBaseShapeFiber_le_sum_fixedSquareClassCounts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:615` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightFixedSquareClassFiber_degree_at_least_three` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:2092` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightFixedSquareClassFiber_degree_two_of_pell` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1425` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightFixedSquareClassFiber_degree_two_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1460` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.card_rightFixedSquareClassFiber_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:472` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.degreeOneFixedFiberEnvelope_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:725` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.degreeTwoFactorPair_injective` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1255` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.leftBaseShapeFiber_subset_squareClassUnion` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:177` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.leftFixedSquareClassSolution_injective_on` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:374` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.leftFixedSquareClassSolution_mem` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:279` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.leftNormalizedCoefficient_pos` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:87` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.mem_leftFixedSquareClassFiber` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:150` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.mem_rightFixedSquareClassFiber` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:163` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.natSolutionToInt_injective` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:877` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.offsetProductNatFiber_atMost_of_evertseSilverman` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:2030` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.offsetProductNatFiber_degree_two_atMost_of_pell` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1020` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.offsetProductNatFiber_degree_two_one_atMost_divisors` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1341` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.offsetProductNatFiber_degree_two_one_atMost_two_mul_divisors` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1376` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.offsetProductNatFiber_degree_two_polynomialBox_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:1102` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.rightBaseShapeFiber_subset_squareClassUnion` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:211` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.rightFixedSquareClassSolution_injective_on` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:405` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.rightFixedSquareClassSolution_mem` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:326` |
| `PaperC.BoundedRatioManyDefectsFixedFibers.rightNormalizedCoefficient_pos` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsFixedFibers.lean:94` |
| `PaperC.BoundedRatioManyDefectsRealFibers.card_leftTwoDefectActiveHosts_cast_le_of_baseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsRealFibers.lean:37` |
| `PaperC.BoundedRatioManyDefectsRealFibers.card_rightTwoDefectActiveHosts_cast_le_of_baseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsRealFibers.lean:90` |
| `PaperC.BoundedRatioManyDefectsRealFibers.manyDefectsSectorStability_of_baseShapeFiberRealEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsRealFibers.lean:447` |
| `PaperC.BoundedRatioManyDefectsRealFibers.manyDefectsSector_rates_of_baseShapeFiberRealEnvelope` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsRealFibers.lean:218` |
| `PaperC.BoundedRatioManyDefectsRealFibers.manyDefectsSector_uniformLittleO_of_baseShapeFiberRealEnvelope` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsRealFibers.lean:413` |
| `PaperC.BoundedRatioManyDefectsRealFibers.manyDefectsSector_uniformThreeHalves_of_baseShapeFiberRealEnvelope` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioManyDefectsRealFibers.lean:377` |
| `PaperC.BoundedRatioManyDefectsRealFibers.orientedHostCover_cast_le_explicit_of_distinctBaseShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsRealFibers.lean:146` |
| `PaperC.BoundedRatioManyDefectsReduction.activeHostCount_le_orientedHostCoverCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:671` |
| `PaperC.BoundedRatioManyDefectsReduction.activeHosts_subset_left_union_right` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:464` |
| `PaperC.BoundedRatioManyDefectsReduction.active_host_certificates` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:387` |
| `PaperC.BoundedRatioManyDefectsReduction.active_host_certificates_of_deepCore_rational_density` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:353` |
| `PaperC.BoundedRatioManyDefectsReduction.active_host_certificates_of_rational_density` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:319` |
| `PaperC.BoundedRatioManyDefectsReduction.canonicalCoreExponent_le_height_add_half_maxDefect` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:538` |
| `PaperC.BoundedRatioManyDefectsReduction.card_activeHosts_le_oriented_sum` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:484` |
| `PaperC.BoundedRatioManyDefectsReduction.deepCore_density_of_mem_active` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:149` |
| `PaperC.BoundedRatioManyDefectsReduction.exists_bounded_component_of_mem_active` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:297` |
| `PaperC.BoundedRatioManyDefectsReduction.exists_bounded_component_of_mem_active_of_deepCore_rational_density` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:269` |
| `PaperC.BoundedRatioManyDefectsReduction.exists_bounded_component_of_rational_density` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:216` |
| `PaperC.BoundedRatioManyDefectsReduction.isCanonicallyNonaligned_of_mem_active` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:100` |
| `PaperC.BoundedRatioManyDefectsReduction.linearResidualWeight_le_envelope_of_mem_active` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:585` |
| `PaperC.BoundedRatioManyDefectsReduction.manyDefectsSectorStability_of_orientedHostEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:1038` |
| `PaperC.BoundedRatioManyDefectsReduction.manyDefectsSector_rates_of_orientedHostEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:877` |
| `PaperC.BoundedRatioManyDefectsReduction.manyDefectsSector_uniformLittleO_of_orientedHostEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:1008` |
| `PaperC.BoundedRatioManyDefectsReduction.manyDefectsSector_uniformThreeHalves_of_orientedHostEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:982` |
| `PaperC.BoundedRatioManyDefectsReduction.manyDefects_tests_of_mem_active` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:62` |
| `PaperC.BoundedRatioManyDefectsReduction.mem_leftTwoDefectActiveHosts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:436` |
| `PaperC.BoundedRatioManyDefectsReduction.mem_rightTwoDefectActiveHosts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:450` |
| `PaperC.BoundedRatioManyDefectsReduction.pairSigma_eq_zero_of_mem_active` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:115` |
| `PaperC.BoundedRatioManyDefectsReduction.pairTau_le_correctedDefect_add_componentCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:513` |
| `PaperC.BoundedRatioManyDefectsReduction.rational_deepCore_density_of_mem_active` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:170` |
| `PaperC.BoundedRatioManyDefectsReduction.residualWeightEnvelope_uniformLinear` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:767` |
| `PaperC.BoundedRatioManyDefectsReduction.sectorResidualMassNat_cast_le_orientedHostCover_mul_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:682` |
| `PaperC.BoundedRatioManyDefectsReduction.sectorResidualMassNat_le_active_card_mul_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:617` |
| `PaperC.BoundedRatioManyDefectsReduction.three_le_correctedDefectCount_of_mem_active` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:133` |
| `PaperC.BoundedRatioManyDefectsReduction.two_defects_in_one_window_of_mem_active` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:191` |
| `PaperC.BoundedRatioManyDefectsReduction.two_pow_half_maxDefect_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioManyDefectsReduction.lean:720` |
| `PaperC.BoundedRatioNonterminalAssembly.exists_nonterminalSectorStability` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalAssembly.lean:139` |
| `PaperC.BoundedRatioNonterminalAssembly.intrinsicNonterminalSector_uniformLittleO_of_arithmeticEnvelopes` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/BoundedRatioNonterminalAssembly.lean:43` |
| `PaperC.BoundedRatioNonterminalAssembly.nonterminalSectorStability_of_arithmeticEnvelopes` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalAssembly.lean:94` |
| `PaperC.BoundedRatioNonterminalCardinality.boundedIntrinsicNonterminalResidualMass_eq_densitySplit` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1073` |
| `PaperC.BoundedRatioNonterminalCardinality.card_highDensityIntrinsicNonterminalPairs_le_of_sizeTwoShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:220` |
| `PaperC.BoundedRatioNonterminalCardinality.card_intrinsicNonterminalPairs_le_shapeFiberMaximum` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1332` |
| `PaperC.BoundedRatioNonterminalCardinality.card_intrinsicNonterminalShapeFiber_le_maximum` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1292` |
| `PaperC.BoundedRatioNonterminalCardinality.highDensityIntrinsicNonterminalMassEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:687` |
| `PaperC.BoundedRatioNonterminalCardinality.highDensityIntrinsicNonterminalMassEnvelope_uniformLittleO` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:990` |
| `PaperC.BoundedRatioNonterminalCardinality.highDensityIntrinsicNonterminalMass_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:703` |
| `PaperC.BoundedRatioNonterminalCardinality.highDensityIntrinsicNonterminalMass_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:637` |
| `PaperC.BoundedRatioNonterminalCardinality.highDensityIntrinsicNonterminalMass_uniformLittleO` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1041` |
| `PaperC.BoundedRatioNonterminalCardinality.highDensityIntrinsicNonterminalPairs_subset_boundedComponentHostsTwo` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:186` |
| `PaperC.BoundedRatioNonterminalCardinality.highDensityIntrinsicNonterminalResidualMass_mul_rankFactor_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:603` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalCardinality_le_shapeFiberMaximum` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1434` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalEffectiveCardinality_le_shapeFiberEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1451` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalNormalizedCardinality_le_shapeFiberEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1472` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalNormalizedCardinality_uniformLittleO_of_shapeFiberEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1492` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalNormalizedShapeFiberEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1423` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalPairs_subset_boundedComponentHostsTen` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:69` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalPairs_subset_shapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1256` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalSectorResidualMass_eq_densitySplit` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1104` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalSector_uniformLittleO_of_densitySplit` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1136` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalSector_uniformLittleO_of_shapeFiberEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1521` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalShapeFiberEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1417` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalShapeFiberMaximum_le_of_hostShapeFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1310` |
| `PaperC.BoundedRatioNonterminalCardinality.intrinsicNonterminalShapeFiber_subset_boundedComponentHostsOfShape` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1244` |
| `PaperC.BoundedRatioNonterminalCardinality.linear_mul_twoThird_uniformFiveThird` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:482` |
| `PaperC.BoundedRatioNonterminalCardinality.mem_highDensityIntrinsicNonterminalPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:104` |
| `PaperC.BoundedRatioNonterminalCardinality.mem_intrinsicNonterminalShapeFiber` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1230` |
| `PaperC.BoundedRatioNonterminalCardinality.mem_moderateDensityIntrinsicNonterminalPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:131` |
| `PaperC.BoundedRatioNonterminalCardinality.moderateDensityIntrinsicNonterminalMass_le_hostEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:359` |
| `PaperC.BoundedRatioNonterminalCardinality.moderateDensityIntrinsicNonterminalMass_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:349` |
| `PaperC.BoundedRatioNonterminalCardinality.moderateDensityIntrinsicNonterminalMass_uniformLittleO` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:537` |
| `PaperC.BoundedRatioNonterminalCardinality.moderateDensityIntrinsicNonterminalPairs_subset_hostsTen` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:329` |
| `PaperC.BoundedRatioNonterminalCardinality.moderateDensityIntrinsicNonterminalResidualMass_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:303` |
| `PaperC.BoundedRatioNonterminalCardinality.moderateDensityResidualWeightEnvelope_uniformTwoThird` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:413` |
| `PaperC.BoundedRatioNonterminalCardinality.moderate_disjoint_highDensityIntrinsicNonterminalPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:168` |
| `PaperC.BoundedRatioNonterminalCardinality.moderate_union_highDensityIntrinsicNonterminalPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:147` |
| `PaperC.BoundedRatioNonterminalCardinality.nonterminalSectorStability_of_densitySplit` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1183` |
| `PaperC.BoundedRatioNonterminalCardinality.nonterminalSectorStability_of_shapeFiberEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:1540` |
| `PaperC.BoundedRatioNonterminalCardinality.residualWeight_le_moderateDensityEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:265` |
| `PaperC.BoundedRatioNonterminalCardinality.terminalRankGapFactor_le_exp_gap` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:789` |
| `PaperC.BoundedRatioNonterminalCardinality.terminalRankGapFactor_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:681` |
| `PaperC.BoundedRatioNonterminalCardinality.terminalRankGapFactor_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalCardinality.lean:882` |
| `PaperC.BoundedRatioNonterminalClosure.boundedIntrinsicNonterminalResidualMass_eq_sectorResidualMassNat` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalClosure.lean:36` |
| `PaperC.BoundedRatioNonterminalClosure.boundedIntrinsicNonterminalResidualMass_mul_two_pow_budget_succ_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalClosure.lean:49` |
| `PaperC.BoundedRatioNonterminalClosure.intrinsicNonterminalEffectiveCardinality_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalClosure.lean:104` |
| `PaperC.BoundedRatioNonterminalClosure.intrinsicNonterminalMassEnvelope_le_normalizedCardinality` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalClosure.lean:181` |
| `PaperC.BoundedRatioNonterminalClosure.intrinsicNonterminalMassEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalClosure.lean:110` |
| `PaperC.BoundedRatioNonterminalClosure.intrinsicNonterminalNormalizedCardinality_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalClosure.lean:118` |
| `PaperC.BoundedRatioNonterminalClosure.intrinsicNonterminalSectorResidualMass_le_massEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalClosure.lean:126` |
| `PaperC.BoundedRatioNonterminalClosure.intrinsicNonterminalSector_uniformLittleO_of_massEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalClosure.lean:225` |
| `PaperC.BoundedRatioNonterminalClosure.intrinsicNonterminalSector_uniformLittleO_of_normalizedCardinality` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalClosure.lean:260` |
| `PaperC.BoundedRatioNonterminalClosure.nonterminalSectorStability_of_massEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalClosure.lean:342` |
| `PaperC.BoundedRatioNonterminalClosure.nonterminalSectorStability_of_normalizedCardinality` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalClosure.lean:358` |
| `PaperC.BoundedRatioNonterminalHostCounts.boundedComponentHostsOfShape_subset_leftBaseUnion` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:81` |
| `PaperC.BoundedRatioNonterminalHostCounts.boundedComponentHostsOfShape_subset_rightBaseUnion` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:94` |
| `PaperC.BoundedRatioNonterminalHostCounts.card_boundedComponentHostsOfShape_le_leftBaseFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:110` |
| `PaperC.BoundedRatioNonterminalHostCounts.card_boundedComponentHostsOfShape_le_rightBaseFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:136` |
| `PaperC.BoundedRatioNonterminalHostCounts.card_boundedComponentHosts_le_sourceDisjunction` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:190` |
| `PaperC.BoundedRatioNonterminalHostCounts.card_boundedStartBases_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:56` |
| `PaperC.BoundedRatioNonterminalHostCounts.card_twoSingletonShapeFiber_le_maximum` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:386` |
| `PaperC.BoundedRatioNonterminalHostCounts.exists_card_boundedComponentHosts_le_explicit_sourceEnvelope` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:509` |
| `PaperC.BoundedRatioNonterminalHostCounts.exists_card_leftBaseShapeFiber_le_mobileArithmeticBound` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:293` |
| `PaperC.BoundedRatioNonterminalHostCounts.exists_card_rightBaseShapeFiber_le_mobileArithmeticBound` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:332` |
| `PaperC.BoundedRatioNonterminalHostCounts.firstBase_mem_boundedStartBases` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:62` |
| `PaperC.BoundedRatioNonterminalHostCounts.leftMobileArithmeticBound_le_maximum` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:420` |
| `PaperC.BoundedRatioNonterminalHostCounts.mobile_degree_dichotomy_of_three_le_total` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:174` |
| `PaperC.BoundedRatioNonterminalHostCounts.rightMobileArithmeticBound_le_maximum` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:458` |
| `PaperC.BoundedRatioNonterminalHostCounts.secondBase_mem_boundedStartBases` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:71` |
| `PaperC.BoundedRatioNonterminalHostCounts.shape_total_card_two_iff_singletons` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalHostCounts.lean:163` |
| `PaperC.BoundedRatioNonterminalMobileAssembly.evertseSilverman_generalizedPell_imply_exists_mobileDegreeAtLeastTwoEnvelope` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/BoundedRatioNonterminalMobileAssembly.lean:229` |
| `PaperC.BoundedRatioNonterminalMobileAssembly.evertseSilverman_generalizedPell_imply_exists_moderateNonterminalHostEnvelope` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/BoundedRatioNonterminalMobileAssembly.lean:638` |
| `PaperC.BoundedRatioNonterminalMobileAssembly.mobileDegreeAtLeastTwoEnvelope_eventually_one_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalMobileAssembly.lean:193` |
| `PaperC.BoundedRatioNonterminalMobileAssembly.mobileDegreeAtLeastTwoEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalMobileAssembly.lean:145` |
| `PaperC.BoundedRatioNonterminalMobileAssembly.mobileDegreeAtLeastTwoEnvelope_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalMobileAssembly.lean:158` |
| `PaperC.BoundedRatioNonterminalMobileAssembly.moderateNonterminalHostEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalMobileAssembly.lean:525` |
| `PaperC.BoundedRatioNonterminalMobileAssembly.moderateNonterminalHostEnvelope_uniformLinear` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalMobileAssembly.lean:542` |
| `PaperC.BoundedRatioNonterminalRealHosts.card_boundedComponentHostsOfShape_cast_le_leftBaseFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalRealHosts.lean:33` |
| `PaperC.BoundedRatioNonterminalRealHosts.card_boundedComponentHostsOfShape_cast_le_rightBaseFibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalRealHosts.lean:73` |
| `PaperC.BoundedRatioNonterminalRealHosts.card_boundedComponentHosts_cast_le_sourceDisjunction` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalRealHosts.lean:122` |
| `PaperC.BoundedRatioPoissonAssembly.abs_boundedCommonGoodRate_sub_fullRate_eq_badMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:328` |
| `PaperC.BoundedRatioPoissonAssembly.boundedAveragedConditionalGoodLaw_eq_boundedFullGoodStartLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:73` |
| `PaperC.BoundedRatioPoissonAssembly.boundedAveragedConditionalGood_natTotalVariation_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:200` |
| `PaperC.BoundedRatioPoissonAssembly.boundedCommonConditionalGoodPoissonLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:145` |
| `PaperC.BoundedRatioPoissonAssembly.boundedCommonConditionalGoodPoissonRate_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:311` |
| `PaperC.BoundedRatioPoissonAssembly.boundedConditionalGoodLaw_eq_finiteNatLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:111` |
| `PaperC.BoundedRatioPoissonAssembly.boundedConditionalGoodLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:138` |
| `PaperC.BoundedRatioPoissonAssembly.boundedConditionalGood_natTotalVariation_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:163` |
| `PaperC.BoundedRatioPoissonAssembly.boundedConditionedGoodIndicatorSum_eq_fullGoodStartCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:49` |
| `PaperC.BoundedRatioPoissonAssembly.boundedFullStartLaw_poisson_uniformLittleOOne` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:455` |
| `PaperC.BoundedRatioPoissonAssembly.natTotalVariation_boundedCommonGoodPoisson_fullRate_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:348` |
| `PaperC.BoundedRatioPoissonAssembly.natTotalVariation_boundedFullStartLaw_fullRate_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:374` |
| `PaperC.BoundedRatioPoissonAssembly.summable_abs_boundedConditionalGoodLaw_sub_commonPoisson` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:150` |
| `PaperC.BoundedRatioPoissonAssembly.summable_boundedCommonConditionalGoodPoissonLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:133` |
| `PaperC.BoundedRatioPoissonAssembly.summable_boundedConditionalGoodLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:126` |
| `PaperC.BoundedRatioPoissonAssembly.terminalBOneAverage_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioPoissonAssembly.lean:280` |
| `PaperC.BoundedRatioRationalMass.boundedRatioThreeHalvesResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRationalMass.lean:75` |
| `PaperC.BoundedRatioRationalMass.boundedRatio_weightedChannelGeometry_uniformLinearSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRationalMass.lean:220` |
| `PaperC.BoundedRatioRationalMass.boundedRationalMassSup_le_common` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRationalMass.lean:54` |
| `PaperC.BoundedRatioRationalMass.boundedRationalMassSup_uniformLittleO_square` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRationalMass.lean:169` |
| `PaperC.BoundedRatioRationalMass.boundedRationalMassSup_uniformThreeHalves` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRationalMass.lean:97` |
| `PaperC.BoundedRatioRationalMass.boundedRationalMass_le_sup` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRationalMass.lean:44` |
| `PaperC.BoundedRatioRationalMass.boundedRationalMass_uniformLittleO_square` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRationalMass.lean:187` |
| `PaperC.BoundedRatioRelationalHosts.assignmentCountBound_le_ratio_mul_kernelWeightQ` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:607` |
| `PaperC.BoundedRatioRelationalHosts.boundedRelationalHosts_subset_certificateCover` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:419` |
| `PaperC.BoundedRatioRelationalHosts.card_boundedRelationalHosts_cast_le_assignmentSum` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:541` |
| `PaperC.BoundedRatioRelationalHosts.card_boundedRelationalHosts_cast_le_kernelSumQ` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:686` |
| `PaperC.BoundedRatioRelationalHosts.card_certificate_union_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:513` |
| `PaperC.BoundedRatioRelationalHosts.card_leftCertificates_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:469` |
| `PaperC.BoundedRatioRelationalHosts.card_rightCertificates_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:491` |
| `PaperC.BoundedRatioRelationalHosts.card_startsForAssignment_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:197` |
| `PaperC.BoundedRatioRelationalHosts.card_startsForSomeAssignment_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:272` |
| `PaperC.BoundedRatioRelationalHosts.card_startsWithSelectedLabel_le_one` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:115` |
| `PaperC.BoundedRatioRelationalHosts.chosenRelation_ne_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:65` |
| `PaperC.BoundedRatioRelationalHosts.left_mem_startsForSomeAssignment_of_selected_right` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:363` |
| `PaperC.BoundedRatioRelationalHosts.mem_boundedRelationalHosts` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:42` |
| `PaperC.BoundedRatioRelationalHosts.mem_startsForAssignment` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:143` |
| `PaperC.BoundedRatioRelationalHosts.mem_startsForSomeAssignment` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:255` |
| `PaperC.BoundedRatioRelationalHosts.mem_startsWithSelectedLabel` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:107` |
| `PaperC.BoundedRatioRelationalHosts.pairwise_modEq_largeOddKernel` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:156` |
| `PaperC.BoundedRatioRelationalHosts.right_mem_startsForSomeAssignment_of_selected_left` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:329` |
| `PaperC.BoundedRatioRelationalHosts.selectedLabel_mem_Icc` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:315` |
| `PaperC.BoundedRatioRelationalHosts.selectedOccurrence_ne_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:84` |
| `PaperC.BoundedRatioRelationalHosts.startCompleteVertexLabel_le_cutoff` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioRelationalHosts.lean:305` |
| `PaperC.BoundedRatioRelationalHostsCritical.boundedRelationalHostEnvelope_uniformThreeHalves` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRelationalHostsCritical.lean:248` |
| `PaperC.BoundedRatioRelationalHostsCritical.boundedRelationalHostResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRelationalHostsCritical.lean:218` |
| `PaperC.BoundedRatioRelationalHostsCritical.card_boundedRelationalHosts_cast_le_common` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRelationalHostsCritical.lean:126` |
| `PaperC.BoundedRatioRelationalHostsCritical.card_boundedRelationalHosts_cast_le_exp_bound` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRelationalHostsCritical.lean:70` |
| `PaperC.BoundedRatioRelationalHostsCritical.card_boundedRelationalHosts_cast_le_kernelSum` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRelationalHostsCritical.lean:32` |
| `PaperC.BoundedRatioRelationalHostsCritical.card_boundedRelationalHosts_uniformThreeHalves` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioRelationalHostsCritical.lean:285` |
| `PaperC.BoundedRatioResidualMasses.activePopulation_subset` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:153` |
| `PaperC.BoundedRatioResidualMasses.activeSectorPairValues_subset_separatedBoundedRatioPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:451` |
| `PaperC.BoundedRatioResidualMasses.activeSectorPairs_subset_sectorPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:327` |
| `PaperC.BoundedRatioResidualMasses.card_activeSectorPairValues` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:439` |
| `PaperC.BoundedRatioResidualMasses.card_populationPairValues` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:207` |
| `PaperC.BoundedRatioResidualMasses.card_population_le_ratio_sq` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:247` |
| `PaperC.BoundedRatioResidualMasses.card_population_le_separatedBoundedRatioPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:226` |
| `PaperC.BoundedRatioResidualMasses.card_population_le_width_sq` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:236` |
| `PaperC.BoundedRatioResidualMasses.linearResidualMass_cast_le_sqrt_card_mul_sqrt_quadratic` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:272` |
| `PaperC.BoundedRatioResidualMasses.linearResidualMass_eq_activePopulation` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:160` |
| `PaperC.BoundedRatioResidualMasses.linearResidualWeight_eq_residualWeight` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:59` |
| `PaperC.BoundedRatioResidualMasses.linearResidualWeight_eq_zero_of_pairTau_eq_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:66` |
| `PaperC.BoundedRatioResidualMasses.linearResidualWeight_sq_le_quadraticResidualWeight` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:101` |
| `PaperC.BoundedRatioResidualMasses.mem_activePopulation` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:145` |
| `PaperC.BoundedRatioResidualMasses.mem_activeSectorPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:317` |
| `PaperC.BoundedRatioResidualMasses.populationPairValues_subset_separatedBoundedRatioPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:215` |
| `PaperC.BoundedRatioResidualMasses.quadraticResidualMass_eq_activePopulation` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:178` |
| `PaperC.BoundedRatioResidualMasses.quadraticResidualWeight_eq_zero_of_pairTau_eq_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:74` |
| `PaperC.BoundedRatioResidualMasses.sectorQuadraticResidualMass_eq_active` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:378` |
| `PaperC.BoundedRatioResidualMasses.sectorResidualMassNat_cast_le_sqrt_active_card_mul_sqrt_quadratic` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:412` |
| `PaperC.BoundedRatioResidualMasses.sectorResidualMassNat_cast_le_sqrt_card_mul_sqrt_quadratic` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:391` |
| `PaperC.BoundedRatioResidualMasses.sectorResidualMassNat_eq_activeLinearResidualMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:366` |
| `PaperC.BoundedRatioResidualMasses.sectorResidualMassNat_eq_linearResidualMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:355` |
| `PaperC.BoundedRatioResidualMasses.sum_linearResidualWeight_sq_le_quadraticResidualMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/BoundedRatioResidualMasses.lean:258` |
| `PaperC.BoundedRatioRetainedTransport.boundedFullStartLaw_eq_retainedStartLaw` | inconditionnel | — | — | — | `PaperC/Probability/BoundedRatioRetainedTransport.lean:96` |
| `PaperC.BoundedRatioRetainedTransport.boundedFullStartMean_eq_retainedStartMean` | inconditionnel | — | — | — | `PaperC/Probability/BoundedRatioRetainedTransport.lean:126` |
| `PaperC.BoundedRatioRetainedTransport.boundedRatioBlock_div_eq_retainedStartIndices` | inconditionnel | — | — | — | `PaperC/Probability/BoundedRatioRetainedTransport.lean:27` |
| `PaperC.BoundedRatioRetainedTransport.boundedRatioCutoff_le_globalCylinderCutoff` | inconditionnel | — | — | — | `PaperC/Probability/BoundedRatioRetainedTransport.lean:36` |
| `PaperC.BoundedRatioRetainedTransport.retainedStartCount_eq_boundedFullStartCount_transport` | inconditionnel | — | — | — | `PaperC/Probability/BoundedRatioRetainedTransport.lean:71` |
| `PaperC.BoundedRatioRetainedTransport.retained_window_le_boundedRatioCutoff` | inconditionnel | — | — | — | `PaperC/Probability/BoundedRatioRetainedTransport.lean:56` |
| `PaperC.BoundedRatioRetainedTransport.two_le_of_mem_retainedStartIndices` | inconditionnel | — | — | — | `PaperC/Probability/BoundedRatioRetainedTransport.lean:45` |
| `PaperC.BoundedRatioSectorAligned.no_aligned_deep_core_of_lower_bounds_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSectorAligned.lean:38` |
| `PaperC.BoundedRatioSectorClosure.activeSectorPairValues_subset_boundedRelationalHosts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSectorClosure.lean:67` |
| `PaperC.BoundedRatioSectorClosure.card_activeSectorPairs_le_boundedRelationalHosts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSectorClosure.lean:82` |
| `PaperC.BoundedRatioSectorClosure.pairRho_pos_of_mem_activeSectorPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSectorClosure.lean:34` |
| `PaperC.BoundedRatioSectorClosure.pairValue_mem_boundedRelationalHosts_of_mem_activeSectorPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSectorClosure.lean:49` |
| `PaperC.BoundedRatioSectorClosure.sectorResidualMassNat_cast_le_host_sqrt_mul_quadratic_sqrt` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSectorClosure.lean:97` |
| `PaperC.BoundedRatioSectorClosure.uniformLittleOInBoundedRatioWindow_of_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSectorClosure.lean:194` |
| `PaperC.BoundedRatioSectorClosure.uniformLittleOInBoundedRatioWindow_of_nonnegative_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSectorClosure.lean:224` |
| `PaperC.BoundedRatioSectorClosure.uniformRationalPowerInBoundedRatioWindow_of_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSectorClosure.lean:128` |
| `PaperC.BoundedRatioSectorClosure.uniformRationalPowerInBoundedRatioWindow_of_nonnegative_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSectorClosure.lean:162` |
| `PaperC.BoundedRatioShallowCoreSector.activeSectorQuadraticResidualMass_cast_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:287` |
| `PaperC.BoundedRatioShallowCoreSector.activeSectorQuadraticResidualMass_le_envelopeNat` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:272` |
| `PaperC.BoundedRatioShallowCoreSector.boundedRatioShallowCoreLinearEnvelope_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:438` |
| `PaperC.BoundedRatioShallowCoreSector.boundedRatioShallowCoreLinearEnvelope_uniformThirtyOneSixteenths` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:394` |
| `PaperC.BoundedRatioShallowCoreSector.boundedRatioShallowCoreQuadraticEnvelope_uniformNineteenEighths` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:306` |
| `PaperC.BoundedRatioShallowCoreSector.canonicalResidualComponentCount_le_envelope_of_mem_shallowCoreSector` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:118` |
| `PaperC.BoundedRatioShallowCoreSector.pairTau_le_canonicalCorrected_add_residual` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:51` |
| `PaperC.BoundedRatioShallowCoreSector.quadraticResidualWeight_le_shallowCore_envelopes_of_mem` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:146` |
| `PaperC.BoundedRatioShallowCoreSector.quadraticResidualWeight_le_systematic_mul_corrected_mul_component` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:76` |
| `PaperC.BoundedRatioShallowCoreSector.sectorQuadraticResidualMass_le_envelopeNat` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:219` |
| `PaperC.BoundedRatioShallowCoreSector.sectorResidualMass_le_linearEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:454` |
| `PaperC.BoundedRatioShallowCoreSector.shallowCoreSectorStability` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSector.lean:506` |
| `PaperC.BoundedRatioShallowCoreSigmaCritical.canonicalPairSigma_le_max_of_mem` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSigmaCritical.lean:138` |
| `PaperC.BoundedRatioShallowCoreSigmaCritical.canonicalPairSigma_le_max_of_mem_shallowCoreSector` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSigmaCritical.lean:155` |
| `PaperC.BoundedRatioShallowCoreSigmaCritical.embedInBoundingBlock_mem_of_mem_shallowCoreSector` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSigmaCritical.lean:98` |
| `PaperC.BoundedRatioShallowCoreSigmaCritical.embedInBoundingBlock_val` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSigmaCritical.lean:87` |
| `PaperC.BoundedRatioShallowCoreSigmaCritical.four_pow_maxBoundedRatioShallowCoreSigma_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSigmaCritical.lean:434` |
| `PaperC.BoundedRatioShallowCoreSigmaCritical.maxBoundedRatioShallowCoreSigma_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSigmaCritical.lean:175` |
| `PaperC.BoundedRatioShallowCoreSigmaCritical.maxBoundedRatioShallowCoreSigma_uniformLittleO` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSigmaCritical.lean:371` |
| `PaperC.BoundedRatioShallowCoreSigmaCritical.mem_boundedRatioShallowCorePairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioShallowCoreSigmaCritical.lean:55` |
| `PaperC.BoundedRatioSmallHeightSector.activeSectorQuadraticResidualMass_cast_le_quadraticEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:959` |
| `PaperC.BoundedRatioSmallHeightSector.activeSectorQuadraticResidualMass_eq_sigma_branches` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:263` |
| `PaperC.BoundedRatioSmallHeightSector.activeSectorQuadraticResidualMass_le_finite_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:497` |
| `PaperC.BoundedRatioSmallHeightSector.boundedRationalMassFourEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:911` |
| `PaperC.BoundedRatioSmallHeightSector.boundedRationalMassFourEnvelope_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:802` |
| `PaperC.BoundedRatioSmallHeightSector.boundedRationalMass_cast_le_fourEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:720` |
| `PaperC.BoundedRatioSmallHeightSector.boundedRationalMass_four_le_common` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:521` |
| `PaperC.BoundedRatioSmallHeightSector.boundedRelationalHostEnvelope_le_quadraticEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:756` |
| `PaperC.BoundedRatioSmallHeightSector.boundedRelationalHostQuadraticEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:919` |
| `PaperC.BoundedRatioSmallHeightSector.boundedRelationalHostQuadraticEnvelope_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:841` |
| `PaperC.BoundedRatioSmallHeightSector.boundedSmallHeightLinearEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:952` |
| `PaperC.BoundedRatioSmallHeightSector.boundedSmallHeightLinearEnvelope_uniformLittleO_square` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:1104` |
| `PaperC.BoundedRatioSmallHeightSector.boundedSmallHeightLinearEnvelope_uniformSevenFourths` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:1076` |
| `PaperC.BoundedRatioSmallHeightSector.boundedSmallHeightQuadraticEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:944` |
| `PaperC.BoundedRatioSmallHeightSector.boundedSmallHeightQuadraticEnvelope_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:898` |
| `PaperC.BoundedRatioSmallHeightSector.canonicalResidualComponentCount_le_smallHeightEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:84` |
| `PaperC.BoundedRatioSmallHeightSector.four_pow_boundedSmallHeightTauEnvelope_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:687` |
| `PaperC.BoundedRatioSmallHeightSector.four_pow_le_two_mul_four_pow_sub_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:366` |
| `PaperC.BoundedRatioSmallHeightSector.hasSmallCanonicalHeight_of_mem_activeSectorPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:65` |
| `PaperC.BoundedRatioSmallHeightSector.mem_positiveSigmaActiveSmallHeightSectorPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:237` |
| `PaperC.BoundedRatioSmallHeightSector.mem_sigmaZeroActiveSmallHeightSectorPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:225` |
| `PaperC.BoundedRatioSmallHeightSector.natSquare_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:789` |
| `PaperC.BoundedRatioSmallHeightSector.pairTau_le_boundedSmallHeightTauEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:148` |
| `PaperC.BoundedRatioSmallHeightSector.pairTau_le_canonicalCorrected_add_residual` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:128` |
| `PaperC.BoundedRatioSmallHeightSector.positiveSigmaQuadraticEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:934` |
| `PaperC.BoundedRatioSmallHeightSector.positiveSigmaQuadraticEnvelope_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:877` |
| `PaperC.BoundedRatioSmallHeightSector.positiveSigmaQuadraticResidualMass_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:454` |
| `PaperC.BoundedRatioSmallHeightSector.quadraticResidualWeight_le_tauEnvelope_mul_four_pow_sigma` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:172` |
| `PaperC.BoundedRatioSmallHeightSector.sectorResidualMassNat_cast_le_linearEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:1028` |
| `PaperC.BoundedRatioSmallHeightSector.sigmaZeroQuadraticEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:926` |
| `PaperC.BoundedRatioSmallHeightSector.sigmaZeroQuadraticEnvelope_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:862` |
| `PaperC.BoundedRatioSmallHeightSector.sigmaZeroQuadraticResidualMass_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:405` |
| `PaperC.BoundedRatioSmallHeightSector.smallCanonicalHeightSectorStability` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:1120` |
| `PaperC.BoundedRatioSmallHeightSector.sum_four_pow_pairSigma_positive_le_two_mul_boundedRationalMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:375` |
| `PaperC.BoundedRatioSmallHeightSector.sum_four_pow_pairSigma_sub_one_le_boundedRationalMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallHeightSector.lean:321` |
| `PaperC.BoundedRatioSmallProductSector.activeSectorQuadraticResidualMass_cast_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1166` |
| `PaperC.BoundedRatioSmallProductSector.activeSectorQuadraticResidualMass_eq_branches` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:551` |
| `PaperC.BoundedRatioSmallProductSector.boundedRationalMassFourEnvelope_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:881` |
| `PaperC.BoundedRatioSmallProductSector.boundedRationalMassFourResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:858` |
| `PaperC.BoundedRatioSmallProductSector.boundedRationalMass_four_cast_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:925` |
| `PaperC.BoundedRatioSmallProductSector.boundedRationalMass_four_le_common` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:720` |
| `PaperC.BoundedRatioSmallProductSector.canonicalResidualComponentCount_le_logQuotient` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:82` |
| `PaperC.BoundedRatioSmallProductSector.disjoint_sigmaZeroPairs_positiveSigmaPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:505` |
| `PaperC.BoundedRatioSmallProductSector.four_pow_componentCount_le_smallProductComponentFactor` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:196` |
| `PaperC.BoundedRatioSmallProductSector.four_pow_le_two_mul_four_pow_sub_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:645` |
| `PaperC.BoundedRatioSmallProductSector.hasSmallCanonicalPrimeProduct_of_mem_smallProductSector` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:181` |
| `PaperC.BoundedRatioSmallProductSector.mem_positiveSigmaPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:494` |
| `PaperC.BoundedRatioSmallProductSector.mem_sigmaZeroPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:482` |
| `PaperC.BoundedRatioSmallProductSector.pairTau_le_correctedDefect_add_componentCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:357` |
| `PaperC.BoundedRatioSmallProductSector.positiveSigmaEnvelope_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1048` |
| `PaperC.BoundedRatioSmallProductSector.positiveSigmaQuadraticMass_cast_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1127` |
| `PaperC.BoundedRatioSmallProductSector.positiveSigmaQuadraticMass_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:682` |
| `PaperC.BoundedRatioSmallProductSector.quadraticResidualWeight_le_loss_mul_four_pow_pairSigma` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:396` |
| `PaperC.BoundedRatioSmallProductSector.sigmaZeroEnvelope_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1004` |
| `PaperC.BoundedRatioSmallProductSector.sigmaZeroPairs_union_positiveSigmaPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:517` |
| `PaperC.BoundedRatioSmallProductSector.sigmaZeroQuadraticMass_cast_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1087` |
| `PaperC.BoundedRatioSmallProductSector.sigmaZeroQuadraticMass_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:568` |
| `PaperC.BoundedRatioSmallProductSector.smallPrimeProductSectorStability` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1482` |
| `PaperC.BoundedRatioSmallProductSector.smallProductComponentFactor_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:221` |
| `PaperC.BoundedRatioSmallProductSector.smallProductLinearEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1304` |
| `PaperC.BoundedRatioSmallProductSector.smallProductLinearEnvelope_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1468` |
| `PaperC.BoundedRatioSmallProductSector.smallProductLinearEnvelope_uniformSevenFourths` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1311` |
| `PaperC.BoundedRatioSmallProductSector.smallProductLoss_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:966` |
| `PaperC.BoundedRatioSmallProductSector.smallProductQuadraticEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1231` |
| `PaperC.BoundedRatioSmallProductSector.smallProductQuadraticEnvelope_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1070` |
| `PaperC.BoundedRatioSmallProductSector.smallProductSectorLinearMass_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1358` |
| `PaperC.BoundedRatioSmallProductSector.smallProductSectorLinearMass_uniformSevenFourths` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1404` |
| `PaperC.BoundedRatioSmallProductSector.smallProductSectorQuadraticMass_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1244` |
| `PaperC.BoundedRatioSmallProductSector.smallProductSectorQuadraticMass_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1222` |
| `PaperC.BoundedRatioSmallProductSector.smallProductSectorQuadraticMass_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:1263` |
| `PaperC.BoundedRatioSmallProductSector.sum_four_pow_pairSigma_positive_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:655` |
| `PaperC.BoundedRatioSmallProductSector.sum_four_pow_pairSigma_sub_one_le_boundedRationalMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSmallProductSector.lean:599` |
| `PaperC.BoundedRatioSteinChen.abs_goodPoissonParameter_sub_boundedTarget_eq_badCard` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:664` |
| `PaperC.BoundedRatioSteinChen.bOne_boundedConditionedGoodIndicator_eq_card_div` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:571` |
| `PaperC.BoundedRatioSteinChen.bOne_boundedConditionedGoodIndicator_le_card_div` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:602` |
| `PaperC.BoundedRatioSteinChen.boundedConditionalGood_totalVariationToPoisson_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:355` |
| `PaperC.BoundedRatioSteinChen.boundedConditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:161` |
| `PaperC.BoundedRatioSteinChen.boundedConditionedGoodIndicator_eq_true_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:151` |
| `PaperC.BoundedRatioSteinChen.boundedLargePrimeDependencyGraph_adj` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:99` |
| `PaperC.BoundedRatioSteinChen.boundedOrderedDependencyEdges_subset_primeWitnessCover` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:742` |
| `PaperC.BoundedRatioSteinChen.boundedOrderedDependencyEdges_terminalCutoff_uniformLittleOInBoundedRatioWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:1101` |
| `PaperC.BoundedRatioSteinChen.boundedRatioDependencyEdgeStatement` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:1398` |
| `PaperC.BoundedRatioSteinChen.boundedRatioFiniteSteinChenCore` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:1369` |
| `PaperC.BoundedRatioSteinChen.boundedStartsUsingPrime_subset_offsetUnion` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:834` |
| `PaperC.BoundedRatioSteinChen.boundedTarget_sub_goodPoissonParameter_eq_badCard` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:640` |
| `PaperC.BoundedRatioSteinChen.boundedTerminalBadStarts_subset_block` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:618` |
| `PaperC.BoundedRatioSteinChen.card_boundedClosedDependencyPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:426` |
| `PaperC.BoundedRatioSteinChen.card_boundedGood_add_card_boundedBad` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:626` |
| `PaperC.BoundedRatioSteinChen.card_boundedOrderedDependencyEdges_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:931` |
| `PaperC.BoundedRatioSteinChen.card_boundedOrderedDependencyEdges_cast_le_div` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:951` |
| `PaperC.BoundedRatioSteinChen.card_boundedOrderedDependencyEdges_cast_le_prime_sum` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:897` |
| `PaperC.BoundedRatioSteinChen.card_boundedOrderedDependencyEdges_le_sum_sq` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:763` |
| `PaperC.BoundedRatioSteinChen.card_boundedOrderedDependencyEdges_terminalCutoff_cast_le_div` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:1063` |
| `PaperC.BoundedRatioSteinChen.card_boundedStartsUsingPrime_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:863` |
| `PaperC.BoundedRatioSteinChen.card_boundedStartsWithDivisibleOffset_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:802` |
| `PaperC.BoundedRatioSteinChen.disjoint_boundedGoodDiag_orderedEdges` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:415` |
| `PaperC.BoundedRatioSteinChen.hasExactDependencyGraph_boundedConditionedGoodIndicator` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:229` |
| `PaperC.BoundedRatioSteinChen.marginal_boundedConditionedGoodIndicator_eq_baseline` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:184` |
| `PaperC.BoundedRatioSteinChen.mem_boundedClosedDependencyPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:407` |
| `PaperC.BoundedRatioSteinChen.mem_boundedGoodStarts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:83` |
| `PaperC.BoundedRatioSteinChen.mem_boundedOrderedDependencyEdges` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:114` |
| `PaperC.BoundedRatioSteinChen.mem_boundedStartsUsingPrime` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:690` |
| `PaperC.BoundedRatioSteinChen.mem_boundedStartsWithDivisibleOffset` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:791` |
| `PaperC.BoundedRatioSteinChen.mem_boundedTerminalBadStarts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:70` |
| `PaperC.BoundedRatioSteinChen.mem_largePrimesInRange_of_mem_bounded_coordinates` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:709` |
| `PaperC.BoundedRatioSteinChen.ne_of_mem_boundedOrderedDependencyEdges` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:124` |
| `PaperC.BoundedRatioSteinChen.pair_mem_boundedClosedDependencyPairs_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:440` |
| `PaperC.BoundedRatioSteinChen.poissonParameter_boundedConditionedGoodIndicator_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:380` |
| `PaperC.BoundedRatioSteinChen.retainedOrderedDependencyEdges_terminalCutoff_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:1226` |
| `PaperC.BoundedRatioSteinChen.sum_card_boundedClosedNeighborhood_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChen.lean:531` |
| `PaperC.BoundedRatioSteinChenRates.abs_retainedLengthRoundingError_le_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:437` |
| `PaperC.BoundedRatioSteinChenRates.boundedGoodStarts_terminalCutoff_card_uniformLittleOInBoundedRatioWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:96` |
| `PaperC.BoundedRatioSteinChenRates.retainedGoodStarts_terminalCutoff_card_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:248` |
| `PaperC.BoundedRatioSteinChenRates.retainedLengthRoundingError_div_twoPow_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:484` |
| `PaperC.BoundedRatioSteinChenRates.retainedLengthRoundingError_lt_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:425` |
| `PaperC.BoundedRatioSteinChenRates.retainedLengthRoundingError_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:419` |
| `PaperC.BoundedRatioSteinChenRates.retainedLength_eq_main_add_roundingError` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:444` |
| `PaperC.BoundedRatioSteinChenRates.retainedLength_mainTerm_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:541` |
| `PaperC.BoundedRatioSteinChenRates.retainedLength_normalized_sub_main_eq_roundingError` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:471` |
| `PaperC.BoundedRatioSteinChenRates.retainedMeanMainTerm_of_badCorrection` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:574` |
| `PaperC.BoundedRatioSteinChenRates.retainedTerminalBOneNumerator_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:306` |
| `PaperC.BoundedRatioSteinChenRates.retainedTerminalBOne_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:337` |
| `PaperC.BoundedRatioSteinChenRates.terminalBOneNumerator_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:68` |
| `PaperC.BoundedRatioSteinChenRates.terminalBOneNumerator_uniformLittleOInBoundedRatioWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:147` |
| `PaperC.BoundedRatioSteinChenRates.terminalBOne_eq_terminalBOneNumerator_div` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:75` |
| `PaperC.BoundedRatioSteinChenRates.terminalBOne_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:183` |
| `PaperC.BoundedRatioSteinChenRates.uniformLittleOOn_neg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenRates.lean:556` |
| `PaperC.BoundedRatioSteinChenSecondTerm.abs_boundedJointPairMass_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:623` |
| `PaperC.BoundedRatioSteinChenSecondTerm.abs_boundedJointStartProbability_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:590` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedConditionalBTwoAverage_eq_boundedSteinBTwoAverage` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:291` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedConditionalBTwoAverage_le_exactFiniteMajorant` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:1232` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedConditionalBTwoAverage_le_finiteMajorant` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:1348` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedConditionalBTwoAverage_le_strongFiniteMajorant` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:1299` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedConditionalJointAverage` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:161` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointDefectMass_separated_le_R2κ` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:698` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointPairMass_mono` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:667` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointPairMass_overlap_eq_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:511` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointPairMass_separated_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:714` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointPairMass_touching_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:885` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointPairMass_touching_le_baseline` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:1174` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointPairMass_touching_le_two_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:915` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointPairMass_touching_le_two_mul_baseline` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:1196` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointPairMass_union` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:482` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointStartProbability_cast_le_marginal` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:847` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointStartProbability_comm` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:1105` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointStartProbability_eq_eta_mul_two_pow_rho_div` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:556` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointStartProbability_eq_uniformSolutionProbability` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:538` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointStartProbability_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:659` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointStartProbability_touching_forward_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:1123` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedJointStartProbability_touching_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:1145` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedMatchingPoissonLaw_eq_common` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:113` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedOrderedDependencyEdges_eq_three_parts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:429` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedPoissonParameter_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:92` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedSeparatedDependencyEdges_subset` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:679` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedSteinBTwoAverage_eq_three_parts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:491` |
| `PaperC.BoundedRatioSteinChenSecondTerm.boundedTouchingDependencyEdges_subset_candidates` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:775` |
| `PaperC.BoundedRatioSteinChenSecondTerm.card_boundedTouchingDependencyEdges_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:808` |
| `PaperC.BoundedRatioSteinChenSecondTerm.disjoint_boundedOverlap_separated` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:462` |
| `PaperC.BoundedRatioSteinChenSecondTerm.disjoint_boundedOverlap_touching` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:452` |
| `PaperC.BoundedRatioSteinChenSecondTerm.disjoint_boundedTouching_separated` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:472` |
| `PaperC.BoundedRatioSteinChenSecondTerm.jointMarginal_le_marginal_left` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:827` |
| `PaperC.BoundedRatioSteinChenSecondTerm.mem_boundedOverlapDependencyEdges` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:403` |
| `PaperC.BoundedRatioSteinChenSecondTerm.mem_boundedSeparatedDependencyEdges` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:421` |
| `PaperC.BoundedRatioSteinChenSecondTerm.mem_boundedTouchingDependencyEdges` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:412` |
| `PaperC.BoundedRatioSteinChenSecondTerm.pair_mem_boundedOrderedDependencyEdges_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:188` |
| `PaperC.BoundedRatioSteinChenSecondTerm.relationRho_bounded_touching_eq_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:978` |
| `PaperC.BoundedRatioSteinChenSecondTerm.touchingDefectIndices_eq_empty_of_boundedGood` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTerm.lean:933` |
| `PaperC.BoundedRatioSteinChenSecondTermCritical.boundedConditionalBTwoAverage_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTermCritical.lean:58` |
| `PaperC.BoundedRatioSteinChenSecondTermCritical.terminalBTwoMajorantNumerator_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTermCritical.lean:52` |
| `PaperC.BoundedRatioSteinChenSecondTermCritical.terminalBTwoMajorantNumerator_uniformLittleOInBoundedRatioWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTermCritical.lean:115` |
| `PaperC.BoundedRatioSteinChenSecondTermCritical.terminalBTwoTouchingNumerator_uniformLittleOInBoundedRatioWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTermCritical.lean:79` |
| `PaperC.BoundedRatioSteinChenSecondTermCritical.terminalBoundedConditionalBTwoAverage_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTermCritical.lean:70` |
| `PaperC.BoundedRatioSteinChenSecondTermCritical.terminalBoundedConditionalBTwoAverage_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTermCritical.lean:183` |
| `PaperC.BoundedRatioSteinChenSecondTermCritical.two_mul_runLength_le_terminalPrimeCutoff_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioSteinChenSecondTermCritical.lean:142` |
| `PaperC.BoundedRatioTerminalClosure.abs_crossDeterminant_startCompleteVertexLabel_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:99` |
| `PaperC.BoundedRatioTerminalClosure.card_completeBoundaryLabelStarts_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:277` |
| `PaperC.BoundedRatioTerminalClosure.card_filter_kernel_above_threshold_le_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:204` |
| `PaperC.BoundedRatioTerminalClosure.card_firstStarts_le_twice_possibleKernelValues` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:335` |
| `PaperC.BoundedRatioTerminalClosure.card_possibleKernelValues_cast_le_exp` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:232` |
| `PaperC.BoundedRatioTerminalClosure.card_possibleKernelValues_fourth_power_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:396` |
| `PaperC.BoundedRatioTerminalClosure.card_possibleKernelValues_uniformThreeQuarter` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:578` |
| `PaperC.BoundedRatioTerminalClosure.determinantBudget_lt_kernelThreshold_sq` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:194` |
| `PaperC.BoundedRatioTerminalClosure.eq_of_startCompleteVertexLabel_eq_at_fixed_offset` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:259` |
| `PaperC.BoundedRatioTerminalClosure.exp_eight_sqrt_runLength_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:513` |
| `PaperC.BoundedRatioTerminalClosure.kernelThreshold_sq_le_four_mul_determinantBudget` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:368` |
| `PaperC.BoundedRatioTerminalClosure.kernel_product_le_of_dvd_crossDeterminant` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:174` |
| `PaperC.BoundedRatioTerminalClosure.natCast_le_abs_of_dvd` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:149` |
| `PaperC.BoundedRatioTerminalClosure.rankTerminalSector_uniformLittleO_of_card_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:601` |
| `PaperC.BoundedRatioTerminalClosure.startCompleteVertexLabel_le_terminalLabelCutoff` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:68` |
| `PaperC.BoundedRatioTerminalClosure.terminalKernelCountResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:548` |
| `PaperC.BoundedRatioTerminalClosure.uniformRationalPower_of_fourth_bound` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalClosure.lean:479` |
| `PaperC.BoundedRatioTerminalFibers.crossDeterminant_ne_of_canonicalNonaligned` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalFibers.lean:305` |
| `PaperC.BoundedRatioTerminalFibers.distinct_pairComponents_kernel_package` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalFibers.lean:115` |
| `PaperC.BoundedRatioTerminalFibers.pairComponentCertificate_cell_injective` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalFibers.lean:328` |
| `PaperC.BoundedRatioTerminalFibers.pairComponentCertificate_mem` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalFibers.lean:79` |
| `PaperC.BoundedRatioTerminalFibers.pairComponentCertificate_shape` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalFibers.lean:96` |
| `PaperC.BoundedRatioTerminalFibers.pairComponents_crossDeterminant_ne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalFibers.lean:357` |
| `PaperC.BoundedRatioTerminalFibers.reducedCandidate_of_crossDeterminant_eq_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalFibers.lean:165` |
| `PaperC.BoundedRatioTerminalPartnerClosure.attachedPairComponents_card_sub_one_le_incident` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:1177` |
| `PaperC.BoundedRatioTerminalPartnerClosure.boundedRankTerminalPartnerFiber_polynomialBound` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:1003` |
| `PaperC.BoundedRatioTerminalPartnerClosure.card_boundedRankTerminalFirstStarts_le_twice_possibleKernelValues` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:1243` |
| `PaperC.BoundedRatioTerminalPartnerClosure.card_exceptionalPairComponents_le_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:1106` |
| `PaperC.BoundedRatioTerminalPartnerClosure.card_nonexceptionalPairComponents_le_incident` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:1120` |
| `PaperC.BoundedRatioTerminalPartnerClosure.card_terminalOffsetQuadruple` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:67` |
| `PaperC.BoundedRatioTerminalPartnerClosure.card_terminalParameterFiber_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:381` |
| `PaperC.BoundedRatioTerminalPartnerClosure.card_terminalParameterUnion_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:590` |
| `PaperC.BoundedRatioTerminalPartnerClosure.card_twoComponentTerminalPartnerFiber_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:678` |
| `PaperC.BoundedRatioTerminalPartnerClosure.codePartnerWitness_injective_on_first` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:222` |
| `PaperC.BoundedRatioTerminalPartnerClosure.codePartnerWitness_mem_box` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:244` |
| `PaperC.BoundedRatioTerminalPartnerClosure.codeRightOffsetDifference_natAbs_le_cutoff` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:711` |
| `PaperC.BoundedRatioTerminalPartnerClosure.componentOffsetQuadruple_distinct` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:142` |
| `PaperC.BoundedRatioTerminalPartnerClosure.mem_boundedRankTerminalPartnerFiber` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:493` |
| `PaperC.BoundedRatioTerminalPartnerClosure.mem_terminalParameterFiber` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:206` |
| `PaperC.BoundedRatioTerminalPartnerClosure.mem_twoComponentTerminalPartnerFiber` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:483` |
| `PaperC.BoundedRatioTerminalPartnerClosure.pairComponentCertificate_left_injective` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:94` |
| `PaperC.BoundedRatioTerminalPartnerClosure.pairComponentCertificate_right_injective` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:118` |
| `PaperC.BoundedRatioTerminalPartnerClosure.pairComponentLeftKernel_product_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:1073` |
| `PaperC.BoundedRatioTerminalPartnerClosure.six_mul_terminalRankBudget_add_two_le_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:1273` |
| `PaperC.BoundedRatioTerminalPartnerClosure.smallOddPart_mem_terminalSmallParts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:436` |
| `PaperC.BoundedRatioTerminalPartnerClosure.terminalPair_incidentPossibleKernelValues_lower` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:1207` |
| `PaperC.BoundedRatioTerminalPartnerClosure.terminalParameterFibers_polynomialBox` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:746` |
| `PaperC.BoundedRatioTerminalPartnerClosure.terminalRankBudget_slack_conditions_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:1347` |
| `PaperC.BoundedRatioTerminalPartnerClosure.twoComponentTerminalPartnerFiber_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:505` |
| `PaperC.BoundedRatioTerminalPartnerClosure.twoComponentTerminalPartnerFiber_polynomialBound` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:976` |
| `PaperC.BoundedRatioTerminalPartnerClosure.twoComponentTerminalPartnerFiber_subset_parameterUnion` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalPartnerClosure.lean:527` |
| `PaperC.BoundedRatioTerminalSummation.TerminalSectorStabilityStatement` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:950` |
| `PaperC.BoundedRatioTerminalSummation.boundedRankTerminalPairs_eq_boundedIntrinsicTerminalPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:901` |
| `PaperC.BoundedRatioTerminalSummation.card_boundedRankTerminalPairs_cast_le_firstStarts_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:56` |
| `PaperC.BoundedRatioTerminalSummation.card_boundedRankTerminalPairs_cast_le_rawEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:95` |
| `PaperC.BoundedRatioTerminalSummation.card_terminalSmallParts_le_smoothKernelChebyshevEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:196` |
| `PaperC.BoundedRatioTerminalSummation.expLogLogBound_terminalLabelCutoff_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:265` |
| `PaperC.BoundedRatioTerminalSummation.generalizedPell_implies_boundedRankTerminalPairs_le_envelope` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:529` |
| `PaperC.BoundedRatioTerminalSummation.generalizedPell_implies_boundedRankTerminalPairs_rawEnvelope` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:149` |
| `PaperC.BoundedRatioTerminalSummation.generalizedPell_implies_intrinsicTerminalSector_uniformSevenFourths` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:985` |
| `PaperC.BoundedRatioTerminalSummation.generalizedPell_implies_rankTerminalSector_uniformLittleO` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:868` |
| `PaperC.BoundedRatioTerminalSummation.generalizedPell_implies_rankTerminalSector_uniformSevenFourths` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:676` |
| `PaperC.BoundedRatioTerminalSummation.intrinsicTerminalSectorStability` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:970` |
| `PaperC.BoundedRatioTerminalSummation.rankTerminalSectorResidualMass_le_massEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:602` |
| `PaperC.BoundedRatioTerminalSummation.rankTerminalSector_uniformLittleO_of_eventual_card_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:733` |
| `PaperC.BoundedRatioTerminalSummation.sectorResidualMass_rank_eq_intrinsic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:912` |
| `PaperC.BoundedRatioTerminalSummation.sectorResidualMass_rank_eq_intrinsic_fun` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:932` |
| `PaperC.BoundedRatioTerminalSummation.terminalPartnerEnvelope_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:413` |
| `PaperC.BoundedRatioTerminalSummation.terminalPopulationEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:473` |
| `PaperC.BoundedRatioTerminalSummation.terminalPopulationEnvelope_uniformThreeQuarter` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:443` |
| `PaperC.BoundedRatioTerminalSummation.terminalPopulationRawEnvelope_le_terminalPopulationEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:205` |
| `PaperC.BoundedRatioTerminalSummation.terminalRankMassEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:480` |
| `PaperC.BoundedRatioTerminalSummation.terminalRankMassEnvelope_uniformSevenFourths` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:496` |
| `PaperC.BoundedRatioTerminalSummation.uniformSubpolynomialOn_fixedPower` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTerminalSummation.lean:393` |
| `PaperC.BoundedRatioTwoDefectStarts.card_equalKernelDefectBases_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoDefectStarts.lean:511` |
| `PaperC.BoundedRatioTwoDefectStarts.card_equalKernelPairedDefectStarts_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoDefectStarts.lean:251` |
| `PaperC.BoundedRatioTwoDefectStarts.card_equalKernelSmoothStarts_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoDefectStarts.lean:357` |
| `PaperC.BoundedRatioTwoDefectStarts.card_equalKernelStartsForParameters_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoDefectStarts.lean:220` |
| `PaperC.BoundedRatioTwoDefectStarts.equalKernelDefectBases_eq_empty` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoDefectStarts.lean:558` |
| `PaperC.BoundedRatioTwoDefectStarts.equalKernelDefectBases_subset_smoothStarts` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoDefectStarts.lean:434` |
| `PaperC.BoundedRatioTwoDefectStarts.equalKernelWitnessBox_atMost` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoDefectStarts.lean:176` |
| `PaperC.BoundedRatioTwoDefectStarts.equalKernelWitness_factorization` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoDefectStarts.lean:48` |
| `PaperC.BoundedRatioTwoDefectStarts.equalKernelWitness_roots_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoDefectStarts.lean:107` |
| `PaperC.BoundedRatioTwoDefectStarts.leftRoot_injective_on_equalKernelWitnessBox` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoDefectStarts.lean:136` |
| `PaperC.BoundedRatioTwoDefectStarts.mem_equalKernelDefectBases` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoDefectStarts.lean:414` |
| `PaperC.BoundedRatioTwoSingletonCritical.boundedRatioCutoff_and_log_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:348` |
| `PaperC.BoundedRatioTwoSingletonCritical.card_boundedComponentHosts_two_cast_le_sizeTwoEnvelope_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:957` |
| `PaperC.BoundedRatioTwoSingletonCritical.card_twoSingletonShapeFiber_cast_le_envelope_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:439` |
| `PaperC.BoundedRatioTwoSingletonCritical.eventually_log_le_fourthRoot` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:603` |
| `PaperC.BoundedRatioTwoSingletonCritical.exists_sizeTwoComponentHostEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:1125` |
| `PaperC.BoundedRatioTwoSingletonCritical.exists_twoSingletonShapeFiberEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:572` |
| `PaperC.BoundedRatioTwoSingletonCritical.real_log_le_two_mul_height` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:314` |
| `PaperC.BoundedRatioTwoSingletonCritical.twoSingletonHarmonicCoefficient_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:158` |
| `PaperC.BoundedRatioTwoSingletonCritical.twoSingletonPolynomialCoefficient_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:841` |
| `PaperC.BoundedRatioTwoSingletonCritical.twoSingletonPolynomialEuler_le_terminalExp` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:860` |
| `PaperC.BoundedRatioTwoSingletonCritical.twoSingletonPrimeExponent_le_criticalRatio_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:648` |
| `PaperC.BoundedRatioTwoSingletonCritical.twoSingletonPrimeExponent_le_sqrt` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:53` |
| `PaperC.BoundedRatioTwoSingletonCritical.twoSingletonShapeFiberEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:169` |
| `PaperC.BoundedRatioTwoSingletonCritical.twoSingletonShapeFiberEnvelope_uniformLinear` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:252` |
| `PaperC.BoundedRatioTwoSingletonCritical.twoSingletonSqrtEnvelope_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:185` |
| `PaperC.BoundedRatioTwoSingletonCritical.twoSingletonTerminalConstant_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonCritical.lean:849` |
| `PaperC.BoundedRatioTwoSingletonHosts.boundedComponentHostsOfShape_subset_squareClassUnion` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:85` |
| `PaperC.BoundedRatioTwoSingletonHosts.card_boundedComponentHosts_two_cast_le_primeSensitive` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:1150` |
| `PaperC.BoundedRatioTwoSingletonHosts.card_boundedComponentHosts_two_le_parameterCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:841` |
| `PaperC.BoundedRatioTwoSingletonHosts.card_divisors_eq_two_pow_primeFactors_card` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:440` |
| `PaperC.BoundedRatioTwoSingletonHosts.card_singletonParameterTuples_cast_le_harmonic` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:396` |
| `PaperC.BoundedRatioTwoSingletonHosts.card_singletonParameterTuples_le_rootSum` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:277` |
| `PaperC.BoundedRatioTwoSingletonHosts.card_singletonRootBox` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:224` |
| `PaperC.BoundedRatioTwoSingletonHosts.card_singletonSummationContainerAt_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:232` |
| `PaperC.BoundedRatioTwoSingletonHosts.card_singletonSummationContainer_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:254` |
| `PaperC.BoundedRatioTwoSingletonHosts.card_twoSingletonShapeFiber_le_parameterCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:782` |
| `PaperC.BoundedRatioTwoSingletonHosts.card_twoSingletonSquareClassFiber_le_parameters` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:741` |
| `PaperC.BoundedRatioTwoSingletonHosts.cast_rootPair_le_harmonicWeight` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:327` |
| `PaperC.BoundedRatioTwoSingletonHosts.mem_twoSingletonSquareClassFiber` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:73` |
| `PaperC.BoundedRatioTwoSingletonHosts.singletonLabelProduct_eq_squareClass` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:524` |
| `PaperC.BoundedRatioTwoSingletonHosts.singletonLabels_pos_le_cutoff` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:497` |
| `PaperC.BoundedRatioTwoSingletonHosts.singletonParameterMap_injective_on` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:655` |
| `PaperC.BoundedRatioTwoSingletonHosts.singletonParameterMap_mem` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:555` |
| `PaperC.BoundedRatioTwoSingletonHosts.singletonParameterTuples_subset_summationContainer` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:174` |
| `PaperC.BoundedRatioTwoSingletonHosts.sqrt_split_denominators` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:294` |
| `PaperC.BoundedRatioTwoSingletonHosts.squarefree_divisorWeight_eq_supportWeight` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:460` |
| `PaperC.BoundedRatioTwoSingletonHosts.sum_harmonicWeights` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:380` |
| `PaperC.BoundedRatioTwoSingletonHosts.sum_squarefreeSmooth_divisorWeights_le_eulerProduct` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:884` |
| `PaperC.BoundedRatioTwoSingletonHosts.sum_supportWeights_eq_twoSingletonEulerProduct` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:870` |
| `PaperC.BoundedRatioTwoSingletonHosts.twoSingletonEulerProduct_le_primeSensitive` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:1027` |
| `PaperC.BoundedRatioTwoSingletonHosts.twoSingletonEulerProduct_le_square` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:1010` |
| `PaperC.BoundedRatioTwoSingletonHosts.twoSingletonParameterCount_cast_le_harmonicEuler` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:937` |
| `PaperC.BoundedRatioTwoSingletonHosts.twoSingletonParameterCount_cast_le_logEuler` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:986` |
| `PaperC.BoundedRatioTwoSingletonHosts.twoSingletonParameterCount_cast_le_primeSensitive` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:1071` |
| `PaperC.BoundedRatioTwoSingletonHosts.twoSingletonShapeFiberMaximum_cast_le_primeSensitive` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:1125` |
| `PaperC.BoundedRatioTwoSingletonHosts.twoSingletonShapeFiberMaximum_le_parameterCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioTwoSingletonHosts.lean:823` |
| `PaperC.BoundedRatioWeightedDefect.boundedBadStartProbabilityMass_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioWeightedDefect.lean:480` |
| `PaperC.BoundedRatioWeightedDefect.boundedTerminalDefectWeightMass_le_canonical` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioWeightedDefect.lean:81` |
| `PaperC.BoundedRatioWeightedDefect.boundedTerminalDefectWeightMass_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioWeightedDefect.lean:208` |
| `PaperC.BoundedRatioWeightedDefect.boundedTerminalDefectWeightMass_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioWeightedDefect.lean:343` |
| `PaperC.BoundedRatioWeightedDefect.boundedTerminalDefectWeightMass_uniformLittleOLinear` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioWeightedDefect.lean:375` |
| `PaperC.BoundedRatioWeightedDefect.boundedWeightedDefectEnvelope_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioWeightedDefect.lean:192` |
| `PaperC.BoundedRatioWeightedDefect.boundedWeightedDefectResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioWeightedDefect.lean:152` |
| `PaperC.BoundedRatioWeightedDefect.boundedWeightedDefectResidual_uniformSubpolynomialOnAdmissible` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioWeightedDefect.lean:135` |
| `PaperC.BoundedRatioWeightedDefect.canonicalBoundedDefectMass_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioWeightedDefect.lean:105` |
| `PaperC.BoundedRatioWeightedDefect.card_startDefectIndicesAt_le_localCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioWeightedDefect.lean:49` |
| `PaperC.BoundedRatioWeightedDefect.normalized_boundedTerminalDefectWeightMass_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioWeightedDefect.lean:421` |
| `PaperC.CRT.admissibleCertificatePairSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCRTInstantiation.lean:260` |
| `PaperC.CRT.admissibleCertificateSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCRTInstantiation.lean:195` |
| `PaperC.CRT.card_Ico_satisfies_cast_le_div_add_one` | inconditionnel | — | — | — | `PaperC/Arithmetic/CertificateCount.lean:28` |
| `PaperC.CRT.card_Ico_satisfies_cast_le_scaled` | inconditionnel | — | — | — | `PaperC/Arithmetic/CertificateCount.lean:107` |
| `PaperC.CRT.card_certificatePairSolutions` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificatePopulationCover.lean:258` |
| `PaperC.CRT.card_certificateSolutions` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificatePopulationCover.lean:36` |
| `PaperC.CRT.card_population_le_sum_admissibleCertificatePairSolutionCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificatePopulationCover.lean:288` |
| `PaperC.CRT.card_population_le_sum_admissibleCertificatePairSolutionCount'` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificatePopulationCover.lean:346` |
| `PaperC.CRT.card_population_le_sum_admissibleCertificateSolutionCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificatePopulationCover.lean:59` |
| `PaperC.CRT.card_population_le_sum_admissibleCertificateSolutionCount'` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificatePopulationCover.lean:112` |
| `PaperC.CRT.card_product_Ico_satisfies_cast_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/CertificateCount.lean:67` |
| `PaperC.CRT.card_product_Ico_satisfies_cast_le_scaled` | inconditionnel | — | — | — | `PaperC/Arithmetic/CertificateCount.lean:161` |
| `PaperC.CRT.certificateCellWeightSum_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateSummation.lean:202` |
| `PaperC.CRT.certificatePairCellWeightSum_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateSummation.lean:225` |
| `PaperC.CRT.certificatePairSolutionCount_cast_le_scaled` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCRTInstantiation.lean:112` |
| `PaperC.CRT.certificateSolutionCount_cast_le_scaled` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCRTInstantiation.lean:85` |
| `PaperC.CRT.certificateWeightSum_le_pow_sum_div_factorial` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateSummation.lean:188` |
| `PaperC.CRT.certificate_pairwise_coprime` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCRTInstantiation.lean:52` |
| `PaperC.CRT.certificate_product_div_modulus` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCRTInstantiation.lean:141` |
| `PaperC.CRT.certificate_product_div_modulus_sq` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCRTInstantiation.lean:152` |
| `PaperC.CRT.dvd_additiveStartResidue_add` | inconditionnel | — | — | — | `PaperC/Arithmetic/StartResidue.lean:29` |
| `PaperC.CRT.factorial_mul_certificateWeightSum_le_pow_sum` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateSummation.lean:177` |
| `PaperC.CRT.labeledCell_admissibleCertificatePairSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateLemmaSevenOne.lean:86` |
| `PaperC.CRT.labeledCell_admissibleCertificatePairSolutionMass_le_exact` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateLemmaSevenOne.lean:54` |
| `PaperC.CRT.labeledCell_admissibleCertificateSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateLemmaSevenOne.lean:26` |
| `PaperC.CRT.modEq_additiveStartResidue_iff_dvd_add` | inconditionnel | — | — | — | `PaperC/Arithmetic/StartResidue.lean:42` |
| `PaperC.CRT.modEq_startResidue_iff_dvd_startCompleteVertexLabel` | inconditionnel | — | — | — | `PaperC/Arithmetic/StartResidue.lean:66` |
| `PaperC.CRT.orderedCertificateToFunction_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateSummation.lean:65` |
| `PaperC.CRT.orderedCertificate_sum_eq_factorial_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateSummation.lean:124` |
| `PaperC.CRT.orderedCertificate_sum_le_all_functions` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateSummation.lean:148` |
| `PaperC.CRT.pow_mul_card_population_le_admissibleCertificatePairSolutionMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificatePopulationCover.lean:404` |
| `PaperC.CRT.pow_mul_card_population_le_admissibleCertificatePairSolutionMass'` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificatePopulationCover.lean:449` |
| `PaperC.CRT.pow_mul_card_population_le_admissibleCertificateSolutionMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificatePopulationCover.lean:163` |
| `PaperC.CRT.pow_mul_card_population_le_admissibleCertificateSolutionMass'` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificatePopulationCover.lean:204` |
| `PaperC.CRT.representative_lt_product` | inconditionnel | — | — | — | `PaperC/Arithmetic/CRT.lean:92` |
| `PaperC.CRT.satisfies_iff_intModEq_representative` | inconditionnel | — | — | — | `PaperC/Arithmetic/CRT.lean:74` |
| `PaperC.CRT.satisfies_iff_modEq_representative` | inconditionnel | — | — | — | `PaperC/Arithmetic/CRT.lean:45` |
| `PaperC.CRT.solutions_modEq` | inconditionnel | — | — | — | `PaperC/Arithmetic/CRT.lean:26` |
| `PaperC.CRT.sum_admissibleCertificatePairSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCRTInstantiation.lean:368` |
| `PaperC.CRT.sum_admissibleCertificateSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCRTInstantiation.lean:333` |
| `PaperC.CRT.sum_certificateWeightSum_le_exponentialMajorant` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateSummation.lean:260` |
| `PaperC.CRT.sum_labeledCell_admissibleCertificatePairSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateLemmaSevenOne.lean:199` |
| `PaperC.CRT.sum_labeledCell_admissibleCertificatePairSolutionMass_le_exact` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateLemmaSevenOne.lean:166` |
| `PaperC.CRT.sum_labeledCell_admissibleCertificateSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateLemmaSevenOne.lean:136` |
| `PaperC.CRT.sum_labeledCell_div_eq` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCellFamilies.lean:39` |
| `PaperC.CRT.sum_labeledCell_div_sq_eq` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCellFamilies.lean:55` |
| `PaperC.CRT.sum_labeledCell_div_sq_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateCellFamilies.lean:73` |
| `PaperC.CRT.unorderedCertificate_card` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateSummation.lean:46` |
| `PaperC.CRT.unorderedCertificate_subset` | inconditionnel | — | — | — | `PaperC/Combinatorics/CertificateSummation.lean:40` |
| `PaperC.CanonicalChannelWindow.card_reducedChannelCandidates_le_one_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/CanonicalChannelWindow.lean:108` |
| `PaperC.CanonicalChannelWindow.determinantThreshold_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/CanonicalChannelWindow.lean:68` |
| `PaperC.CanonicalChannelWindow.four_mul_height_sq_mul_lt_succ_pow` | inconditionnel | — | — | — | `PaperC/Asymptotics/CanonicalChannelWindow.lean:47` |
| `PaperC.CanonicalChannelWindow.four_mul_pow_lt_succ_pow_add_two` | inconditionnel | — | — | — | `PaperC/Asymptotics/CanonicalChannelWindow.lean:26` |
| `PaperC.CanonicalDefectCode.length_lt_of_log` | inconditionnel | — | — | — | `PaperC/Coding/CanonicalDefectCode.lean:61` |
| `PaperC.CanonicalDefectCode.volume_le_two_pow_of_log` | inconditionnel | — | — | — | `PaperC/Coding/CanonicalDefectCode.lean:22` |
| `PaperC.CanonicalExactRank.canonicalSmallRowRank_le_corrected_add_components` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:250` |
| `PaperC.CanonicalExactRank.card_canonicalCoreCoordinate` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:207` |
| `PaperC.CanonicalExactRank.card_canonicalCorrectedDefectiveVertices` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:169` |
| `PaperC.CanonicalExactRank.card_correctedDefectiveVertices` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:134` |
| `PaperC.CanonicalExactRank.card_exactDefectiveVertices` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:97` |
| `PaperC.CanonicalExactRank.exactDefectiveVertices_subset_defectiveVertices` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:83` |
| `PaperC.CanonicalExactRank.finrank_canonicalSmallRowKernel` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:237` |
| `PaperC.CanonicalExactRank.mem_exactDefectiveVertices` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:74` |
| `PaperC.CanonicalExactRank.pairTau_add_kTilde_eq_corrected_add_components` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:369` |
| `PaperC.CanonicalExactRank.pairTau_eq_corrected_add_components_sub_kTilde` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:346` |
| `PaperC.CanonicalExactRank.residualTau_add_kTilde_eq_corrected_add_components` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:328` |
| `PaperC.CanonicalExactRank.residualTau_eq_corrected_add_components_sub_kTilde` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalExactRank.lean:293` |
| `PaperC.CanonicalRationalCodeWindow.canonicalRationalCode_eq_of_nonzero_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/CanonicalRationalCodeWindow.lean:25` |
| `PaperC.CanonicalResidualComponents.canonicalResidualAmbientCertificate_admissible_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:372` |
| `PaperC.CanonicalResidualComponents.canonicalResidualAmbientCertificate_coe` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:242` |
| `PaperC.CanonicalResidualComponents.canonicalResidualAmbientCertificate_moduli_pairwise` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:317` |
| `PaperC.CanonicalResidualComponents.canonicalResidualAmbientCertificate_modulusProduct` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:285` |
| `PaperC.CanonicalResidualComponents.canonicalResidualAmbientPrimeModulus_prime` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:57` |
| `PaperC.CanonicalResidualComponents.canonicalResidualAmbient_admissibleCertificateSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCertificateMassBound.lean:52` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificateModulus_prime` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCRTCertificate.lean:60` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificateToAmbientCell_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:175` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificateToAmbientCell_leftResidue` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:133` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificateToAmbientCell_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:262` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificateToAmbientCell_modulus` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:113` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificateToAmbientCell_rightResidue` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:153` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificate_mem_oneUnitExceptionalComponents_of_choice` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:624` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificates_leftOffset_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:429` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificates_mem_residualVertexPrimeCells_of_choice` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCellMembership.lean:84` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificates_not_onChannel_of_choice` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:531` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificates_prime_dvd_left` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:405` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificates_prime_dvd_residualVertexExpression` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCellMembership.lean:38` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificates_prime_dvd_right` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:417` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificates_prime_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:463` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificates_prime_large` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:396` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificates_prime_mem_residualPrimeRange_of_choice` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCellMembership.lean:117` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificates_residualExpression_ne_of_choice` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:554` |
| `PaperC.CanonicalResidualComponents.canonicalResidualCertificates_rightOffset_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:446` |
| `PaperC.CanonicalResidualComponents.canonicalResidualFullCertificate_admissible_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCRTCertificate.lean:153` |
| `PaperC.CanonicalResidualComponents.canonicalResidualFullCertificate_card` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCRTCertificate.lean:93` |
| `PaperC.CanonicalResidualComponents.canonicalResidualFullCertificate_coe` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCRTCertificate.lean:84` |
| `PaperC.CanonicalResidualComponents.canonicalResidualFullCertificate_moduli_pairwise` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCRTCertificate.lean:126` |
| `PaperC.CanonicalResidualComponents.canonicalResidualFullCertificate_modulusProduct` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCRTCertificate.lean:108` |
| `PaperC.CanonicalResidualComponents.canonicalResidualPrimeProductAtMost_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualPrimeProduct.lean:124` |
| `PaperC.CanonicalResidualComponents.canonicalResidualPrimeProductAtMost_iff_not_exceeds` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualPrimeProduct.lean:167` |
| `PaperC.CanonicalResidualComponents.canonicalResidualPrimeProductExceeds_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualPrimeProduct.lean:134` |
| `PaperC.CanonicalResidualComponents.canonicalResidualPrimeProductExceeds_iff_not_atMost` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualPrimeProduct.lean:178` |
| `PaperC.CanonicalResidualComponents.canonicalResidualPrimeProduct_branches_disjoint` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualPrimeProduct.lean:156` |
| `PaperC.CanonicalResidualComponents.canonicalResidualPrimeProduct_dichotomy` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualPrimeProduct.lean:144` |
| `PaperC.CanonicalResidualComponents.canonicalResidualPrimeProduct_eq_product_certificates` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualPrimeProduct.lean:38` |
| `PaperC.CanonicalResidualComponents.canonicalResidualPrimeProduct_factorCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualPrimeProduct.lean:98` |
| `PaperC.CanonicalResidualComponents.canonicalResidualPrimeProduct_pos` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualPrimeProduct.lean:74` |
| `PaperC.CanonicalResidualComponents.canonicalResidual_left_modEq` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCRTCertificate.lean:185` |
| `PaperC.CanonicalResidualComponents.canonicalResidual_left_satisfies_ambientCertificate` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:403` |
| `PaperC.CanonicalResidualComponents.canonicalResidual_left_satisfies_fullCertificate` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCRTCertificate.lean:213` |
| `PaperC.CanonicalResidualComponents.canonicalResidual_pair_mem_ambientCertificatePairSolutions` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:472` |
| `PaperC.CanonicalResidualComponents.canonicalResidual_pair_mem_fullCertificateSolutions` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCRTCertificate.lean:258` |
| `PaperC.CanonicalResidualComponents.canonicalResidual_right_modEq` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCRTCertificate.lean:199` |
| `PaperC.CanonicalResidualComponents.canonicalResidual_right_satisfies_ambientCertificate` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualAmbientCertificate.lean:436` |
| `PaperC.CanonicalResidualComponents.canonicalResidual_right_satisfies_fullCertificate` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCRTCertificate.lean:234` |
| `PaperC.CanonicalResidualComponents.canonical_onChannel_component_not_mem_of_choice` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:352` |
| `PaperC.CanonicalResidualComponents.card_canonicalOneUnitExceptionalComponents_le_two` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:603` |
| `PaperC.CanonicalResidualComponents.card_canonicalResidualCertificateIndex` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:482` |
| `PaperC.CanonicalResidualComponents.card_canonicalResidualCertificatePrimes` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:505` |
| `PaperC.CanonicalResidualComponents.card_canonicalResidualComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:320` |
| `PaperC.CanonicalResidualComponents.card_exactNondefectiveComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:133` |
| `PaperC.CanonicalResidualComponents.card_residualComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:165` |
| `PaperC.CanonicalResidualComponents.exactNondefectiveComponents_subset_nontrivial` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:113` |
| `PaperC.CanonicalResidualComponents.isNontrivialUnpinnedComponent_of_mem_canonicalResidualComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:296` |
| `PaperC.CanonicalResidualComponents.isNontrivialUnpinnedComponent_of_mem_residualComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:91` |
| `PaperC.CanonicalResidualComponents.mem_exactNondefectiveComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:59` |
| `PaperC.CanonicalResidualComponents.onChannel_component_not_mem_residualComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:203` |
| `PaperC.CanonicalResidualComponents.one_le_canonicalResidualPrimeProduct` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualPrimeProduct.lean:87` |
| `PaperC.CanonicalResidualComponents.prime_large_of_mem_canonicalResidualCertificatePrimes` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualPrimeProduct.lean:59` |
| `PaperC.CanonicalResidualComponents.residualCertificates_not_onChannel` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualComponents.lean:261` |
| `PaperC.CanonicalResidualComponents.sum_canonicalResidualAmbientCells_card_div_eq_residualPrimeMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCertificateMassBound.lean:31` |
| `PaperC.CanonicalResidualComponents.sum_canonicalResidualAmbient_admissibleCertificateSolutionMass_cast_le_exp` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCertificateMassBound.lean:174` |
| `PaperC.CanonicalResidualComponents.sum_canonicalResidualAmbient_admissibleCertificateSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalResidualCertificateMassBound.lean:126` |
| `PaperC.CanonicalResidualQuotient.residualTau_eq_finrank_quotient` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalResidualQuotient.lean:46` |
| `PaperC.CanonicalResidualQuotient.residualTau_eq_finrank_residualQuotient` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalResidualQuotient.lean:34` |
| `PaperC.CanonicalSectionElevenPartition.canonicalSectionElevenSectorOf_eq_nonterminal_budget_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:372` |
| `PaperC.CanonicalSectionElevenPartition.canonicalSectionElevenSectorOf_eq_seven_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:221` |
| `PaperC.CanonicalSectionElevenPartition.canonicalSectionElevenSectorOf_eq_six_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:188` |
| `PaperC.CanonicalSectionElevenPartition.canonicalSectionElevenSectorOf_eq_terminal_budget_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:340` |
| `PaperC.CanonicalSectionElevenPartition.canonicalSectionElevenSectorOf_eq_terminal_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:294` |
| `PaperC.CanonicalSectionElevenPartition.canonicalSectionElevenSectorPairs_disjoint` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:95` |
| `PaperC.CanonicalSectionElevenPartition.canonicalSectionElevenSectorPairs_terminal_eq_filter` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:466` |
| `PaperC.CanonicalSectionElevenPartition.canonical_lateSectors_eq_deepCorePairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:159` |
| `PaperC.CanonicalSectionElevenPartition.canonical_lemma_eleven_one_existsUnique_sector` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:142` |
| `PaperC.CanonicalSectionElevenPartition.canonical_lemma_eleven_one_populations_cover` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:111` |
| `PaperC.CanonicalSectionElevenPartition.mem_canonicalSectionElevenSectorPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:78` |
| `PaperC.CanonicalSectionElevenPartition.mem_deepCorePairs_iff_sectionEleven_prefix` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:266` |
| `PaperC.CanonicalSectionElevenPartition.mem_nonalignedTerminalPairsAtBudget` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:447` |
| `PaperC.CanonicalSectionElevenPartition.pairSigma_eq_zero_of_isCanonicallyNonaligned` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalSectionElevenPartition.lean:253` |
| `PaperC.CanonicalSmallRows.blockBoundaryRow_one_apply` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:506` |
| `PaperC.CanonicalSmallRows.blockBoundaryRow_zero_apply` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:499` |
| `PaperC.CanonicalSmallRows.canonicalArithmeticKernelEquivalence_of_choice_none` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:1179` |
| `PaperC.CanonicalSmallRows.canonicalArithmeticKernelStatement` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:1204` |
| `PaperC.CanonicalSmallRows.canonicalArithmeticSmallRowMatrixRaw_mulVec` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:647` |
| `PaperC.CanonicalSmallRows.canonicalArithmeticSmallRowMatrix_block_apply` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:565` |
| `PaperC.CanonicalSmallRows.canonicalArithmeticSmallRowMatrix_mulVec_block` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:702` |
| `PaperC.CanonicalSmallRows.canonicalArithmeticSmallRowMatrix_mulVec_prime` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:672` |
| `PaperC.CanonicalSmallRows.canonicalArithmeticSmallRowMatrix_prime_apply` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:551` |
| `PaperC.CanonicalSmallRows.canonicalArithmeticSmallRowMatrix_prime_inl` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:578` |
| `PaperC.CanonicalSmallRows.canonicalArithmeticSmallRowMatrix_prime_inr` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:605` |
| `PaperC.CanonicalSmallRows.canonicalCoreBoundaryColumn_apply` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:179` |
| `PaperC.CanonicalSmallRows.canonicalCoreBoundaryColumn_eq_indicator` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:193` |
| `PaperC.CanonicalSmallRows.canonicalCoreBoundaryColumn_inl` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:208` |
| `PaperC.CanonicalSmallRows.canonicalCoreBoundaryColumn_mem_largePrimeSolution` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:229` |
| `PaperC.CanonicalSmallRows.canonicalCoreBoundarySynthesis_apply` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:348` |
| `PaperC.CanonicalSmallRows.canonicalCoreBoundarySynthesis_apply_componentOut` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:386` |
| `PaperC.CanonicalSmallRows.canonicalCoreBoundarySynthesis_injective` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:416` |
| `PaperC.CanonicalSmallRows.canonicalCoreBoundarySynthesis_mem_largePrimeSolution` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:359` |
| `PaperC.CanonicalSmallRows.canonicalCoreBoundarySynthesis_relationToCoordinates_of_choice_none` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:1035` |
| `PaperC.CanonicalSmallRows.canonicalCoreBoundaryToLargePrime_injective` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:430` |
| `PaperC.CanonicalSmallRows.canonicalCoreComponent_injective` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:260` |
| `PaperC.CanonicalSmallRows.canonicalCoreComponent_unpinned` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:118` |
| `PaperC.CanonicalSmallRows.canonicalSmallRowPresentation_of_arithmeticKernel` | conditionnel | `PCv07c-L9.10-arithmetic-kernel-equivalence` | `internal` | `discharged` | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:1217` |
| `PaperC.CanonicalSmallRows.componentVertices_defective_eq_singleton` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:142` |
| `PaperC.CanonicalSmallRows.correctedDefectiveVertices_subset_defectiveVertices` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:88` |
| `PaperC.CanonicalSmallRows.existsUnique_twoStartCompleteBoundary_eq_of_blockRows` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:736` |
| `PaperC.CanonicalSmallRows.finrank_canonicalCoreCoordinates_eq_largePrimeSolution_of_choice_none` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:977` |
| `PaperC.CanonicalSmallRows.isDefective_of_mem_canonicalCorrectedDefectiveVertices` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:100` |
| `PaperC.CanonicalSmallRows.mem_kernel_iff_existsUnique_relation_boundary` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:799` |
| `PaperC.CanonicalSmallRows.primeBoundaryRow_apply` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:467` |
| `PaperC.CanonicalSmallRows.primeBoundaryRow_eq_zero_of_mem_largePrimeSolution` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:775` |
| `PaperC.CanonicalSmallRows.relationToCanonicalArithmeticKernel_of_choice_none_injective` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:1092` |
| `PaperC.CanonicalSmallRows.relationToCanonicalArithmeticKernel_of_choice_none_surjective` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:1123` |
| `PaperC.CanonicalSmallRows.residualTau_eq_corrected_add_components_sub_arithmeticRank` | conditionnel | `PCv07c-L9.10-arithmetic-kernel-equivalence` | `internal` | `discharged` | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:1242` |
| `PaperC.CanonicalSmallRows.residualTau_eq_corrected_add_components_sub_arithmeticRank_of_choice_none` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/CanonicalSmallRows.lean:1272` |
| `PaperC.CanonicalTerminalPopulation.canonicalResidualComponentCount_le_runLength` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalTerminalPopulation.lean:85` |
| `PaperC.CanonicalTerminalPopulation.canonical_terminal_component_count` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalTerminalPopulation.lean:122` |
| `PaperC.CanonicalTerminalPopulation.card_canonicalResidualComponents_eq_runLength_sub_slack` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalTerminalPopulation.lean:102` |
| `PaperC.CanonicalTerminalPopulation.card_terminalPairsAtBudget_eq_sum_partnerFibers` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalTerminalPopulation.lean:294` |
| `PaperC.CanonicalTerminalPopulation.card_terminalPairsAtBudget_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalTerminalPopulation.lean:350` |
| `PaperC.CanonicalTerminalPopulation.card_terminalPairsAtBudget_le_firstStarts_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalTerminalPopulation.lean:319` |
| `PaperC.CanonicalTerminalPopulation.linearResidualWeight_eq_two_pow_sub_one` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalTerminalPopulation.lean:234` |
| `PaperC.CanonicalTerminalPopulation.mem_terminalPairsAtBudget` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalTerminalPopulation.lean:196` |
| `PaperC.CanonicalTerminalPopulation.pairTau_le_runLength_add_two` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalTerminalPopulation.lean:212` |
| `PaperC.CanonicalTerminalPopulation.terminalResidualMassAtBudget_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/CanonicalTerminalPopulation.lean:262` |
| `PaperC.CappedRadiusDyadic.pow_two_cappedRadius_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/CappedRadiusDyadic.lean:22` |
| `PaperC.CappedRadiusDyadic.pow_two_cappedRadius_le_of_threshold` | inconditionnel | — | — | — | `PaperC/Asymptotics/CappedRadiusDyadic.lean:79` |
| `PaperC.CappedRadiusDyadic.uniformSubpolynomialOn_two_cappedRadius` | inconditionnel | — | — | — | `PaperC/Asymptotics/CappedRadiusDyadic.lean:109` |
| `PaperC.ChebyshevPrimeCount.count_le_pow_halfLog_add_div` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChebyshevPrimeCount.lean:112` |
| `PaperC.ChebyshevPrimeCount.count_le_pow_halfLog_add_div_of_four_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChebyshevPrimeCount.lean:120` |
| `PaperC.ChebyshevPrimeCount.count_le_seven_mul_div_log` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChebyshevPrimeCount.lean:233` |
| `PaperC.ChebyshevPrimeCount.halfLog_mul_card_highPrimes_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChebyshevPrimeCount.lean:79` |
| `PaperC.ChebyshevPrimeCount.log_mul_count_le_seven_mul` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChebyshevPrimeCount.lean:217` |
| `PaperC.ComponentNormalization.canonical_normalization` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:234` |
| `PaperC.ComponentNormalization.canonical_normalization_polynomial_bound` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:296` |
| `PaperC.ComponentNormalization.canonical_squarefree_decomposition` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:86` |
| `PaperC.ComponentNormalization.exists_normalized_right_factor` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:271` |
| `PaperC.ComponentNormalization.normalizedShiftedEquation_atMost_of_evertseSilverman` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Diophantine/ComponentNormalization.lean:591` |
| `PaperC.ComponentNormalization.oneShiftEquation_atMost_sqrt` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:362` |
| `PaperC.ComponentNormalization.oneShiftEquation_root_le_sqrt` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:345` |
| `PaperC.ComponentNormalization.parityVec_right_factor` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:195` |
| `PaperC.ComponentNormalization.prime_of_mem_oddPrimeSupport'` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:39` |
| `PaperC.ComponentNormalization.snd_injective_on_oneShiftEquation` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:329` |
| `PaperC.ComponentNormalization.squarefreeKernel_dvd` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:98` |
| `PaperC.ComponentNormalization.squarefreeKernel_eq_of_parityVec_eq` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:114` |
| `PaperC.ComponentNormalization.squarefreeKernel_le` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:105` |
| `PaperC.ComponentNormalization.squarefreeKernel_pos` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:76` |
| `PaperC.ComponentNormalization.squarefreeKernel_squarefree` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:69` |
| `PaperC.ComponentNormalization.squarefree_decomposition_unique` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:168` |
| `PaperC.ComponentNormalization.squarefree_factor_unique` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:127` |
| `PaperC.ComponentNormalization.squarefree_prod_primes` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:45` |
| `PaperC.ComponentNormalization.toPellPair_injective` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:413` |
| `PaperC.ComponentNormalization.twoShiftEquation_maps_to_pell` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:444` |
| `PaperC.ComponentNormalization.twoShiftEquation_one_factorization` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:460` |
| `PaperC.ComponentNormalization.twoShiftPellBox_atMost` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:489` |
| `PaperC.ComponentNormalization.twoShiftPolynomialBox_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Diophantine/ComponentNormalization.lean:570` |
| `PaperC.ComponentNormalization.twoShiftPolynomialBox_of_pell` | inconditionnel | — | — | — | `PaperC/Diophantine/ComponentNormalization.lean:544` |
| `PaperC.ComponentProductParity.card_componentVertices` | inconditionnel | — | — | — | `PaperC/Combinatorics/ComponentProductParity.lean:61` |
| `PaperC.ComponentProductParity.componentVertexLabel_pos` | inconditionnel | — | — | — | `PaperC/Combinatorics/ComponentProductParity.lean:89` |
| `PaperC.ComponentProductParity.componentVertexProduct_large_parity_eq_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/ComponentProductParity.lean:113` |
| `PaperC.ComponentProductParity.componentVertexProduct_pos` | inconditionnel | — | — | — | `PaperC/Combinatorics/ComponentProductParity.lean:100` |
| `PaperC.ComponentProductParity.componentVertexProduct_smallPrime_coverage` | inconditionnel | — | — | — | `PaperC/Combinatorics/ComponentProductParity.lean:152` |
| `PaperC.ComponentProductParity.not_isPinnedComponent_of_isNontrivialUnpinned` | inconditionnel | — | — | — | `PaperC/Combinatorics/ComponentProductParity.lean:72` |
| `PaperC.ComponentSquareClass.canonical_decomposition` | inconditionnel | — | — | — | `PaperC/Arithmetic/ComponentSquareClass.lean:83` |
| `PaperC.ComponentSquareClass.componentProduct_pos` | inconditionnel | — | — | — | `PaperC/Arithmetic/ComponentSquareClass.lean:41` |
| `PaperC.ComponentSquareClass.componentSquareClass_unique` | inconditionnel | — | — | — | `PaperC/Arithmetic/ComponentSquareClass.lean:135` |
| `PaperC.ComponentSquareClass.decomposition_unique` | inconditionnel | — | — | — | `PaperC/Arithmetic/ComponentSquareClass.lean:185` |
| `PaperC.ComponentSquareClass.exists_squarefree_mul_sq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ComponentSquareClass.lean:118` |
| `PaperC.ComponentSquareClass.largeOddKernel_componentProduct_eq_one` | inconditionnel | — | — | — | `PaperC/Arithmetic/ComponentSquareClass.lean:52` |
| `PaperC.ConditionalAGGAverage.averagedConditionalGood_natTotalVariation_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/ConditionalAGGAverage.lean:235` |
| `PaperC.ConditionalAGGAverage.averagedConditionalGood_natTotalVariation_le_finiteMajorant` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/ConditionalAGGAverage.lean:847` |
| `PaperC.ConditionalAGGAverage.averagedConditionalGood_natTotalVariation_le_steinTerms` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/ConditionalAGGAverage.lean:827` |
| `PaperC.ConditionalAGGAverage.bOne_conditionedGoodIndicator_eq_steinBOne` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:427` |
| `PaperC.ConditionalAGGAverage.card_event_eq_sum_card_fibers` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:534` |
| `PaperC.ConditionalAGGAverage.card_sampleSpace_eq_mul` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:552` |
| `PaperC.ConditionalAGGAverage.commonConditionalGoodPoissonLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:173` |
| `PaperC.ConditionalAGGAverage.conditionalBOneAverage_eq_steinBOne` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:454` |
| `PaperC.ConditionalAGGAverage.conditionalBTwoAverage_eq_steinBTwoAverage` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:819` |
| `PaperC.ConditionalAGGAverage.conditionalBTwoAverage_eq_steinBTwoAverage_of_jointAverage` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:738` |
| `PaperC.ConditionalAGGAverage.conditionalGoodLaw_eq_finiteNatLaw` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:145` |
| `PaperC.ConditionalAGGAverage.conditionalGoodLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:179` |
| `PaperC.ConditionalAGGAverage.conditionalGood_natTotalVariation_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/ConditionalAGGAverage.lean:202` |
| `PaperC.ConditionalAGGAverage.conditionalJointAverageStatement` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:637` |
| `PaperC.ConditionalAGGAverage.finiteUniformAverage_finsetSum` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:477` |
| `PaperC.ConditionalAGGAverage.finiteUniformAverage_fintypeSum` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:468` |
| `PaperC.ConditionalAGGAverage.finiteUniformAverage_largeEventProbability_eq_full` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:600` |
| `PaperC.ConditionalAGGAverage.finiteUniformAverage_mono` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:89` |
| `PaperC.ConditionalAGGAverage.finiteUniformProbability_eq_average_fibers` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:567` |
| `PaperC.ConditionalAGGAverage.finiteUniformProbability_eq_uniformEventProbability` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:587` |
| `PaperC.ConditionalAGGAverage.matchingPoissonLaw_conditionedGoodIndicator_eq_common` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:123` |
| `PaperC.ConditionalAGGAverage.pair_mem_closedDependencyPairs_iff` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:304` |
| `PaperC.ConditionalAGGAverage.pair_mem_orderedDependencyEdges_iff` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:655` |
| `PaperC.ConditionalAGGAverage.poissonParameter_conditionedGoodIndicator_eq` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:104` |
| `PaperC.ConditionalAGGAverage.sum_card_closedNeighborhood_eq` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:395` |
| `PaperC.ConditionalAGGAverage.summable_abs_conditionalGoodLaw_sub_commonPoisson` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:187` |
| `PaperC.ConditionalAGGAverage.summable_commonConditionalGoodPoissonLaw` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:167` |
| `PaperC.ConditionalAGGAverage.summable_conditionalGoodLaw` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGAverage.lean:159` |
| `PaperC.ConditionalAGGCritical.averagedConditionalGoodTotalVariation_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/ConditionalAGGCritical.lean:39` |
| `PaperC.ConditionalAGGInstantiation.conditionalGood_totalVariationToPoisson_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/ConditionalAGGInstantiation.lean:322` |
| `PaperC.ConditionalAGGInstantiation.conditionedGoodIndicator_eq_false_iff` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGInstantiation.lean:86` |
| `PaperC.ConditionalAGGInstantiation.conditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGInstantiation.lean:96` |
| `PaperC.ConditionalAGGInstantiation.conditionedGoodIndicator_eq_true_iff` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGInstantiation.lean:75` |
| `PaperC.ConditionalAGGInstantiation.eventProbability_largeUniformPMF_eq` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGInstantiation.lean:46` |
| `PaperC.ConditionalAGGInstantiation.finiteUniformProbability_conditionedStart_eq` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGInstantiation.lean:141` |
| `PaperC.ConditionalAGGInstantiation.hasExactDependencyGraph_conditionedGoodIndicator` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGInstantiation.lean:197` |
| `PaperC.ConditionalAGGInstantiation.marginal_conditionedGoodIndicator_eq_baseline` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalAGGInstantiation.lean:163` |
| `PaperC.ConditionalDependencyGraph.card_jointConditionedStartSolutions_mul_two_pow` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:716` |
| `PaperC.ConditionalDependencyGraph.conditionedStartAt_iff_of_eqOn_largePrimeCoordinates` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:343` |
| `PaperC.ConditionalDependencyGraph.conditionedStart_independent_of_nonNeighbors` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:426` |
| `PaperC.ConditionalDependencyGraph.disjoint_largePrimeCoordinates_of_not_adjacent` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:327` |
| `PaperC.ConditionalDependencyGraph.finiteUniformProbability_and_eq_mul_of_product_support` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:60` |
| `PaperC.ConditionalDependencyGraph.goodStart_independent_of_graph_nonNeighbors` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:526` |
| `PaperC.ConditionalDependencyGraph.jointConditionedStartProbability_eq_baseline` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:789` |
| `PaperC.ConditionalDependencyGraph.jointConditionedStartProbability_eq_product` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:834` |
| `PaperC.ConditionalDependencyGraph.jointConditionedSystem_eq_iff_forall_startAt` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:594` |
| `PaperC.ConditionalDependencyGraph.jointLargeStartSystem_apply` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:583` |
| `PaperC.ConditionalDependencyGraph.jointLargeStartSystem_surjective` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:635` |
| `PaperC.ConditionalDependencyGraph.largeStartSystem_eq_of_eqOn_largePrimeCoordinates` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:207` |
| `PaperC.ConditionalDependencyGraph.largeStartSystem_maskToStartCoordinates` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:281` |
| `PaperC.ConditionalDependencyGraph.largeStartSystem_mask_eq_zero_of_disjoint` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:299` |
| `PaperC.ConditionalDependencyGraph.largeStartSystem_surjective_of_mem_goodStarts` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:612` |
| `PaperC.ConditionalDependencyGraph.valueBit_extendLarge_eq_of_eqOn_largePrimeCoordinates` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalDependencyGraph.lean:173` |
| `PaperC.ConditionalExpectationAverage.abs_finiteUniformAverage_sub_le` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalExpectationAverage.lean:35` |
| `PaperC.ConditionalExpectationAverage.finiteRademacherIntegral_eq_uniformPMFExpectation` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalExpectationAverage.lean:101` |
| `PaperC.ConditionalExpectationAverage.finiteUniformAverage_largePMFExpectation_eq_full` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalExpectationAverage.lean:60` |
| `PaperC.ConditionalStartProbability.assemble_restrictions` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:162` |
| `PaperC.ConditionalStartProbability.assemble_solves_start_iff` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:206` |
| `PaperC.ConditionalStartProbability.assemble_startAt_iff` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:219` |
| `PaperC.ConditionalStartProbability.card_conditionedStartSolutions_mul_two_pow` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:532` |
| `PaperC.ConditionalStartProbability.conditionedStartProbability_eq_baseline` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:581` |
| `PaperC.ConditionalStartProbability.conditionedStartProbability_eq_baseline_of_not_terminalBad` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:623` |
| `PaperC.ConditionalStartProbability.largeStartSystem_surjective` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:483` |
| `PaperC.ConditionalStartProbability.relationSpace_largeStartSystem_eq_bot` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:361` |
| `PaperC.ConditionalStartProbability.restrictLarge_assemble` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:156` |
| `PaperC.ConditionalStartProbability.restrictLarge_extendLarge` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:143` |
| `PaperC.ConditionalStartProbability.restrictLarge_extendSmall` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:136` |
| `PaperC.ConditionalStartProbability.restrictSmall_assemble` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:150` |
| `PaperC.ConditionalStartProbability.restrictSmall_extendLarge` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:129` |
| `PaperC.ConditionalStartProbability.restrictSmall_extendSmall` | inconditionnel | — | — | — | `PaperC/Probability/ConditionalStartProbability.lean:122` |
| `PaperC.CorollaryFourteenEightCounts.coe_independentPoissonExactLengthRate` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:57` |
| `PaperC.CorollaryFourteenEightCounts.corollary_fourteen_eight_counts` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:364` |
| `PaperC.CorollaryFourteenEightCounts.corollary_fourteen_eight_counts_of_averaged_conditional_law` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:319` |
| `PaperC.CorollaryFourteenEightCounts.corollary_fourteen_eight_counts_of_retained_finite_law` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:253` |
| `PaperC.CorollaryFourteenEightCounts.encodedIndependentPoissonExactLengthLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:93` |
| `PaperC.CorollaryFourteenEightCounts.encodedIndependentPoissonExactLengthLaw_primeCode` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:123` |
| `PaperC.CorollaryFourteenEightCounts.encodedIndependentPoissonExactLengthLaw_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:114` |
| `PaperC.CorollaryFourteenEightCounts.hasSum_encodedIndependentPoissonExactLengthLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:99` |
| `PaperC.CorollaryFourteenEightCounts.independentPoissonExactLengthVectorMass_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:75` |
| `PaperC.CorollaryFourteenEightCounts.inversePowerTransform_encodedIndependentPoissonExactLengthLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:135` |
| `PaperC.CorollaryFourteenEightCounts.inversePowerTransform_encodedIndependentPoissonExactLengthLaw_eq_limit` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:169` |
| `PaperC.CorollaryFourteenEightCounts.totalRemovedInfiniteExactLengthProbability_tendsto_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightCounts.lean:211` |
| `PaperC.CorollaryFourteenEightMaximum.abs_infiniteMaximumAtMostProbability_sub_exp_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightMaximum.lean:208` |
| `PaperC.CorollaryFourteenEightMaximum.corollary_fourteen_eight_maximum` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/CorollaryFourteenEightMaximum.lean:238` |
| `PaperC.CorollaryFourteenEightMaximum.fullMaskedDyadicCount_eq_zero_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightMaximum.lean:132` |
| `PaperC.CorollaryFourteenEightMaximum.fullMaskedDyadicStartLaw_zero_eq_finiteUniform` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightMaximum.lean:141` |
| `PaperC.CorollaryFourteenEightMaximum.infiniteMaximumAtMostProbability_eq_finiteLaw_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightMaximum.lean:177` |
| `PaperC.CorollaryFourteenEightMaximum.infiniteNoDyadicStartEvent_eq_preimage` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightMaximum.lean:71` |
| `PaperC.CorollaryFourteenEightMaximum.infiniteNoDyadicStartProbability_eq_finiteUniform` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightMaximum.lean:110` |
| `PaperC.CorollaryFourteenEightMaximum.measurableSet_finiteNoDyadicStartEvent` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightMaximum.lean:63` |
| `PaperC.CorollaryFourteenEightMaximum.shiftedMaskedTargetPoissonLaw_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryFourteenEightMaximum.lean:188` |
| `PaperC.CorollaryPrefixLaw.boundary_or_exists_overflow_start_of_counts_ne` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:407` |
| `PaperC.CorollaryPrefixLaw.disagreementProbability_prefix_global_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:441` |
| `PaperC.CorollaryPrefixLaw.finitePrefixStartCount_restrictToFinite_eq_infinitePrefixStartCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:246` |
| `PaperC.CorollaryPrefixLaw.globalStartIndices_eq_prefixInterior_union_overflow` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:385` |
| `PaperC.CorollaryPrefixLaw.infinitePrefixBoundaryEvent_eq_preimage` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:612` |
| `PaperC.CorollaryPrefixLaw.infinitePrefixBoundaryEvent_subset_zeroPrefix` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:676` |
| `PaperC.CorollaryPrefixLaw.infinitePrefixStartCountEvent_eq_preimage` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:318` |
| `PaperC.CorollaryPrefixLaw.infinitePrefixStartCount_eq_zero_iff_longest_lt` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:231` |
| `PaperC.CorollaryPrefixLaw.infinitePrefixStartCount_law_eq_prefixStartLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:354` |
| `PaperC.CorollaryPrefixLaw.measurableSet_finitePrefixStartCountEvent` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:332` |
| `PaperC.CorollaryPrefixLaw.measurableSet_infinitePrefixBoundaryEvent` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:642` |
| `PaperC.CorollaryPrefixLaw.measurableSet_infinitePrefixStartCountEvent` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:336` |
| `PaperC.CorollaryPrefixLaw.natTotalVariation_prefix_global_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:529` |
| `PaperC.CorollaryPrefixLaw.prefixBoundaryProbability_eq_measure` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:652` |
| `PaperC.CorollaryPrefixLaw.prefixBoundaryProbability_le_geometric` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:706` |
| `PaperC.CorollaryPrefixLaw.prefixConstantStretchLengths_nonempty` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:51` |
| `PaperC.CorollaryPrefixLaw.prefixConstantStretch_length_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:65` |
| `PaperC.CorollaryPrefixLaw.prefixHasConstantStretch_iff_boundary_or_start` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:137` |
| `PaperC.CorollaryPrefixLaw.prefixHasConstantStretch_mono` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:72` |
| `PaperC.CorollaryPrefixLaw.prefixInterior_overflow_disjoint` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:394` |
| `PaperC.CorollaryPrefixLaw.prefixLongestConstantStretch_lt_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:84` |
| `PaperC.CorollaryPrefixLaw.prefixLongestStretchBelowProbability_eq_measure` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:791` |
| `PaperC.CorollaryPrefixLaw.prefixOverflowBase_in_runLengthWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:727` |
| `PaperC.CorollaryPrefixLaw.prefixOverflowStartIndices_card_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:561` |
| `PaperC.CorollaryPrefixLaw.prefixOverflowStartIndices_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:546` |
| `PaperC.CorollaryPrefixLaw.prefixOverflowStartIndices_subset_dyadicBlock` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:551` |
| `PaperC.CorollaryPrefixLaw.prefixOverflowStartMass_eq_maskedDyadicExpectation` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:568` |
| `PaperC.CorollaryPrefixLaw.prefixStartCount_eq_zero_iff_longest_lt` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLaw.lean:208` |
| `PaperC.CorollaryPrefixLawCanonical.corollary_prefix_law_canonical` | conditionnel | `ADGR07-PNT`, `AGG89-T1-finite-dependency-b3-zero`, `BS93-Theorem-1`, `ES86-T1b-Q-split-n2`, `LS04-Corollary-1`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/CorollaryPrefixLawCanonical.lean:320` |
| `PaperC.CorollaryPrefixLawCanonical.finitePrefixBoundaryProbability_eq_infinite` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLawCanonical.lean:34` |
| `PaperC.CorollaryPrefixLawCanonical.finitePrefixBoundaryProbability_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLawCanonical.lean:45` |
| `PaperC.CorollaryPrefixLawCanonical.infinitePrefixEmptyProbability_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLawCanonical.lean:190` |
| `PaperC.CorollaryPrefixLawCanonical.infinitePrefixLongestStretchBelowProbability_eq_empty` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLawCanonical.lean:267` |
| `PaperC.CorollaryPrefixLawCanonical.infinitePrefixLongestStretchBelowProbability_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLawCanonical.lean:278` |
| `PaperC.CorollaryPrefixLawCanonical.infinitePrefixStartLaw_poisson_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLawCanonical.lean:172` |
| `PaperC.CorollaryPrefixLawCanonical.prefixRange_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLawCanonical.lean:62` |
| `PaperC.CorollaryPrefixLawCanonical.prefixStartLaw_poisson_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryPrefixLawCanonical.lean:99` |
| `PaperC.CorollaryThirteenTen.averagedConditionalGoodTotalVariation_uniformBigO_explicitRate_of_steinBTwo` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/CorollaryThirteenTen.lean:698` |
| `PaperC.CorollaryThirteenTen.corollary_thirteen_ten_uniformBigO_canonical` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/CorollaryThirteenTen.lean:873` |
| `PaperC.CorollaryThirteenTen.corollary_thirteen_ten_uniformBigO_of_averagedConditional` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:759` |
| `PaperC.CorollaryThirteenTen.corollary_thirteen_ten_uniformBigO_of_homogeneousMass` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/CorollaryThirteenTen.lean:839` |
| `PaperC.CorollaryThirteenTen.dependencyEdgeHarmonicTerm_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:53` |
| `PaperC.CorollaryThirteenTen.dependencyEdgeLinearTerm_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:96` |
| `PaperC.CorollaryThirteenTen.dependencyEdgeMainTerm_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:138` |
| `PaperC.CorollaryThirteenTen.dependencyEdgeMainTerm_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:286` |
| `PaperC.CorollaryThirteenTen.dyadicLength_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:439` |
| `PaperC.CorollaryThirteenTen.orderedDependencyEdges_terminalCutoff_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:349` |
| `PaperC.CorollaryThirteenTen.runLengthAddOneSquared_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:41` |
| `PaperC.CorollaryThirteenTen.separatedDefectMass_uniformBigO_of_homogeneousMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:524` |
| `PaperC.CorollaryThirteenTen.steinBOneNumerator_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:545` |
| `PaperC.CorollaryThirteenTen.steinBOne_uniformBigO_explicitRate` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:596` |
| `PaperC.CorollaryThirteenTen.steinBTwoAverage_uniformBigO_explicitRate_of_numerator` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:638` |
| `PaperC.CorollaryThirteenTen.steinBTwoNumerator_uniformBigO_of_separatedDefectMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:568` |
| `PaperC.CorollaryThirteenTen.theorem_one_one_infinite_model` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/CorollaryThirteenTen.lean:915` |
| `PaperC.CorollaryThirteenTen.theorem_one_one_uniformBigO_canonical` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/CorollaryThirteenTen.lean:894` |
| `PaperC.CorollaryThirteenTen.touchingMass_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:494` |
| `PaperC.CorollaryThirteenTen.touchingOffDiagPairs_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorollaryThirteenTen.lean:458` |
| `PaperC.CorrectedDefectEnvelope.canonicalCorrectedDefectCount_le_max` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorrectedDefectEnvelope.lean:35` |
| `PaperC.CorrectedDefectEnvelope.four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorrectedDefectEnvelope.lean:178` |
| `PaperC.CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorrectedDefectEnvelope.lean:52` |
| `PaperC.CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount_log_bound_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/CorrectedDefectEnvelope.lean:90` |
| `PaperC.CriticalChannelPowers.four_pow_half_cast_le_balance_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalChannelPowers.lean:100` |
| `PaperC.CriticalChannelPowers.four_pow_third_cast_cube_le_balance_sq_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalChannelPowers.lean:130` |
| `PaperC.CriticalChannelPowers.two_pow_runLength_le_balance_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalChannelPowers.lean:24` |
| `PaperC.CriticalChannelPowers.two_pow_third_cast_cube_le_balance_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalChannelPowers.lean:113` |
| `PaperC.CriticalFirstMoment.abs_cast_dyadicExpectation_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Probability/CriticalFirstMoment.lean:50` |
| `PaperC.CriticalFirstMoment.abs_dyadicExpectation_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Probability/CriticalFirstMoment.lean:20` |
| `PaperC.CriticalFirstMoment.normalized_error_le_defectMass` | inconditionnel | — | — | — | `PaperC/Probability/CriticalFirstMoment.lean:81` |
| `PaperC.CriticalFirstMoment.normalized_error_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Probability/CriticalFirstMoment.lean:126` |
| `PaperC.CriticalPointwiseIntervals.criticalWindow_transport` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalPointwiseIntervals.lean:26` |
| `PaperC.CriticalPointwiseIntervals.log_div_loglog_le_four` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalPointwiseIntervals.lean:84` |
| `PaperC.CriticalPointwiseIntervals.pointwise_all_intervals_on_window` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalPointwiseIntervals.lean:190` |
| `PaperC.CriticalRationalMass.rationalMass_four_uniformFiveThird` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalRationalMass.lean:46` |
| `PaperC.CriticalRationalMass.rationalMass_two_uniformFourThird` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalRationalMass.lean:21` |
| `PaperC.CriticalRationalMassEnvelopes.fiveThirdResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalRationalMassEnvelopes.lean:219` |
| `PaperC.CriticalRationalMassEnvelopes.fourThirdResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalRationalMassEnvelopes.lean:203` |
| `PaperC.CriticalRationalMassEnvelopes.rationalMassEnvelope_four_cube_bound` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalRationalMassEnvelopes.lean:344` |
| `PaperC.CriticalRationalMassEnvelopes.rationalMassEnvelope_four_uniformFiveThird` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalRationalMassEnvelopes.lean:461` |
| `PaperC.CriticalRationalMassEnvelopes.rationalMassEnvelope_le_common` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalRationalMassEnvelopes.lean:34` |
| `PaperC.CriticalRationalMassEnvelopes.rationalMassEnvelope_two_cube_bound` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalRationalMassEnvelopes.lean:236` |
| `PaperC.CriticalRationalMassEnvelopes.rationalMassEnvelope_two_uniformFourThird` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalRationalMassEnvelopes.lean:449` |
| `PaperC.CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/CriticalRationalMassEnvelopes.lean:146` |
| `PaperC.CriticalRunWindow.balanceConstant_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/CriticalRunWindow.lean:41` |
| `PaperC.CriticalRunWindow.firstMomentWindow_eventually` | inconditionnel | — | — | — | `PaperC/Probability/CriticalRunWindow.lean:51` |
| `PaperC.CriticalRunWindow.firstMoment_error_uniformNegativeHalfPower` | inconditionnel | — | — | — | `PaperC/Probability/CriticalRunWindow.lean:176` |
| `PaperC.CriticalRunWindow.lowerConstant_lt_upperConstant` | inconditionnel | — | — | — | `PaperC/Probability/CriticalRunWindow.lean:34` |
| `PaperC.CriticalRunWindow.lowerConstant_pos` | inconditionnel | — | — | — | `PaperC/Probability/CriticalRunWindow.lean:30` |
| `PaperC.CriticalRunWindow.normalized_error_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Probability/CriticalRunWindow.lean:150` |
| `PaperC.CriticalTouchingPairs.maxTouchingRho_log_bound_eventually` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalTouchingPairs.lean:40` |
| `PaperC.CriticalTouchingPairs.touchingMass_uniformLinearSubpolynomial` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalTouchingPairs.lean:127` |
| `PaperC.CriticalTouchingPairs.touchingRho_le_card_defectsInInterval` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalTouchingPairs.lean:24` |
| `PaperC.CriticalTouchingPairs.two_pow_maxTouchingRho_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalTouchingPairs.lean:104` |
| `PaperC.CriticalWeightedDefect.admissible_eventually` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWeightedDefect.lean:335` |
| `PaperC.CriticalWeightedDefect.dyadicDefectMass_cast_le` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWeightedDefect.lean:54` |
| `PaperC.CriticalWeightedDefect.dyadicDefectMass_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWeightedDefect.lean:195` |
| `PaperC.CriticalWeightedDefect.dyadicDefectMass_uniformHalfPower_on_window` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWeightedDefect.lean:409` |
| `PaperC.CriticalWeightedDefect.eventually_loglog_le_eight_log_height` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWeightedDefect.lean:226` |
| `PaperC.CriticalWeightedDefect.height_tends_to_infinity` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWeightedDefect.lean:95` |
| `PaperC.CriticalWeightedDefect.pointwise_uniformBigO` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWeightedDefect.lean:288` |
| `PaperC.CriticalWeightedDefect.pointwise_uniformBigO_on_window` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWeightedDefect.lean:428` |
| `PaperC.CriticalWeightedDefect.residualFactor_nonneg` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWeightedDefect.lean:84` |
| `PaperC.CriticalWeightedDefect.residualFactor_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWeightedDefect.lean:120` |
| `PaperC.CriticalWindowParameters.H_le_codingConstant_mul_logarithmicCap` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:193` |
| `PaperC.CriticalWindowParameters.cappedRadius_conditions_of_criticalWindow` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:356` |
| `PaperC.CriticalWindowParameters.cappedRadius_le_logarithmicCap` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:119` |
| `PaperC.CriticalWindowParameters.chebyshevDemand_le_mul_requiredRadius` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:279` |
| `PaperC.CriticalWindowParameters.chebyshev_budget_of_scaled_log_le` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:303` |
| `PaperC.CriticalWindowParameters.c₂_le_codingConstant` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:172` |
| `PaperC.CriticalWindowParameters.four_le_H_of_criticalWindow` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:324` |
| `PaperC.CriticalWindowParameters.le_cappedRadius_of_scaled_log_le` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:142` |
| `PaperC.CriticalWindowParameters.log_le_logarithmicCap` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:66` |
| `PaperC.CriticalWindowParameters.one_le_codingConstant` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:163` |
| `PaperC.CriticalWindowParameters.one_le_logarithmicCap` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:71` |
| `PaperC.CriticalWindowParameters.one_le_requiredRadius` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:287` |
| `PaperC.CriticalWindowParameters.one_le_rungeDenominator` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:98` |
| `PaperC.CriticalWindowParameters.rungeDenominator_pos` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:78` |
| `PaperC.CriticalWindowParameters.rungeLog_le_criticalEnvelope` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:217` |
| `PaperC.CriticalWindowParameters.scaled_log_le_of_criticalEnvelope` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:252` |
| `PaperC.CriticalWindowParameters.sum_two_pow_localCount_sub_one_cast_le_of_criticalWindow` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:410` |
| `PaperC.CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowParameters.lean:335` |
| `PaperC.CriticalWindowScale.log_comparisons_of_criticalLogThreshold` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowScale.lean:314` |
| `PaperC.CriticalWindowScale.one_zero_two_four_mul_log_le_self` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowScale.lean:281` |
| `PaperC.CriticalWindowScale.real_log_le_nat_log_two` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowScale.lean:28` |
| `PaperC.CriticalWindowScale.requiredRadius_cast_le` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowScale.lean:110` |
| `PaperC.CriticalWindowScale.scaled_log_le_eventually` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowScale.lean:457` |
| `PaperC.CriticalWindowScale.scaled_log_le_of_criticalLogThreshold` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowScale.lean:435` |
| `PaperC.CriticalWindowScale.scaled_log_le_of_log_comparisons` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowScale.lean:206` |
| `PaperC.CriticalWindowScale.two_fifty_six_mul_c₂_le_codingConstant` | inconditionnel | — | — | — | `PaperC/Analysis/CriticalWindowScale.lean:92` |
| `PaperC.CycleSpaceDimension.card_nonRoot` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:187` |
| `PaperC.CycleSpaceDimension.card_vertices_sub_components_le_finrank_incidenceRange` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:200` |
| `PaperC.CycleSpaceDimension.card_vertices_sub_components_le_rank_representedEdgeMap` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:313` |
| `PaperC.CycleSpaceDimension.endpointVector_add_endpointVector` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:88` |
| `PaperC.CycleSpaceDimension.endpointVector_mem_range_of_adjacent` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:102` |
| `PaperC.CycleSpaceDimension.endpointVector_mem_range_of_reachable` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:113` |
| `PaperC.CycleSpaceDimension.endpointVector_self` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:82` |
| `PaperC.CycleSpaceDimension.finrank_cycleSpace_le_card_edges_sub_nonRoot` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:227` |
| `PaperC.CycleSpaceDimension.finrank_cycleSpace_le_cyclomaticNumber` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:252` |
| `PaperC.CycleSpaceDimension.finrank_ker_representedEdgeMap_le_card_edges_sub_nonRoot` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:293` |
| `PaperC.CycleSpaceDimension.finrank_ker_representedEdgeMap_le_cyclomaticNumber` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:274` |
| `PaperC.CycleSpaceDimension.incidenceVector_mem_range` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:95` |
| `PaperC.CycleSpaceDimension.linearIndependent_rootedEndpointVector` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:161` |
| `PaperC.CycleSpaceDimension.rootedEndpointVector_apply_ne` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:143` |
| `PaperC.CycleSpaceDimension.rootedEndpointVector_apply_self` | inconditionnel | — | — | — | `PaperC/Combinatorics/CycleSpaceDimension.lean:137` |
| `PaperC.DeepCoreSmallComponent.exists_bounded_connectedComponent_of_rational_density` | inconditionnel | — | — | — | `PaperC/Combinatorics/DeepCoreSmallComponent.lean:196` |
| `PaperC.DeepCoreSmallComponent.exists_bounded_connectedComponent_of_reciprocal_density` | inconditionnel | — | — | — | `PaperC/Combinatorics/DeepCoreSmallComponent.lean:175` |
| `PaperC.DeepCoreSmallComponent.exists_member_size_le_of_mass_lt` | inconditionnel | — | — | — | `PaperC/Combinatorics/DeepCoreSmallComponent.lean:46` |
| `PaperC.DeepCoreSmallComponent.exists_nontrivial_small_of_rational_density` | inconditionnel | — | — | — | `PaperC/Combinatorics/DeepCoreSmallComponent.lean:152` |
| `PaperC.DeepCoreSmallComponent.exists_nontrivial_small_of_reciprocal_density` | inconditionnel | — | — | — | `PaperC/Combinatorics/DeepCoreSmallComponent.lean:100` |
| `PaperC.DeepCoreSmallComponent.exists_small_of_rational_density` | inconditionnel | — | — | — | `PaperC/Combinatorics/DeepCoreSmallComponent.lean:121` |
| `PaperC.DeepCoreSmallComponent.exists_small_of_reciprocal_density` | inconditionnel | — | — | — | `PaperC/Combinatorics/DeepCoreSmallComponent.lean:73` |
| `PaperC.DeepCoreSmallComponent.residualComponents_exists_bounded_of_rational_density` | inconditionnel | — | — | — | `PaperC/Combinatorics/DeepCoreSmallComponent.lean:259` |
| `PaperC.DeepCoreSmallComponent.residualComponents_exists_bounded_of_reciprocal_density` | inconditionnel | — | — | — | `PaperC/Combinatorics/DeepCoreSmallComponent.lean:232` |
| `PaperC.DefectCodeDistance.minWeightAbove_augmentedParityMap_of_noShortRungeSquare` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeDistance.lean:79` |
| `PaperC.DefectCodeDistance.reindex_translatedRungeInput` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeDistance.lean:35` |
| `PaperC.DefectCodeHamming.defectCode_length_lt` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeHamming.lean:54` |
| `PaperC.DefectCodeHamming.defectCode_volume_le_two_pow` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeHamming.lean:32` |
| `PaperC.DefectCodeProposition.defectCode_length_lt_of_representations` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeProposition.lean:52` |
| `PaperC.DefectCodeProposition.defectCode_volume_le_two_pow_of_representations` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeProposition.lean:23` |
| `PaperC.DefectCodeRank.appendOne_castSucc` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:59` |
| `PaperC.DefectCodeRank.appendOne_last` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:54` |
| `PaperC.DefectCodeRank.augmentedColumnMap_apply_castSucc` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:79` |
| `PaperC.DefectCodeRank.augmentedColumnMap_apply_last` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:85` |
| `PaperC.DefectCodeRank.columns_sub_augmentedRows_le_finrank_ker` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:73` |
| `PaperC.DefectCodeRank.columns_sub_rows_le_finrank_ker` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:34` |
| `PaperC.DefectCodeRank.defectCode_finrank_ge` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:140` |
| `PaperC.DefectCodeRank.defectCode_kernelWord_even` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:147` |
| `PaperC.DefectCodeRank.defectCode_kernel_coordinate` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:158` |
| `PaperC.DefectCodeRank.even_hammingNorm_of_mem_ker_augmentedColumnMap` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:109` |
| `PaperC.DefectCodeRank.square_product_of_mem_ker_augmentedParityMap` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:175` |
| `PaperC.DefectCodeRank.sum_wordSupport_eq_weighted_sum` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRank.lean:94` |
| `PaperC.DefectCodeRepresentation.kernelWord_translatedRungeInput_of_defectRepresentations` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRepresentation.lean:54` |
| `PaperC.DefectCodeRepresentation.square_product_of_defectRepresentations` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRepresentation.lean:25` |
| `PaperC.DefectCodeRunge.kernelWord_support_card_eq_two_mul` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRunge.lean:31` |
| `PaperC.DefectCodeRunge.kernelWord_translatedRungeInput` | inconditionnel | — | — | — | `PaperC/Coding/DefectCodeRunge.lean:68` |
| `PaperC.DefectCounting.DefectRepresentation.value_eq_defectPart_mul_sq` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:60` |
| `PaperC.DefectCounting.card_HDefectValues_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:183` |
| `PaperC.DefectCounting.card_defectValues_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:168` |
| `PaperC.DefectCounting.card_defectValues_le_sum` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:158` |
| `PaperC.DefectCounting.card_intervalStartsContaining_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:211` |
| `PaperC.DefectCounting.card_valuesForSupport_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:148` |
| `PaperC.DefectCounting.intervalStartsContaining_subset_Icc` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:197` |
| `PaperC.DefectCounting.mem_defectValues_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:89` |
| `PaperC.DefectCounting.mem_defectValues_of_HDefectRepresentation` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:138` |
| `PaperC.DefectCounting.mem_defectValues_of_representation` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:127` |
| `PaperC.DefectCounting.mem_smallPrimesUpTo` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:38` |
| `PaperC.DefectCounting.mem_valuesForSupport_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:82` |
| `PaperC.DefectCounting.smallPrimesUpTo_subset_Icc` | inconditionnel | — | — | — | `PaperC/Analysis/SmoothEulerProduct.lean:51` |
| `PaperC.DefectCounting.squarePart_le_sqrt` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectCounting.lean:107` |
| `PaperC.DefectFirstMoment.abs_dyadicExpectation_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Probability/DefectFirstMoment.lean:121` |
| `PaperC.DefectFirstMoment.abs_dyadicExpectation_sub_baseline_le_globalDefectWeight` | inconditionnel | — | — | — | `PaperC/Probability/DefectFirstMoment.lean:178` |
| `PaperC.DefectFirstMoment.abs_dyadicExpectation_sub_baseline_le_weight` | inconditionnel | — | — | — | `PaperC/Probability/DefectFirstMoment.lean:147` |
| `PaperC.DefectFirstMoment.abs_startProbability_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Probability/DefectFirstMoment.lean:88` |
| `PaperC.DefectFirstMoment.startProbability_eq_eta_mul_two_pow_rho_div` | inconditionnel | — | — | — | `PaperC/Probability/DefectFirstMoment.lean:32` |
| `PaperC.DefectParitySupport.dvd_defectPart_of_eq_mul_sq_of_parityVec_ne_zero` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectParitySupport.lean:44` |
| `PaperC.DefectParitySupport.dvd_of_parityVec_mul_sq_ne_zero` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectParitySupport.lean:30` |
| `PaperC.DefectParitySupport.parityCoverage_of_eq_mul_sq` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectParitySupport.lean:68` |
| `PaperC.DefectParitySupport.parityVec_mul_sq` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectParitySupport.lean:21` |
| `PaperC.DefectParitySupport.prime_of_parityVec_ne_zero` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectParitySupport.lean:56` |
| `PaperC.DefectPointwiseRate.cappedRadius_cast_le_log_div` | inconditionnel | — | — | — | `PaperC/Analysis/DefectPointwiseRate.lean:18` |
| `PaperC.DefectPointwiseRate.card_defectsInInterval_cast_lt_log_div` | inconditionnel | — | — | — | `PaperC/Analysis/DefectPointwiseRate.lean:67` |
| `PaperC.DefectivePredicate.canonical_odd_mul_sq_decomposition` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectivePredicate.lean:156` |
| `PaperC.DefectivePredicate.defectPart_ne_zero_of_HDefectRepresentation` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectivePredicate.lean:58` |
| `PaperC.DefectivePredicate.even_factorization_of_HDefectRepresentation` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectivePredicate.lean:96` |
| `PaperC.DefectivePredicate.factorization_eq_odd_add_two_half` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectivePredicate.lean:124` |
| `PaperC.DefectivePredicate.hDefective_iff_even_factorization` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectivePredicate.lean:36` |
| `PaperC.DefectivePredicate.hDefective_iff_exists_HDefectRepresentation` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectivePredicate.lean:219` |
| `PaperC.DefectivePredicate.hDefective_iff_parity_support_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectivePredicate.lean:46` |
| `PaperC.DefectivePredicate.hDefective_of_HDefectRepresentation` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectivePredicate.lean:72` |
| `PaperC.DefectivePredicate.oddFactorization_apply_eq_one_of_mem` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectivePredicate.lean:133` |
| `PaperC.DefectivePredicate.oddPrimeSupport_subset_smallPrimesUpTo` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectivePredicate.lean:184` |
| `PaperC.DefectivePredicate.prod_oddPrimeSupport_eq_prod_oddFactorization` | inconditionnel | — | — | — | `PaperC/Arithmetic/DefectivePredicate.lean:145` |
| `PaperC.DefectiveVertexIntervalBound.canonicalCorrectedDefectCount_le_defectiveVertexCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/DefectiveVertexIntervalBound.lean:212` |
| `PaperC.DefectiveVertexIntervalBound.canonicalCorrectedDefectCount_le_interval_sum` | inconditionnel | — | — | — | `PaperC/Combinatorics/DefectiveVertexIntervalBound.lean:232` |
| `PaperC.DefectiveVertexIntervalBound.canonicalCorrectedDefectCount_uniform_B_div_log_B` | inconditionnel | — | — | — | `PaperC/Combinatorics/DefectiveVertexIntervalBound.lean:511` |
| `PaperC.DefectiveVertexIntervalBound.canonicalCorrectedDefectCount_uniform_on_dyadicBlock` | inconditionnel | — | — | — | `PaperC/Combinatorics/DefectiveVertexIntervalBound.lean:311` |
| `PaperC.DefectiveVertexIntervalBound.canonicalCorrectedDefectCount_uniform_on_window` | inconditionnel | — | — | — | `PaperC/Combinatorics/DefectiveVertexIntervalBound.lean:251` |
| `PaperC.DefectiveVertexIntervalBound.defectiveVertexCount_le_interval_sum` | inconditionnel | — | — | — | `PaperC/Combinatorics/DefectiveVertexIntervalBound.lean:169` |
| `PaperC.DefectiveVertexIntervalBound.defectiveVertexToIntervals_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/DefectiveVertexIntervalBound.lean:113` |
| `PaperC.DefectiveVertexIntervalBound.log_div_loglog_le_height_div_log_eventually` | inconditionnel | — | — | — | `PaperC/Combinatorics/DefectiveVertexIntervalBound.lean:433` |
| `PaperC.DefectiveVertexIntervalBound.log_div_loglog_le_two_div_lower_mul_height_div_log` | inconditionnel | — | — | — | `PaperC/Combinatorics/DefectiveVertexIntervalBound.lean:361` |
| `PaperC.DefectiveVertexIntervalBound.mem_defectsInInterval_of_hDefective` | inconditionnel | — | — | — | `PaperC/Combinatorics/DefectiveVertexIntervalBound.lean:45` |
| `PaperC.DependencyEdgeBound.card_largePrimesInRange_le` | inconditionnel | — | — | — | `PaperC/Analysis/DependencyEdgeBound.lean:64` |
| `PaperC.DependencyEdgeBound.card_orderedDependencyEdges_cast_le` | inconditionnel | — | — | — | `PaperC/Analysis/DependencyEdgeBound.lean:179` |
| `PaperC.DependencyEdgeBound.largePrimesInRange_subset_dyadicPrimes` | inconditionnel | — | — | — | `PaperC/Analysis/DependencyEdgeBound.lean:38` |
| `PaperC.DependencyEdgeBound.sum_div_add_one_sq_eq` | inconditionnel | — | — | — | `PaperC/Analysis/DependencyEdgeBound.lean:115` |
| `PaperC.DependencyEdgeBound.sum_div_add_one_sq_le` | inconditionnel | — | — | — | `PaperC/Analysis/DependencyEdgeBound.lean:138` |
| `PaperC.DependencyEdgeBound.sum_inv_largePrimesInRange_le` | inconditionnel | — | — | — | `PaperC/Analysis/DependencyEdgeBound.lean:82` |
| `PaperC.DependencyEdgeBound.sum_inv_sq_largePrimesInRange_le` | inconditionnel | — | — | — | `PaperC/Analysis/DependencyEdgeBound.lean:54` |
| `PaperC.DependencyEdgesCritical.card_orderedDependencyEdges_cast_le_div` | inconditionnel | — | — | — | `PaperC/Asymptotics/DependencyEdgesCritical.lean:56` |
| `PaperC.DependencyEdgesCritical.card_orderedDependencyEdges_terminalCutoff_cast_le_div` | inconditionnel | — | — | — | `PaperC/Asymptotics/DependencyEdgesCritical.lean:177` |
| `PaperC.DependencyEdgesCritical.mul_sq_le_terminalPrimeCutoff` | inconditionnel | — | — | — | `PaperC/Asymptotics/DependencyEdgesCritical.lean:38` |
| `PaperC.DependencyEdgesCritical.orderedDependencyEdges_terminalCutoff_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/DependencyEdgesCritical.lean:245` |
| `PaperC.DependencyEdgesCritical.runLengthAddOne_tends_to_infinity` | inconditionnel | — | — | — | `PaperC/Asymptotics/DependencyEdgesCritical.lean:209` |
| `PaperC.DirichletAtomConvergence.abs_scaledInversePowerTail_sub_le` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:204` |
| `PaperC.DirichletAtomConvergence.inversePowerWeight_le_one` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:29` |
| `PaperC.DirichletAtomConvergence.inversePowerWeight_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:26` |
| `PaperC.DirichletAtomConvergence.scaledInversePowerTail_le` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:148` |
| `PaperC.DirichletAtomConvergence.scaledInversePowerTail_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:138` |
| `PaperC.DirichletAtomConvergence.scaledInversePowerTerm_self` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:85` |
| `PaperC.DirichletAtomConvergence.scaledInversePowerTransform_eq` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:58` |
| `PaperC.DirichletAtomConvergence.scaledInversePowerTransform_sub_lower_sub_eq_tail` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:96` |
| `PaperC.DirichletAtomConvergence.shifted_mass_tsum_le_one` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:127` |
| `PaperC.DirichletAtomConvergence.summable_inversePowerTransform` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:40` |
| `PaperC.DirichletAtomConvergence.summable_scaledInversePowerTerm` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:70` |
| `PaperC.DirichletAtomConvergence.tailRatio_lt_one` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:120` |
| `PaperC.DirichletAtomConvergence.tailRatio_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:115` |
| `PaperC.DirichletAtomConvergence.tendsto_atoms_of_inversePowerTransforms` | inconditionnel | — | — | — | `PaperC/Probability/DirichletAtomConvergence.lean:230` |
| `PaperC.DyadicKappaQuantitative.R2κ_dyadic_uniformBigO` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/DyadicKappaQuantitative.lean:521` |
| `PaperC.DyadicKappaQuantitative.corollary_eleven_three_canonical` | conditionnel | `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/DyadicKappaQuantitative.lean:820` |
| `PaperC.DyadicKappaQuantitative.everySector_dyadic_uniformBigO` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/DyadicKappaQuantitative.lean:437` |
| `PaperC.DyadicKappaQuantitative.highDensityMass_dyadic_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaQuantitative.lean:212` |
| `PaperC.DyadicKappaQuantitative.homogeneousMass_uniformBigO` | conditionnel | `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/DyadicKappaQuantitative.lean:588` |
| `PaperC.DyadicKappaQuantitative.moderateDensityMass_dyadic_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaQuantitative.lean:70` |
| `PaperC.DyadicKappaQuantitative.nonterminalSector_dyadic_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaQuantitative.lean:336` |
| `PaperC.DyadicKappaTransport.R2κ_two_mul_eq_zero_of_not_two_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaTransport.lean:115` |
| `PaperC.DyadicKappaTransport.boundedRatioBlock_two_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaTransport.lean:31` |
| `PaperC.DyadicKappaTransport.boundedRatioCutoff_two_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaTransport.lean:38` |
| `PaperC.DyadicKappaTransport.homogeneousMassNat_two_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaTransport.lean:78` |
| `PaperC.DyadicKappaTransport.homogeneousMass_eq_R2κ_two_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaTransport.lean:132` |
| `PaperC.DyadicKappaTransport.homogeneousWeight_two_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaTransport.lean:68` |
| `PaperC.DyadicKappaTransport.pairRho_two_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaTransport.lean:58` |
| `PaperC.DyadicKappaTransport.separatedBoundedRatioPair_two_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaTransport.lean:51` |
| `PaperC.DyadicKappaTransport.separatedBoundedRatioPairs_two_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaTransport.lean:45` |
| `PaperC.DyadicKappaTransport.separatedBoundedRatioPairs_two_mul_eq_empty_of_not_two_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/DyadicKappaTransport.lean:91` |
| `PaperC.DyadicPrimeReciprocalSums.four_mul_q_mul_B_le_dyadicCutoff` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:394` |
| `PaperC.DyadicPrimeReciprocalSums.mem_dyadicPrimes` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:56` |
| `PaperC.DyadicPrimeReciprocalSums.mem_dyadicPrimes_add_two_of_prime_lt_four_mul` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:408` |
| `PaperC.DyadicPrimeReciprocalSums.mem_primesBetween` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:39` |
| `PaperC.DyadicPrimeReciprocalSums.primesBetween_self` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:46` |
| `PaperC.DyadicPrimeReciprocalSums.subset_dyadicPrimes_add_two_of_prime_lt_four_mul` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:421` |
| `PaperC.DyadicPrimeReciprocalSums.sum_inv_dyadicPrimes_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:241` |
| `PaperC.DyadicPrimeReciprocalSums.sum_inv_primes_lt_four_mul_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:435` |
| `PaperC.DyadicPrimeReciprocalSums.sum_inv_sq_dyadicPrimes_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:332` |
| `PaperC.DyadicPrimeReciprocalSums.sum_inv_sq_primes_lt_four_mul_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:451` |
| `PaperC.DyadicPrimeReciprocalSums.sum_inv_sq_subset_dyadicPrimes_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:376` |
| `PaperC.DyadicPrimeReciprocalSums.sum_inv_subset_dyadicPrimes_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicPrimeReciprocalSums.lean:359` |
| `PaperC.EvertseSilvermanInput.shiftedSquareEquation_atMost_of_evertseSilverman` | conditionnel | `ES86-T1b-Q-split-n2` | `external` | `open` | `PaperC/Diophantine/EvertseSilvermanInput.lean:442` |
| `PaperC.ExactLengthBadStartMass.baseDefectiveExactLengthStarts_subset_removed` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:398` |
| `PaperC.ExactLengthBadStartMass.card_startDefectIndicesAt_le_of_le` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:271` |
| `PaperC.ExactLengthBadStartMass.exactLengthProbabilityMass_terminalBadStarts_eq_split` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:303` |
| `PaperC.ExactLengthBadStartMass.exactLengthProbabilityMass_terminalBadStarts_le_two_windows` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:344` |
| `PaperC.ExactLengthBadStartMass.exactLengthProbabilityMass_terminalBadStarts_le_weight` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:213` |
| `PaperC.ExactLengthBadStartMass.exactLengthProbability_eq_baseline_of_not_bad` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:154` |
| `PaperC.ExactLengthBadStartMass.exactLengthProbability_eq_eta_mul_two_pow_rho_div` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:98` |
| `PaperC.ExactLengthBadStartMass.exactLengthProbability_eq_uniformSolutionProbability` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:77` |
| `PaperC.ExactLengthBadStartMass.exactLengthProbability_le_of_relationRho` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:123` |
| `PaperC.ExactLengthBadStartMass.exactLengthProbability_le_two_mul_defectWeight_div` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:173` |
| `PaperC.ExactLengthBadStartMass.exactLengthProbability_le_two_pow_defect_div` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:139` |
| `PaperC.ExactLengthBadStartMass.exactLengthProbability_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:113` |
| `PaperC.ExactLengthBadStartMass.removedExactLengthProbabilityMass_cast_le_terminalEnvelope` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:584` |
| `PaperC.ExactLengthBadStartMass.removedExactLengthProbabilityMass_eq_split` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:413` |
| `PaperC.ExactLengthBadStartMass.removedExactLengthProbabilityMass_le` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:442` |
| `PaperC.ExactLengthBadStartMass.removedExactLengthProbabilityMass_le_compact` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:468` |
| `PaperC.ExactLengthBadStartMass.terminalBadStarts_mono_length_cutoff` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:257` |
| `PaperC.ExactLengthBadStartMass.terminalDefectWeightMass_mono_length` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:284` |
| `PaperC.ExactLengthBadStartMass.totalRemovedExactLengthProbabilityMass_cast_le_terminalEnvelope` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:655` |
| `PaperC.ExactLengthBadStartMass.totalRemovedExactLengthProbabilityMass_le` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthBadStartMass.lean:510` |
| `PaperC.ExactLengthBadStartMassCritical.commonExactRowCount_in_runLengthWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExactLengthBadStartMassCritical.lean:55` |
| `PaperC.ExactLengthBadStartMassCritical.commonNormalizedDefectContribution_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExactLengthBadStartMassCritical.lean:171` |
| `PaperC.ExactLengthBadStartMassCritical.commonNormalizedRemovedCountContribution_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExactLengthBadStartMassCritical.lean:191` |
| `PaperC.ExactLengthBadStartMassCritical.lemma_fourteen_seven` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExactLengthBadStartMassCritical.lean:357` |
| `PaperC.ExactLengthBadStartMassCritical.lemma_fourteen_seven_finiteCylinder` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExactLengthBadStartMassCritical.lean:332` |
| `PaperC.ExactLengthBadStartMassCritical.totalRemovedExactLengthEnvelope_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExactLengthBadStartMassCritical.lean:256` |
| `PaperC.ExactLengthBadStartMassCritical.totalRemovedExactLengthProbabilityMassReal_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExactLengthBadStartMassCritical.lean:113` |
| `PaperC.ExactLengthBadStartMassCritical.totalRemovedExactLengthProbabilityMassReal_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExactLengthBadStartMassCritical.lean:275` |
| `PaperC.ExactLengthConditionalRank.assemble_exactLengthAt_iff` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:156` |
| `PaperC.ExactLengthConditionalRank.assemble_mixedExactLengthAt_iff` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:250` |
| `PaperC.ExactLengthConditionalRank.assemble_solves_exactLength_iff` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:142` |
| `PaperC.ExactLengthConditionalRank.assemble_solves_mixedLength_iff` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:234` |
| `PaperC.ExactLengthConditionalRank.conditionedExactLengthProbability_eq_baseline_of_privatePivots` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:487` |
| `PaperC.ExactLengthConditionalRank.conditionedExactLengthProbability_eq_baseline_of_surjective` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:206` |
| `PaperC.ExactLengthConditionalRank.conditionedExactLengthProbability_eq_eta_mul_two_pow_rho_div` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:174` |
| `PaperC.ExactLengthConditionalRank.conditionedExactLengthProbability_le_of_relationRho` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:191` |
| `PaperC.ExactLengthConditionalRank.conditionedMixedLengthProbability_eq_eta_mul_two_pow_rho_div` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:269` |
| `PaperC.ExactLengthConditionalRank.conditionedMixedLengthProbability_le_local_of_privatePivots` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:444` |
| `PaperC.ExactLengthConditionalRank.conditionedMixedLengthProbability_le_local_of_relationRho_le_one` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:300` |
| `PaperC.ExactLengthConditionalRank.conditionedMixedLengthProbability_le_of_relationRho` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:284` |
| `PaperC.ExactLengthConditionalRank.relationRho_le_card_edges_sub_nonRoot_of_privatePivots` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:405` |
| `PaperC.ExactLengthConditionalRank.relationRho_le_cyclomaticNumber_of_privatePivots` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:370` |
| `PaperC.ExactLengthConditionalRank.relationSpace_le_ker_representedEdgeMap` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:333` |
| `PaperC.ExactLengthConditionalRank.uniformSolutionProbability_eq_inv_two_pow_of_relationRho_eq_zero` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:106` |
| `PaperC.ExactLengthConditionalRank.uniformSolutionProbability_eq_inv_two_pow_of_surjective` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:78` |
| `PaperC.ExactLengthConditionalRank.uniformSolutionProbability_le_two_pow_relation_bound` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthConditionalRank.lean:53` |
| `PaperC.ExactLengthCountVectorTransfer.abs_infiniteExactLengthCountVectorLaw_sub_retained_le_mass` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:481` |
| `PaperC.ExactLengthCountVectorTransfer.finiteExactLengthCountVectorOn_restrictToFinite` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:121` |
| `PaperC.ExactLengthCountVectorTransfer.finiteExactLengthCountVector_restrictToFinite` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:159` |
| `PaperC.ExactLengthCountVectorTransfer.finiteRetainedExactLengthCountVector_restrictToFinite` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:168` |
| `PaperC.ExactLengthCountVectorTransfer.infiniteCountVector_disagreement_subset_removed` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:388` |
| `PaperC.ExactLengthCountVectorTransfer.infiniteExactLengthCountVectorEvent_eq_preimage` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:215` |
| `PaperC.ExactLengthCountVectorTransfer.infiniteExactLengthCountVectorLaw_eq_finite` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:288` |
| `PaperC.ExactLengthCountVectorTransfer.infiniteExactLengthCountVector_apply` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:104` |
| `PaperC.ExactLengthCountVectorTransfer.infiniteExactLengthCountVector_eq_retained_of_no_removed` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:364` |
| `PaperC.ExactLengthCountVectorTransfer.infiniteRemovedExactLengthEvent_eq_biUnion` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:340` |
| `PaperC.ExactLengthCountVectorTransfer.infiniteRemovedExactLengthEvent_measureReal_le_mass` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:403` |
| `PaperC.ExactLengthCountVectorTransfer.infiniteRetainedExactLengthCountVectorEvent_eq_preimage` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:229` |
| `PaperC.ExactLengthCountVectorTransfer.infiniteRetainedExactLengthCountVectorLaw_eq_finite` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:307` |
| `PaperC.ExactLengthCountVectorTransfer.measurableSet_finiteExactLengthCountVectorEvent` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:204` |
| `PaperC.ExactLengthCountVectorTransfer.measurableSet_finiteRetainedExactLengthCountVectorEvent` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:209` |
| `PaperC.ExactLengthCountVectorTransfer.measurableSet_infiniteExactLengthCountVectorEvent` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:244` |
| `PaperC.ExactLengthCountVectorTransfer.measurableSet_infiniteRemovedExactLengthEvent` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:349` |
| `PaperC.ExactLengthCountVectorTransfer.measurableSet_infiniteRetainedExactLengthCountVectorEvent` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:252` |
| `PaperC.ExactLengthCountVectorTransfer.retainedMarkedStarts_subset_dyadicBlock` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthCountVectorTransfer.lean:111` |
| `PaperC.ExactLengthDecomposition.add_eq_one_iff_ne` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthDecomposition.lean:29` |
| `PaperC.ExactLengthDecomposition.exactLengthEvent_excess_unique` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthDecomposition.lean:116` |
| `PaperC.ExactLengthDecomposition.exactLengthEvent_start` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthDecomposition.lean:38` |
| `PaperC.ExactLengthDecomposition.exactLengthEvent_start_longer_of_excess_gt` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthDecomposition.lean:65` |
| `PaperC.ExactLengthDecomposition.exactLengthEvent_tailChangesAt` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthDecomposition.lean:53` |
| `PaperC.ExactLengthDecomposition.exists_exactLengthEvent_of_start_of_tailChangesAt` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthDecomposition.lean:83` |
| `PaperC.ExactLengthDecomposition.ncard_exactExcessSet_of_not_start` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthDecomposition.lean:193` |
| `PaperC.ExactLengthDecomposition.ncard_exactExcessSet_of_start` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthDecomposition.lean:170` |
| `PaperC.ExactLengthDecomposition.startEvent_iff_existsUnique_exactLengthEvent` | inconditionnel | — | — | — | `PaperC/Probability/ExactLengthDecomposition.lean:150` |
| `PaperC.ExactUnitIsolation.channelUnitOccurrencePair_disjoint` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:565` |
| `PaperC.ExactUnitIsolation.channelUnit_exactUnitFactorization` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:73` |
| `PaperC.ExactUnitIsolation.channelUnit_left_ne_of_ne` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:523` |
| `PaperC.ExactUnitIsolation.channelUnit_right_ne_of_ne` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:534` |
| `PaperC.ExactUnitIsolation.distinct_channelUnits_components_ne` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:631` |
| `PaperC.ExactUnitIsolation.distinct_channelUnits_nondefective_components` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:656` |
| `PaperC.ExactUnitIsolation.eq_left_of_adj_right` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:207` |
| `PaperC.ExactUnitIsolation.eq_right_of_adj_left` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:180` |
| `PaperC.ExactUnitIsolation.exactUnit_component_card_eq_two` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:357` |
| `PaperC.ExactUnitIsolation.exactUnit_component_unpinned` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:328` |
| `PaperC.ExactUnitIsolation.exactUnit_endpoints_adj` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:280` |
| `PaperC.ExactUnitIsolation.exactUnit_graph_dichotomy` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:480` |
| `PaperC.ExactUnitIsolation.exactUnit_left_components_ne` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:602` |
| `PaperC.ExactUnitIsolation.exactUnit_nontrivial_component` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:451` |
| `PaperC.ExactUnitIsolation.exists_exactUnitFactorization_of_crossProduct` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:39` |
| `PaperC.ExactUnitIsolation.isDefective_iff_hDefective` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:98` |
| `PaperC.ExactUnitIsolation.left_mem_primeOccurrences_iff_right_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:118` |
| `PaperC.ExactUnitIsolation.mem_channelUnitOccurrencePair` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:552` |
| `PaperC.ExactUnitIsolation.not_isPinned_left` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:138` |
| `PaperC.ExactUnitIsolation.not_isPinned_right` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:159` |
| `PaperC.ExactUnitIsolation.reachable_from_left_stays_in_pair` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:310` |
| `PaperC.ExactUnitIsolation.walk_from_left_stays_in_pair` | inconditionnel | — | — | — | `PaperC/Combinatorics/ExactUnitIsolation.lean:237` |
| `PaperC.ExactUnitLargeKernel.common_largeOddKernel_dvd` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:175` |
| `PaperC.ExactUnitLargeKernel.exactUnit_defect_dichotomy` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:210` |
| `PaperC.ExactUnitLargeKernel.exactUnit_largeOddKernel_eq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:164` |
| `PaperC.ExactUnitLargeKernel.exactUnit_largeOddPrimeSupport_eq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:142` |
| `PaperC.ExactUnitLargeKernel.exactUnit_large_factorization_odd_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:84` |
| `PaperC.ExactUnitLargeKernel.exactUnit_large_parity_eq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:65` |
| `PaperC.ExactUnitLargeKernel.exists_common_large_odd_prime` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:243` |
| `PaperC.ExactUnitLargeKernel.hDefective_left_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:189` |
| `PaperC.ExactUnitLargeKernel.hDefective_right_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:198` |
| `PaperC.ExactUnitLargeKernel.largeOddKernel_mul_small_eq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:133` |
| `PaperC.ExactUnitLargeKernel.largeOddPrimeSupport_mul_small_eq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:104` |
| `PaperC.ExactUnitLargeKernel.parityVec_mul_small_eq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:42` |
| `PaperC.ExactUnitLargeKernel.parityVec_ne_zero_unique_in_block` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:306` |
| `PaperC.ExactUnitLargeKernel.prime_dvd_unique_in_block` | inconditionnel | — | — | — | `PaperC/Arithmetic/ExactUnitLargeKernel.lean:286` |
| `PaperC.ExpLogDivLogLog.criticalRunWindow_exp_height_div_natLog_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpLogDivLogLog.lean:115` |
| `PaperC.ExpLogDivLogLog.exp_log_div_loglog_pow_le_nat_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpLogDivLogLog.lean:28` |
| `PaperC.ExpLogDivLogLog.uniformSubpolynomialOn_exp_log_div_loglog_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpLogDivLogLog.lean:86` |
| `PaperC.ExpSqrtLog.exp_sqrt_of_le_log_pow_le_nat_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:96` |
| `PaperC.ExpSqrtLog.le_exp_two_mul_sqrt` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:151` |
| `PaperC.ExpSqrtLog.linear_log_add_one_le_exp_sqrt_log` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:173` |
| `PaperC.ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:219` |
| `PaperC.ExpSqrtLog.mul_pow_le_nat_of_twice` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:266` |
| `PaperC.ExpSqrtLog.pow_le_nat_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:28` |
| `PaperC.ExpSqrtLog.two_pow_log_div_loglog_pow_le_nat_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:338` |
| `PaperC.ExpSqrtLog.uniformSubpolynomialOn` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:81` |
| `PaperC.ExpSqrtLog.uniformSubpolynomialOn_const` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:310` |
| `PaperC.ExpSqrtLog.uniformSubpolynomialOn_const_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:320` |
| `PaperC.ExpSqrtLog.uniformSubpolynomialOn_exp_sqrt_of_le_log` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:132` |
| `PaperC.ExpSqrtLog.uniformSubpolynomialOn_linear_log_add_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:245` |
| `PaperC.ExpSqrtLog.uniformSubpolynomialOn_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:290` |
| `PaperC.ExpSqrtLog.uniformSubpolynomialOn_two_pow_log_div_loglog` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:412` |
| `PaperC.ExpSqrtLog.uniformSubpolynomialOn_two_pow_log_div_loglog_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/LinearPower.lean:23` |
| `PaperC.ExpSqrtLog.uniformSubpolynomialOn_weighted_defect_factor` | inconditionnel | — | — | — | `PaperC/Asymptotics/ExpSqrtLog.lean:438` |
| `PaperC.FiniteCylinderCountTransport.boundedBadStartProbabilityMass_le_two_cutoffs` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:684` |
| `PaperC.FiniteCylinderCountTransport.boundedFullStartMean_eq_goodParameter_add_badMass` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:638` |
| `PaperC.FiniteCylinderCountTransport.boundedStartProbability_eq_baseline_of_not_bad` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:606` |
| `PaperC.FiniteCylinderCountTransport.boundedStartProbability_eq_selfStartProbability` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:516` |
| `PaperC.FiniteCylinderCountTransport.boundedStartProbability_le_two_mul_defectWeight_div` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:577` |
| `PaperC.FiniteCylinderCountTransport.boundedTerminalBadStarts_mono` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:552` |
| `PaperC.FiniteCylinderCountTransport.disagreementProbability_boundedGood_full_le_badMass` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:800` |
| `PaperC.FiniteCylinderCountTransport.exists_bad_start_of_boundedGood_ne_full` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:778` |
| `PaperC.FiniteCylinderCountTransport.finiteNatLaw_startCountOn_cutoff_invariant` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:400` |
| `PaperC.FiniteCylinderCountTransport.natTotalVariation_boundedGood_full_le_badMass` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:883` |
| `PaperC.FiniteCylinderCountTransport.startAt_assemble_iff_local` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:182` |
| `PaperC.FiniteCylinderCountTransport.startAt_sampleSpaceEquivLocalProd_iff` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:228` |
| `PaperC.FiniteCylinderCountTransport.startCountOn_sampleSpaceEquivLocalProd` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:328` |
| `PaperC.FiniteCylinderCountTransport.uniformEventProbability_startAt_cutoff_invariant` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:244` |
| `PaperC.FiniteCylinderCountTransport.valueBit_assemble_eq_local` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:147` |
| `PaperC.FiniteCylinderCountTransport.valueBit_extendSmall_eq_local` | inconditionnel | — | — | — | `PaperC/Probability/FiniteCylinderCountTransport.lean:86` |
| `PaperC.FinitePMF.tvDist_comm` | inconditionnel | — | — | — | `PaperC/Probability/FinitePMF.lean:55` |
| `PaperC.FinitePMF.tvDist_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/FinitePMF.lean:49` |
| `PaperC.FinitePMF.tvDist_self` | inconditionnel | — | — | — | `PaperC/Probability/FinitePMF.lean:52` |
| `PaperC.FinitePMF.uniform_prob` | inconditionnel | — | — | — | `PaperC/Probability/FinitePMF.lean:40` |
| `PaperC.FourPowLittleOHeight.uniformSubpolynomialOn_four_pow_of_uniformLittleO_height` | inconditionnel | — | — | — | `PaperC/Asymptotics/FourPowLittleOHeight.lean:23` |
| `PaperC.FullMarkedLaplaceTransfer.infiniteFullMarkedLaplaceExpectation_eq_truncated` | inconditionnel | — | — | — | `PaperC/Probability/FullMarkedLaplaceTransfer.lean:100` |
| `PaperC.FullMarkedLaplaceTransfer.infiniteFullMarkedLaplaceFunctional_eq_truncated` | inconditionnel | — | — | — | `PaperC/Probability/FullMarkedLaplaceTransfer.lean:58` |
| `PaperC.FullMarkedLaplaceTransfer.measurable_infiniteFullMarkedLaplaceFunctional_of_vanishesAbove` | inconditionnel | — | — | — | `PaperC/Probability/FullMarkedLaplaceTransfer.lean:84` |
| `PaperC.GeometricTail.div_le_half` | inconditionnel | — | — | — | `PaperC/Analysis/GeometricTail.lean:54` |
| `PaperC.GeometricTail.runge_ratio_tail` | inconditionnel | — | — | — | `PaperC/Analysis/GeometricTail.lean:64` |
| `PaperC.GeometricTail.tsum_pow_natAdd_eq` | inconditionnel | — | — | — | `PaperC/Analysis/GeometricTail.lean:21` |
| `PaperC.GeometricTail.tsum_pow_natAdd_le_two_mul` | inconditionnel | — | — | — | `PaperC/Analysis/GeometricTail.lean:36` |
| `PaperC.GraphCycleRank.finrank_ker_representedEdgeMap_le_beta` | inconditionnel | — | — | — | `PaperC/Combinatorics/GraphCycleRank.lean:241` |
| `PaperC.GraphCycleRank.finrank_ker_representedEdgeMap_le_cycleSpace` | inconditionnel | — | — | — | `PaperC/Combinatorics/GraphCycleRank.lean:228` |
| `PaperC.GraphCycleRank.finrank_ker_representedEdgeMap_le_cyclomaticNumber` | inconditionnel | — | — | — | `PaperC/Combinatorics/GraphCycleRank.lean:256` |
| `PaperC.GraphCycleRank.incidenceMap_apply` | inconditionnel | — | — | — | `PaperC/Combinatorics/GraphCycleRank.lean:73` |
| `PaperC.GraphCycleRank.incidenceMap_apply_eq_privateCoordinate` | inconditionnel | — | — | — | `PaperC/Combinatorics/GraphCycleRank.lean:84` |
| `PaperC.GraphCycleRank.incidenceVector_apply` | inconditionnel | — | — | — | `PaperC/Combinatorics/GraphCycleRank.lean:66` |
| `PaperC.GraphCycleRank.incidence_eq_zero_at_nonRoot_of_mem_ker` | inconditionnel | — | — | — | `PaperC/Combinatorics/GraphCycleRank.lean:104` |
| `PaperC.GraphCycleRank.ker_representedEdgeMap_le_cycleSpace` | inconditionnel | — | — | — | `PaperC/Combinatorics/GraphCycleRank.lean:159` |
| `PaperC.GraphCycleRank.representedEdge_dependence_has_even_degree` | inconditionnel | — | — | — | `PaperC/Combinatorics/GraphCycleRank.lean:209` |
| `PaperC.GraphCycleRank.sum_incidenceMap_on_component_eq_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/GraphCycleRank.lean:122` |
| `PaperC.HammingBound.card_ball` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:152` |
| `PaperC.HammingBound.card_ball_eq_card_smallSupports` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:113` |
| `PaperC.HammingBound.card_smallSupports` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:131` |
| `PaperC.HammingBound.card_submoduleCodewords` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:231` |
| `PaperC.HammingBound.card_wordSupport` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:35` |
| `PaperC.HammingBound.differenceSupportEquiv_apply` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:92` |
| `PaperC.HammingBound.disjoint_balls_of_two_mul_lt_distance` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:158` |
| `PaperC.HammingBound.eq_one_of_ne_zero` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:40` |
| `PaperC.HammingBound.hammingDist_eq_card_differenceSupport` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:76` |
| `PaperC.HammingBound.hamming_bound` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:185` |
| `PaperC.HammingBound.hamming_bound_codimension` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:209` |
| `PaperC.HammingBound.hamming_bound_submodule` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:278` |
| `PaperC.HammingBound.hamming_bound_submodule_codimension` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:289` |
| `PaperC.HammingBound.hamming_bound_submodule_of_finrank_ge` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:302` |
| `PaperC.HammingBound.hamming_bound_sum_choose` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:201` |
| `PaperC.HammingBound.mem_ball` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:101` |
| `PaperC.HammingBound.mem_submoduleCodewords` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:224` |
| `PaperC.HammingBound.minDistanceAbove_submoduleCodewords` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:255` |
| `PaperC.HammingBound.pairwiseDisjoint_balls` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:178` |
| `PaperC.HammingBound.sum_choose_le_pow_of_finrank_ge` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:320` |
| `PaperC.HammingBound.wordOfSupport_wordSupport` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:57` |
| `PaperC.HammingBound.wordSupport_wordOfSupport` | inconditionnel | — | — | — | `PaperC/Coding/HammingBound.lean:51` |
| `PaperC.HammingDefectBound.base_lt_two_pow_div_add_one` | inconditionnel | — | — | — | `PaperC/Coding/HammingDefectBound.lean:106` |
| `PaperC.HammingDefectBound.choose_le_volume` | inconditionnel | — | — | — | `PaperC/Coding/HammingDefectBound.lean:83` |
| `PaperC.HammingDefectBound.half_ratio_pow_le_choose` | inconditionnel | — | — | — | `PaperC/Coding/HammingDefectBound.lean:38` |
| `PaperC.HammingDefectBound.half_ratio_pow_le_two_pow` | inconditionnel | — | — | — | `PaperC/Coding/HammingDefectBound.lean:94` |
| `PaperC.HammingDefectBound.length_lt_of_sum_choose_le_two_pow` | inconditionnel | — | — | — | `PaperC/Coding/HammingDefectBound.lean:128` |
| `PaperC.HighZoneTwoDefects.canonicalSquarePart_le_self` | inconditionnel | — | — | — | `PaperC/Asymptotics/HighZoneTwoDefects.lean:395` |
| `PaperC.HighZoneTwoDefects.card_distinctPairedDefectStarts_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/HighZoneTwoDefects.lean:265` |
| `PaperC.HighZoneTwoDefects.card_pairedDefectStarts_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/HighZoneTwoDefects.lean:144` |
| `PaperC.HighZoneTwoDefects.card_startsForParameters_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/HighZoneTwoDefects.lean:104` |
| `PaperC.HighZoneTwoDefects.card_twoDefectWindowBases_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/HighZoneTwoDefects.lean:599` |
| `PaperC.HighZoneTwoDefects.equal_kernel_offsets_impossible` | inconditionnel | — | — | — | `PaperC/Asymptotics/HighZoneTwoDefects.lean:454` |
| `PaperC.HighZoneTwoDefects.generalizedPell_implies_twoDefectWindow_bound` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Asymptotics/HighZoneTwoDefects.lean:625` |
| `PaperC.HighZoneTwoDefects.mem_boundedTwoDefectWitnesses` | inconditionnel | — | — | — | `PaperC/Asymptotics/HighZoneTwoDefects.lean:62` |
| `PaperC.HighZoneTwoDefects.mem_twoDefectWindowStarts` | inconditionnel | — | — | — | `PaperC/Asymptotics/HighZoneTwoDefects.lean:476` |
| `PaperC.HighZoneTwoDefects.squarefreeKernel_isSmoothAt_of_hDefective` | inconditionnel | — | — | — | `PaperC/Asymptotics/HighZoneTwoDefects.lean:377` |
| `PaperC.HighZoneTwoDefects.twoDefectWindowBases_subset_distinctPaired` | inconditionnel | — | — | — | `PaperC/Asymptotics/HighZoneTwoDefects.lean:490` |
| `PaperC.IndependentThinning.bOne_thinnedIndicator_le` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:894` |
| `PaperC.IndependentThinning.bTwo_thinnedIndicator_le` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:926` |
| `PaperC.IndependentThinning.eventProbability_all_true_eq_prod` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:241` |
| `PaperC.IndependentThinning.eventProbability_coordinateEvent_and_of_disjoint` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:394` |
| `PaperC.IndependentThinning.eventProbability_coordinateEvent_eq_prod` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:317` |
| `PaperC.IndependentThinning.eventProbability_coordinate_true` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:458` |
| `PaperC.IndependentThinning.eventProbability_no_thinned_active_eq_exponentialFunctional` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:962` |
| `PaperC.IndependentThinning.eventProbability_product_and` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:49` |
| `PaperC.IndependentThinning.eventProbability_product_eq_iterated` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:98` |
| `PaperC.IndependentThinning.eventProbability_two_coordinates_true` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:471` |
| `PaperC.IndependentThinning.finitePMFExpectation_eq_sum_fibers` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:117` |
| `PaperC.IndependentThinning.finitePMFExpectation_indicator` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:86` |
| `PaperC.IndependentThinning.finitePMFExpectation_mul_of_hasExactDependencyGraph` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:157` |
| `PaperC.IndependentThinning.hasExactDependencyGraph_combineIndicator` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:596` |
| `PaperC.IndependentThinning.hasExactDependencyGraph_coordinateIndicator` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:520` |
| `PaperC.IndependentThinning.hasExactDependencyGraph_thinnedIndicator` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:790` |
| `PaperC.IndependentThinning.jointMarginal_thinnedIndicator` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:852` |
| `PaperC.IndependentThinning.marginal_thinnedIndicator` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:818` |
| `PaperC.IndependentThinning.mem_outsideVertices` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:499` |
| `PaperC.IndependentThinning.thinnedIndicator_eq_true_iff` | inconditionnel | — | — | — | `PaperC/Probability/IndependentThinning.lean:779` |
| `PaperC.InfiniteCylinderTransfer.finitePrimeCoordinate_injective` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteCylinderTransfer.lean:40` |
| `PaperC.InfiniteCylinderTransfer.finitePrimeReindex_restrict` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteCylinderTransfer.lean:235` |
| `PaperC.InfiniteCylinderTransfer.finiteRademacherMeasure_singleton` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteCylinderTransfer.lean:275` |
| `PaperC.InfiniteCylinderTransfer.map_infiniteRademacherMeasure_restrictToFinite` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteCylinderTransfer.lean:251` |
| `PaperC.InfiniteCylinderTransfer.parityVec_support_subset_range` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteCylinderTransfer.lean:102` |
| `PaperC.InfiniteCylinderTransfer.primeCoordinateEquiv_apply_val` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteCylinderTransfer.lean:85` |
| `PaperC.InfiniteCylinderTransfer.randomMultiplicativeValue_restrictToFinite_eq_infiniteRandomValue` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteCylinderTransfer.lean:169` |
| `PaperC.InfiniteCylinderTransfer.restrictToFinite_apply` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteCylinderTransfer.lean:95` |
| `PaperC.InfiniteCylinderTransfer.startAt_restrictToFinite_iff` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteCylinderTransfer.lean:178` |
| `PaperC.InfiniteCylinderTransfer.valueBit_restrictToFinite_eq_infiniteValueBit` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteCylinderTransfer.lean:114` |
| `PaperC.InfiniteExactLengthDecomposition.ae_exactExcessSet_cardinal` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthDecomposition.lean:82` |
| `PaperC.InfiniteExactLengthDecomposition.ae_startEvent_iff_existsUnique_exactLengthEvent` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthDecomposition.lean:49` |
| `PaperC.InfiniteExactLengthDecomposition.ae_startEvent_iff_existsUnique_exactLengthEvent_fixed` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthDecomposition.lean:65` |
| `PaperC.InfiniteExactLengthDecomposition.ae_tailChangesAt_infiniteValueBit` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthDecomposition.lean:34` |
| `PaperC.InfiniteExactLengthProbabilityTransfer.exactLengthAt_restrictToFinite_iff` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthProbabilityTransfer.lean:75` |
| `PaperC.InfiniteExactLengthProbabilityTransfer.finiteRademacherMeasure_event_eq_uniformEventProbability` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthProbabilityTransfer.lean:145` |
| `PaperC.InfiniteExactLengthProbabilityTransfer.infiniteExactLengthEvent_eq_preimage` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthProbabilityTransfer.lean:122` |
| `PaperC.InfiniteExactLengthProbabilityTransfer.infiniteExactLengthEvent_measure_eq_exactLengthProbability` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthProbabilityTransfer.lean:199` |
| `PaperC.InfiniteExactLengthProbabilityTransfer.infiniteExactLengthEvent_measure_eq_finiteProbabilityAtCutoff` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthProbabilityTransfer.lean:174` |
| `PaperC.InfiniteExactLengthProbabilityTransfer.infiniteExactLengthProbability_eq_exactLengthProbability` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthProbabilityTransfer.lean:226` |
| `PaperC.InfiniteExactLengthProbabilityTransfer.measurableSet_finiteExactLengthEvent` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthProbabilityTransfer.lean:67` |
| `PaperC.InfiniteExactLengthProbabilityTransfer.measurableSet_infiniteExactLengthEvent` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthProbabilityTransfer.lean:130` |
| `PaperC.InfiniteExactLengthProbabilityTransfer.measurable_restrictToFinite` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthProbabilityTransfer.lean:61` |
| `PaperC.InfiniteExactLengthProbabilityTransfer.totalRemovedInfiniteExactLengthProbability_eq_finiteMass` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteExactLengthProbabilityTransfer.lean:249` |
| `PaperC.InfiniteLaplaceTransfer.finiteMarkedLaplaceFunctional_restrictToFinite` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:213` |
| `PaperC.InfiniteLaplaceTransfer.finiteMarkedLaplaceFunctional_restrictToFinite_dyadicCutoff` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:257` |
| `PaperC.InfiniteLaplaceTransfer.finiteSpatialLaplaceFunctional_restrictToFinite` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:66` |
| `PaperC.InfiniteLaplaceTransfer.finiteSpatialLaplaceFunctional_restrictToFinite_dyadicCutoff` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:94` |
| `PaperC.InfiniteLaplaceTransfer.infiniteMarkedLaplaceExpectation_eq_finite` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:306` |
| `PaperC.InfiniteLaplaceTransfer.infiniteMarkedLaplaceExpectation_eq_finite_dyadicCutoff` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:336` |
| `PaperC.InfiniteLaplaceTransfer.infiniteSpatialLaplaceExpectation_eq_finite` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:141` |
| `PaperC.InfiniteLaplaceTransfer.infiniteSpatialLaplaceExpectation_eq_finite_dyadicCutoff` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:170` |
| `PaperC.InfiniteLaplaceTransfer.measurable_finiteMarkedLaplaceFunctional` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:271` |
| `PaperC.InfiniteLaplaceTransfer.measurable_finiteSpatialLaplaceFunctional` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:103` |
| `PaperC.InfiniteLaplaceTransfer.measurable_infiniteMarkedLaplaceFunctional` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:277` |
| `PaperC.InfiniteLaplaceTransfer.measurable_infiniteSpatialLaplaceFunctional` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteLaplaceTransfer.lean:109` |
| `PaperC.InfiniteRademacher.ae_not_constantTail` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:207` |
| `PaperC.InfiniteRademacher.constantTail_subset_zeroTail` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:179` |
| `PaperC.InfiniteRademacher.coordinateMeasure_singleton` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:59` |
| `PaperC.InfiniteRademacher.infiniteRandomValue_mul` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:132` |
| `PaperC.InfiniteRademacher.infiniteRandomValue_nth_prime` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:152` |
| `PaperC.InfiniteRademacher.infiniteRandomValue_sq` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:158` |
| `PaperC.InfiniteRademacher.infiniteValueBit_mul` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:119` |
| `PaperC.InfiniteRademacher.infiniteValueBit_nth_prime` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:140` |
| `PaperC.InfiniteRademacher.infiniteValueBit_sq` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:146` |
| `PaperC.InfiniteRademacher.lemma_fourteen_four` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:219` |
| `PaperC.InfiniteRademacher.measure_constantTail` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:202` |
| `PaperC.InfiniteRademacher.measure_zeroPrefix` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:72` |
| `PaperC.InfiniteRademacher.measure_zeroTail` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:95` |
| `PaperC.InfiniteRademacher.phase_eq_one_iff` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:163` |
| `PaperC.InfiniteRademacher.zeroTail_subset_zeroPrefix` | inconditionnel | — | — | — | `PaperC/Model/InfiniteRademacher.lean:85` |
| `PaperC.InfiniteStartProbabilityTransfer.dyadicCount_restrictToFinite_eq_infiniteDyadicStartCount` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:201` |
| `PaperC.InfiniteStartProbabilityTransfer.infiniteDyadicStartCountEvent_eq_preimage` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:235` |
| `PaperC.InfiniteStartProbabilityTransfer.infiniteDyadicStartCount_law_eq_fullDyadicStartLaw` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:274` |
| `PaperC.InfiniteStartProbabilityTransfer.infiniteDyadicStartEvent_eq_biUnion` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:117` |
| `PaperC.InfiniteStartProbabilityTransfer.infiniteDyadicStartEvent_measure_toReal_le_expectation` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:135` |
| `PaperC.InfiniteStartProbabilityTransfer.infiniteStartEvent_eq_preimage` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:52` |
| `PaperC.InfiniteStartProbabilityTransfer.infiniteStartEvent_measure_eq_startProbability` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:77` |
| `PaperC.InfiniteStartProbabilityTransfer.infiniteStartProbability_eq_startProbability` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:100` |
| `PaperC.InfiniteStartProbabilityTransfer.measurableSet_finiteDyadicStartCountEvent` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:250` |
| `PaperC.InfiniteStartProbabilityTransfer.measurableSet_finiteStartEvent` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:60` |
| `PaperC.InfiniteStartProbabilityTransfer.measurableSet_infiniteDyadicStartCountEvent` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:256` |
| `PaperC.InfiniteStartProbabilityTransfer.measurableSet_infiniteDyadicStartEvent` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:124` |
| `PaperC.InfiniteStartProbabilityTransfer.measurableSet_infiniteStartEvent` | inconditionnel | — | — | — | `PaperC/Probability/InfiniteStartProbabilityTransfer.lean:65` |
| `PaperC.IntervalDefectAggregation.mem_defectsInInterval` | inconditionnel | — | — | — | `PaperC/Combinatorics/IntervalDefectAggregation.lean:32` |
| `PaperC.IntervalDefectAggregation.sum_localCount_eq_sum_intervalStartsContaining` | inconditionnel | — | — | — | `PaperC/Combinatorics/IntervalDefectAggregation.lean:42` |
| `PaperC.IntervalDefectAggregation.sum_localCount_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/IntervalDefectAggregation.lean:57` |
| `PaperC.IntervalDefectAggregation.sum_two_pow_localCount_sub_one_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/IntervalDefectAggregation.lean:97` |
| `PaperC.IntervalDefectAggregation.two_pow_sub_one_le_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/IntervalDefectAggregation.lean:76` |
| `PaperC.IntervalDefectBound.card_defectsInInterval_lt_of_cappedRadius` | inconditionnel | — | — | — | `PaperC/Coding/IntervalDefectBound.lean:243` |
| `PaperC.IntervalDefectBound.card_defectsInInterval_lt_of_log` | inconditionnel | — | — | — | `PaperC/Coding/IntervalDefectBound.lean:43` |
| `PaperC.IntervalDefectBound.card_defectsInInterval_lt_of_log_of_chebyshev_budget` | inconditionnel | — | — | — | `PaperC/Coding/IntervalDefectBound.lean:219` |
| `PaperC.IntervalDefectBound.card_defectsInInterval_lt_of_log_of_count_ratio` | inconditionnel | — | — | — | `PaperC/Coding/IntervalDefectBound.lean:161` |
| `PaperC.IntervalDefectBound.mem_defectsInInterval` | inconditionnel | — | — | — | `PaperC/Coding/IntervalDefectBound.lean:28` |
| `PaperC.LaishramShoreyInput.manuscript_bound_of_laishramShorey` | conditionnel | `LS04-Corollary-1` | `external` | `open` | `PaperC/Arithmetic/LaishramShoreyInput.lean:80` |
| `PaperC.LaplaceVoidClosure.abs_exponentialFunctional_sub_exp_neg_parameter_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/LaplaceVoidClosure.lean:77` |
| `PaperC.LaplaceVoidClosure.abs_exponentialFunctional_sub_exp_neg_parameter_le_of_dependency` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/LaplaceVoidClosure.lean:145` |
| `PaperC.LaplaceVoidClosure.indicatorSum_thinnedIndicator_eq_thinnedCount` | inconditionnel | — | — | — | `PaperC/Probability/LaplaceVoidClosure.lean:33` |
| `PaperC.LaplaceVoidClosure.indicatorSum_thinnedIndicator_eq_zero_iff` | inconditionnel | — | — | — | `PaperC/Probability/LaplaceVoidClosure.lean:47` |
| `PaperC.LaplaceVoidClosure.poissonParameter_thinnedIndicator` | inconditionnel | — | — | — | `PaperC/Probability/LaplaceVoidClosure.lean:57` |
| `PaperC.LargeEulerProduct.prod_one_add_B_div_mul_sqrt_le_exp_two_sqrt` | inconditionnel | — | — | — | `PaperC/Analysis/LargeEulerProduct.lean:128` |
| `PaperC.LargeEulerProduct.prod_one_add_mul_rpow_neg_three_halves_le_exp_sum` | inconditionnel | — | — | — | `PaperC/Analysis/LargeEulerProduct.lean:21` |
| `PaperC.LargeEulerProduct.prod_one_add_mul_rpow_neg_three_halves_le_exp_two_sqrt` | inconditionnel | — | — | — | `PaperC/Analysis/LargeEulerProduct.lean:50` |
| `PaperC.LargeEulerProduct.rpow_neg_three_halves_eq_inv_mul_sqrt` | inconditionnel | — | — | — | `PaperC/Analysis/LargeEulerProduct.lean:106` |
| `PaperC.LargeKernelAssignments.card_allAssignments` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargeKernelAssignments.lean:43` |
| `PaperC.LargeKernelAssignments.card_startsForAssignment_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargeKernelAssignments.lean:184` |
| `PaperC.LargeKernelAssignments.card_startsForSomeAssignment_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargeKernelAssignments.lean:253` |
| `PaperC.LargeKernelAssignments.largeSupport_toList_pairwise_coprime` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargeKernelAssignments.lean:124` |
| `PaperC.LargeKernelAssignments.left_mem_startsForSomeAssignment_of_selected_right` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargeKernelAssignments.lean:339` |
| `PaperC.LargeKernelAssignments.mem_startsForAssignment` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargeKernelAssignments.lean:67` |
| `PaperC.LargeKernelAssignments.mem_startsForSomeAssignment` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargeKernelAssignments.lean:241` |
| `PaperC.LargeKernelAssignments.pairwise_modEq_largeOddKernel` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargeKernelAssignments.lean:139` |
| `PaperC.LargeKernelAssignments.right_mem_startsForSomeAssignment_of_selected_left` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargeKernelAssignments.lean:305` |
| `PaperC.LargeKernelAssignments.startCompleteVertexLabel_le_dyadicCutoff` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargeKernelAssignments.lean:291` |
| `PaperC.LargeKernelAssignments.start_modEq_of_assigned_labels_dvd` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargeKernelAssignments.lean:83` |
| `PaperC.LargeKernelWeightedCounting.canonicalKernelTriple_injective_of_ne_zero` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:101` |
| `PaperC.LargeKernelWeightedCounting.canonicalKernelTriple_mem_kernelTriplesUpTo` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:126` |
| `PaperC.LargeKernelWeightedCounting.canonicalKernelTriplesUpTo_subset_kernelTriplesUpTo` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:180` |
| `PaperC.LargeKernelWeightedCounting.cast_sqrt_div_small_mul_large_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:268` |
| `PaperC.LargeKernelWeightedCounting.disjoint_of_subset_smallPrimesUpTo_of_subset_largePrimesBetween` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:251` |
| `PaperC.LargeKernelWeightedCounting.invSqrtWeight_mul_kernelWeight_eq_denominatorWeight` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:292` |
| `PaperC.LargeKernelWeightedCounting.kernelTripleWeight_canonical` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:85` |
| `PaperC.LargeKernelWeightedCounting.kernelTripleWeight_nonneg` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:74` |
| `PaperC.LargeKernelWeightedCounting.largeKernelWeight_eq_cardDistinctFactors` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:55` |
| `PaperC.LargeKernelWeightedCounting.largeKernelWeight_nonneg` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:49` |
| `PaperC.LargeKernelWeightedCounting.largePrimesBetween_subset_Ioc` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:38` |
| `PaperC.LargeKernelWeightedCounting.largeSupportDenominatorWeight_eq_largeSupportWeight` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:305` |
| `PaperC.LargeKernelWeightedCounting.mem_largePrimesBetween` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:31` |
| `PaperC.LargeKernelWeightedCounting.sum_kernelTriplesUpTo_eq_support_sums` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:219` |
| `PaperC.LargeKernelWeightedCounting.sum_kernelTriplesUpTo_le_support_weight_sums` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:359` |
| `PaperC.LargeKernelWeightedCounting.sum_largeKernelWeight_eq_sum_canonicalKernelTriplesUpTo` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:188` |
| `PaperC.LargeKernelWeightedCounting.sum_largeKernelWeight_le_eulerProducts` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:443` |
| `PaperC.LargeKernelWeightedCounting.sum_largeKernelWeight_le_sum_kernelTriplesUpTo` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:209` |
| `PaperC.LargeKernelWeightedCounting.support_pair_contribution_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:324` |
| `PaperC.LargeKernelWeightedCounting.support_weight_sums_eq_eulerProducts` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeKernelWeightedCounting.lean:375` |
| `PaperC.LargeOddKernel.canonicalSquarePart_ne_zero` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:353` |
| `PaperC.LargeOddKernel.canonical_largeOddKernel_decomposition` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:338` |
| `PaperC.LargeOddKernel.cardDistinctFactors_largeOddKernel` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:274` |
| `PaperC.LargeOddKernel.disjoint_smallOddPrimeSupport_largeOddPrimeSupport` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:285` |
| `PaperC.LargeOddKernel.factorization_largeOddKernel` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:402` |
| `PaperC.LargeOddKernel.factorization_smallOddPart` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:418` |
| `PaperC.LargeOddKernel.largeOddKernel_dvd` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:237` |
| `PaperC.LargeOddKernel.largeOddKernel_eq_one_iff_hDefective` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:448` |
| `PaperC.LargeOddKernel.largeOddKernel_eq_one_iff_support_eq_empty` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:434` |
| `PaperC.LargeOddKernel.largeOddKernel_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:264` |
| `PaperC.LargeOddKernel.largeOddKernel_mem_Icc` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:269` |
| `PaperC.LargeOddKernel.largeOddKernel_ne_zero` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:156` |
| `PaperC.LargeOddKernel.largeOddKernel_squarefree` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:223` |
| `PaperC.LargeOddKernel.largeOddPrimeSupport_subset_primeFactors` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:144` |
| `PaperC.LargeOddKernel.mem_largeOddPrimeSupport` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:43` |
| `PaperC.LargeOddKernel.mem_largeOddPrimeSupport_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:67` |
| `PaperC.LargeOddKernel.mem_largeOddPrimeSupport_iff_prime_large_odd` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:114` |
| `PaperC.LargeOddKernel.mem_oddPrimeSupport_iff_parityVec_ne_zero` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:55` |
| `PaperC.LargeOddKernel.mem_smallOddPrimeSupport` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:49` |
| `PaperC.LargeOddKernel.mem_smallOddPrimeSupport_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:74` |
| `PaperC.LargeOddKernel.mem_smallOddPrimeSupport_iff_prime_small_odd` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:129` |
| `PaperC.LargeOddKernel.one_le_largeOddKernel` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:259` |
| `PaperC.LargeOddKernel.parityVec_ne_zero_iff_mem_largeOddPrimeSupport` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:105` |
| `PaperC.LargeOddKernel.primeFactors_largeOddKernel` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:186` |
| `PaperC.LargeOddKernel.primeFactors_smallOddPart` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:193` |
| `PaperC.LargeOddKernel.primeFinset_product_injective` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:174` |
| `PaperC.LargeOddKernel.prime_and_large_of_mem_largeOddPrimeSupport` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:88` |
| `PaperC.LargeOddKernel.prime_and_small_of_mem_smallOddPrimeSupport` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:95` |
| `PaperC.LargeOddKernel.prime_dvd_largeOddKernel_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:362` |
| `PaperC.LargeOddKernel.prime_dvd_largeOddKernel_iff_large_odd` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:373` |
| `PaperC.LargeOddKernel.prime_dvd_smallOddPart_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:382` |
| `PaperC.LargeOddKernel.prime_dvd_smallOddPart_iff_small_odd` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:393` |
| `PaperC.LargeOddKernel.prime_of_mem_oddPrimeSupport` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:81` |
| `PaperC.LargeOddKernel.smallOddPart_coprime_largeOddKernel` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:317` |
| `PaperC.LargeOddKernel.smallOddPart_dvd` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:248` |
| `PaperC.LargeOddKernel.smallOddPart_mul_largeOddKernel` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:308` |
| `PaperC.LargeOddKernel.smallOddPart_ne_zero` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:163` |
| `PaperC.LargeOddKernel.smallOddPart_squarefree` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:230` |
| `PaperC.LargeOddKernel.smallOddPrimeSupport_subset_primeFactors` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:150` |
| `PaperC.LargeOddKernel.smallOddPrimeSupport_union_largeOddPrimeSupport` | inconditionnel | — | — | — | `PaperC/Arithmetic/LargeOddKernel.lean:294` |
| `PaperC.LargePrimeComponents.componentLabels_large_parity_eq_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:348` |
| `PaperC.LargePrimeComponents.componentLabels_pos` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:320` |
| `PaperC.LargePrimeComponents.componentVertices_nonempty` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:64` |
| `PaperC.LargePrimeComponents.component_large_parity_eq_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:218` |
| `PaperC.LargePrimeComponents.exists_component_square_class` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:372` |
| `PaperC.LargePrimeComponents.mem_componentVertices` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:40` |
| `PaperC.LargePrimeComponents.ordered_gap_of_lt_dist` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:91` |
| `PaperC.LargePrimeComponents.parityVec_eq_zero_of_not_mem_primeOccurrences` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:170` |
| `PaperC.LargePrimeComponents.startCompleteVertexLabel_lower` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:75` |
| `PaperC.LargePrimeComponents.startCompleteVertexLabel_upper` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:83` |
| `PaperC.LargePrimeComponents.sum_parityVec_eq_filtered_card` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:188` |
| `PaperC.LargePrimeComponents.twoStartCompleteVertexLabel_injective_of_separated` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeComponents.lean:106` |
| `PaperC.LargePrimeDependencyGraph.card_orderedDependencyEdges_cast_le_prime_sum` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:633` |
| `PaperC.LargePrimeDependencyGraph.card_orderedDependencyEdges_le_sum_sq` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:438` |
| `PaperC.LargePrimeDependencyGraph.card_startsUsingPrime_cast_le` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:595` |
| `PaperC.LargePrimeDependencyGraph.card_startsWithDivisibleOffset_cast_le` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:518` |
| `PaperC.LargePrimeDependencyGraph.dvd_sub_one_add_iff_modEq` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:481` |
| `PaperC.LargePrimeDependencyGraph.exists_largePrime_of_mem_runSupport_of_good` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:153` |
| `PaperC.LargePrimeDependencyGraph.exists_shared_largePrime_of_good_of_dist_eq` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:273` |
| `PaperC.LargePrimeDependencyGraph.exists_shared_largePrime_of_good_of_dist_le` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:238` |
| `PaperC.LargePrimeDependencyGraph.exists_shared_largePrime_of_good_of_dist_lt` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:259` |
| `PaperC.LargePrimeDependencyGraph.largePrimeAdjacent_iff` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:135` |
| `PaperC.LargePrimeDependencyGraph.largePrimeAdjacent_of_common_run_tree_vertex` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:183` |
| `PaperC.LargePrimeDependencyGraph.largePrimeAdjacent_of_good_of_dist_le` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:220` |
| `PaperC.LargePrimeDependencyGraph.largePrimeAdjacent_of_lt_of_sub_le` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:200` |
| `PaperC.LargePrimeDependencyGraph.largePrimeAdjacent_symm` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:105` |
| `PaperC.LargePrimeDependencyGraph.largePrimeDependencyGraph_adj` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:128` |
| `PaperC.LargePrimeDependencyGraph.mem_goodStarts` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:91` |
| `PaperC.LargePrimeDependencyGraph.mem_largePrimeCoordinates` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:80` |
| `PaperC.LargePrimeDependencyGraph.mem_largePrimesInRange` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:334` |
| `PaperC.LargePrimeDependencyGraph.mem_largePrimesInRange_of_mem_coordinates` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:377` |
| `PaperC.LargePrimeDependencyGraph.mem_orderedDependencyEdges` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:296` |
| `PaperC.LargePrimeDependencyGraph.mem_orderedPairsUsingPrime` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:360` |
| `PaperC.LargePrimeDependencyGraph.mem_startRunSupport` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:56` |
| `PaperC.LargePrimeDependencyGraph.mem_startTreeSupport` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:66` |
| `PaperC.LargePrimeDependencyGraph.mem_startsUsingPrime` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:347` |
| `PaperC.LargePrimeDependencyGraph.mem_startsWithDivisibleOffset` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:471` |
| `PaperC.LargePrimeDependencyGraph.ne_of_mem_orderedDependencyEdges` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:316` |
| `PaperC.LargePrimeDependencyGraph.not_largePrimeAdjacent_self` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:114` |
| `PaperC.LargePrimeDependencyGraph.orderedDependencyEdges_subset_primeWitnessCover` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:416` |
| `PaperC.LargePrimeDependencyGraph.pair_self_not_mem_orderedDependencyEdges` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:323` |
| `PaperC.LargePrimeDependencyGraph.startsUsingPrime_subset_offsetUnion` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:557` |
| `PaperC.LargePrimeDependencyGraph.swap_mem_orderedDependencyEdges` | inconditionnel | — | — | — | `PaperC/Probability/LargePrimeDependencyGraph.lean:307` |
| `PaperC.LargePrimeGraph.eq_on_adj_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:203` |
| `PaperC.LargePrimeGraph.eq_zero_of_isPinned_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:224` |
| `PaperC.LargePrimeGraph.isDefective_of_not_isPinned_of_isolated` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:324` |
| `PaperC.LargePrimeGraph.largePrimeGraph_adj` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:57` |
| `PaperC.LargePrimeGraph.mem_largePrimeSolution` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:100` |
| `PaperC.LargePrimeGraph.mem_largePrimeSolution_iff_boundary_prime_equations` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:147` |
| `PaperC.LargePrimeGraph.mem_largePrimeSolution_iff_graph_rules` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:285` |
| `PaperC.LargePrimeGraph.mem_largePrimeSolution_of_graph_rules` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:240` |
| `PaperC.LargePrimeGraph.not_adj_of_isDefective` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:312` |
| `PaperC.LargePrimeGraph.not_isPinned_of_isDefective` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:304` |
| `PaperC.LargePrimeGraph.primeOccurrences_eq_pair_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:164` |
| `PaperC.LargePrimeGraph.sum_mul_parityVec_eq_sum_primeOccurrences` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraph.lean:110` |
| `PaperC.LargePrimeGraphResolution.card_occurrence` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:112` |
| `PaperC.LargePrimeGraphResolution.defectiveVertexCount_eq_defectiveComponentCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:297` |
| `PaperC.LargePrimeGraphResolution.defectiveVertex_add_twice_nontrivial_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:320` |
| `PaperC.LargePrimeGraphResolution.defective_add_twice_nontrivial_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:118` |
| `PaperC.LargePrimeGraphResolution.eq_of_reachable_of_no_adj` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:154` |
| `PaperC.LargePrimeGraphResolution.finrank_largePrimeSolution` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:100` |
| `PaperC.LargePrimeGraphResolution.finrank_largePrimeSolution_eq_defective_add_components` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:310` |
| `PaperC.LargePrimeGraphResolution.isDefective_of_isolatedUnpinnedComponent` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:214` |
| `PaperC.LargePrimeGraphResolution.isIsolatedUnpinnedComponent_of_isDefective` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:168` |
| `PaperC.LargePrimeGraphResolution.largePrimeSolution_eq_pinnedGraphSpace` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:48` |
| `PaperC.LargePrimeGraphResolution.mem_defectiveVertices` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:139` |
| `PaperC.LargePrimeGraphResolution.mem_pinnedVertices` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeGraphResolution.lean:37` |
| `PaperC.LargePrimeOccurrences.card_primeOccurrences_le_two` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeOccurrences.lean:115` |
| `PaperC.LargePrimeOccurrences.eq_pair_inl_inr_of_card_eq_two` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeOccurrences.lean:171` |
| `PaperC.LargePrimeOccurrences.exists_pin_of_card_eq_one` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeOccurrences.lean:210` |
| `PaperC.LargePrimeOccurrences.inOppositeBlocks_of_mem_of_ne` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeOccurrences.lean:142` |
| `PaperC.LargePrimeOccurrences.inl_eq_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeOccurrences.lean:55` |
| `PaperC.LargePrimeOccurrences.inr_eq_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeOccurrences.lean:69` |
| `PaperC.LargePrimeOccurrences.mem_primeOccurrences` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeOccurrences.lean:35` |
| `PaperC.LargePrimeOccurrences.occurrenceBlock_injOn` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeOccurrences.lean:91` |
| `PaperC.LargePrimeOccurrences.parityVec_ne_zero_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeOccurrences.lean:42` |
| `PaperC.LargePrimeRelationBoundary.exactUnitBoundaryVector_mem_largePrimeSolution` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:213` |
| `PaperC.LargePrimeRelationBoundary.leftBlockParityOnLargePrime_ne_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:283` |
| `PaperC.LargePrimeRelationBoundary.leftBlockParityOnLargePrime_surjective` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:252` |
| `PaperC.LargePrimeRelationBoundary.leftBlockParity_apply` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:169` |
| `PaperC.LargePrimeRelationBoundary.leftBlockParity_exactUnitBoundaryVector` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:236` |
| `PaperC.LargePrimeRelationBoundary.leftBlockParity_relationBoundaryMap` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:176` |
| `PaperC.LargePrimeRelationBoundary.relationBoundaryMap_apply` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:43` |
| `PaperC.LargePrimeRelationBoundary.relationBoundaryMap_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:52` |
| `PaperC.LargePrimeRelationBoundary.relationBoundaryMap_mem_largePrimeSolution` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:96` |
| `PaperC.LargePrimeRelationBoundary.relationBoundaryToLargePrime_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:145` |
| `PaperC.LargePrimeRelationBoundary.relationRho_le_finrank_largePrimeSolution` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:303` |
| `PaperC.LargePrimeRelationBoundary.relationRho_le_finrank_largePrimeSolution_sub_one` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:319` |
| `PaperC.LargePrimeRelationBoundary.sum_exactUnitBoundaryVector_mul_parityVec` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:197` |
| `PaperC.LargePrimeRelationBoundary.twoStartCompleteVertexLabel_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:75` |
| `PaperC.LargePrimeRelationBoundary.twoStartCompleteVertexLabel_pos` | inconditionnel | — | — | — | `PaperC/Combinatorics/LargePrimeRelationBoundary.lean:61` |
| `PaperC.LemmaFifteenThree.assemble_twoDefectWindow_bound` | inconditionnel | — | — | — | `PaperC/Asymptotics/LemmaFifteenThree.lean:442` |
| `PaperC.LemmaFifteenThree.combined_exponent_le_critical` | inconditionnel | — | — | — | `PaperC/Asymptotics/LemmaFifteenThree.lean:269` |
| `PaperC.LemmaFifteenThree.combined_exponent_le_critical_range` | inconditionnel | — | — | — | `PaperC/Asymptotics/LemmaFifteenThree.lean:402` |
| `PaperC.LemmaFifteenThree.criticalExponentConstant_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/LemmaFifteenThree.lean:255` |
| `PaperC.LemmaFifteenThree.lemma_fifteen_three` | conditionnel | `ADGR07-PNT`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/LemmaFifteenThree.lean:569` |
| `PaperC.LemmaFifteenThree.lemma_fifteen_three_uniform_height_range` | conditionnel | `ADGR07-PNT`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/LemmaFifteenThree.lean:824` |
| `PaperC.LemmaFifteenThree.log_const_le_loglog_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/LemmaFifteenThree.lean:66` |
| `PaperC.LemmaFifteenThree.log_div_loglog_monotone_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/LemmaFifteenThree.lean:187` |
| `PaperC.LemmaFifteenThree.log_sq_le_linear_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/LemmaFifteenThree.lean:40` |
| `PaperC.LemmaFifteenThree.log_sq_le_self_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/LemmaFifteenThree.lean:58` |
| `PaperC.LemmaFifteenThree.succ_div_log_le_two_mul_div_log` | inconditionnel | — | — | — | `PaperC/Asymptotics/LemmaFifteenThree.lean:100` |
| `PaperC.LemmaFifteenThree.three_mul_log_div_loglog_le_two` | inconditionnel | — | — | — | `PaperC/Asymptotics/LemmaFifteenThree.lean:133` |
| `PaperC.LogLogRunWindow.balanceRatio_le_envelope_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/LogLogRunWindow.lean:314` |
| `PaperC.LogLogRunWindow.balanceRatio_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/LogLogRunWindow.lean:400` |
| `PaperC.LogLogRunWindow.heightWindow_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/LogLogRunWindow.lean:177` |
| `PaperC.LogLogRunWindow.loglog_le_two_mul_sqrt_log` | inconditionnel | — | — | — | `PaperC/Asymptotics/LogLogRunWindow.lean:159` |
| `PaperC.LowZoneCritical.card_lowZoneStarts_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:61` |
| `PaperC.LowZoneCritical.lowZonePowerEnvelope_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:317` |
| `PaperC.LowZoneCritical.lowZoneProbabilityMassQ_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:134` |
| `PaperC.LowZoneCritical.lowZoneProbabilityMassQ_le_primeCountEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:169` |
| `PaperC.LowZoneCritical.lowZoneProbabilityMassQ_le_primeCountSum` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:104` |
| `PaperC.LowZoneCritical.lowZoneProbabilityMassQ_le_primeSum` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:84` |
| `PaperC.LowZoneCritical.lowZoneProbabilityMassQ_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:66` |
| `PaperC.LowZoneCritical.lowZoneProbabilityMass_le_primeCountEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:185` |
| `PaperC.LowZoneCritical.lowZoneProbabilityMass_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:73` |
| `PaperC.LowZoneCritical.lowZoneProbabilityMass_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:746` |
| `PaperC.LowZoneCritical.lowZoneProbabilityMass_uniformLittleOOne_power` | conditionnel | `ADGR07-PNT` | `external` | `open` | `PaperC/Asymptotics/LowZoneCritical.lean:794` |
| `PaperC.LowZoneCritical.lowZoneSquareGapOn_power` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:261` |
| `PaperC.LowZoneCritical.mem_lowZoneStarts` | inconditionnel | — | — | — | `PaperC/Asymptotics/LowZoneCritical.lean:48` |
| `PaperC.LowZoneCritical.primeNumberTheorem_implies_lowZonePrimeGrowth_power` | conditionnel | `ADGR07-PNT` | `external` | `open` | `PaperC/Asymptotics/LowZoneCritical.lean:498` |
| `PaperC.LowZonePrimePivots.card_intermediatePrimes_eq_primeCount_sub` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:567` |
| `PaperC.LowZonePrimePivots.card_intermediatePrimes_eq_primeCount_sub_of_gap` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:602` |
| `PaperC.LowZonePrimePivots.card_intermediatePrimes_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:508` |
| `PaperC.LowZonePrimePivots.disjoint_primeVertexSet` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:184` |
| `PaperC.LowZonePrimePivots.factorization_eq_one_of_mem_primeVertexSet` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:143` |
| `PaperC.LowZonePrimePivots.lowZoneConstraintMap_evenPrimeTestVector` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:447` |
| `PaperC.LowZonePrimePivots.lowZoneConstraintMap_rightInverse` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:477` |
| `PaperC.LowZonePrimePivots.lowZoneConstraintMap_surjective` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:499` |
| `PaperC.LowZonePrimePivots.lowZoneSquareLabel_lt` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:279` |
| `PaperC.LowZonePrimePivots.lowZoneSquareOffset_pos_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:229` |
| `PaperC.LowZonePrimePivots.lowZoneSquareVertex_not_mem` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:289` |
| `PaperC.LowZonePrimePivots.mem_intermediatePrimes` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:59` |
| `PaperC.LowZonePrimePivots.mem_primeVertexSet` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:70` |
| `PaperC.LowZonePrimePivots.parityVec_eq_one_of_mem_primeVertexSet` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:174` |
| `PaperC.LowZonePrimePivots.parityVec_eq_zero_of_not_mem_primeVertexSet` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:366` |
| `PaperC.LowZonePrimePivots.parityVec_lowZoneSquareVertex` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:400` |
| `PaperC.LowZonePrimePivots.parityVec_primePivot` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:379` |
| `PaperC.LowZonePrimePivots.primePivot_mem` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:359` |
| `PaperC.LowZonePrimePivots.primeVertexSet_nonempty` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:92` |
| `PaperC.LowZonePrimePivots.primeVertexSet_nonempty_of_intermediate` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:126` |
| `PaperC.LowZonePrimePivots.relationRho_startSystem_le_sub_card_intermediatePrimes` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:678` |
| `PaperC.LowZonePrimePivots.relation_boundary_constraint_eq_zero` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:636` |
| `PaperC.LowZonePrimePivots.sqrt_window_le_of_gap` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:536` |
| `PaperC.LowZonePrimePivots.startCompleteVertexLabel_bounds` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:76` |
| `PaperC.LowZonePrimePivots.startCompleteVertexLabel_lowZoneSquareVertex` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:262` |
| `PaperC.LowZonePrimePivots.startProbability_le_inv_two_pow_card_intermediatePrimes` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:755` |
| `PaperC.LowZonePrimePivots.window_lt_prime_sq` | inconditionnel | — | — | — | `PaperC/Arithmetic/LowZonePrimePivots.lean:134` |
| `PaperC.MarkedConditionalDependencyGraph.conditionalMarked_totalVariationToPoisson_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:488` |
| `PaperC.MarkedConditionalDependencyGraph.conditionedExactLengthAt_iff_of_eqOn_markedCoordinateSupport` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:226` |
| `PaperC.MarkedConditionalDependencyGraph.conditionedMarkedIndicator_eq_false_iff` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:210` |
| `PaperC.MarkedConditionalDependencyGraph.conditionedMarkedIndicator_eq_of_eqOn_support` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:244` |
| `PaperC.MarkedConditionalDependencyGraph.conditionedMarkedIndicator_eq_true_iff` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:197` |
| `PaperC.MarkedConditionalDependencyGraph.disjoint_markedCoordinateSupport_of_not_adjacent` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:167` |
| `PaperC.MarkedConditionalDependencyGraph.finiteUniformProbability_conditionedExactLength_eq` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:285` |
| `PaperC.MarkedConditionalDependencyGraph.hasExactDependencyGraph_conditionedMarkedIndicator` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:379` |
| `PaperC.MarkedConditionalDependencyGraph.largeExactLengthSystem_surjective_of_retained` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:304` |
| `PaperC.MarkedConditionalDependencyGraph.largePrimeCoordinates_mono_length` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:104` |
| `PaperC.MarkedConditionalDependencyGraph.marginal_conditionedMarkedIndicator_eq_baseline` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:341` |
| `PaperC.MarkedConditionalDependencyGraph.markedAdjacent_symm` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:137` |
| `PaperC.MarkedConditionalDependencyGraph.markedCoordinateSupport_subset_common` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:118` |
| `PaperC.MarkedConditionalDependencyGraph.markedDependencyGraph_adj` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:160` |
| `PaperC.MarkedConditionalDependencyGraph.markedRowCount_le_common` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:85` |
| `PaperC.MarkedConditionalDependencyGraph.mem_retainedMarkedStarts` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:71` |
| `PaperC.MarkedConditionalDependencyGraph.not_markedAdjacent_self` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:146` |
| `PaperC.MarkedConditionalDependencyGraph.two_le_markedRowCount` | inconditionnel | — | — | — | `PaperC/Probability/MarkedConditionalDependencyGraph.lean:92` |
| `PaperC.MarkedCountVectorMixture.averagedConditionalRetainedExactLengthCountVectorLaw_eq_finite` | inconditionnel | — | — | — | `PaperC/Probability/MarkedCountVectorMixture.lean:74` |
| `PaperC.MarkedDetruncation.ae_mem_infiniteMarkTailEvent_iff_longStartEvent` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:131` |
| `PaperC.MarkedDetruncation.ae_mem_infiniteMaximumAtMostEvent_iff_no_longStart` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:206` |
| `PaperC.MarkedDetruncation.infiniteMarkTailEvent_eq_biUnion_iUnion` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:61` |
| `PaperC.MarkedDetruncation.infiniteMarkTailEvent_subset_longStartEvent` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:83` |
| `PaperC.MarkedDetruncation.infiniteMarkTailProbability_le_longStartExpectation` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:163` |
| `PaperC.MarkedDetruncation.longStartEvent_subset_infiniteMarkTailEvent_of_tailChanges` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:97` |
| `PaperC.MarkedDetruncation.measurableSet_infiniteMarkTailEvent` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:69` |
| `PaperC.MarkedDetruncation.measurableSet_infiniteMaximumAtMostEvent` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:198` |
| `PaperC.MarkedDetruncation.measure_infiniteMarkTailEvent_eq_longStartEvent` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:142` |
| `PaperC.MarkedDetruncation.measure_infiniteMaximumAtMostEvent_eq_no_longStart` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:218` |
| `PaperC.MarkedDetruncation.measure_infiniteMaximumAtMostEvent_eq_one_sub_longStart` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:234` |
| `PaperC.MarkedDetruncation.mem_infiniteMarkTailEvent_iff_longStartEvent_of_tailChanges` | inconditionnel | — | — | — | `PaperC/Probability/MarkedDetruncation.lean:117` |
| `PaperC.MarkedDetruncationCritical.infiniteMarkTailProbability_le_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedDetruncationCritical.lean:147` |
| `PaperC.MarkedDetruncationCritical.infiniteMarkTailProbability_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedDetruncationCritical.lean:141` |
| `PaperC.MarkedDetruncationCritical.longStartExpectation_eventually_le_baseline_add` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedDetruncationCritical.lean:74` |
| `PaperC.MarkedDetruncationCritical.markTailProbabilities_uniformly_tight` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedDetruncationCritical.lean:290` |
| `PaperC.MarkedDetruncationCritical.markTailProbability_eventual_geometric_bound` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedDetruncationCritical.lean:161` |
| `PaperC.MarkedDetruncationCritical.markTailProbability_eventually_le_baseline_add` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedDetruncationCritical.lean:123` |
| `PaperC.MarkedDetruncationCritical.markTailProbability_limsup_le_geometric` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedDetruncationCritical.lean:237` |
| `PaperC.MarkedDetruncationCritical.shifted_runLength_mem` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedDetruncationCritical.lean:43` |
| `PaperC.MarkedLaplaceCritical.infiniteMarkedLaplaceExpectation_eq_uniformPMFExpectation` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedLaplaceCritical.lean:173` |
| `PaperC.MarkedLaplaceCritical.markedBTwoAverageReal_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedLaplaceCritical.lean:56` |
| `PaperC.MarkedLaplaceCritical.markedBTwoAverageReal_uniformLittleOOne_of_split` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedLaplaceCritical.lean:79` |
| `PaperC.MarkedLaplaceCritical.markedBTwoSplitReal_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedLaplaceCritical.lean:66` |
| `PaperC.MarkedLaplaceCritical.markedBTwoSplitReal_uniformLittleOOne` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/MarkedLaplaceCritical.lean:120` |
| `PaperC.MarkedLaplaceCritical.removedMarkedParameterEnvelope_tendsto_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedLaplaceCritical.lean:192` |
| `PaperC.MarkedLaplaceCritical.sectionFourteenFour_laplaceFunctional` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/MarkedLaplaceCritical.lean:400` |
| `PaperC.MarkedLaplaceCritical.sectionFourteenFour_laplaceFunctional_of_bTwo` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/MarkedLaplaceCritical.lean:269` |
| `PaperC.MarkedLaplaceCritical.sectionFourteenFour_laplaceFunctional_of_split` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/MarkedLaplaceCritical.lean:357` |
| `PaperC.MarkedLaplaceCritical.tendsto_retainedMarkedThinnedParameter` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedLaplaceCritical.lean:215` |
| `PaperC.MarkedLaplaceFiniteClosure.abs_finiteMarkedLaplaceFunctional_sub_retained_le_count` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:488` |
| `PaperC.MarkedLaplaceFiniteClosure.abs_fullMarkedExpectation_sub_retained_le_removedMass` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:595` |
| `PaperC.MarkedLaplaceFiniteClosure.abs_markedThinnedParameter_sub_retained_le_envelope` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:781` |
| `PaperC.MarkedLaplaceFiniteClosure.averagedRetainedMarkedLaplace_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:290` |
| `PaperC.MarkedLaplaceFiniteClosure.conditionalRetainedMarkedLaplace_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:247` |
| `PaperC.MarkedLaplaceFiniteClosure.conditionedMarked_thinnedParameter_eq_retained` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:191` |
| `PaperC.MarkedLaplaceFiniteClosure.eventProbability_uniform_exactLength_eq_infinite` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:549` |
| `PaperC.MarkedLaplaceFiniteClosure.exponentialFunctional_conditionedMarkedIndicator_eq_retained` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:129` |
| `PaperC.MarkedLaplaceFiniteClosure.finiteMarkedLaplaceFunctional_eq_retained_of_no_removed` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:406` |
| `PaperC.MarkedLaplaceFiniteClosure.finiteMarkedLaplaceFunctional_mem_unitInterval` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:447` |
| `PaperC.MarkedLaplaceFiniteClosure.fullMarkedLaplace_le_retainedPoisson` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:796` |
| `PaperC.MarkedLaplaceFiniteClosure.markedThinnedParameter_eq_retained_add_removed` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:677` |
| `PaperC.MarkedLaplaceFiniteClosure.removedExactLengthStarts_subset_dyadicBlock` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:389` |
| `PaperC.MarkedLaplaceFiniteClosure.removedMarkedParameterEnvelope_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:726` |
| `PaperC.MarkedLaplaceFiniteClosure.removedMarkedThinnedParameter_le_envelope` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:736` |
| `PaperC.MarkedLaplaceFiniteClosure.removedMarkedThinnedParameter_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:714` |
| `PaperC.MarkedLaplaceFiniteClosure.retainedMarkedLaplaceFunctional_mem_unitInterval` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:467` |
| `PaperC.MarkedLaplaceFiniteClosure.retainedMarkedStarts_eq_sdiff` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLaplaceFiniteClosure.lean:395` |
| `PaperC.MarkedLocalGeometry.exactLengthEvent_eq_start_of_before_right` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:42` |
| `PaperC.MarkedLocalGeometry.exactLengthEvents_excess_incompatible_of_left_overlap` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:118` |
| `PaperC.MarkedLocalGeometry.exactLengthEvents_incompatible_of_strict_overlap` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:84` |
| `PaperC.MarkedLocalGeometry.exactLengthEvents_same_start_incompatible` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:56` |
| `PaperC.MarkedLocalGeometry.exactLengthSupport_diameter` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:35` |
| `PaperC.MarkedLocalGeometry.exactLengthSupport_disjoint_of_separated` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:226` |
| `PaperC.MarkedLocalGeometry.exactLengthSupport_inter_eq_boundaryPair` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:199` |
| `PaperC.MarkedLocalGeometry.exactLengthSupport_inter_eq_singleton` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:214` |
| `PaperC.MarkedLocalGeometry.mem_exactLengthSupport` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:29` |
| `PaperC.MarkedLocalGeometry.mixedExactLengthProbability_eq_zero_of_strict_overlap` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:158` |
| `PaperC.MarkedLocalGeometry.mixedExactLengthProbability_excess_eq_zero_of_left_overlap` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:182` |
| `PaperC.MarkedLocalGeometry.mixedExactLengthProbability_same_start_eq_zero` | inconditionnel | — | — | — | `PaperC/Probability/MarkedLocalGeometry.lean:135` |
| `PaperC.MarkedSteinChenCritical.commonSteinBOne_shift_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:101` |
| `PaperC.MarkedSteinChenCritical.commonSteinBTwoNumerator_shift_uniformLittleOQuadratic` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:279` |
| `PaperC.MarkedSteinChenCritical.markedBOneReal_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:62` |
| `PaperC.MarkedSteinChenCritical.markedBOneReal_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:124` |
| `PaperC.MarkedSteinChenCritical.markedBTwoRelationEnvelopeReal_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:69` |
| `PaperC.MarkedSteinChenCritical.markedBTwoSplitEnvelopeReal_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:78` |
| `PaperC.MarkedSteinChenCritical.markedBTwoSplitEnvelopeReal_uniformLittleOOne` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:506` |
| `PaperC.MarkedSteinChenCritical.markedBTwoSplitEnvelopeReal_uniformLittleOOne_canonical` | conditionnel | `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:558` |
| `PaperC.MarkedSteinChenCritical.markedBTwoSplitNumeratorReal_le_common` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:344` |
| `PaperC.MarkedSteinChenCritical.markedBTwoSplitNumeratorReal_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:87` |
| `PaperC.MarkedSteinChenCritical.markedBTwoSplitNumeratorReal_uniformLittleOQuadratic` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:373` |
| `PaperC.MarkedSteinChenCritical.markedLocalSplitNumeratorReal_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:92` |
| `PaperC.MarkedSteinChenCritical.markedLocalSplitNumeratorReal_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:202` |
| `PaperC.MarkedSteinChenCritical.retainedMarkedTotalVariation_uniformLittleOOne_canonical` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:735` |
| `PaperC.MarkedSteinChenCritical.retainedMarkedTotalVariation_uniformLittleOOne_of_bTwoEnvelope` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:578` |
| `PaperC.MarkedSteinChenCritical.retainedMarkedTotalVariation_uniformLittleOOne_of_bTwoSplitEnvelope` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/MarkedSteinChenCritical.lean:656` |
| `PaperC.MarkedSteinChenSplitBound.card_markedLocalPairs_le` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:140` |
| `PaperC.MarkedSteinChenSplitBound.card_markedLocalPairs_le_explicit` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:162` |
| `PaperC.MarkedSteinChenSplitBound.commonPair_mem_separatedDependencyEdges` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:178` |
| `PaperC.MarkedSteinChenSplitBound.markedBTwoSplitEnvelope_eq_add` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:268` |
| `PaperC.MarkedSteinChenSplitBound.markedBTwoSplitEnvelope_le_explicit` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:646` |
| `PaperC.MarkedSteinChenSplitBound.markedLocalPairCode_injective` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:117` |
| `PaperC.MarkedSteinChenSplitBound.markedLocalRelationEnvelope_le` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:306` |
| `PaperC.MarkedSteinChenSplitBound.markedSeparatedPairCode_injective` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:215` |
| `PaperC.MarkedSteinChenSplitBound.markedSeparatedRelationEnvelope_eq_sigmaSum` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:432` |
| `PaperC.MarkedSteinChenSplitBound.markedSeparatedRelationEnvelope_le` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:611` |
| `PaperC.MarkedSteinChenSplitBound.markedSeparatedSigmaCode_injective` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:494` |
| `PaperC.MarkedSteinChenSplitBound.markedSeparatedSigmaToPair_injective` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:418` |
| `PaperC.MarkedSteinChenSplitBound.mem_markedLocalPairs` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:49` |
| `PaperC.MarkedSteinChenSplitBound.mem_markedSeparatedDependencyPairs` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:76` |
| `PaperC.MarkedSteinChenSplitBound.sum_markedSeparatedSigma_weight_le` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:504` |
| `PaperC.MarkedSteinChenSplitBound.sum_separatedDependencyEdges_two_pow_jointRho_le` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:599` |
| `PaperC.MarkedSteinChenSplitBound.sum_two_pow_jointRho_eq_card_add_defect` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenSplitBound.lean:581` |
| `PaperC.MarkedSteinChenTerms.averagedConditionalMarked_natTotalVariation_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/MarkedSteinChenTerms.lean:837` |
| `PaperC.MarkedSteinChenTerms.averagedConditionalMarked_natTotalVariation_le_explicit` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/MarkedSteinChenTerms.lean:933` |
| `PaperC.MarkedSteinChenTerms.bOne_conditionedMarkedIndicator_eq` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:270` |
| `PaperC.MarkedSteinChenTerms.commonStart_mem_closedNeighborhood_of_marked` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:142` |
| `PaperC.MarkedSteinChenTerms.conditionalMarkedBOneAverage_eq` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:425` |
| `PaperC.MarkedSteinChenTerms.conditionalMarkedBTwoAverage_eq` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:434` |
| `PaperC.MarkedSteinChenTerms.conditionalMarkedJointAverage_eq` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:376` |
| `PaperC.MarkedSteinChenTerms.conditionalMarkedLaw_eq_finiteNatLaw` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:803` |
| `PaperC.MarkedSteinChenTerms.jointRho_orderedMarkedStartPair_le` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:602` |
| `PaperC.MarkedSteinChenTerms.markedBOneFinite_le_closedPairCount` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:290` |
| `PaperC.MarkedSteinChenTerms.markedBOneFinite_le_commonSteinBOne` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:331` |
| `PaperC.MarkedSteinChenTerms.markedBTwoAverage_le_relationEnvelope` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:709` |
| `PaperC.MarkedSteinChenTerms.markedBTwoAverage_le_splitEnvelope` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:677` |
| `PaperC.MarkedSteinChenTerms.markedClosedPairCode_injective` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:192` |
| `PaperC.MarkedSteinChenTerms.markedClosedPairCount_le_common` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:228` |
| `PaperC.MarkedSteinChenTerms.matchingPoissonLaw_conditionedMarkedIndicator_eq_common` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:780` |
| `PaperC.MarkedSteinChenTerms.mixedExactLengthProbability_eq_zero_of_markedStrictOverlap` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:511` |
| `PaperC.MarkedSteinChenTerms.mixedExactLengthProbability_le_commonRelation` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:528` |
| `PaperC.MarkedSteinChenTerms.mixedExactLengthProbability_le_orderedCommonRelation` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:579` |
| `PaperC.MarkedSteinChenTerms.mixedExactLengthProbability_same_markedStart_eq_zero` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:467` |
| `PaperC.MarkedSteinChenTerms.mixedExactLengthProbability_swap` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:499` |
| `PaperC.MarkedSteinChenTerms.poissonParameter_conditionedMarkedIndicator_eq` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:762` |
| `PaperC.MarkedSteinChenTerms.pow_jointRho_orderedMarkedStartPair_le` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:660` |
| `PaperC.MarkedSteinChenTerms.summable_abs_conditionalMarkedLaw_sub_commonPoisson` | inconditionnel | — | — | — | `PaperC/Probability/MarkedSteinChenTerms.lean:818` |
| `PaperC.MaskedFirstMoment.abs_maskedDyadicExpectation_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Probability/MaskedFirstMoment.lean:42` |
| `PaperC.MaskedFirstMoment.sum_baseline_over_mask` | inconditionnel | — | — | — | `PaperC/Probability/MaskedFirstMoment.lean:31` |
| `PaperC.MaskedFirstMomentCritical.maskedFirstMomentEnvelope_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedFirstMomentCritical.lean:193` |
| `PaperC.MaskedFirstMomentCritical.maskedFirstMomentEnvelope_uniformNegativeHalfPower` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedFirstMomentCritical.lean:168` |
| `PaperC.MaskedFirstMomentCritical.maskedFirstMomentErrorReal_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedFirstMomentCritical.lean:65` |
| `PaperC.MaskedFirstMomentCritical.maskedFirstMomentErrorReal_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedFirstMomentCritical.lean:44` |
| `PaperC.MaskedFirstMomentCritical.maskedFirstMomentError_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedFirstMomentCritical.lean:249` |
| `PaperC.MaskedFirstMomentCritical.maskedFirstMomentError_uniformLittleOOne_loglogWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedFirstMomentCritical.lean:208` |
| `PaperC.MaskedFirstMomentCritical.terminalDefectWeightMass_uniformHalfPower_loglogWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedFirstMomentCritical.lean:115` |
| `PaperC.MaskedPoissonCanonical.maskedPoissonTotalVariation_uniformLittleOOne` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/MaskedPoissonCanonical.lean:37` |
| `PaperC.MaskedPoissonCanonical.theorem_one_two_i` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/MaskedPoissonCanonical.lean:71` |
| `PaperC.MaskedPoissonCritical.abs_maskedCommonRate_sub_targetRate_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:642` |
| `PaperC.MaskedPoissonCritical.averagedMaskedConditionalGoodLaw_eq_fullMaskedGoodStartLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:772` |
| `PaperC.MaskedPoissonCritical.averagedMaskedConditionalGood_natTotalVariation_le_steinTerms` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/MaskedPoissonCritical.lean:526` |
| `PaperC.MaskedPoissonCritical.bOne_masked_le_unmasked` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:300` |
| `PaperC.MaskedPoissonCritical.bTwo_masked_le_unmasked` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:322` |
| `PaperC.MaskedPoissonCritical.conditionedMaskedIndicatorSum_eq_fullMaskedGoodStartCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:755` |
| `PaperC.MaskedPoissonCritical.disagreementProbability_fullMaskedGood_dyadic_le_badMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:885` |
| `PaperC.MaskedPoissonCritical.exists_bad_start_of_fullMaskedGood_ne_fullMaskedDyadic` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:861` |
| `PaperC.MaskedPoissonCritical.fullMaskedGoodIndicator_eq_true_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:719` |
| `PaperC.MaskedPoissonCritical.fullMaskedGoodStartCount_eq_sum` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:824` |
| `PaperC.MaskedPoissonCritical.fullMaskedGoodStartLaw_eq_finiteNatLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:741` |
| `PaperC.MaskedPoissonCritical.hasExactDependencyGraph_maskedConditionedGoodIndicator` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:106` |
| `PaperC.MaskedPoissonCritical.jointMarginal_masked_le_unmasked` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:268` |
| `PaperC.MaskedPoissonCritical.marginal_maskedConditionedGoodIndicator` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:227` |
| `PaperC.MaskedPoissonCritical.marginal_masked_le_unmasked` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:245` |
| `PaperC.MaskedPoissonCritical.maskedCommonGoodPoissonLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:440` |
| `PaperC.MaskedPoissonCritical.maskedCommonGoodPoissonRate_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:599` |
| `PaperC.MaskedPoissonCritical.maskedConditionalGoodLaw_eq_finiteNatLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:407` |
| `PaperC.MaskedPoissonCritical.maskedConditionalGoodLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:429` |
| `PaperC.MaskedPoissonCritical.maskedConditionalGood_natTotalVariation_le_unmaskedTerms` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/MaskedPoissonCritical.lean:461` |
| `PaperC.MaskedPoissonCritical.maskedConditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:81` |
| `PaperC.MaskedPoissonCritical.maskedConditionedGoodIndicator_eq_true_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:69` |
| `PaperC.MaskedPoissonCritical.maskedPoissonTotalVariation_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:1086` |
| `PaperC.MaskedPoissonCritical.maskedPoissonTotalVariation_uniformLittleOOne_of_homogeneousMass` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/MaskedPoissonCritical.lean:1101` |
| `PaperC.MaskedPoissonCritical.matchingPoissonLaw_maskedConditioned_eq_common` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:385` |
| `PaperC.MaskedPoissonCritical.natTotalVariation_averagedMaskedGood_fullMasked_le_badMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:983` |
| `PaperC.MaskedPoissonCritical.natTotalVariation_fullMasked_target_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/MaskedPoissonCritical.lean:1006` |
| `PaperC.MaskedPoissonCritical.natTotalVariation_maskedCommon_target_le_badCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:676` |
| `PaperC.MaskedPoissonCritical.poissonParameter_maskedConditioned_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:366` |
| `PaperC.MaskedPoissonCritical.summable_abs_maskedConditional_sub_common` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:445` |
| `PaperC.MaskedPoissonCritical.summable_maskedCommonGoodPoissonLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:435` |
| `PaperC.MaskedPoissonCritical.summable_maskedConditionalGoodLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/MaskedPoissonCritical.lean:422` |
| `PaperC.MaskedPoissonRate.maskedPoissonTotalVariation_uniformBigO_canonical` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/MaskedPoissonRate.lean:121` |
| `PaperC.MaskedPoissonRate.maskedRateEnvelope_uniformBigO_canonical` | conditionnel | `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/MaskedPoissonRate.lean:53` |
| `PaperC.MaskedSteinChen.abs_maskedPoissonParameter_sub_good_le` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:357` |
| `PaperC.MaskedSteinChen.card_maskedGoodStarts_le` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:52` |
| `PaperC.MaskedSteinChen.card_maskedGood_add_card_bad` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:303` |
| `PaperC.MaskedSteinChen.card_maskedTerminalBadStarts_le` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:220` |
| `PaperC.MaskedSteinChen.maskedBadStartProbabilityMass_le_two_cutoffs` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:249` |
| `PaperC.MaskedSteinChen.maskedBadStartProbabilityMass_le_unmasked` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:234` |
| `PaperC.MaskedSteinChen.maskedClosedDependencyPairs_eq_diag_union_edges` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:123` |
| `PaperC.MaskedSteinChen.maskedClosedDependencyPairs_subset` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:96` |
| `PaperC.MaskedSteinChen.maskedDependencyEdges_subset` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:73` |
| `PaperC.MaskedSteinChen.maskedGoodPoissonParameter_le` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:338` |
| `PaperC.MaskedSteinChen.maskedGoodStarts_eq_sdiff` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:280` |
| `PaperC.MaskedSteinChen.maskedGoodStarts_subset_goodStarts` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:46` |
| `PaperC.MaskedSteinChen.maskedPoissonParameter_sub_good_eq` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:318` |
| `PaperC.MaskedSteinChen.maskedSteinBOne_eq_card_div` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:157` |
| `PaperC.MaskedSteinChen.maskedSteinBOne_le_unmasked` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:168` |
| `PaperC.MaskedSteinChen.maskedSteinBTwoAverage_le_unmasked` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:189` |
| `PaperC.MaskedSteinChen.maskedTerminalBadStarts_eq_inter` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:295` |
| `PaperC.MaskedSteinChen.maskedTerminalBadStarts_subset` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:213` |
| `PaperC.MaskedSteinChen.mem_maskedClosedDependencyPairs` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:88` |
| `PaperC.MaskedSteinChen.mem_maskedClosedNeighborhood` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:111` |
| `PaperC.MaskedSteinChen.mem_maskedDependencyEdges` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:65` |
| `PaperC.MaskedSteinChen.mem_maskedGoodStarts` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:39` |
| `PaperC.MaskedSteinChen.mem_maskedTerminalBadStarts` | inconditionnel | — | — | — | `PaperC/Probability/MaskedSteinChen.lean:206` |
| `PaperC.MixedLengthAffine.dotProduct_zeroExtendMixedCoefficients` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:309` |
| `PaperC.MixedLengthAffine.exactLengthRhs_apply` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:49` |
| `PaperC.MixedLengthAffine.mixedExactLengthProbability_eq_eta_mul_two_pow_rho_div` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:207` |
| `PaperC.MixedLengthAffine.mixedExactLengthProbability_eq_uniformSolutionProbability` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:186` |
| `PaperC.MixedLengthAffine.mixedExcessProbability_eq_eta_mul_two_pow_rho_div` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:415` |
| `PaperC.MixedLengthAffine.mixedExcess_relationRho_le_common` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:440` |
| `PaperC.MixedLengthAffine.mixedIndexEmbedding_injective` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:238` |
| `PaperC.MixedLengthAffine.mixedLengthRhs_apply_inl` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:145` |
| `PaperC.MixedLengthAffine.mixedLengthRhs_apply_inr` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:151` |
| `PaperC.MixedLengthAffine.mixedLengthSystem_apply_embedding` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:292` |
| `PaperC.MixedLengthAffine.mixedLengthSystem_apply_inl` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:131` |
| `PaperC.MixedLengthAffine.mixedLengthSystem_apply_inr` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:138` |
| `PaperC.MixedLengthAffine.mixedLengthSystem_eq_rhs_iff` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:157` |
| `PaperC.MixedLengthAffine.mixedRelationEmbedding_injective` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:383` |
| `PaperC.MixedLengthAffine.mixed_relationRho_le_common` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:396` |
| `PaperC.MixedLengthAffine.startSystem_eq_exactLengthRhs_iff` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:75` |
| `PaperC.MixedLengthAffine.zeroExtendMixedCoefficients_apply_embedding` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:273` |
| `PaperC.MixedLengthAffine.zeroExtendMixedCoefficients_injective` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:283` |
| `PaperC.MixedLengthAffine.zeroExtendMixedCoefficients_mem_relationSpace` | inconditionnel | — | — | — | `PaperC/Probability/MixedLengthAffine.lean:351` |
| `PaperC.MultipleDefects.coefficient_dvd_offset_difference` | inconditionnel | — | — | — | `PaperC/Diophantine/MultipleDefects.lean:198` |
| `PaperC.MultipleDefects.equal_coefficient_factorization` | inconditionnel | — | — | — | `PaperC/Diophantine/MultipleDefects.lean:211` |
| `PaperC.MultipleDefects.twoDefectPolynomialBox_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Diophantine/MultipleDefects.lean:186` |
| `PaperC.MultipleDefects.twoDefectPolynomialBox_of_pell` | inconditionnel | — | — | — | `PaperC/Diophantine/MultipleDefects.lean:164` |
| `PaperC.MultipleDefects.twoDefectWitnessBox_atMost` | inconditionnel | — | — | — | `PaperC/Diophantine/MultipleDefects.lean:110` |
| `PaperC.MultipleDefects.twoDefectWitness_maps_to_pell` | inconditionnel | — | — | — | `PaperC/Diophantine/MultipleDefects.lean:57` |
| `PaperC.MultipleDefects.witnessToPell_injective_on` | inconditionnel | — | — | — | `PaperC/Diophantine/MultipleDefects.lean:83` |
| `PaperC.NonalignedCoreRank.finrank_componentKernel_eq_card_sub_kTilde` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/NonalignedCoreRank.lean:48` |
| `PaperC.NonalignedCoreRank.largePrimeKTilde_eq_kTilde` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/NonalignedCoreRank.lean:94` |
| `PaperC.NonalignedCoreRank.largePrime_exact_rank` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/NonalignedCoreRank.lean:113` |
| `PaperC.NonalignedCoreRank.lemma_nine_ten_exact_rank` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/NonalignedCoreRank.lean:146` |
| `PaperC.NonterminalSectorSaving.quadraticDivLogLogSquaredScale_uniformLittleO_quadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/NonterminalSectorSaving.lean:72` |
| `PaperC.NonterminalSectorSaving.quantitativeHomogeneousScale_uniformLittleO_quadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/NonterminalSectorSaving.lean:137` |
| `PaperC.NonterminalSectorSaving.uniformBigOOn_trans_uniformLittleOOn` | inconditionnel | — | — | — | `PaperC/Asymptotics/NonterminalSectorSaving.lean:31` |
| `PaperC.NonterminalSectorSaving.uniformBigO_quantitativeHomogeneousScale_implies_littleO_quadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/NonterminalSectorSaving.lean:152` |
| `PaperC.OneUnitResidualExceptions.canonicalCertificate_mem_oneUnitExceptionalComponents_of_onChannel` | inconditionnel | — | — | — | `PaperC/Combinatorics/OneUnitResidualExceptions.lean:126` |
| `PaperC.OneUnitResidualExceptions.card_oneUnitExceptionalComponents_le_two` | inconditionnel | — | — | — | `PaperC/Combinatorics/OneUnitResidualExceptions.lean:108` |
| `PaperC.OneUnitResidualExceptions.channelCell_eq_uniqueChannelUnit` | inconditionnel | — | — | — | `PaperC/Combinatorics/OneUnitResidualExceptions.lean:68` |
| `PaperC.OneUnitResidualExceptions.channelUnit_eq_uniqueChannelUnit` | inconditionnel | — | — | — | `PaperC/Combinatorics/OneUnitResidualExceptions.lean:57` |
| `PaperC.OneUnitResidualExceptions.mem_oneUnitExceptionalComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/OneUnitResidualExceptions.lean:93` |
| `PaperC.PellInput.act_injective` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:199` |
| `PaperC.PellInput.act_inv` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:179` |
| `PaperC.PellInput.act_preserves_equation` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:163` |
| `PaperC.PellInput.card_pellUnits_y_natAbs_le` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:428` |
| `PaperC.PellInput.card_samePrincipalIdeal_solutionFiber` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:565` |
| `PaperC.PellInput.constant_mul_log_le_exp_log_div_loglog` | inconditionnel | — | — | — | `PaperC/Diophantine/PellDivisorEnvelope.lean:346` |
| `PaperC.PellInput.div_log_mono_on_exp_one` | inconditionnel | — | — | — | `PaperC/Diophantine/PellDivisorEnvelope.lean:99` |
| `PaperC.PellInput.divisor_log_ratio_le_polynomial_ratio` | inconditionnel | — | — | — | `PaperC/Diophantine/PellDivisorEnvelope.lean:145` |
| `PaperC.PellInput.exists_squarefree_reduction` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:779` |
| `PaperC.PellInput.exp_one_le_log_nat_of_sixtyFour_le` | inconditionnel | — | — | — | `PaperC/Diophantine/PellDivisorEnvelope.lean:119` |
| `PaperC.PellInput.generalizedPellEquation_iff_norm` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:46` |
| `PaperC.PellInput.generalizedPellPolynomialBox_of_divisorLogBound` | conditionnel | `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Diophantine/PellDivisorEnvelope.lean:597` |
| `PaperC.PellInput.generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound` | conditionnel | `HK13-QO-conductor-fibres`, `NR83-T1-divisor-log-bound` | `external` | `discharged`, `open` | `PaperC/Diophantine/PellDivisorEnvelope.lean:585` |
| `PaperC.PellInput.generalizedPellPolynomialBox_of_quadraticOrder_nicolasRobin` | conditionnel | `HK13-QO-conductor-fibres`, `NR83-T1-divisor-bound` | `external` | `discharged` | `PaperC/Diophantine/GeneralizedPell.lean:843` |
| `PaperC.PellInput.generalizedPellRealPolynomialBox_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Diophantine/PellRealExponent.lean:123` |
| `PaperC.PellInput.hasAtMostSolutionsReal_of_squarefree_reduction` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:802` |
| `PaperC.PellInput.loglog_le_four_log_div_loglog` | inconditionnel | — | — | — | `PaperC/Diophantine/PellDivisorEnvelope.lean:306` |
| `PaperC.PellInput.natAbs_exponent_le_log_add_one` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:399` |
| `PaperC.PellInput.nicolasRobinConstant_nonneg` | inconditionnel | — | — | — | `PaperC/Diophantine/PellDivisorEnvelope.lean:88` |
| `PaperC.PellInput.nicolasRobinPellEnvelope_of_divisorLogBound` | conditionnel | `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Diophantine/PellDivisorEnvelope.lean:409` |
| `PaperC.PellInput.norm_toZsqrtd` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:40` |
| `PaperC.PellInput.pellPolynomialBox_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Diophantine/PellInput.lean:256` |
| `PaperC.PellInput.pellRealPolynomialBox_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Diophantine/PellRealExponent.lean:160` |
| `PaperC.PellInput.pellSourceExactRealPolynomialBox_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Diophantine/PellRealExponent.lean:206` |
| `PaperC.PellInput.pellUnitOrbitEnvelope_le_log` | inconditionnel | — | — | — | `PaperC/Diophantine/PellDivisorEnvelope.lean:202` |
| `PaperC.PellInput.pellUnit_y_natAbs_le` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:268` |
| `PaperC.PellInput.principalIdeal_dvd_intCast` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:211` |
| `PaperC.PellInput.quadraticOrderConductorFiberBound` | inconditionnel | — | — | — | `PaperC/Diophantine/HalterKochConductorDescent.lean:646` |
| `PaperC.PellInput.quadraticOrderConductorFiberBound_of_halterKochConductorDescent` | inconditionnel | — | — | — | `PaperC/Diophantine/HalterKochConductorDescent.lean:189` |
| `PaperC.PellInput.same_principalIdeal_gives_pell_unit` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:230` |
| `PaperC.PellInput.scaleImag_height` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:764` |
| `PaperC.PellInput.scaleImag_injective` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:754` |
| `PaperC.PellInput.scaleImag_preserves_equation` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:741` |
| `PaperC.PellInput.squarefreeGeneralizedPellBox_atMost_of_conductorComparison` | conditionnel | `HK13-QO-conductor-fibres` | `external` | `discharged` | `PaperC/Diophantine/GeneralizedPell.lean:639` |
| `PaperC.PellInput.toZsqrtd_act` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:147` |
| `PaperC.PellInput.toZsqrtd_im` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:35` |
| `PaperC.PellInput.toZsqrtd_re` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:30` |
| `PaperC.PellInput.two_pow_le_y_natAbs_pow_succ` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:362` |
| `PaperC.PellInput.two_pow_le_y_pow_succ` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:320` |
| `PaperC.PellInput.two_pow_pred_natAbs_le_y_natAbs_zpow` | inconditionnel | — | — | — | `PaperC/Diophantine/GeneralizedPell.lean:378` |
| `PaperC.PinnedGraphResolution.card_isolated_add_twice_card_nontrivial_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:441` |
| `PaperC.PinnedGraphResolution.card_unpinnedComponent_eq_isolated_add_nontrivial` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:425` |
| `PaperC.PinnedGraphResolution.card_unpinnedComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:362` |
| `PaperC.PinnedGraphResolution.componentExtension_eq_of_adj` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:175` |
| `PaperC.PinnedGraphResolution.componentExtension_eq_zero_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:199` |
| `PaperC.PinnedGraphResolution.componentRestriction_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:134` |
| `PaperC.PinnedGraphResolution.componentRestriction_surjective` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:209` |
| `PaperC.PinnedGraphResolution.disjoint_isolated_nontrivial` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:408` |
| `PaperC.PinnedGraphResolution.eq_of_connectedComponentMk_eq` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:82` |
| `PaperC.PinnedGraphResolution.eq_of_reachable` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:74` |
| `PaperC.PinnedGraphResolution.eq_of_walk` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:63` |
| `PaperC.PinnedGraphResolution.eq_zero_of_componentPinned` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:107` |
| `PaperC.PinnedGraphResolution.finrank_pinnedGraphSpace` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:246` |
| `PaperC.PinnedGraphResolution.isolated_union_nontrivial_eq_unpinned` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:380` |
| `PaperC.PinnedGraphResolution.mem_isolatedUnpinnedComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:313` |
| `PaperC.PinnedGraphResolution.mem_nontrivialUnpinnedComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:321` |
| `PaperC.PinnedGraphResolution.mem_pinnedGraphSpace` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:55` |
| `PaperC.PinnedGraphResolution.mem_unpinnedComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:340` |
| `PaperC.PinnedGraphResolution.sum_card_component_support` | inconditionnel | — | — | — | `PaperC/Combinatorics/PinnedGraphResolution.lean:283` |
| `PaperC.PoissonLaplaceFunctional.poissonLaplaceTransform_eq` | inconditionnel | — | — | — | `PaperC/Probability/PoissonLaplaceFunctional.lean:31` |
| `PaperC.PoissonLaplaceFunctional.prod_poissonLaplaceTransform_eq` | inconditionnel | — | — | — | `PaperC/Probability/PoissonLaplaceFunctional.lean:70` |
| `PaperC.PoissonLaplaceFunctional.sectionFourteenFour_laplaceFunctional` | inconditionnel | — | — | — | `PaperC/Probability/PoissonLaplaceFunctional.lean:157` |
| `PaperC.PoissonLaplaceFunctional.sectionFourteenTwo_laplaceFunctional` | inconditionnel | — | — | — | `PaperC/Probability/PoissonLaplaceFunctional.lean:126` |
| `PaperC.PoissonLaplaceFunctional.tendsto_laplace_of_parameter_and_error` | inconditionnel | — | — | — | `PaperC/Probability/PoissonLaplaceFunctional.lean:88` |
| `PaperC.PoissonVectorMass.hasSum_independentPoissonVectorLaplace` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVectorMass.lean:118` |
| `PaperC.PoissonVectorMass.hasSum_independentPoissonVectorMass` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVectorMass.lean:95` |
| `PaperC.PoissonVectorMass.hasSum_pi_prod` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVectorMass.lean:79` |
| `PaperC.PoissonVectorMass.hasSum_pi_prod_general` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVectorMass.lean:21` |
| `PaperC.PoissonVectorMass.independentPoissonVectorMass_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVectorMass.lean:89` |
| `PaperC.PoissonVectorMass.summable_independentPoissonVectorMass` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVectorMass.lean:106` |
| `PaperC.PoissonVoidApproximation.abs_indicatorSumLaw_zero_sub_matching_le` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVoidApproximation.lean:121` |
| `PaperC.PoissonVoidApproximation.abs_mass_zero_sub_le_two_mul_natTotalVariation` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVoidApproximation.lean:79` |
| `PaperC.PoissonVoidApproximation.abs_voidProbability_sub_exp_neg_parameter_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/PoissonVoidApproximation.lean:142` |
| `PaperC.PoissonVoidApproximation.indicatorSumLaw_eq_finiteNatLaw` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVoidApproximation.lean:30` |
| `PaperC.PoissonVoidApproximation.matchingPoissonLaw_zero` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVoidApproximation.lean:64` |
| `PaperC.PoissonVoidApproximation.summable_indicatorSumLaw` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVoidApproximation.lean:43` |
| `PaperC.PoissonVoidApproximation.summable_matchingPoissonLaw` | inconditionnel | — | — | — | `PaperC/Probability/PoissonVoidApproximation.lean:51` |
| `PaperC.PolynomialZoneCritical.card_complete_nondefective_le_one_add_start` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneCritical.lean:117` |
| `PaperC.PolynomialZoneCritical.card_startDefect_add_card_startNondefect` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneCritical.lean:96` |
| `PaperC.PolynomialZoneCritical.card_startDefect_le_of_complete_nondefective` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneCritical.lean:174` |
| `PaperC.PolynomialZoneCritical.card_startNondefectNatIndicesAt_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneCritical.lean:75` |
| `PaperC.PolynomialZoneCritical.exists_c3_polynomialVertexRank` | conditionnel | `ADGR07-PNT` | `external` | `open` | `PaperC/Asymptotics/PolynomialZoneCritical.lean:496` |
| `PaperC.PolynomialZoneCritical.laishramShorey_completeWindow_lower_bound` | conditionnel | `LS04-Corollary-1` | `external` | `open` | `PaperC/Asymptotics/PolynomialZoneCritical.lean:197` |
| `PaperC.PolynomialZoneCritical.laishramShorey_startProbability_bound` | conditionnel | `LS04-Corollary-1` | `external` | `open` | `PaperC/Asymptotics/PolynomialZoneCritical.lean:543` |
| `PaperC.PolynomialZoneCritical.mem_startNondefectIndicesAt` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneCritical.lean:61` |
| `PaperC.PolynomialZoneCritical.mem_startNondefectNatIndicesAt` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneCritical.lean:68` |
| `PaperC.PolynomialZoneCritical.primeNumberTheorem_implies_polynomialVertexRank_lower` | conditionnel | `ADGR07-PNT` | `external` | `open` | `PaperC/Asymptotics/PolynomialZoneCritical.lean:249` |
| `PaperC.PolynomialZoneCritical.startProbability_le_of_complete_nondefective` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneCritical.lean:514` |
| `PaperC.PolynomialZoneLargePrimes.card_simpleLargePrimeFactors_le_two_mul_nondefective` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:538` |
| `PaperC.PolynomialZoneLargePrimes.card_simpleLargePrimesAt_le_two` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:311` |
| `PaperC.PolynomialZoneLargePrimes.card_squarefulLargePrimeFactors_le_three` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:493` |
| `PaperC.PolynomialZoneLargePrimes.card_squareful_add_card_simple` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:522` |
| `PaperC.PolynomialZoneLargePrimes.existsUnique_index_dvd_of_mem_largePrimeFactors` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:219` |
| `PaperC.PolynomialZoneLargePrimes.factorization_eq_one_of_mem_simpleLargePrimeFactors_of_dvd` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:244` |
| `PaperC.PolynomialZoneLargePrimes.laishramShorey_largePrimeFactors` | conditionnel | `LS04-Corollary-1` | `external` | `open` | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:178` |
| `PaperC.PolynomialZoneLargePrimes.laishramShorey_nondefectiveWindow_lower_bound` | conditionnel | `LS04-Corollary-1` | `external` | `open` | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:587` |
| `PaperC.PolynomialZoneLargePrimes.largePrimeFactors_sub_three_div_two_le_nondefective` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:565` |
| `PaperC.PolynomialZoneLargePrimes.mem_largePrimeFactors` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:79` |
| `PaperC.PolynomialZoneLargePrimes.mem_nondefectiveWindowIndices` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:99` |
| `PaperC.PolynomialZoneLargePrimes.mem_simpleLargePrimeFactors` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:92` |
| `PaperC.PolynomialZoneLargePrimes.mem_simpleLargePrimesAt` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:105` |
| `PaperC.PolynomialZoneLargePrimes.mem_squarefulLargePrimeFactors` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:85` |
| `PaperC.PolynomialZoneLargePrimes.not_hDefective_of_mem_simpleLargePrimeFactors_of_dvd` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:270` |
| `PaperC.PolynomialZoneLargePrimes.primeFactors_card_sub_primeCount_le_largePrimeFactors_card` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:138` |
| `PaperC.PolynomialZoneLargePrimes.prime_and_large_of_mem_largePrimeFactors` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:126` |
| `PaperC.PolynomialZoneLargePrimes.simpleLargePrimeFactors_subset_nondefective_biUnion` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:289` |
| `PaperC.PolynomialZoneLargePrimes.squarefulIndex_spec` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:110` |
| `PaperC.PolynomialZoneLargePrimes.squarefulQuotient_injOn` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:408` |
| `PaperC.PolynomialZoneLargePrimes.squarefulQuotient_le_three` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:383` |
| `PaperC.PolynomialZoneLargePrimes.squarefulQuotient_pos` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:366` |
| `PaperC.PolynomialZoneLargePrimes.squareful_value_eq` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:117` |
| `PaperC.PolynomialZoneLargePrimes.unique_index_of_large_prime_dvd` | inconditionnel | — | — | — | `PaperC/Arithmetic/PolynomialZoneLargePrimes.lean:199` |
| `PaperC.PolynomialZoneSum.card_polynomialZoneStarts_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneSum.lean:47` |
| `PaperC.PolynomialZoneSum.mem_polynomialZoneStarts` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneSum.lean:34` |
| `PaperC.PolynomialZoneSum.polynomialZonePowerEnvelope_tendsto_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneSum.lean:299` |
| `PaperC.PolynomialZoneSum.polynomialZoneProbabilityMassQ_le_rankEnvelope` | conditionnel | `LS04-Corollary-1` | `external` | `open` | `PaperC/Asymptotics/PolynomialZoneSum.lean:133` |
| `PaperC.PolynomialZoneSum.polynomialZoneProbabilityMassQ_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneSum.lean:52` |
| `PaperC.PolynomialZoneSum.polynomialZoneProbabilityMass_le_rankEnvelope` | conditionnel | `LS04-Corollary-1` | `external` | `open` | `PaperC/Asymptotics/PolynomialZoneSum.lean:161` |
| `PaperC.PolynomialZoneSum.polynomialZoneProbabilityMass_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/PolynomialZoneSum.lean:58` |
| `PaperC.PolynomialZoneSum.polynomialZoneProbabilityMass_tendsto_zero` | conditionnel | `ADGR07-PNT`, `LS04-Corollary-1` | `external` | `open` | `PaperC/Asymptotics/PolynomialZoneSum.lean:386` |
| `PaperC.PolynomialZoneSum.primeNumberTheorem_implies_polynomialZoneLogRank` | conditionnel | `ADGR07-PNT` | `external` | `open` | `PaperC/Asymptotics/PolynomialZoneSum.lean:182` |
| `PaperC.PolynomialZoneSum.startProbability_le_two_div_pow_of_rank` | conditionnel | `LS04-Corollary-1` | `external` | `open` | `PaperC/Asymptotics/PolynomialZoneSum.lean:68` |
| `PaperC.PositiveSigmaFixedChannelCover.card_fixedChannelFirstCoordinates` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelCover.lean:171` |
| `PaperC.PositiveSigmaFixedChannelCover.exists_fixedChannelPairs_of_mem_positiveSigmaSmallProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelCover.lean:122` |
| `PaperC.PositiveSigmaFixedChannelCover.four_pow_mul_card_fixedChannelPairs_le_effective` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelBound.lean:29` |
| `PaperC.PositiveSigmaFixedChannelCover.four_pow_mul_card_fixedChannelPairs_le_lemmaSevenOne` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelCover.lean:352` |
| `PaperC.PositiveSigmaFixedChannelCover.four_pow_mul_card_fixedChannelPairs_le_solutionMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelCover.lean:321` |
| `PaperC.PositiveSigmaFixedChannelCover.fst_injOn_fixedChannelPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelCover.lean:156` |
| `PaperC.PositiveSigmaFixedChannelCover.mem_fixedChannelPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelCover.lean:73` |
| `PaperC.PositiveSigmaFixedChannelCover.pairOfFirstCoordinate_fst` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelCover.lean:205` |
| `PaperC.PositiveSigmaFixedChannelCover.pairOfFirstCoordinate_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelCover.lean:196` |
| `PaperC.PositiveSigmaFixedChannelCover.pairSigma_eq_channelSigma_of_mem_fixedChannelPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelCover.lean:104` |
| `PaperC.PositiveSigmaFixedChannelCover.pair_mem_channelStartPairs_of_mem_fixedChannelPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelCover.lean:89` |
| `PaperC.PositiveSigmaFixedChannelCover.sum_four_pow_mul_card_fixedChannelPairs_cast_le_exp` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelBound.lean:72` |
| `PaperC.PositiveSigmaFixedChannelCover.sum_four_pow_mul_card_fixedChannelPairs_le_effective` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaFixedChannelBound.lean:50` |
| `PaperC.PositiveSigmaGlobalGrouping.existsUnique_key_of_mem_positiveSigmaSmallProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaGlobalGrouping.lean:193` |
| `PaperC.PositiveSigmaGlobalGrouping.key_eq_of_pair_mem_fixedChannelFiber` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaGlobalGrouping.lean:82` |
| `PaperC.PositiveSigmaGlobalGrouping.mem_positiveChannelKeys` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaGlobalGrouping.lean:54` |
| `PaperC.PositiveSigmaGlobalGrouping.positiveSigmaQuadraticResidualMass_le_channelCertificateMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaGlobalGrouping.lean:263` |
| `PaperC.PositiveSigmaKeyMassBound.positiveSigmaChannelCertificateMass_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaKeyMassBound.lean:186` |
| `PaperC.PositiveSigmaKeyMassBound.sum_four_pow_channelSigma_positiveChannelKeys` | inconditionnel | — | — | — | `PaperC/Combinatorics/PositiveSigmaKeyMassBound.lean:117` |
| `PaperC.PositiveSigmaQuadraticCritical.positiveSigmaChannelCertificateMass_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PositiveSigmaQuadraticCritical.lean:45` |
| `PaperC.PositiveSigmaQuadraticCritical.positiveSigmaQuadraticResidualMass_cast_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/PositiveSigmaQuadraticCritical.lean:57` |
| `PaperC.PositiveSigmaQuadraticCritical.positiveSigmaQuadraticResidualMass_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/PositiveSigmaQuadraticCritical.lean:184` |
| `PaperC.PositiveSigmaQuadraticCritical.runLengthAddTwo_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/PositiveSigmaQuadraticCritical.lean:137` |
| `PaperC.PositiveSigmaQuadraticCritical.uniformQuadratic_mul_subpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/PositiveSigmaQuadraticCritical.lean:94` |
| `PaperC.PrefixBoundaryProbability.card_primeUpTo_eq_primeCounting` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:58` |
| `PaperC.PrefixBoundaryProbability.finitePrefixBoundaryEvent_eq_singleton_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:122` |
| `PaperC.PrefixBoundaryProbability.infinitePrefixBoundaryEvent_eq_preimage` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:148` |
| `PaperC.PrefixBoundaryProbability.infinitePrefixBoundaryProbability_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:192` |
| `PaperC.PrefixBoundaryProbability.infinitePrefixBoundaryProbability_tendsto_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:200` |
| `PaperC.PrefixBoundaryProbability.infinitePrefixBoundaryProbability_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:216` |
| `PaperC.PrefixBoundaryProbability.measurableSet_finitePrefixBoundaryEvent` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:154` |
| `PaperC.PrefixBoundaryProbability.measurableSet_infinitePrefixBoundaryEvent` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:158` |
| `PaperC.PrefixBoundaryProbability.measure_infinitePrefixBoundaryEvent` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:168` |
| `PaperC.PrefixBoundaryProbability.measure_prefixBoundaryEvent_infiniteValueBit` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:180` |
| `PaperC.PrefixBoundaryProbability.prefixBoundaryEvent_restrictToFinite_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:128` |
| `PaperC.PrefixBoundaryProbability.prefixBoundaryEvent_valueBit_iff_eq_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:96` |
| `PaperC.PrefixBoundaryProbability.valueBit_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:88` |
| `PaperC.PrefixBoundaryProbability.valueBit_primeUpTo` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixBoundaryProbability.lean:69` |
| `PaperC.PrefixOverflowCoupling.boundary_or_overflow_start_of_finitePrefix_ne_global` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:90` |
| `PaperC.PrefixOverflowCoupling.commonCylinderStartProbability_eq_shiftedStartProbability` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:235` |
| `PaperC.PrefixOverflowCoupling.const_div_sqrt_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:433` |
| `PaperC.PrefixOverflowCoupling.disagreementProbability_finitePrefix_global_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:104` |
| `PaperC.PrefixOverflowCoupling.finitePrefixBoundaryProbability_eq_infinitePrefixBoundaryProbability` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:599` |
| `PaperC.PrefixOverflowCoupling.finitePrefixBoundaryProbability_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:608` |
| `PaperC.PrefixOverflowCoupling.finitePrefixStartCount_eq_globalStartCount_of_no_exceptions` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:68` |
| `PaperC.PrefixOverflowCoupling.natTotalVariation_finitePrefix_global_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:204` |
| `PaperC.PrefixOverflowCoupling.natTotalVariation_finitePrefix_global_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:655` |
| `PaperC.PrefixOverflowCoupling.natTotalVariation_prefixStartLaw_global_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:695` |
| `PaperC.PrefixOverflowCoupling.prefixGlobalCouplingCost_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:629` |
| `PaperC.PrefixOverflowCoupling.prefixGlobalCouplingCost_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:639` |
| `PaperC.PrefixOverflowCoupling.prefixInteriorStartIndices_subset_globalStartIndices` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:59` |
| `PaperC.PrefixOverflowCoupling.prefixOverflowBaseline_le_invSqrt` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:367` |
| `PaperC.PrefixOverflowCoupling.prefixOverflowBaseline_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:360` |
| `PaperC.PrefixOverflowCoupling.prefixOverflowBaseline_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:459` |
| `PaperC.PrefixOverflowCoupling.prefixOverflowStartIndices_card_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:354` |
| `PaperC.PrefixOverflowCoupling.prefixOverflowStartIndices_subset_dyadicBlock` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:223` |
| `PaperC.PrefixOverflowCoupling.prefixOverflowStartProbabilityMass_eq_maskedDyadicExpectation` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:261` |
| `PaperC.PrefixOverflowCoupling.prefixOverflowStartProbabilityMass_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:54` |
| `PaperC.PrefixOverflowCoupling.prefixOverflowStartProbabilityMass_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:508` |
| `PaperC.PrefixOverflowCoupling.shiftedPrefixBase_inRunLengthWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/PrefixOverflowCoupling.lean:279` |
| `PaperC.PrimeCountBridge.count_eq_card_smallPrimesUpTo` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimeCountBridge.lean:35` |
| `PaperC.PrimeEncodedCountLaplace.continuousOn_primeLogTest` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:173` |
| `PaperC.PrimeEncodedCountLaplace.finiteEncodedExactLengthCountLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:59` |
| `PaperC.PrimeEncodedCountLaplace.finiteEncodedExactLengthCountLaw_primeCode` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:86` |
| `PaperC.PrimeEncodedCountLaplace.finiteEncodedExactLengthCountLaw_zero` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:71` |
| `PaperC.PrimeEncodedCountLaplace.finiteMarkedLaplaceFunctional_primeLogTest` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:273` |
| `PaperC.PrimeEncodedCountLaplace.hasSum_finiteEncodedExactLengthCountLaw` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:64` |
| `PaperC.PrimeEncodedCountLaplace.infiniteMarkedLaplaceExpectation_eq_uniformPMFExpectation` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:315` |
| `PaperC.PrimeEncodedCountLaplace.inversePowerTransform_finiteEncodedExactLengthCountLaw_eq` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:333` |
| `PaperC.PrimeEncodedCountLaplace.inversePowerTransform_finiteNatLaw_eq_expectation` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:117` |
| `PaperC.PrimeEncodedCountLaplace.inversePrimeCodeWeight_eq_prod` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:192` |
| `PaperC.PrimeEncodedCountLaplace.log_primeCode` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:153` |
| `PaperC.PrimeEncodedCountLaplace.markedPrimeLogExponent_eq` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:233` |
| `PaperC.PrimeEncodedCountLaplace.primeLogTest_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountLaplace.lean:178` |
| `PaperC.PrimeEncodedCountVector.factorization_primeCode` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountVector.lean:45` |
| `PaperC.PrimeEncodedCountVector.hasSum_injectivePushforwardMass` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountVector.lean:120` |
| `PaperC.PrimeEncodedCountVector.injectivePushforwardMass_apply` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountVector.lean:91` |
| `PaperC.PrimeEncodedCountVector.injectivePushforwardMass_eq_zero_of_not_mem_range` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountVector.lean:102` |
| `PaperC.PrimeEncodedCountVector.injectivePushforwardMass_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountVector.lean:109` |
| `PaperC.PrimeEncodedCountVector.nthPrime_injective` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountVector.lean:35` |
| `PaperC.PrimeEncodedCountVector.primeCode_injective` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountVector.lean:72` |
| `PaperC.PrimeEncodedCountVector.primeCode_pos` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountVector.lean:28` |
| `PaperC.PrimeEncodedCountVector.summable_injectivePushforwardMass` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountVector.lean:136` |
| `PaperC.PrimeEncodedCountVector.tsum_injectivePushforwardMass_mul` | inconditionnel | — | — | — | `PaperC/Probability/PrimeEncodedCountVector.lean:143` |
| `PaperC.PrimeFactorsFactorialBound.affinePow_polynomialHeightOmega_pow_le_eventually` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimeFactorsFactorialBound.lean:240` |
| `PaperC.PrimeFactorsFactorialBound.affinePow_primeFactorsCard_pow_le_of_polynomialHeight` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimeFactorsFactorialBound.lean:109` |
| `PaperC.PrimeFactorsFactorialBound.exists_primeFactors_card_eq_polynomialHeightOmega` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimeFactorsFactorialBound.lean:197` |
| `PaperC.PrimeFactorsFactorialBound.factorial_card_le_prod` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimeFactorsFactorialBound.lean:53` |
| `PaperC.PrimeFactorsFactorialBound.polynomialHeightOmega_mono_of_pow_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimeFactorsFactorialBound.lean:225` |
| `PaperC.PrimeFactorsFactorialBound.primeFactors_card_factorial_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimeFactorsFactorialBound.lean:89` |
| `PaperC.PrimeFactorsFactorialBound.primeFactors_card_le_polynomialHeightOmega` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimeFactorsFactorialBound.lean:180` |
| `PaperC.PrimeReciprocalSqrtSum.dyadicCover_eq_two_pow` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:289` |
| `PaperC.PrimeReciprocalSqrtSum.dyadicCover_le_two_mul` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:301` |
| `PaperC.PrimeReciprocalSqrtSum.four_le_rootCutoff` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:324` |
| `PaperC.PrimeReciprocalSqrtSum.le_dyadicCover` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:296` |
| `PaperC.PrimeReciprocalSqrtSum.log_mul_card_primesBetween_le` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:74` |
| `PaperC.PrimeReciprocalSqrtSum.log_rootCutoff` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:333` |
| `PaperC.PrimeReciprocalSqrtSum.mul_prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:528` |
| `PaperC.PrimeReciprocalSqrtSum.prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:463` |
| `PaperC.PrimeReciprocalSqrtSum.prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive_two_mul` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:488` |
| `PaperC.PrimeReciprocalSqrtSum.prod_smallPrimesUpTo_one_add_rpow_neg_one_half_le_primeSensitive` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:511` |
| `PaperC.PrimeReciprocalSqrtSum.rootCutoff_eq` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:285` |
| `PaperC.PrimeReciprocalSqrtSum.rootCutoff_sq_le` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:312` |
| `PaperC.PrimeReciprocalSqrtSum.sum_inv_sqrt_dyadicPrimes_le` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:227` |
| `PaperC.PrimeReciprocalSqrtSum.sum_inv_sqrt_primesBetween_le` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:96` |
| `PaperC.PrimeReciprocalSqrtSum.sum_smallPrimesUpTo_inv_sqrt_le` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:411` |
| `PaperC.PrimeReciprocalSqrtSum.sum_smallPrimesUpTo_inv_sqrt_le_two_mul` | inconditionnel | — | — | — | `PaperC/Analysis/PrimeReciprocalSqrtSum.lean:426` |
| `PaperC.PrimesUpTo.covers_primeDivisors` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimesUpTo.lean:92` |
| `PaperC.PrimesUpTo.exists_smallPrime_eq_of_prime_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimesUpTo.lean:64` |
| `PaperC.PrimesUpTo.mem_range_smallPrime_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimesUpTo.lean:77` |
| `PaperC.PrimesUpTo.smallPrime_injective` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimesUpTo.lean:54` |
| `PaperC.PrimesUpTo.smallPrime_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimesUpTo.lean:49` |
| `PaperC.PrimesUpTo.smallPrime_prime` | inconditionnel | — | — | — | `PaperC/Arithmetic/PrimesUpTo.lean:44` |
| `PaperC.PrivatePivots.edgeSum_apply_private` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/PrivatePivots.lean:91` |
| `PaperC.PrivatePivots.edgeSum_pair` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/PrivatePivots.lean:79` |
| `PaperC.PrivatePivots.finsupp_linearIndependent_of_private_pivots` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/PrivatePivots.lean:62` |
| `PaperC.PrivatePivots.linearIndependent_of_private_pivots` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/PrivatePivots.lean:34` |
| `PaperC.PrivatePivots.not_dvd_of_dvd_and_dist_lt` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/PrivatePivots.lean:237` |
| `PaperC.PrivatePivots.parityVecAbove_apply` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/PrivatePivots.lean:309` |
| `PaperC.PrivatePivots.tree_edgeSum_linearIndependent_of_private_nonroot` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/PrivatePivots.lean:132` |
| `PaperC.PrivatePivots.tree_parityEdge_linearIndependent_of_large_odd_primes` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/PrivatePivots.lean:261` |
| `PaperC.PrivatePivots.tree_projectedParityEdge_linearIndependent_of_large_odd_primes` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/PrivatePivots.lean:317` |
| `PaperC.PropositionElevenThree.alignedDeepCoreSector_uniformBigO_quantitative` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenThree.lean:376` |
| `PaperC.PropositionElevenThree.rationalPower_uniformBigO_quantitativeHomogeneousScale` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenThree.lean:48` |
| `PaperC.PropositionElevenThree.shallowCoreSector_uniformBigO_quantitative` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenThree.lean:349` |
| `PaperC.PropositionElevenThree.smallCanonicalHeightSector_uniformBigO_quantitative` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenThree.lean:320` |
| `PaperC.PropositionElevenThree.smallPrimeProductSector_uniformBigO_quantitative` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenThree.lean:292` |
| `PaperC.PropositionElevenThree.systematicMass_uniformBigO_quantitative` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenThree.lean:265` |
| `PaperC.PropositionElevenThree.uniformBigOOn_add` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenThree.lean:200` |
| `PaperC.PropositionElevenThree.uniformBigOOn_finset_sum` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenThree.lean:221` |
| `PaperC.PropositionElevenThree.uniformBigOOn_fintype_sum` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenThree.lean:248` |
| `PaperC.PropositionElevenTwo.alignedDeepCoreSector_eventually_empty` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:510` |
| `PaperC.PropositionElevenTwo.alignedDeepCoreSector_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:753` |
| `PaperC.PropositionElevenTwo.homogeneousMassNat_eq_systematic_add_residual` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:117` |
| `PaperC.PropositionElevenTwo.homogeneousMass_eq_systematic_add_residual` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:171` |
| `PaperC.PropositionElevenTwo.homogeneousWeight_eq_systematic_add_residual` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:88` |
| `PaperC.PropositionElevenTwo.linearResidualMass_union_canonicalSectors` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:262` |
| `PaperC.PropositionElevenTwo.manyDefectsSectorResidualMassNat_le_propositionNineNine` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:467` |
| `PaperC.PropositionElevenTwo.manyDefectsSector_subset_propositionNineNine` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:429` |
| `PaperC.PropositionElevenTwo.residualMassNat_eq_sum_sectors` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:224` |
| `PaperC.PropositionElevenTwo.residualMass_eq_sum_sectorResidualMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:302` |
| `PaperC.PropositionElevenTwo.sectorResidualMass_manyDefects_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:483` |
| `PaperC.PropositionElevenTwo.sectorResidualMass_shallowCore_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:389` |
| `PaperC.PropositionElevenTwo.sectorResidualMass_smallCanonicalHeight_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:354` |
| `PaperC.PropositionElevenTwo.sectorResidualMass_smallPrimeProduct_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:320` |
| `PaperC.PropositionElevenTwo.shallowCoreSector_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:730` |
| `PaperC.PropositionElevenTwo.smallCanonicalHeightSector_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:707` |
| `PaperC.PropositionElevenTwo.smallPrimeProductSector_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:680` |
| `PaperC.PropositionElevenTwo.systematicMassNat_eq_rationalMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:133` |
| `PaperC.PropositionElevenTwo.systematicMass_eq_rationalMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:184` |
| `PaperC.PropositionElevenTwo.systematicMass_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:655` |
| `PaperC.PropositionElevenTwo.terminalSectorResidualMassNat_le_card_mul_weight` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:818` |
| `PaperC.PropositionElevenTwo.terminalSectorResidualMassNat_le_terminalResidualMassAtBudget` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:798` |
| `PaperC.PropositionElevenTwo.terminalSector_subset_terminalPairsAtBudget` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:784` |
| `PaperC.PropositionElevenTwo.two_pow_add_sub_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:58` |
| `PaperC.PropositionElevenTwo.uniformLittleOOn_add` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:587` |
| `PaperC.PropositionElevenTwo.uniformLittleOOn_finset_sum` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:612` |
| `PaperC.PropositionElevenTwo.uniformLittleOOn_fintype_sum` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionElevenTwo.lean:638` |
| `PaperC.PropositionFifteenFive.balasubramanianShorey_highBlockProbabilityMass_le` | conditionnel | `BS93-Theorem-1` | `external` | `open` | `PaperC/Asymptotics/PropositionFifteenFive.lean:295` |
| `PaperC.PropositionFifteenFive.card_startDefectIndicesAt_le_defectiveOffsets` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFive.lean:48` |
| `PaperC.PropositionFifteenFive.globalStartProbability_le_baseline_of_card_le_one` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFive.lean:107` |
| `PaperC.PropositionFifteenFive.globalStartProbability_le_defectiveWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFive.lean:83` |
| `PaperC.PropositionFifteenFive.globalStartProbability_le_of_real_defect_bound` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFive.lean:122` |
| `PaperC.PropositionFifteenFive.globalStartProbability_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFive.lean:156` |
| `PaperC.PropositionFifteenFive.highBlockProbabilityMass_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFive.lean:171` |
| `PaperC.PropositionFifteenFive.highBlockProbabilityMass_le_of_exceptional_card_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFive.lean:273` |
| `PaperC.PropositionFifteenFive.highBlockProbabilityMass_le_uniform_height_range` | conditionnel | `ADGR07-PNT`, `BS93-Theorem-1`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/PropositionFifteenFive.lean:329` |
| `PaperC.PropositionFifteenFive.mem_twoDefectWindowStarts_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFive.lean:147` |
| `PaperC.PropositionFifteenFiveClosure.deepStartProbabilityMass_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:41` |
| `PaperC.PropositionFifteenFiveClosure.deepTruncationDoubleLimit_of_uniformLittleO_remainder` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:81` |
| `PaperC.PropositionFifteenFiveClosure.finite_dyadic_tail_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:489` |
| `PaperC.PropositionFifteenFiveClosure.finite_scaled_dyadic_tail_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:506` |
| `PaperC.PropositionFifteenFiveClosure.highZoneExceptionalEnvelope_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:176` |
| `PaperC.PropositionFifteenFiveClosure.lowHeightProbabilityMass_le_lowPolynomialRemainder` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:314` |
| `PaperC.PropositionFifteenFiveClosure.lowPolynomialRemainder_tendsto_zero` | conditionnel | `ADGR07-PNT`, `LS04-Corollary-1` | `external` | `open` | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:282` |
| `PaperC.PropositionFifteenFiveClosure.lowPolynomialRemainder_uniformLittleOOne` | conditionnel | `ADGR07-PNT`, `LS04-Corollary-1` | `external` | `open` | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:293` |
| `PaperC.PropositionFifteenFiveClosure.lowZoneLinearProbabilityMass_tendsto_zero` | conditionnel | `ADGR07-PNT` | `external` | `open` | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:242` |
| `PaperC.PropositionFifteenFiveClosure.proposition_fifteen_five_of_eventual_uniformLittleO_remainder` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:418` |
| `PaperC.PropositionFifteenFiveClosure.proposition_fifteen_five_of_uniformLittleO_remainder` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:393` |
| `PaperC.PropositionFifteenFiveClosure.two_mul_runLength_lowZonePowerAdmissible_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:197` |
| `PaperC.PropositionFifteenFiveClosure.uniformLittleOOn_runLength_of_tendsto_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveClosure.lean:149` |
| `PaperC.PropositionFifteenFiveDecay.gapFactor_tendsto_atTop` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveDecay.lean:34` |
| `PaperC.PropositionFifteenFiveDecay.gap_ge_pell_and_log_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveDecay.lean:93` |
| `PaperC.PropositionFifteenFiveDecay.highZoneExceptionalEnvelope_tendsto_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFiveDecay.lean:266` |
| `PaperC.PropositionFifteenFivePartition.completeRemainder_uniformLittleOOne` | conditionnel | `ADGR07-PNT`, `LS04-Corollary-1` | `external` | `open` | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:522` |
| `PaperC.PropositionFifteenFivePartition.deepStartProbabilityMass_le_low_add_baseline_add_exceptional` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:295` |
| `PaperC.PropositionFifteenFivePartition.deepStartProbabilityMass_le_low_add_blocks` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:206` |
| `PaperC.PropositionFifteenFivePartition.exceptionalBlockTerm_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:359` |
| `PaperC.PropositionFifteenFivePartition.four_cutoff_div_pow_le_criticalTail` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:380` |
| `PaperC.PropositionFifteenFivePartition.highDyadicBase_pos` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:43` |
| `PaperC.PropositionFifteenFivePartition.highDyadicBlock_eq_manuscriptBlock` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:48` |
| `PaperC.PropositionFifteenFivePartition.highDyadicBlocks_pairwiseDisjoint` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:59` |
| `PaperC.PropositionFifteenFivePartition.mem_activeDyadicBlock_of_mem_highRange` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:87` |
| `PaperC.PropositionFifteenFivePartition.proposition_fifteen_five` | conditionnel | `ADGR07-PNT`, `BS93-Theorem-1`, `LS04-Corollary-1`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:586` |
| `PaperC.PropositionFifteenFivePartition.sum_activeDyadicBases_le_cutoff` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:148` |
| `PaperC.PropositionFifteenFivePartition.twice_highZoneExceptionalEnvelope_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:484` |
| `PaperC.PropositionFifteenFivePartition.two_mul_runLength_blocks_cover_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionFifteenFivePartition.lean:419` |
| `PaperC.PropositionNineNine.activeHostPairValues_subset_relationalHosts` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:255` |
| `PaperC.PropositionNineNine.activeHost_defectInterval_and_boundedComponent` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:202` |
| `PaperC.PropositionNineNine.activeHosts_subset_left_union_right` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:350` |
| `PaperC.PropositionNineNine.activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs_subset` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:189` |
| `PaperC.PropositionNineNine.canonicalCoreExponent_le_height_add_half_defect` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:395` |
| `PaperC.PropositionNineNine.canonicalCoreExponent_le_height_add_half_maxDefect` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:414` |
| `PaperC.PropositionNineNine.card_activeHostPairValues` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:239` |
| `PaperC.PropositionNineNine.card_activeHosts_le_oriented_sum` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:370` |
| `PaperC.PropositionNineNine.card_activeHosts_le_relationalHosts` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:283` |
| `PaperC.PropositionNineNine.defect_add_component_le_height_add_half_defect` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:87` |
| `PaperC.PropositionNineNine.defect_add_component_le_height_add_half_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:97` |
| `PaperC.PropositionNineNine.defect_add_component_le_height_add_slack` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:110` |
| `PaperC.PropositionNineNine.halfPower_mul_linear` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:673` |
| `PaperC.PropositionNineNine.hostCount_le_orientedHostCoverCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:744` |
| `PaperC.PropositionNineNine.linearMass_le_hostCount_mul_residualWeightEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:764` |
| `PaperC.PropositionNineNine.linearResidualMass_le_card_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:467` |
| `PaperC.PropositionNineNine.linearResidualWeight_le_two_pow_height_add_half_maxDefect` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:444` |
| `PaperC.PropositionNineNine.mem_activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:176` |
| `PaperC.PropositionNineNine.mem_leftTwoDefectActiveHosts` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:320` |
| `PaperC.PropositionNineNine.mem_rightTwoDefectActiveHosts` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:333` |
| `PaperC.PropositionNineNine.mem_sigmaZeroDeepCoreAtLeastThreeDefectsPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:136` |
| `PaperC.PropositionNineNine.pairSigma_eq_zero_of_mem` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:147` |
| `PaperC.PropositionNineNine.residualWeightEnvelope_uniformLinear` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:584` |
| `PaperC.PropositionNineNine.sigmaZeroDeepCoreAtLeastThreeDefects_linearResidualMass_eq_active` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:486` |
| `PaperC.PropositionNineNine.sigmaZeroDeepCoreAtLeastThreeDefects_linearResidualMass_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:510` |
| `PaperC.PropositionNineNine.three_le_correctedDefectCount_of_mem` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:156` |
| `PaperC.PropositionNineNine.twice_defect_add_component_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:73` |
| `PaperC.PropositionNineNine.two_pow_half_maxDefect_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNine.lean:536` |
| `PaperC.PropositionNineNineHostGeometry.defectInterval_and_boundedComponent_of_deepCore` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNineHostGeometry.lean:286` |
| `PaperC.PropositionNineNineHostGeometry.defectInterval_and_boundedComponent_of_deepCore_rational_density` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNineHostGeometry.lean:252` |
| `PaperC.PropositionNineNineHostGeometry.defectInterval_and_boundedComponent_of_rational_density` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNineHostGeometry.lean:216` |
| `PaperC.PropositionNineNineHostGeometry.exists_canonicalResidualComponent_support_le_of_deepCore_rational_density` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNineHostGeometry.lean:171` |
| `PaperC.PropositionNineNineHostGeometry.exists_canonicalResidualComponent_support_le_of_rational_density` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNineHostGeometry.lean:119` |
| `PaperC.PropositionNineNineHostGeometry.exists_canonicalResidualComponent_support_le_ten_of_deepCore` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNineHostGeometry.lean:197` |
| `PaperC.PropositionNineNineHostGeometry.rational_density_of_three_sixteenths` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNineHostGeometry.lean:85` |
| `PaperC.PropositionNineNineHostGeometry.two_le_one_defectInterval_of_three_le_corrected` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionNineNineHostGeometry.lean:62` |
| `PaperC.PropositionSevenFiveCritical.shallowCoreLinearResidualMassTotal_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenFiveCritical.lean:156` |
| `PaperC.PropositionSevenFiveCritical.shallowCoreLinearResidualMass_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenFiveCritical.lean:211` |
| `PaperC.PropositionSevenFiveCritical.shallowCoreLinearResidualMass_uniformThirtyOneSixteenths` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenFiveCritical.lean:174` |
| `PaperC.PropositionSevenFiveCritical.shallowCoreQuadraticResidualMassTotal_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenFiveCritical.lean:58` |
| `PaperC.PropositionSevenFiveCritical.shallowCoreQuadraticResidualMass_uniformNineteenEighths` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenFiveCritical.lean:92` |
| `PaperC.PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMassTotal_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenFourCritical.lean:116` |
| `PaperC.PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMass_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenFourCritical.lean:179` |
| `PaperC.PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMass_uniformNineteenTwelfths` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenFourCritical.lean:137` |
| `PaperC.PropositionSevenFourCritical.smallHeightLargeProductQuadraticResidualMassTotal_eq_branches` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenFourCritical.lean:56` |
| `PaperC.PropositionSevenFourCritical.smallHeightLargeProductQuadraticResidualMass_uniformFiveThird` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenFourCritical.lean:83` |
| `PaperC.PropositionSevenThreeCritical.smallProductLinearResidualMassTotal_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenThreeCritical.lean:98` |
| `PaperC.PropositionSevenThreeCritical.smallProductLinearResidualMass_uniformSevenFourths` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenThreeCritical.lean:113` |
| `PaperC.PropositionSevenThreeCritical.smallProductQuadraticResidualMassTotal_eq_branches` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenThreeCritical.lean:46` |
| `PaperC.PropositionSevenThreeCritical.smallProductQuadraticResidualMass_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSevenThreeCritical.lean:70` |
| `PaperC.PropositionSevenThreeSigmaZeroCover.ambientPairSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/PropositionSevenThreeSigmaZeroCover.lean:184` |
| `PaperC.PropositionSevenThreeSigmaZeroCover.four_pow_mul_card_le_ambientPairSolutionMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/PropositionSevenThreeSigmaZeroCover.lean:162` |
| `PaperC.PropositionSevenThreeSigmaZeroCover.four_pow_mul_card_sigmaZeroSmallProductPairs_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/PropositionSevenThreeSigmaZeroCover.lean:215` |
| `PaperC.PropositionSevenThreeSigmaZeroCover.mem_sigmaZeroSmallProductPairs_componentCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/PropositionSevenThreeSigmaZeroCover.lean:84` |
| `PaperC.PropositionSevenThreeSigmaZeroCover.mem_sigmaZeroSmallProductPairs_separated` | inconditionnel | — | — | — | `PaperC/Combinatorics/PropositionSevenThreeSigmaZeroCover.lean:74` |
| `PaperC.PropositionSevenThreeSigmaZeroCover.mem_sigmaZeroSmallProductPairs_smallProduct` | inconditionnel | — | — | — | `PaperC/Combinatorics/PropositionSevenThreeSigmaZeroCover.lean:94` |
| `PaperC.PropositionSevenThreeSigmaZeroCover.mem_sigmaZeroSmallProductSubtypePairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/PropositionSevenThreeSigmaZeroCover.lean:55` |
| `PaperC.PropositionSevenThreeSigmaZeroCover.sigmaZeroAmbientAssignment_admissible` | inconditionnel | — | — | — | `PaperC/Combinatorics/PropositionSevenThreeSigmaZeroCover.lean:128` |
| `PaperC.PropositionSevenThreeSigmaZeroCover.sigmaZeroAmbientAssignment_solution` | inconditionnel | — | — | — | `PaperC/Combinatorics/PropositionSevenThreeSigmaZeroCover.lean:142` |
| `PaperC.PropositionSevenThreeSigmaZeroCover.sum_ambientPairSolutionMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/PropositionSevenThreeSigmaZeroCover.lean:231` |
| `PaperC.PropositionSevenThreeSigmaZeroCover.sum_four_pow_mul_card_sigmaZeroSmallProductPairs_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/PropositionSevenThreeSigmaZeroCover.lean:265` |
| `PaperC.PropositionSixteenOne.R2κ_eq_filtered_sum` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:190` |
| `PaperC.PropositionSixteenOne.R2κ_eq_systematic_add_residual` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:295` |
| `PaperC.PropositionSixteenOne.R2κ_eq_systematic_add_sum_sectors` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:456` |
| `PaperC.PropositionSixteenOne.alignedDeepCoreSector_eventually_empty` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:671` |
| `PaperC.PropositionSixteenOne.alignedDeepCoreSector_uniformLittleOInBoundedRatioWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:743` |
| `PaperC.PropositionSixteenOne.boundedRatioSectorPairs_disjoint` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:381` |
| `PaperC.PropositionSixteenOne.boundedRatio_existsUnique_sector` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:392` |
| `PaperC.PropositionSixteenOne.homogeneousMassNat_eq_systematic_add_residual` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:260` |
| `PaperC.PropositionSixteenOne.homogeneousWeight_eq_systematic_add_residual` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:163` |
| `PaperC.PropositionSixteenOne.mem_boundedRatioBlock` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:55` |
| `PaperC.PropositionSixteenOne.mem_boundedRatioSectorPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:370` |
| `PaperC.PropositionSixteenOne.mem_separatedBoundedRatioPairs` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:82` |
| `PaperC.PropositionSixteenOne.pairRho_eq_pairSigma_add_pairTau` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:131` |
| `PaperC.PropositionSixteenOne.pair_coordinates_two_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:96` |
| `PaperC.PropositionSixteenOne.proposition_sixteen_one` | conditionnel | `ES86-T1b-Q-split-n2`, `PCv07c-L17.26-bounded-ratio-many-defects`, `PCv07c-L17.28-bounded-ratio-nonterminal-sector`, `PCv07c-L17.30-bounded-ratio-terminal-sector`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/PropositionSixteenOne.lean:37` |
| `PaperC.PropositionSixteenOne.proposition_sixteen_one_canonical` | conditionnel | `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/PropositionSixteenOne.lean:85` |
| `PaperC.PropositionSixteenOne.proposition_sixteen_one_of_sector_estimates` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:577` |
| `PaperC.PropositionSixteenOne.residualMassNat_eq_sum_sectors` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:413` |
| `PaperC.PropositionSixteenOne.residualMass_eq_sum_sectorResidualMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:444` |
| `PaperC.PropositionSixteenOne.startWindow_le_boundedRatioCutoff` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:68` |
| `PaperC.PropositionSixteenOne.systematicMassNat_eq_boundedRationalMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:221` |
| `PaperC.PropositionSixteenOne.systematicMassNat_le_boundedRatioEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:239` |
| `PaperC.PropositionSixteenOne.systematicMass_eq_boundedRationalMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:279` |
| `PaperC.PropositionSixteenOne.systematicMass_uniformLittleOInBoundedRatioWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:625` |
| `PaperC.PropositionSixteenOne.uniformLittleOInBoundedRatioWindow_add` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:502` |
| `PaperC.PropositionSixteenOne.uniformLittleOInBoundedRatioWindow_finset_sum` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:529` |
| `PaperC.PropositionSixteenOne.uniformLittleOInBoundedRatioWindow_fintype_sum` | inconditionnel | — | — | — | `PaperC/Asymptotics/PropositionSixteenOneCore.lean:558` |
| `PaperC.QuadraticIdealDivisors.disjoint_normalizedFactors_of_isCoprime` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:188` |
| `PaperC.QuadraticIdealDivisors.factorCountProduct_finset_prod_of_pairwise` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:235` |
| `PaperC.QuadraticIdealDivisors.factorCountProduct_mappedPrimePower_le` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:289` |
| `PaperC.QuadraticIdealDivisors.factorCountProduct_mul_of_isCoprime` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:203` |
| `PaperC.QuadraticIdealDivisors.factorCountProduct_primeFactors_assembly` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:421` |
| `PaperC.QuadraticIdealDivisors.factorCountProduct_rationalPrimePowerIdeal_le` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:444` |
| `PaperC.QuadraticIdealDivisors.factorCountProduct_span_natCast_le_tauSq` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:470` |
| `PaperC.QuadraticIdealDivisors.factorCountProduct_span_natPrime_pow_le` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:362` |
| `PaperC.QuadraticIdealDivisors.factorization_ne_zero_of_mem_primeFactors` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:388` |
| `PaperC.QuadraticIdealDivisors.local_quadratic_factor_bound` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:271` |
| `PaperC.QuadraticIdealDivisors.map_span_int_eq_span_intCast` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:43` |
| `PaperC.QuadraticIdealDivisors.natCard_idealDivisors_eq_prod_factorCounts` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:131` |
| `PaperC.QuadraticIdealDivisors.natCard_idealDivisors_span_natCast_le_tauSq` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:497` |
| `PaperC.QuadraticIdealDivisors.prod_factorCountProduct_rationalPrimePowerIdeal_le` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:455` |
| `PaperC.QuadraticIdealDivisors.quadraticIdealDivisorTauSq` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:523` |
| `PaperC.QuadraticIdealDivisors.rationalPrimePowerIdeal_isCoprime` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:404` |
| `PaperC.QuadraticIdealDivisors.rationalPrimePowerIdeal_ne_bot` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:395` |
| `PaperC.QuadraticIdealDivisors.span_intCast_eq_span_natAbs` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:51` |
| `PaperC.QuadraticIdealDivisors.span_natCast_eq_prod_primeFactors` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:78` |
| `PaperC.QuadraticIdealDivisors.span_natCast_eq_prod_rationalPrimePowerIdeal` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:436` |
| `PaperC.QuadraticIdealDivisors.span_natPrime_isMaximal` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:60` |
| `PaperC.QuadraticIdealDivisors.span_natPrime_ne_bot` | inconditionnel | — | — | — | `PaperC/Diophantine/QuadraticIdealDivisors.lean:71` |
| `PaperC.QuotientParity.finrank_comap_subtype_of_le` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/QuotientParity.lean:75` |
| `PaperC.QuotientParity.finrank_le_finrank_sub_one_of_le_ker` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/QuotientParity.lean:88` |
| `PaperC.QuotientParity.finrank_nested_quotient_le_finrank_sub` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/QuotientParity.lean:158` |
| `PaperC.QuotientParity.finrank_nested_quotient_le_of_functional_on_W` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/QuotientParity.lean:203` |
| `PaperC.QuotientParity.finrank_quotient_le_finrank_sub` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/QuotientParity.lean:110` |
| `PaperC.QuotientParity.finrank_quotient_le_finrank_sub_of_induced_ne_zero` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/QuotientParity.lean:133` |
| `PaperC.QuotientParity.quotientFunctional_mkQ` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/QuotientParity.lean:37` |
| `PaperC.QuotientParity.quotientFunctional_ne_zero_iff` | inconditionnel | — | — | — | `PaperC/LinearAlgebra/QuotientParity.lean:50` |
| `PaperC.RationalMassFinite.canonicalPairHeight_eq_of_choice` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:103` |
| `PaperC.RationalMassFinite.canonicalPairSigma_eq_channelSigma_of_choice` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:89` |
| `PaperC.RationalMassFinite.canonicalPairSigma_eq_rationalSigma` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:72` |
| `PaperC.RationalMassFinite.canonicalPairWeight_le_coverWeights` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:343` |
| `PaperC.RationalMassFinite.canonicalPairWeight_le_pow_div_of_choice` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:311` |
| `PaperC.RationalMassFinite.card_largeChannelPairCoverAtHeight_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:186` |
| `PaperC.RationalMassFinite.card_largeChannelPairCoverAtRatio_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:138` |
| `PaperC.RationalMassFinite.card_largeChannelPairCover_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:215` |
| `PaperC.RationalMassFinite.mem_separatedDyadicPairs` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:45` |
| `PaperC.RationalMassFinite.pair_mem_heightTwoBoundaryPairs_of_choice` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:249` |
| `PaperC.RationalMassFinite.pair_mem_largeChannelPairCover_of_choice` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:272` |
| `PaperC.RationalMassFinite.rationalMass_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:443` |
| `PaperC.RationalMassFinite.two_le_canonicalMultiplicity_of_sigma_pos` | inconditionnel | — | — | — | `PaperC/Arithmetic/RationalMassFinite.lean:81` |
| `PaperC.RelationalHostBound.card_relationalHosts_cast_le_exp_bound` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalHostBound.lean:139` |
| `PaperC.RelationalHostBound.card_relationalHosts_cast_le_kernelSum` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalHostBound.lean:35` |
| `PaperC.RelationalHostBound.cast_largeKernelWeightQ` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalHostBound.lean:24` |
| `PaperC.RelationalHostBound.sum_largeKernelWeight_le_sqrt_mul_exp` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalHostBound.lean:73` |
| `PaperC.RelationalHosts.assignmentCountBound_le_four_mul_kernelWeightQ` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:407` |
| `PaperC.RelationalHosts.card_certificate_union_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:307` |
| `PaperC.RelationalHosts.card_leftCertificates_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:241` |
| `PaperC.RelationalHosts.card_relationalHosts_cast_le_assignmentSum` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:336` |
| `PaperC.RelationalHosts.card_relationalHosts_cast_le_kernelSumQ` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:469` |
| `PaperC.RelationalHosts.card_rightCertificates_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:274` |
| `PaperC.RelationalHosts.card_startsWithSelectedLabel_le_one` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:124` |
| `PaperC.RelationalHosts.chosenRelation_ne_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:74` |
| `PaperC.RelationalHosts.exists_nonzero_relation_of_rho_pos` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:54` |
| `PaperC.RelationalHosts.mem_relationalHosts` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:40` |
| `PaperC.RelationalHosts.mem_startsWithSelectedLabel` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:116` |
| `PaperC.RelationalHosts.relationalHosts_subset_certificateCover` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:181` |
| `PaperC.RelationalHosts.selectedLabel_mem_Icc` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:161` |
| `PaperC.RelationalHosts.selectedOccurrence_ne_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/RelationalHosts.lean:93` |
| `PaperC.RelationalHostsThreeHalves.card_relationalHosts_uniformThreeHalves` | inconditionnel | — | — | — | `PaperC/Asymptotics/RelationalHostsThreeHalves.lean:81` |
| `PaperC.RelationalHostsThreeHalves.card_relationalHosts_uniformThreeHalves_inRunLengthWindow` | inconditionnel | — | — | — | `PaperC/Asymptotics/RelationalHostsThreeHalves.lean:112` |
| `PaperC.RelationalHostsThreeHalves.relationalHostResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/RelationalHostsThreeHalves.lean:38` |
| `PaperC.RelationalInterpolation.eventually_sum_nonneg_and_le_sqrt_mul_sqrt` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalInterpolation.lean:208` |
| `PaperC.RelationalInterpolation.sum_le_rpow_average` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalInterpolation.lean:123` |
| `PaperC.RelationalInterpolation.sum_le_sqrt_card_mul_sqrt_sum_sq` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalInterpolation.lean:31` |
| `PaperC.RelationalInterpolation.sum_le_sqrt_relationalHosts_bound_mul_sqrt_sqBound` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalInterpolation.lean:98` |
| `PaperC.RelationalInterpolation.sum_le_sqrt_relationalHosts_bound_mul_sqrt_sum_sq` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalInterpolation.lean:64` |
| `PaperC.RelationalInterpolation.sum_le_two_sub_half_delta_add_error` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalInterpolation.lean:162` |
| `PaperC.RelationalInterpolation.sum_le_two_sub_half_delta_add_error_of_subset` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalInterpolation.lean:181` |
| `PaperC.RelationalInterpolation.sum_nonneg_and_le_sqrt_card_mul_sqrt_sum_sq` | inconditionnel | — | — | — | `PaperC/Analysis/RelationalInterpolation.lean:45` |
| `PaperC.ResidualCertificates.ComponentCertificate.adj` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:388` |
| `PaperC.ResidualCertificates.ComponentCertificate.prime_dvd_left_label` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:410` |
| `PaperC.ResidualCertificates.ComponentCertificate.prime_dvd_left_start_add_offset` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:433` |
| `PaperC.ResidualCertificates.ComponentCertificate.prime_dvd_right_label` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:420` |
| `PaperC.ResidualCertificates.ComponentCertificate.prime_dvd_right_start_add_offset` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:447` |
| `PaperC.ResidualCertificates.ComponentCertificate.right_component` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:399` |
| `PaperC.ResidualCertificates.adj_of_isComponentPrimeCell` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:88` |
| `PaperC.ResidualCertificates.canonicalCertificates_leftOffset_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:597` |
| `PaperC.ResidualCertificates.canonicalCertificates_left_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:492` |
| `PaperC.ResidualCertificates.canonicalCertificates_not_onChannel_of_excluded` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:674` |
| `PaperC.ResidualCertificates.canonicalCertificates_prime_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:564` |
| `PaperC.ResidualCertificates.canonicalCertificates_residualExpression_ne` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:709` |
| `PaperC.ResidualCertificates.canonicalCertificates_rightOffset_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:618` |
| `PaperC.ResidualCertificates.canonicalCertificates_right_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:528` |
| `PaperC.ResidualCertificates.canonicalComponentCertificate_cell` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:374` |
| `PaperC.ResidualCertificates.canonicalComponentCertificate_prime` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:361` |
| `PaperC.ResidualCertificates.card_canonicalCertificatePrimes` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:820` |
| `PaperC.ResidualCertificates.card_componentsMeetingPair_le_two` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:776` |
| `PaperC.ResidualCertificates.channelVertexOffset_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:458` |
| `PaperC.ResidualCertificates.componentPrimeCells_least_nonempty` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:256` |
| `PaperC.ResidualCertificates.exists_adj_in_component_of_two_le_card` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:115` |
| `PaperC.ResidualCertificates.exists_componentCarriesPrime` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:165` |
| `PaperC.ResidualCertificates.leastComponentCell_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:303` |
| `PaperC.ResidualCertificates.leastComponentCell_spec` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:288` |
| `PaperC.ResidualCertificates.leastComponentPrime_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:220` |
| `PaperC.ResidualCertificates.leastComponentPrime_spec` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:206` |
| `PaperC.ResidualCertificates.mem_componentPrimeCells` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:246` |
| `PaperC.ResidualCertificates.mem_componentsMeetingPair` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:758` |
| `PaperC.ResidualCertificates.not_onChannel_iff_residualExpression_ne` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:653` |
| `PaperC.ResidualCertificates.right_component_of_isComponentPrimeCell` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualCertificates.lean:99` |
| `PaperC.ResidualChannelLemmaSevenTwo.mem_residualPrimeRange` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelLemmaSevenTwo.lean:41` |
| `PaperC.ResidualChannelLemmaSevenTwo.mem_residualPrimeRange_of_nonempty` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelLemmaSevenTwo.lean:51` |
| `PaperC.ResidualChannelLemmaSevenTwo.residualPrimeMass_eq_sum_primesBetween` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelLemmaSevenTwo.lean:102` |
| `PaperC.ResidualChannelLemmaSevenTwo.residualPrimeMass_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelLemmaSevenTwo.lean:139` |
| `PaperC.ResidualComponentCounts.canonicalCorrected_add_twice_residual_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:470` |
| `PaperC.ResidualComponentCounts.channelUnitCount_eq_card_channelCells` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:77` |
| `PaperC.ResidualComponentCounts.channelUnitCount_eq_card_rationalChannelUnits` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:70` |
| `PaperC.ResidualComponentCounts.correctedDefectCount_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:268` |
| `PaperC.ResidualComponentCounts.corrected_add_twice_residual_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:283` |
| `PaperC.ResidualComponentCounts.defectiveExactUnitCount_le_defectiveVertexCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:124` |
| `PaperC.ResidualComponentCounts.defectiveUnitVertex_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:111` |
| `PaperC.ResidualComponentCounts.defective_add_nondefective_eq_channelUnitCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:85` |
| `PaperC.ResidualComponentCounts.localResidualTau_le_corrected_add_residual` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:303` |
| `PaperC.ResidualComponentCounts.nondefectiveExactUnitCount_le_nontrivialComponentCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:203` |
| `PaperC.ResidualComponentCounts.nondefectiveUnitComponent_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:184` |
| `PaperC.ResidualComponentCounts.residualComponentCount_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:275` |
| `PaperC.ResidualComponentCounts.residualTau_eq_localResidualTau_of_choice` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:386` |
| `PaperC.ResidualComponentCounts.residualTau_le_canonicalCorrected_add_residual` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualComponentCounts.lean:426` |
| `PaperC.ResidualMasses.activeSmallProductLinearResidualMass_eq_sigmaZero_add_positiveSigma` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:524` |
| `PaperC.ResidualMasses.activeSmallProductPairValues_subset_relationalHosts` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:441` |
| `PaperC.ResidualMasses.activeSmallProductPairs_subset_smallProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:357` |
| `PaperC.ResidualMasses.activeSmallProductQuadraticResidualMass_eq_sigmaZero_add_positiveSigma` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:508` |
| `PaperC.ResidualMasses.card_activeSmallProductPairValues` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:432` |
| `PaperC.ResidualMasses.card_activeSmallProductPairs_le_relationalHosts` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:463` |
| `PaperC.ResidualMasses.disjoint_sigmaZero_positiveSigmaSmallProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:399` |
| `PaperC.ResidualMasses.linearResidualMass_cast_le_sqrt_card_mul_sqrt_quadratic` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:262` |
| `PaperC.ResidualMasses.linearResidualWeight_eq_zero_of_pairTau_eq_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:125` |
| `PaperC.ResidualMasses.linearResidualWeight_sq_le_quadraticResidualWeight` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:160` |
| `PaperC.ResidualMasses.mem_activeSmallProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:341` |
| `PaperC.ResidualMasses.mem_positiveSigmaSmallProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:391` |
| `PaperC.ResidualMasses.mem_sigmaZeroSmallProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:382` |
| `PaperC.ResidualMasses.mem_smallProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:314` |
| `PaperC.ResidualMasses.pairRho_eq_pairSigma_add_pairTau` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:72` |
| `PaperC.ResidualMasses.pairTau_le_canonicalCorrected_add_residual` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:88` |
| `PaperC.ResidualMasses.pair_coordinates_two_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:49` |
| `PaperC.ResidualMasses.quadraticResidualWeight_eq_zero_of_pairTau_eq_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:133` |
| `PaperC.ResidualMasses.quadraticResidualWeight_le_corrected_mul_certificate_of_sigma_eq_zero` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:222` |
| `PaperC.ResidualMasses.quadraticResidualWeight_le_systematic_mul_corrected_mul_certificate` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:184` |
| `PaperC.ResidualMasses.sigmaZero_union_positiveSigma_eq_activeSmallProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:410` |
| `PaperC.ResidualMasses.smallProductLinearResidualMass_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:623` |
| `PaperC.ResidualMasses.smallProductLinearResidualMass_eq_active` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:575` |
| `PaperC.ResidualMasses.smallProductLinearResidualMass_eq_sigmaZero_add_positiveSigma` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:609` |
| `PaperC.ResidualMasses.smallProductQuadraticResidualMass_eq_active` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:552` |
| `PaperC.ResidualMasses.smallProductQuadraticResidualMass_eq_sigmaZero_add_positiveSigma` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:598` |
| `PaperC.ResidualMasses.sum_linearResidualWeight_sq_le_quadraticResidualMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/ResidualMasses.lean:248` |
| `PaperC.RungeAnalyticProduct.abs_halfBinomialSum_sub_one_le` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:169` |
| `PaperC.RungeAnalyticProduct.halfBinomialSum_eq_sqrt` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:318` |
| `PaperC.RungeAnalyticProduct.halfBinomialSum_eq_sqrt_of_abs_le_half` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:229` |
| `PaperC.RungeAnalyticProduct.halfBinomialSum_nonneg_of_abs_le_half` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:201` |
| `PaperC.RungeAnalyticProduct.halfBinomialSum_pos` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:283` |
| `PaperC.RungeAnalyticProduct.halfBinomialSum_pos_of_abs_le_half` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:215` |
| `PaperC.RungeAnalyticProduct.halfBinomialSum_sq` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:118` |
| `PaperC.RungeAnalyticProduct.halfBinomialSum_zero` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:263` |
| `PaperC.RungeAnalyticProduct.hasSum_halfBinomialTerm` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:66` |
| `PaperC.RungeAnalyticProduct.hasSum_rungeCoefficient_mul_pow_eq_prod_halfBinomialSum` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:547` |
| `PaperC.RungeAnalyticProduct.hasSum_rungeCoefficient_mul_pow_eq_prod_sqrt` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:594` |
| `PaperC.RungeAnalyticProduct.hasSum_rungeCoefficient_mul_pow_eq_prod_sqrt_of_abs_lt_one` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:570` |
| `PaperC.RungeAnalyticProduct.hasSum_sqrtFactorSeries` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:333` |
| `PaperC.RungeAnalyticProduct.hasSum_sqrtFactorSeries_eq_sqrt` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:362` |
| `PaperC.RungeAnalyticProduct.hasSum_sqrtFactorSeries_eq_sqrt_of_abs_lt_one` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:348` |
| `PaperC.RungeAnalyticProduct.norm_halfBinomialTerm_le` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:41` |
| `PaperC.RungeAnalyticProduct.realPowerSeriesTerm_sqrtFactorSeries` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:442` |
| `PaperC.RungeAnalyticProduct.summable_halfBinomialTerm` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:52` |
| `PaperC.RungeAnalyticProduct.summable_norm_halfBinomialTerm` | inconditionnel | — | — | — | `PaperC/Analysis/RungeAnalyticProduct.lean:59` |
| `PaperC.RungeBound.one_le_radius_of_injective` | inconditionnel | — | — | — | `PaperC/Algebra/RungeBound.lean:30` |
| `PaperC.RungeBound.quantitative_runge` | inconditionnel | — | — | — | `PaperC/Algebra/RungeBound.lean:57` |
| `PaperC.RungeBound.quantitative_runge_of_distinct` | inconditionnel | — | — | — | `PaperC/Algebra/RungeBound.lean:106` |
| `PaperC.RungeCoefficients.abs_halfChoose_le_one` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:82` |
| `PaperC.RungeCoefficients.abs_rungeCoefficient_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:352` |
| `PaperC.RungeCoefficients.abs_rungeCoefficient_le_card_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:334` |
| `PaperC.RungeCoefficients.abs_rungeCoefficient_le_eight_mul_pow` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:363` |
| `PaperC.RungeCoefficients.card_weakComposition` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:168` |
| `PaperC.RungeCoefficients.card_weakComposition_eq_choose_parts` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:179` |
| `PaperC.RungeCoefficients.card_weakComposition_le_two_pow` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:187` |
| `PaperC.RungeCoefficients.choose_succ_eq` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:64` |
| `PaperC.RungeCoefficients.choose_succ_recursion` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:40` |
| `PaperC.RungeCoefficients.halfChoose_succ_eq_catalan` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:117` |
| `PaperC.RungeCoefficients.two_pow_mul_rungeCoefficient_isRatInteger` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:296` |
| `PaperC.RungeCoefficients.two_pow_two_mul_halfChoose_isInt` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:146` |
| `PaperC.RungeCoefficients.two_pow_two_mul_rungeCoefficient_isRatInteger` | inconditionnel | — | — | — | `PaperC/Combinatorics/RungeCoefficients.lean:285` |
| `PaperC.RungeDefectApplication.defectCode_length_lt_of_endpoint_growth` | inconditionnel | — | — | — | `PaperC/Coding/RungeDefectApplication.lean:164` |
| `PaperC.RungeDefectApplication.defectCode_length_lt_of_growth` | inconditionnel | — | — | — | `PaperC/Coding/RungeDefectApplication.lean:104` |
| `PaperC.RungeDefectApplication.defectCode_volume_le_two_pow_of_endpoint_growth` | inconditionnel | — | — | — | `PaperC/Coding/RungeDefectApplication.lean:137` |
| `PaperC.RungeDefectApplication.defectCode_volume_le_two_pow_of_growth` | inconditionnel | — | — | — | `PaperC/Coding/RungeDefectApplication.lean:75` |
| `PaperC.RungeDefectApplication.noShortRungeSquare_of_endpoint_growth` | inconditionnel | — | — | — | `PaperC/Coding/RungeDefectApplication.lean:61` |
| `PaperC.RungeDefectApplication.noShortRungeSquare_of_growth` | inconditionnel | — | — | — | `PaperC/Coding/RungeDefectApplication.lean:22` |
| `PaperC.RungeDefectApplication.rungeScale_mono` | inconditionnel | — | — | — | `PaperC/Coding/RungeDefectApplication.lean:39` |
| `PaperC.RungeDichotomy.nat_le_max_dyadic_or_height` | inconditionnel | — | — | — | `PaperC/Algebra/RungeDichotomy.lean:98` |
| `PaperC.RungeDichotomy.nat_le_one_add_height_of_auxiliary_root` | inconditionnel | — | — | — | `PaperC/Algebra/RungeDichotomy.lean:86` |
| `PaperC.RungeDichotomy.nat_le_two_pow_mul_of_dyadic_gap_and_tail` | inconditionnel | — | — | — | `PaperC/Algebra/RungeDichotomy.lean:28` |
| `PaperC.RungeDichotomy.nat_le_two_pow_mul_of_rungeTruncation_gap` | inconditionnel | — | — | — | `PaperC/Algebra/RungeDichotomy.lean:58` |
| `PaperC.RungeEquality.base_le_paperScale_of_eq` | inconditionnel | — | — | — | `PaperC/Algebra/RungeEquality.lean:74` |
| `PaperC.RungeEstimate.abs_natAbs_sub_rungeTruncation_le` | inconditionnel | — | — | — | `PaperC/Analysis/RungeEstimate.lean:203` |
| `PaperC.RungeEstimate.abs_natAbs_sub_rungeTruncation_le_real` | inconditionnel | — | — | — | `PaperC/Analysis/RungeEstimate.lean:77` |
| `PaperC.RungeLogarithmicGrowth.cappedRadius_log_condition` | inconditionnel | — | — | — | `PaperC/Analysis/RungeLogarithmicGrowth.lean:127` |
| `PaperC.RungeLogarithmicGrowth.cappedRadius_log_endpoint` | inconditionnel | — | — | — | `PaperC/Analysis/RungeLogarithmicGrowth.lean:189` |
| `PaperC.RungeLogarithmicGrowth.endpoint_growth_cappedRadius` | inconditionnel | — | — | — | `PaperC/Analysis/RungeLogarithmicGrowth.lean:176` |
| `PaperC.RungeLogarithmicGrowth.endpoint_growth_of_log` | inconditionnel | — | — | — | `PaperC/Analysis/RungeLogarithmicGrowth.lean:25` |
| `PaperC.RungeLogarithmicGrowth.endpoint_growth_of_log_cap` | inconditionnel | — | — | — | `PaperC/Analysis/RungeLogarithmicGrowth.lean:78` |
| `PaperC.RungeLogarithmicGrowth.log_endpoint_mono` | inconditionnel | — | — | — | `PaperC/Analysis/RungeLogarithmicGrowth.lean:203` |
| `PaperC.RungeLogarithmicGrowth.log_endpoint_of_growth` | inconditionnel | — | — | — | `PaperC/Analysis/RungeLogarithmicGrowth.lean:51` |
| `PaperC.RungeLogarithmicGrowth.noShortRungeSquare_of_log` | inconditionnel | — | — | — | `PaperC/Analysis/RungeLogarithmicGrowth.lean:222` |
| `PaperC.RungeNonEquality.base_le_dyadicTailNumerator` | inconditionnel | — | — | — | `PaperC/Algebra/RungeNonEquality.lean:18` |
| `PaperC.RungeNonEquality.base_le_paperScale_of_ne` | inconditionnel | — | — | — | `PaperC/Algebra/RungeNonEquality.lean:45` |
| `PaperC.RungeNumerics.dyadicTailNumerator_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeNumerics.lean:57` |
| `PaperC.RungeNumerics.dyadicTailNumerator_le_paperScale` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeNumerics.lean:73` |
| `PaperC.RungeNumerics.one_add_auxiliaryHeightExpression_le_paperScale` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeNumerics.lean:90` |
| `PaperC.RungeNumerics.tailNumerator_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeNumerics.lean:27` |
| `PaperC.RungePowerSeries.binomialSeries_half_sq` | inconditionnel | — | — | — | `PaperC/Analysis/RungePowerSeries.lean:88` |
| `PaperC.RungePowerSeries.coeff_rungeProductSeries` | inconditionnel | — | — | — | `PaperC/Analysis/RungePowerSeries.lean:71` |
| `PaperC.RungePowerSeries.coeff_sqrtFactorSeries` | inconditionnel | — | — | — | `PaperC/Analysis/RungePowerSeries.lean:42` |
| `PaperC.RungePowerSeries.rungeProductSeries_sq` | inconditionnel | — | — | — | `PaperC/Analysis/RungePowerSeries.lean:126` |
| `PaperC.RungePowerSeries.sqrtFactorSeries_sq` | inconditionnel | — | — | — | `PaperC/Analysis/RungePowerSeries.lean:108` |
| `PaperC.RungeQPolynomial.coe_reciprocalSplitProduct_eq_rungeProductSeries_sq` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:348` |
| `PaperC.RungeQPolynomial.coeff_integerSplitProduct_natAbs_le` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:112` |
| `PaperC.RungeQPolynomial.coeff_map_integerSplitProduct_eq_rungeTruncation_sq` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:453` |
| `PaperC.RungeQPolynomial.coeff_map_integerSplitProduct_high` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:427` |
| `PaperC.RungeQPolynomial.coeff_rungeQ` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:678` |
| `PaperC.RungeQPolynomial.coeff_rungeQ_high_eq_zero` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:569` |
| `PaperC.RungeQPolynomial.coeff_rungeQ_natAbs_le` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:689` |
| `PaperC.RungeQPolynomial.coeff_rungeTruncation_sq_high` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:366` |
| `PaperC.RungeQPolynomial.forwardRungeTruncation_eq_trunc` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:220` |
| `PaperC.RungeQPolynomial.integerPolynomialHeight_integerSplitProduct_le` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:176` |
| `PaperC.RungeQPolynomial.integerPolynomialHeight_rungeQ_explicit` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:778` |
| `PaperC.RungeQPolynomial.integerPolynomialHeight_rungeQ_le` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:722` |
| `PaperC.RungeQPolynomial.integerPolynomialHeight_rungeQ_le_of_truncationHeight` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:737` |
| `PaperC.RungeQPolynomial.integerSplitProduct_ne_zero` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:93` |
| `PaperC.RungeQPolynomial.map_integerSplitProduct` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:51` |
| `PaperC.RungeQPolynomial.map_integerSplitProduct_not_isSquare` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:466` |
| `PaperC.RungeQPolynomial.map_integralRungeTruncation_eq_scale_mul` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:539` |
| `PaperC.RungeQPolynomial.map_rungeQ` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:552` |
| `PaperC.RungeQPolynomial.monic_integerSplitProduct` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:61` |
| `PaperC.RungeQPolynomial.natDegree_forwardRungeTruncation_le` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:233` |
| `PaperC.RungeQPolynomial.natDegree_integerSplitProduct` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:74` |
| `PaperC.RungeQPolynomial.natDegree_integralRungeTruncation_le` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:503` |
| `PaperC.RungeQPolynomial.natDegree_rungeQ_le_pred` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:612` |
| `PaperC.RungeQPolynomial.natDegree_rungeQ_le_two_mul` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:516` |
| `PaperC.RungeQPolynomial.reflect_forwardRungeTruncation` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:245` |
| `PaperC.RungeQPolynomial.reflect_reciprocalSplitProduct` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:332` |
| `PaperC.RungeQPolynomial.rungeEquality_root_natAbs_le_explicit` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:838` |
| `PaperC.RungeQPolynomial.rungeEquality_root_natAbs_le_height` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:811` |
| `PaperC.RungeQPolynomial.rungeQ_isRoot_of_square_and_truncation` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:822` |
| `PaperC.RungeQPolynomial.rungeQ_ne_zero` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:637` |
| `PaperC.RungeQPolynomial.rungeScale_sq` | inconditionnel | — | — | — | `PaperC/Algebra/RungeQPolynomial.lean:495` |
| `PaperC.RungeScaling.scaledRungeValue_eq_abs_integer` | inconditionnel | — | — | — | `PaperC/Analysis/RungeScaling.lean:76` |
| `PaperC.RungeScaling.scaledRungeValue_sq` | inconditionnel | — | — | — | `PaperC/Analysis/RungeScaling.lean:35` |
| `PaperC.RungeSplitProduct.natDegree_splitProduct` | inconditionnel | — | — | — | `PaperC/Algebra/RungeSplitProduct.lean:32` |
| `PaperC.RungeSplitProduct.splitProduct_not_isSquare` | inconditionnel | — | — | — | `PaperC/Algebra/RungeSplitProduct.lean:47` |
| `PaperC.RungeSplitProduct.splitProduct_separable_iff` | inconditionnel | — | — | — | `PaperC/Algebra/RungeSplitProduct.lean:37` |
| `PaperC.RungeTailEstimate.abs_realRungeCoefficient_le` | inconditionnel | — | — | — | `PaperC/Analysis/RungeTailEstimate.lean:219` |
| `PaperC.RungeTailEstimate.abs_tail_le_two_mul` | inconditionnel | — | — | — | `PaperC/Analysis/RungeTailEstimate.lean:94` |
| `PaperC.RungeTailEstimate.cast_eval_rungeTruncation_eq_pow_mul_realPartialSum` | inconditionnel | — | — | — | `PaperC/Analysis/RungeTailEstimate.lean:203` |
| `PaperC.RungeTailEstimate.eval_rungeTruncation_eq_pow_mul_partialSum` | inconditionnel | — | — | — | `PaperC/Analysis/RungeTailEstimate.lean:171` |
| `PaperC.RungeTailEstimate.norm_coefficientSeriesTerm_le` | inconditionnel | — | — | — | `PaperC/Analysis/RungeTailEstimate.lean:50` |
| `PaperC.RungeTailEstimate.pow_mul_abs_tail_le` | inconditionnel | — | — | — | `PaperC/Analysis/RungeTailEstimate.lean:144` |
| `PaperC.RungeTailEstimate.rungeCoefficient_pow_mul_abs_tail_le` | inconditionnel | — | — | — | `PaperC/Analysis/RungeTailEstimate.lean:245` |
| `PaperC.RungeTailEstimate.summable_coefficientSeriesTerm` | inconditionnel | — | — | — | `PaperC/Analysis/RungeTailEstimate.lean:68` |
| `PaperC.RungeTailEstimate.tsum_sub_sum_range_eq_tail` | inconditionnel | — | — | — | `PaperC/Analysis/RungeTailEstimate.lean:84` |
| `PaperC.RungeTranslation.abs_translatedShift_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeTranslation.lean:50` |
| `PaperC.RungeTranslation.base_add_translatedShift` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeTranslation.lean:34` |
| `PaperC.RungeTranslation.prod_base_add_translatedShift` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeTranslation.lean:68` |
| `PaperC.RungeTranslation.prod_natCast` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeTranslation.lean:74` |
| `PaperC.RungeTranslation.translatedProduct_isSquare` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeTranslation.lean:82` |
| `PaperC.RungeTranslation.translatedRungeInput` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeTranslation.lean:97` |
| `PaperC.RungeTranslation.translatedShift_injective` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeTranslation.lean:57` |
| `PaperC.RungeTranslation.translatedShift_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeTranslation.lean:44` |
| `PaperC.RungeTranslation.translatedShift_nonneg` | inconditionnel | — | — | — | `PaperC/Arithmetic/RungeTranslation.lean:38` |
| `PaperC.RungeTruncation.eval_rungeTruncation_eq_integral_div` | inconditionnel | — | — | — | `PaperC/Algebra/RungeTruncation.lean:97` |
| `PaperC.RungeTruncation.map_integralRungeTruncation` | inconditionnel | — | — | — | `PaperC/Algebra/RungeTruncation.lean:76` |
| `PaperC.RungeTruncation.one_div_two_pow_le_abs_integer_sub_rungeTruncation` | inconditionnel | — | — | — | `PaperC/Algebra/RungeTruncation.lean:124` |
| `PaperC.RungeTruncation.scaledRungeCoefficientUpTo_spec` | inconditionnel | — | — | — | `PaperC/Algebra/RungeTruncation.lean:50` |
| `PaperC.RungeTruncation.scaledRungeCoefficient_spec` | inconditionnel | — | — | — | `PaperC/Algebra/RungeTruncation.lean:31` |
| `PaperC.RungeTruncationBounds.coeff_integralRungeTruncation_natAbs_le` | inconditionnel | — | — | — | `PaperC/Algebra/RungeTruncationBounds.lean:66` |
| `PaperC.RungeTruncationBounds.integerPolynomialHeight_integralRungeTruncation_le` | inconditionnel | — | — | — | `PaperC/Algebra/RungeTruncationBounds.lean:98` |
| `PaperC.RungeTruncationBounds.scaledRungeCoefficientUpTo_natAbs_le` | inconditionnel | — | — | — | `PaperC/Algebra/RungeTruncationBounds.lean:22` |
| `PaperC.SectionElevenPartition.existsUnique_sector` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:268` |
| `PaperC.SectionElevenPartition.lemma_eleven_one_existsUnique_sector` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:720` |
| `PaperC.SectionElevenPartition.lemma_eleven_one_populations_cover` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:695` |
| `PaperC.SectionElevenPartition.mem_sectionElevenSectorPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:419` |
| `PaperC.SectionElevenPartition.mem_sectorPopulation` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:220` |
| `PaperC.SectionElevenPartition.not_atLeastThreeCorrectedDefects_iff_atMostTwo` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:368` |
| `PaperC.SectionElevenPartition.not_isCanonicallyAligned_iff_nonaligned` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:336` |
| `PaperC.SectionElevenPartition.not_isCanonicallyNonaligned_iff_aligned` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:347` |
| `PaperC.SectionElevenPartition.not_smallCanonicalPrimeProduct_iff_large` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:310` |
| `PaperC.SectionElevenPartition.sectionElevenSectorOf_eq_five_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:484` |
| `PaperC.SectionElevenPartition.sectionElevenSectorOf_eq_four_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:468` |
| `PaperC.SectionElevenPartition.sectionElevenSectorOf_eq_one_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:432` |
| `PaperC.SectionElevenPartition.sectionElevenSectorOf_eq_seven_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:521` |
| `PaperC.SectionElevenPartition.sectionElevenSectorOf_eq_six_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:502` |
| `PaperC.SectionElevenPartition.sectionElevenSectorOf_eq_three_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:454` |
| `PaperC.SectionElevenPartition.sectionElevenSectorOf_eq_two_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:442` |
| `PaperC.SectionElevenPartition.sectionElevenSectorPairs_disjoint` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:681` |
| `PaperC.SectionElevenPartition.sectionElevenSectorPairs_one_eq_smallProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:545` |
| `PaperC.SectionElevenPartition.sectionElevenSectorPairs_three_eq_shallowCorePairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:574` |
| `PaperC.SectionElevenPartition.sectionElevenSectorPairs_two_eq_smallHeightLargeProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:559` |
| `PaperC.SectionElevenPartition.sectionEleven_lateSectors_eq_deepCorePairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:590` |
| `PaperC.SectionElevenPartition.sectorOf_eq_alignedDeepCore_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:139` |
| `PaperC.SectionElevenPartition.sectorOf_eq_manyDefects_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:156` |
| `PaperC.SectionElevenPartition.sectorOf_eq_nonterminal_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:174` |
| `PaperC.SectionElevenPartition.sectorOf_eq_shallowCore_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:123` |
| `PaperC.SectionElevenPartition.sectorOf_eq_smallCanonicalHeight_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:108` |
| `PaperC.SectionElevenPartition.sectorOf_eq_smallPrimeProduct_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:94` |
| `PaperC.SectionElevenPartition.sectorOf_eq_terminal_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:193` |
| `PaperC.SectionElevenPartition.sectorPopulations_disjoint` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:230` |
| `PaperC.SectionElevenPartition.seven_sector_populations_cover` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionElevenPartition.lean:250` |
| `PaperC.SectionFourteenClosure.compactMarkedPPPLaplaceTarget_eq_tsum` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionFourteenClosure.lean:73` |
| `PaperC.SectionFourteenClosure.compactMarkedTest_tsum_eq_finset` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionFourteenClosure.lean:54` |
| `PaperC.SectionFourteenClosure.theorem_one_two_ii_laplace` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/SectionFourteenClosure.lean:131` |
| `PaperC.SectionFourteenClosure.theorem_one_two_iii_laplace_and_tightness` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/SectionFourteenClosure.lean:157` |
| `PaperC.SectionSevenPartition.mem_deepCorePairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionSevenPartition.lean:60` |
| `PaperC.SectionSevenPartition.sectionSeven_populations_cover` | inconditionnel | — | — | — | `PaperC/Combinatorics/SectionSevenPartition.lean:84` |
| `PaperC.SectionThirteenCouplings.abs_commonGoodPoissonRate_sub_targetRate_eq` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:545` |
| `PaperC.SectionThirteenCouplings.averagedConditionalGoodLaw_eq_fullGoodStartLaw` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:139` |
| `PaperC.SectionThirteenCouplings.card_goodStarts_add_card_terminalBadStarts` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:531` |
| `PaperC.SectionThirteenCouplings.commonConditionalGoodPoissonRate_eq` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:503` |
| `PaperC.SectionThirteenCouplings.conditionedGoodIndicatorSum_eq_fullGoodStartCount` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:91` |
| `PaperC.SectionThirteenCouplings.disagreementProbability_fullGood_dyadic_le_badMass` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:219` |
| `PaperC.SectionThirteenCouplings.eventProbability_fullUniformPMF_eq` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:107` |
| `PaperC.SectionThirteenCouplings.exists_bad_start_of_fullGoodStartCount_ne_dyadicCount` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:195` |
| `PaperC.SectionThirteenCouplings.fullGoodIndicator_eq_true_iff` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:54` |
| `PaperC.SectionThirteenCouplings.fullGoodStartCount_eq_sum` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:177` |
| `PaperC.SectionThirteenCouplings.fullGoodStartLaw_eq_finiteNatLaw` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:122` |
| `PaperC.SectionThirteenCouplings.natTotalVariation_averagedGood_fullDyadic_le_badMass` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:312` |
| `PaperC.SectionThirteenCouplings.natTotalVariation_commonGoodPoisson_target_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:581` |
| `PaperC.SectionThirteenCouplings.natTotalVariation_fullDyadic_targetPoisson_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Probability/SectionThirteenCouplings.lean:683` |
| `PaperC.SectionThirteenCouplings.natTotalVariation_fullDyadic_targetPoisson_le_components` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:613` |
| `PaperC.SectionThirteenCouplings.natTotalVariation_poisson_le_abs_rate_sub` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:470` |
| `PaperC.SectionThirteenCouplings.natTotalVariation_poisson_le_one_sub_exp_of_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:372` |
| `PaperC.SectionThirteenCouplings.scaled_poissonPMFReal_le_of_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:333` |
| `PaperC.SectionThirteenCouplings.terminalBadStarts_subset_dyadicBlock` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenCouplings.lean:524` |
| `PaperC.SectionThirteenCritical.fullDyadicTargetPoissonTotalVariation_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenCritical.lean:40` |
| `PaperC.SectionThirteenFiniteBound.finiteNatLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenFiniteBound.lean:223` |
| `PaperC.SectionThirteenFiniteBound.finite_corollary_thirteen_nine` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenFiniteBound.lean:422` |
| `PaperC.SectionThirteenFiniteBound.finite_corollary_thirteen_nine_of_component_bounds` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenFiniteBound.lean:464` |
| `PaperC.SectionThirteenFiniteBound.hasSum_finiteNatLaw` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenFiniteBound.lean:235` |
| `PaperC.SectionThirteenFiniteBound.natTotalVariation_comm` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenFiniteBound.lean:63` |
| `PaperC.SectionThirteenFiniteBound.natTotalVariation_finiteNatLaw_le_disagreement` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenFiniteBound.lean:289` |
| `PaperC.SectionThirteenFiniteBound.natTotalVariation_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenFiniteBound.lean:55` |
| `PaperC.SectionThirteenFiniteBound.natTotalVariation_triangle` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenFiniteBound.lean:73` |
| `PaperC.SectionThirteenFiniteBound.natTotalVariation_uniformMixture_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenFiniteBound.lean:123` |
| `PaperC.SectionThirteenFiniteBound.summable_abs_sub_of_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenFiniteBound.lean:42` |
| `PaperC.SectionThirteenFiniteBound.summable_finiteNatLaw` | inconditionnel | — | — | — | `PaperC/Probability/SectionThirteenFiniteBound.lean:272` |
| `PaperC.SectionThirteenRate.card_orderedDependencyEdges_cast_le_harmonic` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:824` |
| `PaperC.SectionThirteenRate.halfPower_uniformBigO_linearDivLogLogSquared` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:502` |
| `PaperC.SectionThirteenRate.loglogSquared_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:286` |
| `PaperC.SectionThirteenRate.loglog_sq_mul_exp_neg_sqrt_log_div_loglog_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:69` |
| `PaperC.SectionThirteenRate.natCast_uniformRationalPowerOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:407` |
| `PaperC.SectionThirteenRate.normalizedLinearLogLog_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:589` |
| `PaperC.SectionThirteenRate.normalizedQuadraticLogLog_uniformBigO` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:522` |
| `PaperC.SectionThirteenRate.normalizedTerminalDefectContribution_uniformBigO_explicitRate` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:672` |
| `PaperC.SectionThirteenRate.normalized_terminalBadStarts_uniformBigO_explicitRate` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:652` |
| `PaperC.SectionThirteenRate.one_add_log_three_mul_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:423` |
| `PaperC.SectionThirteenRate.quantitativeHomogeneousScale_uniformBigO_loglogSquared` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:162` |
| `PaperC.SectionThirteenRate.rationalPower_uniformBigO_natPowerDivLogLogSquared` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:340` |
| `PaperC.SectionThirteenRate.sum_inv_largePrimesInRange_le_harmonic` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:784` |
| `PaperC.SectionThirteenRate.sum_inv_largePrimesInRange_le_one_add_log` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:808` |
| `PaperC.SectionThirteenRate.terminalBadStartProbabilityMass_uniformBigO_explicitRate` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:702` |
| `PaperC.SectionThirteenRate.uniformBigOOn_const_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:250` |
| `PaperC.SectionThirteenRate.uniformBigOOn_mono` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:264` |
| `PaperC.SectionThirteenRate.uniformBigOOn_trans` | inconditionnel | — | — | — | `PaperC/Asymptotics/SectionThirteenRate.lean:231` |
| `PaperC.SectionTwelveMoments.abs_dyadicSecondFactorialMoment_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1015` |
| `PaperC.SectionTwelveMoments.abs_factorialMomentError_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1350` |
| `PaperC.SectionTwelveMoments.abs_jointPairMass_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:669` |
| `PaperC.SectionTwelveMoments.abs_jointStartProbability_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:635` |
| `PaperC.SectionTwelveMoments.abs_jointStartProbability_touching_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:904` |
| `PaperC.SectionTwelveMoments.abs_touchingPairMass_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:929` |
| `PaperC.SectionTwelveMoments.card_backwardOverlapCandidates_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:364` |
| `PaperC.SectionTwelveMoments.card_forwardOverlapCandidates_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:351` |
| `PaperC.SectionTwelveMoments.card_offDiag_eq_overlap_add_touching_add_separated` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:978` |
| `PaperC.SectionTwelveMoments.card_overlapOffsets_le` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:347` |
| `PaperC.SectionTwelveMoments.card_overlappingPairs_le_two_mul` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:378` |
| `PaperC.SectionTwelveMoments.disjoint_overlapping_separated` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:283` |
| `PaperC.SectionTwelveMoments.disjoint_overlapping_touching` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:274` |
| `PaperC.SectionTwelveMoments.disjoint_touching_separated` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:292` |
| `PaperC.SectionTwelveMoments.dyadicCount_factorial_eq_sum_offDiag` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:424` |
| `PaperC.SectionTwelveMoments.dyadicFirstMomentPoissonError_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1578` |
| `PaperC.SectionTwelveMoments.dyadicSecondFactorialMoment_eq_offDiag` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:443` |
| `PaperC.SectionTwelveMoments.dyadicSecondFactorialMoment_eq_overlap_touching_separated` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:494` |
| `PaperC.SectionTwelveMoments.dyadicSecondFactorialMoment_eq_touching_add_separated` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:966` |
| `PaperC.SectionTwelveMoments.dyadicSecondFactorialPoissonError_eq` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1600` |
| `PaperC.SectionTwelveMoments.dyadicVariancePoissonError_eq` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1618` |
| `PaperC.SectionTwelveMoments.dyadicVariance_eq_factorial_add_expectation_sub_sq` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1168` |
| `PaperC.SectionTwelveMoments.factorialBaselinePoissonError_eq` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1473` |
| `PaperC.SectionTwelveMoments.factorialBaselinePoissonError_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1486` |
| `PaperC.SectionTwelveMoments.factorialBaseline_eq` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:999` |
| `PaperC.SectionTwelveMoments.jointDefectMass_separated_cast_eq_homogeneousMass` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1199` |
| `PaperC.SectionTwelveMoments.jointDefectMass_separated_eq_homogeneousMassNat` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1180` |
| `PaperC.SectionTwelveMoments.jointPairMass_diag_eq_dyadicExpectation` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1129` |
| `PaperC.SectionTwelveMoments.jointPairMass_overlappingPairs_eq_zero` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:532` |
| `PaperC.SectionTwelveMoments.jointPairMass_union` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:481` |
| `PaperC.SectionTwelveMoments.jointStartProbability_comm` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:864` |
| `PaperC.SectionTwelveMoments.jointStartProbability_eq_eta_mul_two_pow_rho_div` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:598` |
| `PaperC.SectionTwelveMoments.jointStartProbability_eq_touchingLower` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:882` |
| `PaperC.SectionTwelveMoments.jointStartProbability_eq_uniformSolutionProbability` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:580` |
| `PaperC.SectionTwelveMoments.jointStartProbability_eq_zero_of_overlap` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:513` |
| `PaperC.SectionTwelveMoments.jointStartProbability_self` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1112` |
| `PaperC.SectionTwelveMoments.mem_overlappingPairs` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:193` |
| `PaperC.SectionTwelveMoments.mem_separatedOffDiagPairs` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:207` |
| `PaperC.SectionTwelveMoments.mem_touchingOffDiagPairs` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:200` |
| `PaperC.SectionTwelveMoments.offDiag_eq_three_distance_populations` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:254` |
| `PaperC.SectionTwelveMoments.overlappingPairs_subset_candidates` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:319` |
| `PaperC.SectionTwelveMoments.overlappingPairs_uniformLinearSubpolynomial` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1225` |
| `PaperC.SectionTwelveMoments.overlappingPairs_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1260` |
| `PaperC.SectionTwelveMoments.relationRho_twoStartSystem_cutoff_invariant` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:745` |
| `PaperC.SectionTwelveMoments.separatedOffDiagPairs_eq_separatedDyadicPairs` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:232` |
| `PaperC.SectionTwelveMoments.theorem_one_four_canonical` | conditionnel | `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/TheoremOneFourCanonical.lean:26` |
| `PaperC.SectionTwelveMoments.touchingLower_add_mem_dyadicBlock` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:814` |
| `PaperC.SectionTwelveMoments.touchingMass_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1270` |
| `PaperC.SectionTwelveMoments.touchingOffDiagPairs_eq_touchingPairs` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:214` |
| `PaperC.SectionTwelveMoments.touchingSystem_eq_twoStartSystem` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:807` |
| `PaperC.SectionTwelveMoments.touching_relationRho_small_eq_large` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:833` |
| `PaperC.SectionTwelveMoments.twoStartCompleteVertexLabel_le_dyadicCutoff` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:721` |
| `PaperC.SectionTwelveMoments.twoStartCompleteVertexLabel_pos` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:706` |
| `PaperC.SectionTwelveMoments.uniformExpectation_add` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:71` |
| `PaperC.SectionTwelveMoments.uniformExpectation_const` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:91` |
| `PaperC.SectionTwelveMoments.uniformExpectation_const_mul` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:103` |
| `PaperC.SectionTwelveMoments.uniformExpectation_dyadicCount_sq_eq_four_sectors` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1143` |
| `PaperC.SectionTwelveMoments.uniformExpectation_finset_sum` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:60` |
| `PaperC.SectionTwelveMoments.uniformExpectation_sub` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:81` |
| `PaperC.SectionTwelveMoments.uniformLittleOQuadratic_of_uniformLinear` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:1210` |
| `PaperC.SectionTwelveMoments.uniformSolutionProbability_eq_eta_mul_two_pow_rho_div` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:549` |
| `PaperC.SectionTwelveMoments.uniformVariance_eq_expectation_sq_sub_sq` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:119` |
| `PaperC.SectionTwelveMoments.uniformVariance_eq_factorial_add_mean_sub_sq` | inconditionnel | — | — | — | `PaperC/Probability/SectionTwelveMoments.lean:153` |
| `PaperC.ShallowCoreDensityCritical.four_pow_shallowCoreComponentEnvelope_uniformThreeEighths` | inconditionnel | — | — | — | `PaperC/Asymptotics/ShallowCoreDensityCritical.lean:118` |
| `PaperC.ShallowCoreDensityCritical.shallowCoreDensity_eighth_cast_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/ShallowCoreDensityCritical.lean:71` |
| `PaperC.ShallowCoreDensityCritical.shallowCoreDensity_eighth_le_runLength_cube` | inconditionnel | — | — | — | `PaperC/Asymptotics/ShallowCoreDensityCritical.lean:48` |
| `PaperC.ShallowCoreDensityCritical.sixteen_mul_shallowCoreComponentEnvelope_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/ShallowCoreDensityCritical.lean:36` |
| `PaperC.ShallowCoreMassBound.quadraticResidualWeight_le_shallowCoreEnvelopes_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCoreMassBound.lean:38` |
| `PaperC.ShallowCoreMassBound.shallowCoreQuadraticResidualMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCoreMassBound.lean:82` |
| `PaperC.ShallowCorePairs.activeShallowCorePairValues_subset_relationalHosts` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:275` |
| `PaperC.ShallowCorePairs.activeShallowCorePairs_subset` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:129` |
| `PaperC.ShallowCorePairs.canonicalResidualComponentCount_le_envelope_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:98` |
| `PaperC.ShallowCorePairs.card_activeShallowCorePairValues` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:246` |
| `PaperC.ShallowCorePairs.card_activeShallowCorePairs_le_relationalHosts` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:284` |
| `PaperC.ShallowCorePairs.card_shallowCorePairValues` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:206` |
| `PaperC.ShallowCorePairs.card_shallowCorePairs_le_sq` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:225` |
| `PaperC.ShallowCorePairs.maxShallowCoreSigma_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:335` |
| `PaperC.ShallowCorePairs.mem_activeShallowCorePairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:121` |
| `PaperC.ShallowCorePairs.mem_shallowCorePairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:76` |
| `PaperC.ShallowCorePairs.pairSigma_le_maxShallowCoreSigma` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:323` |
| `PaperC.ShallowCorePairs.pair_mem_relationalHosts_of_mem_active` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:255` |
| `PaperC.ShallowCorePairs.shallowCoreLinearResidualMass_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:294` |
| `PaperC.ShallowCorePairs.shallowCoreLinearResidualMass_eq_active` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:179` |
| `PaperC.ShallowCorePairs.shallowCorePairValues_subset_dyadicProduct` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:214` |
| `PaperC.ShallowCorePairs.shallowCoreQuadraticResidualMass_eq_active` | inconditionnel | — | — | — | `PaperC/Combinatorics/ShallowCorePairs.lean:158` |
| `PaperC.ShallowCoreSigmaCritical.four_pow_maxShallowCoreSigma_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/ShallowCoreSigmaCritical.lean:265` |
| `PaperC.ShallowCoreSigmaCritical.maxShallowCoreSigma_uniformLittleO` | inconditionnel | — | — | — | `PaperC/Asymptotics/ShallowCoreSigmaCritical.lean:196` |
| `PaperC.SigmaZeroAmbientCertificate.ambientCertificate_admissible_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:367` |
| `PaperC.SigmaZeroAmbientCertificate.ambientCertificate_card` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:257` |
| `PaperC.SigmaZeroAmbientCertificate.ambientCertificate_coe` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:248` |
| `PaperC.SigmaZeroAmbientCertificate.ambientCertificate_moduli_pairwise` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:347` |
| `PaperC.SigmaZeroAmbientCertificate.ambientCertificate_modulusProduct` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:305` |
| `PaperC.SigmaZeroAmbientCertificate.ambientLeftResidue_componentAmbientCell` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:278` |
| `PaperC.SigmaZeroAmbientCertificate.ambientModulus_componentAmbientCell` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:266` |
| `PaperC.SigmaZeroAmbientCertificate.ambientModulus_injOn_ambientCertificate` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:325` |
| `PaperC.SigmaZeroAmbientCertificate.ambientModulus_prime` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:94` |
| `PaperC.SigmaZeroAmbientCertificate.ambientRightResidue_componentAmbientCell` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:290` |
| `PaperC.SigmaZeroAmbientCertificate.canonicalResidualCertificatePrime_mem_ambientPrimes` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:121` |
| `PaperC.SigmaZeroAmbientCertificate.card_ambientCells` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:60` |
| `PaperC.SigmaZeroAmbientCertificate.componentAmbientCell_injective` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:190` |
| `PaperC.SigmaZeroAmbientCertificate.left_modEq_componentAmbientCell` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:389` |
| `PaperC.SigmaZeroAmbientCertificate.left_satisfies_ambientCertificate` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:423` |
| `PaperC.SigmaZeroAmbientCertificate.mem_ambientPrimes` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:88` |
| `PaperC.SigmaZeroAmbientCertificate.one_le_ambientCertificate_pairSolutionCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:482` |
| `PaperC.SigmaZeroAmbientCertificate.pair_left_one_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:99` |
| `PaperC.SigmaZeroAmbientCertificate.pair_mem_ambientCertificateSolutions` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:456` |
| `PaperC.SigmaZeroAmbientCertificate.pair_right_one_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:108` |
| `PaperC.SigmaZeroAmbientCertificate.right_modEq_componentAmbientCell` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:406` |
| `PaperC.SigmaZeroAmbientCertificate.right_satisfies_ambientCertificate` | inconditionnel | — | — | — | `PaperC/Combinatorics/SigmaZeroAmbientCertificate.lean:438` |
| `PaperC.SigmaZeroQuadraticCritical.card_literalSigmaZeroPairsOfCount_le_cover` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:52` |
| `PaperC.SigmaZeroQuadraticCritical.componentCount_mem_range` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:86` |
| `PaperC.SigmaZeroQuadraticCritical.mem_literalSigmaZeroPairsOfCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:40` |
| `PaperC.SigmaZeroQuadraticCritical.sigmaZeroQuadraticEnvelope_eq_corrected_mul_certificate` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:365` |
| `PaperC.SigmaZeroQuadraticCritical.sigmaZeroQuadraticEnvelope_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:440` |
| `PaperC.SigmaZeroQuadraticCritical.sigmaZeroQuadraticResidualMass_cast_le_envelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:381` |
| `PaperC.SigmaZeroQuadraticCritical.sigmaZeroQuadraticResidualMass_le_corrected_mul_cover` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:155` |
| `PaperC.SigmaZeroQuadraticCritical.sigmaZeroQuadraticResidualMass_uniformQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:507` |
| `PaperC.SigmaZeroQuadraticCritical.sum_ambientPrime_inv_sq_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:210` |
| `PaperC.SigmaZeroQuadraticCritical.sum_four_pow_componentCount_eq_fibers` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:102` |
| `PaperC.SigmaZeroQuadraticCritical.sum_four_pow_componentCount_le_cover` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:135` |
| `PaperC.SigmaZeroQuadraticCritical.sum_four_pow_mul_card_cover_cast_le_exp` | inconditionnel | — | — | — | `PaperC/Asymptotics/SigmaZeroQuadraticCritical.lean:249` |
| `PaperC.SingletonProductParametrization.canonicalCommonPart_coprime` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:109` |
| `PaperC.SingletonProductParametrization.canonicalCommonPart_dvd_first` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:341` |
| `PaperC.SingletonProductParametrization.canonicalCommonPart_dvd_second` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:409` |
| `PaperC.SingletonProductParametrization.canonicalCommonPart_le_first` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:349` |
| `PaperC.SingletonProductParametrization.canonicalCommonPart_polynomial_bound` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:455` |
| `PaperC.SingletonProductParametrization.canonicalCommonPart_pos` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:73` |
| `PaperC.SingletonProductParametrization.canonicalCommonPart_squarefree` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:98` |
| `PaperC.SingletonProductParametrization.canonicalDPart_dvd_kernel` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:62` |
| `PaperC.SingletonProductParametrization.canonicalDPart_dvd_right` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:57` |
| `PaperC.SingletonProductParametrization.canonicalDPart_le` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:335` |
| `PaperC.SingletonProductParametrization.canonicalDPart_pos` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:67` |
| `PaperC.SingletonProductParametrization.canonicalDPart_squarefree` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:91` |
| `PaperC.SingletonProductParametrization.canonicalFirstRoot_le_sqrt` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:441` |
| `PaperC.SingletonProductParametrization.canonicalSecondRoot_le_sqrt` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:448` |
| `PaperC.SingletonProductParametrization.canonical_factorizations` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:263` |
| `PaperC.SingletonProductParametrization.canonical_parts_mul` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:82` |
| `PaperC.SingletonProductParametrization.complementaryDPart_le` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:371` |
| `PaperC.SingletonProductParametrization.complementaryDPart_pos` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:117` |
| `PaperC.SingletonProductParametrization.complementaryDPart_squarefree` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:125` |
| `PaperC.SingletonProductParametrization.complementary_mul_common_squarefree` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:145` |
| `PaperC.SingletonProductParametrization.exists_singleton_product_parametrization` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:294` |
| `PaperC.SingletonProductParametrization.first_coefficient_dvd` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:356` |
| `PaperC.SingletonProductParametrization.first_coefficient_le` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:364` |
| `PaperC.SingletonProductParametrization.first_kernel_eq` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:135` |
| `PaperC.SingletonProductParametrization.first_parameters_unique` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:503` |
| `PaperC.SingletonProductParametrization.first_square_dvd` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:425` |
| `PaperC.SingletonProductParametrization.parameters_give_square_product` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:488` |
| `PaperC.SingletonProductParametrization.product_identity_of_parameters` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:467` |
| `PaperC.SingletonProductParametrization.second_coefficient_dvd` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:379` |
| `PaperC.SingletonProductParametrization.second_coefficient_le` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:394` |
| `PaperC.SingletonProductParametrization.second_kernel_eq` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:173` |
| `PaperC.SingletonProductParametrization.second_square_dvd` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:433` |
| `PaperC.SingletonProductParametrization.singleton_product_parametrization_unique` | inconditionnel | — | — | — | `PaperC/Diophantine/SingletonProductParametrization.lean:561` |
| `PaperC.SmallComponentExtraction.card_largeMembers_le_budget_div` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallComponentExtraction.lean:108` |
| `PaperC.SmallComponentExtraction.card_largeMembers_mul_succ_le_sum` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallComponentExtraction.lean:89` |
| `PaperC.SmallComponentExtraction.card_smallMembers_add_card_largeMembers` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallComponentExtraction.lean:76` |
| `PaperC.SmallComponentExtraction.disjoint_smallMembers_largeMembers` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallComponentExtraction.lean:66` |
| `PaperC.SmallComponentExtraction.mem_largeMembers` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallComponentExtraction.lean:46` |
| `PaperC.SmallComponentExtraction.mem_smallMembers` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallComponentExtraction.lean:40` |
| `PaperC.SmallComponentExtraction.smallMembers_union_largeMembers` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallComponentExtraction.lean:52` |
| `PaperC.SmallComponentExtraction.sum_component_support_sizes_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallComponentExtraction.lean:143` |
| `PaperC.SmallComponentExtraction.target_le_card_smallMembers` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallComponentExtraction.lean:120` |
| `PaperC.SmallComponentExtraction.target_small_components` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallComponentExtraction.lean:159` |
| `PaperC.SmallHeightComponentEnvelopeCritical.four_pow_smallHeightResidualComponentEnvelope_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/SmallHeightComponentEnvelopeCritical.lean:254` |
| `PaperC.SmallHeightComponentEnvelopeCritical.smallHeightResidualComponentEnvelope_uniformLittleO` | inconditionnel | — | — | — | `PaperC/Asymptotics/SmallHeightComponentEnvelopeCritical.lean:125` |
| `PaperC.SmallHeightLargeProductMassBound.activeSmallHeightLargeProductPairValues_subset_relationalHosts` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:543` |
| `PaperC.SmallHeightLargeProductMassBound.canonicalCoreExponent_le_max` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:58` |
| `PaperC.SmallHeightLargeProductMassBound.card_activeSmallHeightLargeProductPairValues` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:509` |
| `PaperC.SmallHeightLargeProductMassBound.card_activeSmallHeightLargeProductPairs_le_relationalHosts` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:553` |
| `PaperC.SmallHeightLargeProductMassBound.four_pow_le_two_mul_four_pow_sub_one` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:202` |
| `PaperC.SmallHeightLargeProductMassBound.pairTau_le_maxSmallHeightLargeProductCoreExponent` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:78` |
| `PaperC.SmallHeightLargeProductMassBound.pair_mem_relationalHosts_of_mem_active` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:519` |
| `PaperC.SmallHeightLargeProductMassBound.positiveSigmaQuadraticResidualMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:253` |
| `PaperC.SmallHeightLargeProductMassBound.positiveSigmaQuadraticResidualMass_le_uniform` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:306` |
| `PaperC.SmallHeightLargeProductMassBound.quadraticResidualWeight_le_coreFactor_mul_four_pow_sigma` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:93` |
| `PaperC.SmallHeightLargeProductMassBound.quadraticResidualWeight_le_uniformCoreFactor_mul_four_pow_sigma` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:126` |
| `PaperC.SmallHeightLargeProductMassBound.sigmaZeroQuadraticResidualMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:362` |
| `PaperC.SmallHeightLargeProductMassBound.sigmaZeroQuadraticResidualMass_le_uniform` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:415` |
| `PaperC.SmallHeightLargeProductMassBound.smallHeightLargeProductLinearResidualMass_cast_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:568` |
| `PaperC.SmallHeightLargeProductMassBound.smallHeightLargeProductQuadraticResidualMass_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:470` |
| `PaperC.SmallHeightLargeProductMassBound.smallHeightLargeProductQuadraticResidualMass_le_uniform` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:489` |
| `PaperC.SmallHeightLargeProductMassBound.sum_four_pow_pairSigma_positive_le_two_mul_rationalMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:215` |
| `PaperC.SmallHeightLargeProductMassBound.sum_four_pow_pairSigma_sub_one_le_rationalMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductMassBound.lean:160` |
| `PaperC.SmallHeightLargeProductPairs.activeSmallHeightLargeProductLinearResidualMass_eq_branches` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:312` |
| `PaperC.SmallHeightLargeProductPairs.activeSmallHeightLargeProductPairs_subset` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:127` |
| `PaperC.SmallHeightLargeProductPairs.activeSmallHeightLargeProductQuadraticResidualMass_eq_branches` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:295` |
| `PaperC.SmallHeightLargeProductPairs.card_sigmaZeroSmallHeightLargeProductPairValues` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:359` |
| `PaperC.SmallHeightLargeProductPairs.card_sigmaZeroSmallHeightLargeProductPairs_le_relationalHosts` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:407` |
| `PaperC.SmallHeightLargeProductPairs.disjoint_sigmaZero_positiveSigmaSmallHeightLargeProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:171` |
| `PaperC.SmallHeightLargeProductPairs.exists_smallHeight_candidate_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:93` |
| `PaperC.SmallHeightLargeProductPairs.mem_activeSmallHeightLargeProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:119` |
| `PaperC.SmallHeightLargeProductPairs.mem_positiveSigmaSmallHeightLargeProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:163` |
| `PaperC.SmallHeightLargeProductPairs.mem_sigmaZeroSmallHeightLargeProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:154` |
| `PaperC.SmallHeightLargeProductPairs.mem_smallHeightLargeProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:76` |
| `PaperC.SmallHeightLargeProductPairs.pair_mem_relationalHosts_of_mem_sigmaZero` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:369` |
| `PaperC.SmallHeightLargeProductPairs.sigmaZeroSmallHeightLargeProductPairValues_subset_relationalHosts` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:396` |
| `PaperC.SmallHeightLargeProductPairs.sigmaZero_union_positiveSigma_eq_activeSmallHeightLargeProductPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:182` |
| `PaperC.SmallHeightLargeProductPairs.smallHeightLargeProductLinearResidualMass_eq_active` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:273` |
| `PaperC.SmallHeightLargeProductPairs.smallHeightLargeProductLinearResidualMass_eq_branches` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:341` |
| `PaperC.SmallHeightLargeProductPairs.smallHeightLargeProductQuadraticResidualMass_eq_active` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:251` |
| `PaperC.SmallHeightLargeProductPairs.smallHeightLargeProductQuadraticResidualMass_eq_branches` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightLargeProductPairs.lean:329` |
| `PaperC.SmallHeightPositiveSigmaCritical.positiveSigmaQuadraticResidualMass_uniformFiveThird` | inconditionnel | — | — | — | `PaperC/Asymptotics/SmallHeightPositiveSigmaCritical.lean:45` |
| `PaperC.SmallHeightPositiveSigmaSystematicBound.four_pow_le_two_mul_four_pow_sub_one` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightPositiveSigmaSystematicBound.lean:75` |
| `PaperC.SmallHeightPositiveSigmaSystematicBound.positiveSigmaQuadraticResidualMass_le_tauEnvelope_mul_systematicSum` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightPositiveSigmaSystematicBound.lean:155` |
| `PaperC.SmallHeightPositiveSigmaSystematicBound.positiveSigmaQuadraticResidualMass_le_two_mul_tauEnvelope_mul_rationalMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightPositiveSigmaSystematicBound.lean:194` |
| `PaperC.SmallHeightPositiveSigmaSystematicBound.quadraticResidualWeight_le_tauEnvelope_mul_four_pow_pairSigma_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightPositiveSigmaSystematicBound.lean:121` |
| `PaperC.SmallHeightPositiveSigmaSystematicBound.sum_four_pow_pairSigma_positive_le_two_mul_rationalMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightPositiveSigmaSystematicBound.lean:88` |
| `PaperC.SmallHeightPositiveSigmaSystematicBound.sum_four_pow_pairSigma_sub_one_le_rationalMass` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightPositiveSigmaSystematicBound.lean:33` |
| `PaperC.SmallHeightResidualComponentEnvelope.height_le_natSqrt_natLog_of_le_realSqrt_realLog` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightResidualComponentEnvelope.lean:51` |
| `PaperC.SmallHeightResidualComponentEnvelope.pairResidualComponentCount_le_envelope_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightResidualComponentEnvelope.lean:110` |
| `PaperC.SmallHeightResidualComponentEnvelope.primeCount_mono` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightResidualComponentEnvelope.lean:91` |
| `PaperC.SmallHeightResidualPrimeSupport.abs_residualVertexExpression_lt_four_mul_max_of_candidate` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightResidualPrimeSupport.lean:43` |
| `PaperC.SmallHeightResidualPrimeSupport.canonicalResidualCertificates_prime_lt_four_mul_max_of_not_onChannel` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightResidualPrimeSupport.lean:136` |
| `PaperC.SmallHeightResidualPrimeSupport.canonicalResidualComponentCount_le_two_add_primeCount_of_choice` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightResidualPrimeSupport.lean:386` |
| `PaperC.SmallHeightResidualPrimeSupport.card_exactCanonicalResidualCertificates_le_two_of_choice` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightResidualPrimeSupport.lean:226` |
| `PaperC.SmallHeightResidualPrimeSupport.card_nonexactCanonicalResidualCertificates_le_primeCount` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightResidualPrimeSupport.lean:336` |
| `PaperC.SmallHeightResidualPrimeSupport.mem_exactCanonicalResidualCertificates` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightResidualPrimeSupport.lean:207` |
| `PaperC.SmallHeightResidualPrimeSupport.mem_nonexactCanonicalResidualCertificates` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightResidualPrimeSupport.lean:318` |
| `PaperC.SmallHeightSigmaZeroCritical.maxSmallHeightLargeProductCoreExponent_le_tauEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/SmallHeightSigmaZeroCritical.lean:37` |
| `PaperC.SmallHeightSigmaZeroCritical.sigmaZeroQuadraticResidualMass_le_tauEnvelope_mul_hosts` | inconditionnel | — | — | — | `PaperC/Asymptotics/SmallHeightSigmaZeroCritical.lean:76` |
| `PaperC.SmallHeightSigmaZeroCritical.sigmaZeroQuadraticResidualMass_uniformThreeHalves` | inconditionnel | — | — | — | `PaperC/Asymptotics/SmallHeightSigmaZeroCritical.lean:113` |
| `PaperC.SmallHeightSigmaZeroCritical.smallHeightLargeProductCoreFactor_le_four_pow_tauEnvelope` | inconditionnel | — | — | — | `PaperC/Asymptotics/SmallHeightSigmaZeroCritical.lean:63` |
| `PaperC.SmallHeightTauEnvelope.four_pow_pairTau_le_canonicalCorrected_mul_residual` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightTauEnvelope.lean:81` |
| `PaperC.SmallHeightTauEnvelope.four_pow_pairTau_le_four_pow_smallHeightTauEnvelope_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightTauEnvelope.lean:117` |
| `PaperC.SmallHeightTauEnvelope.four_pow_pairTau_le_maxCorrected_mul_residualEnvelope_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightTauEnvelope.lean:132` |
| `PaperC.SmallHeightTauEnvelope.four_pow_smallHeightTauEnvelope_eq` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightTauEnvelope.lean:108` |
| `PaperC.SmallHeightTauEnvelope.pairTau_le_smallHeightTauEnvelope_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/SmallHeightTauEnvelope.lean:48` |
| `PaperC.SmallHeightTauEnvelopeCritical.four_pow_smallHeightTauEnvelope_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/SmallHeightTauEnvelopeCritical.lean:30` |
| `PaperC.SpatialLaplaceCritical.abs_averagedGoodSpatialLaplace_sub_exp_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:211` |
| `PaperC.SpatialLaplaceCritical.abs_exp_neg_good_sub_full_le_badCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:419` |
| `PaperC.SpatialLaplaceCritical.abs_exp_neg_sub_exp_neg_le` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:388` |
| `PaperC.SpatialLaplaceCritical.abs_finiteSpatialLaplaceExpectation_sub_averagedGood_le_badMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:572` |
| `PaperC.SpatialLaplaceCritical.abs_finiteSpatialLaplaceFunctional_sub_good_le_count` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:524` |
| `PaperC.SpatialLaplaceCritical.abs_finiteSpatialLaplace_sub_exp_le` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:645` |
| `PaperC.SpatialLaplaceCritical.abs_finiteSpatialLaplace_sub_exp_le_error` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:696` |
| `PaperC.SpatialLaplaceCritical.averagedGoodSpatialLaplaceExpectation_eq_fullPMF` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:130` |
| `PaperC.SpatialLaplaceCritical.conditionalSpatialParameter_eq_good` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:178` |
| `PaperC.SpatialLaplaceCritical.dyadicBlock_sdiff_goodStarts_eq_terminalBadStarts` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:281` |
| `PaperC.SpatialLaplaceCritical.exponentialFunctional_conditionedGood_eq` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:100` |
| `PaperC.SpatialLaplaceCritical.finiteGoodSpatialLaplaceFunctional_mem_unitInterval` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:504` |
| `PaperC.SpatialLaplaceCritical.finiteSpatialLaplaceExpectation_eq_fullPMF` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:163` |
| `PaperC.SpatialLaplaceCritical.finiteSpatialLaplaceFunctional_eq_good_of_no_bad` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:445` |
| `PaperC.SpatialLaplaceCritical.finiteSpatialLaplaceFunctional_mem_unitInterval` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:484` |
| `PaperC.SpatialLaplaceCritical.goodSpatialThinnedParameter_le_full` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:353` |
| `PaperC.SpatialLaplaceCritical.goodSpatialThinnedParameter_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:343` |
| `PaperC.SpatialLaplaceCritical.goodStarts_subset_dyadicBlock` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:298` |
| `PaperC.SpatialLaplaceCritical.sectionFourteenTwo_spatialLaplaceFunctional` | conditionnel | `AGG89-T1-finite-dependency-b3-zero`, `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:918` |
| `PaperC.SpatialLaplaceCritical.sectionFourteenTwo_spatialLaplaceFunctional_of_homogeneousMass` | conditionnel | `AGG89-T1-finite-dependency-b3-zero` | `external` | `open` | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:850` |
| `PaperC.SpatialLaplaceCritical.spatialLaplaceError_uniformLittleOOne` | conditionnel | `ES86-T1b-Q-split-n2`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:796` |
| `PaperC.SpatialLaplaceCritical.spatialLaplaceError_uniformLittleOOne_of_homogeneousMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:718` |
| `PaperC.SpatialLaplaceCritical.spatialThinnedParameter_sub_good_eq_badSum` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:304` |
| `PaperC.SpatialLaplaceCritical.spatialThinnedParameter_sub_good_le_badCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/SpatialLaplaceCritical.lean:366` |
| `PaperC.SpatialMarkedParameters.continuousOn_spatialRetention` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:32` |
| `PaperC.SpatialMarkedParameters.continuous_markedRetentionIntegrand` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:251` |
| `PaperC.SpatialMarkedParameters.continuous_spatialRetention` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:27` |
| `PaperC.SpatialMarkedParameters.geometricMarkWeight_eq_half_pow` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:136` |
| `PaperC.SpatialMarkedParameters.geometricMarkWeight_nonneg` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:131` |
| `PaperC.SpatialMarkedParameters.hasSum_geometricMarkWeight` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:141` |
| `PaperC.SpatialMarkedParameters.integral_markedRetentionIntegrand` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:274` |
| `PaperC.SpatialMarkedParameters.markedRetentionIntegrand_nonneg` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:264` |
| `PaperC.SpatialMarkedParameters.markedThinnedParameter_eq_literal` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:212` |
| `PaperC.SpatialMarkedParameters.spatialRetention_le_one` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:47` |
| `PaperC.SpatialMarkedParameters.spatialRetention_nonneg` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:40` |
| `PaperC.SpatialMarkedParameters.spatialThinnedParameter_eq_scale_mul` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:68` |
| `PaperC.SpatialMarkedParameters.tendsto_exp_neg_markedThinnedParameter` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:345` |
| `PaperC.SpatialMarkedParameters.tendsto_exp_neg_spatialThinnedParameter` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:110` |
| `PaperC.SpatialMarkedParameters.tendsto_geometricMarkWeight_tail_zero` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:183` |
| `PaperC.SpatialMarkedParameters.tendsto_markedThinnedParameter` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:303` |
| `PaperC.SpatialMarkedParameters.tendsto_spatialThinnedParameter` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:81` |
| `PaperC.SpatialMarkedParameters.tsum_geometricMarkWeight` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:156` |
| `PaperC.SpatialMarkedParameters.tsum_geometricMarkWeight_tail` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialMarkedParameters.lean:164` |
| `PaperC.SpatialRiemannSums.continuous_dyadicClamp` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialRiemannSums.lean:316` |
| `PaperC.SpatialRiemannSums.dyadicClamp_eq_self` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialRiemannSums.lean:327` |
| `PaperC.SpatialRiemannSums.dyadicClamp_mem_Icc` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialRiemannSums.lean:320` |
| `PaperC.SpatialRiemannSums.spatialRiemannSum_eq_dyadicRiemannSum` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialRiemannSums.lean:272` |
| `PaperC.SpatialRiemannSums.tendsto_dyadicRiemannSum` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialRiemannSums.lean:303` |
| `PaperC.SpatialRiemannSums.tendsto_dyadicRiemannSum_of_continuousOn` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialRiemannSums.lean:373` |
| `PaperC.SpatialRiemannSums.tendsto_spatialRiemannSum` | inconditionnel | — | — | — | `PaperC/Analysis/SpatialRiemannSums.lean:103` |
| `PaperC.SpatialThinningFinite.eventProbability_noRetainedActive_eq_prod` | inconditionnel | — | — | — | `PaperC/Probability/SpatialThinningFinite.lean:134` |
| `PaperC.SpatialThinningFinite.eventProbability_noRetainedActive_exponential_eq` | inconditionnel | — | — | — | `PaperC/Probability/SpatialThinningFinite.lean:197` |
| `PaperC.SpatialThinningFinite.eventProbability_thinnedCount_zero_exponential_eq` | inconditionnel | — | — | — | `PaperC/Probability/SpatialThinningFinite.lean:237` |
| `PaperC.SpatialThinningFinite.exponentialRetention_le_one` | inconditionnel | — | — | — | `PaperC/Probability/SpatialThinningFinite.lean:186` |
| `PaperC.SpatialThinningFinite.exponentialRetention_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/SpatialThinningFinite.lean:178` |
| `PaperC.SpatialThinningFinite.sum_pair_retention_mul_le_sum` | inconditionnel | — | — | — | `PaperC/Probability/SpatialThinningFinite.lean:275` |
| `PaperC.SpatialThinningFinite.sum_retention_mul_le_sum` | inconditionnel | — | — | — | `PaperC/Probability/SpatialThinningFinite.lean:262` |
| `PaperC.SpatialThinningFinite.thinnedCount_eq_zero_iff` | inconditionnel | — | — | — | `PaperC/Probability/SpatialThinningFinite.lean:73` |
| `PaperC.SpatialThinningFinite.voidIndicator_mul_product_eq` | inconditionnel | — | — | — | `PaperC/Probability/SpatialThinningFinite.lean:99` |
| `PaperC.SquarefreeSmoothCount.card_squarefreeSmoothUpTo_le_two_pow` | inconditionnel | — | — | — | `PaperC/Arithmetic/SquarefreeSmoothCount.lean:66` |
| `PaperC.SquarefreeSmoothCount.mem_squarefreeSmoothUpTo` | inconditionnel | — | — | — | `PaperC/Arithmetic/SquarefreeSmoothCount.lean:28` |
| `PaperC.SquarefreeSmoothCount.primeFactors_injective_on_squarefreeSmoothUpTo` | inconditionnel | — | — | — | `PaperC/Arithmetic/SquarefreeSmoothCount.lean:44` |
| `PaperC.SquarefreeSmoothCount.primeFactors_subset_smallPrimesUpTo` | inconditionnel | — | — | — | `PaperC/Arithmetic/SquarefreeSmoothCount.lean:35` |
| `PaperC.SquarefreeSmoothCritical.primeNumberTheorem_implies_squarefreeSmooth_bound` | conditionnel | `ADGR07-PNT` | `external` | `open` | `PaperC/Asymptotics/SquarefreeSmoothCritical.lean:28` |
| `PaperC.StartEvent.eq_at_offset` | inconditionnel | — | — | — | `PaperC/Runs/Starts.lean:40` |
| `PaperC.StartEvent.eq_at_zero` | inconditionnel | — | — | — | `PaperC/Runs/Starts.lean:46` |
| `PaperC.StartEvent.eq_of_mem_run` | inconditionnel | — | — | — | `PaperC/Runs/Starts.lean:58` |
| `PaperC.StartEvent.eq_on_run` | inconditionnel | — | — | — | `PaperC/Runs/Starts.lean:51` |
| `PaperC.StartEvent.left_boundary` | inconditionnel | — | — | — | `PaperC/Runs/Starts.lean:35` |
| `PaperC.StartEvent.left_ne` | inconditionnel | — | — | — | `PaperC/Runs/Starts.lean:65` |
| `PaperC.StartEvent.not_of_lt` | inconditionnel | — | — | — | `PaperC/Runs/Starts.lean:89` |
| `PaperC.SteinChenCritical.dyadicLength_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/SteinChenCritical.lean:58` |
| `PaperC.SteinChenCritical.separatedDefectMass_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/SteinChenCritical.lean:129` |
| `PaperC.SteinChenCritical.steinBOneNumerator_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/SteinChenCritical.lean:221` |
| `PaperC.SteinChenCritical.steinBOne_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/SteinChenCritical.lean:249` |
| `PaperC.SteinChenCritical.steinBTwoAverage_uniformLittleOOne_of_propositionElevenTwo` | inconditionnel | — | — | — | `PaperC/Asymptotics/SteinChenCritical.lean:324` |
| `PaperC.SteinChenCritical.steinBTwoNumerator_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/SteinChenCritical.lean:292` |
| `PaperC.SteinChenCritical.touchingOffDiagPairs_uniformLittleOQuadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/SteinChenCritical.lean:81` |
| `PaperC.SteinChenTerms.card_closedDependencyPairs` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:65` |
| `PaperC.SteinChenTerms.card_goodStarts_le` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:76` |
| `PaperC.SteinChenTerms.disjoint_goodDiag_orderedDependencyEdges` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:54` |
| `PaperC.SteinChenTerms.disjoint_overlapDependencyEdges_separated` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:179` |
| `PaperC.SteinChenTerms.disjoint_overlapDependencyEdges_touching` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:168` |
| `PaperC.SteinChenTerms.disjoint_touchingDependencyEdges_separated` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:190` |
| `PaperC.SteinChenTerms.jointDefectMass_mono` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:257` |
| `PaperC.SteinChenTerms.jointPairMass_mono` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:247` |
| `PaperC.SteinChenTerms.jointPairMass_overlapDependencyEdges_eq_zero` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:225` |
| `PaperC.SteinChenTerms.jointPairMass_separatedDependencyEdges_le` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:276` |
| `PaperC.SteinChenTerms.jointPairMass_touchingDependencyEdges_le` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:266` |
| `PaperC.SteinChenTerms.jointPairMass_touchingDependencyEdges_le_complete` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:318` |
| `PaperC.SteinChenTerms.jointStartProbability_nonneg` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:239` |
| `PaperC.SteinChenTerms.mem_closedDependencyPairs` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:46` |
| `PaperC.SteinChenTerms.orderedDependencyEdges_eq_three_parts` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:143` |
| `PaperC.SteinChenTerms.orderedDependencyEdges_subset_offDiag` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:132` |
| `PaperC.SteinChenTerms.steinBOne_eq_card_div` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:94` |
| `PaperC.SteinChenTerms.steinBOne_le` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:105` |
| `PaperC.SteinChenTerms.steinBTwoAverage_eq_three_parts` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:209` |
| `PaperC.SteinChenTerms.steinBTwoAverage_le` | inconditionnel | — | — | — | `PaperC/Probability/SteinChenTerms.lean:346` |
| `PaperC.TerminalBadStartBound.card_terminalBadStarts_terminalPrimeCutoff_le` | inconditionnel | — | — | — | `PaperC/Probability/TerminalBadStartBound.lean:91` |
| `PaperC.TerminalBadStartBound.card_terminalBadStarts_terminalPrimeCutoff_le_readable` | inconditionnel | — | — | — | `PaperC/Probability/TerminalBadStartBound.lean:330` |
| `PaperC.TerminalBadStartBound.card_terminalBadStarts_terminalPrimeCutoff_le_scale` | inconditionnel | — | — | — | `PaperC/Probability/TerminalBadStartBound.lean:308` |
| `PaperC.TerminalBadStartBound.card_terminalBadStarts_terminalPrimeCutoff_le_with_B` | inconditionnel | — | — | — | `PaperC/Probability/TerminalBadStartBound.lean:353` |
| `PaperC.TerminalBadStartBound.sixteen_le_terminalPrimeCutoff` | inconditionnel | — | — | — | `PaperC/Probability/TerminalBadStartBound.lean:79` |
| `PaperC.TerminalBadStartBound.terminalBadStartPrimeExponent_le_scaleExponent` | inconditionnel | — | — | — | `PaperC/Probability/TerminalBadStartBound.lean:128` |
| `PaperC.TerminalBadStartBound.terminalBadStartScaleExponent_le_readableExponent` | inconditionnel | — | — | — | `PaperC/Probability/TerminalBadStartBound.lean:198` |
| `PaperC.TerminalBadStartsCritical.normalized_terminalBadStarts_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/TerminalBadStartsCritical.lean:370` |
| `PaperC.TerminalBadStartsCritical.terminalBadStartReadableExponent_le_div` | inconditionnel | — | — | — | `PaperC/Asymptotics/TerminalBadStartsCritical.lean:40` |
| `PaperC.TerminalBadStartsCritical.terminalBadStartResidual_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/TerminalBadStartsCritical.lean:248` |
| `PaperC.TerminalBadStartsCritical.terminalBadStarts_terminalCutoff_uniformHalfPower` | inconditionnel | — | — | — | `PaperC/Asymptotics/TerminalBadStartsCritical.lean:270` |
| `PaperC.TerminalBadStartsCritical.terminalBadStarts_terminalCutoff_uniformLittleOLinear` | inconditionnel | — | — | — | `PaperC/Asymptotics/TerminalBadStartsCritical.lean:344` |
| `PaperC.TerminalBadStartsCritical.terminalExponentFactor_uniformSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/TerminalBadStartsCritical.lean:122` |
| `PaperC.TerminalClosureCounting.card_filter_large_le_one` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalClosureCounting.lean:39` |
| `PaperC.TerminalClosureCounting.card_incidences_eq_sum_left_fibers` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalClosureCounting.lean:119` |
| `PaperC.TerminalClosureCounting.card_incidences_eq_sum_right_fibers` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalClosureCounting.lean:106` |
| `PaperC.TerminalClosureCounting.card_left_le_twice_card_right` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalClosureCounting.lean:205` |
| `PaperC.TerminalClosureCounting.eq_of_both_large` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalClosureCounting.lean:64` |
| `PaperC.TerminalClosureCounting.incidence_double_count` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalClosureCounting.lean:137` |
| `PaperC.TerminalClosureCounting.incidence_half_specialization` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalClosureCounting.lean:185` |
| `PaperC.TerminalClosureCounting.mem_incidences` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalClosureCounting.lean:95` |
| `PaperC.TerminalClosureCounting.sum_le_card_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalClosureCounting.lean:234` |
| `PaperC.TerminalClosureCounting.sum_two_pow_sub_one_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalClosureCounting.lean:261` |
| `PaperC.TerminalClosureCounting.two_pow_sub_one_le_four_mul_two_pow` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalClosureCounting.lean:247` |
| `PaperC.TerminalComponentCount.card_largeComponents_le_two_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalComponentCount.lean:94` |
| `PaperC.TerminalComponentCount.card_pairComponents_ge_sub_three_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalComponentCount.lean:142` |
| `PaperC.TerminalComponentCount.connectedComponent_terminal_count` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalComponentCount.lean:199` |
| `PaperC.TerminalComponentCount.disjoint_pairComponents_largeComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalComponentCount.lean:76` |
| `PaperC.TerminalComponentCount.mem_largeComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalComponentCount.lean:48` |
| `PaperC.TerminalComponentCount.mem_pairComponents` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalComponentCount.lean:41` |
| `PaperC.TerminalComponentCount.pair_union_large_eq` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalComponentCount.lean:58` |
| `PaperC.TerminalComponentCount.terminal_component_count` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalComponentCount.lean:161` |
| `PaperC.TerminalComponentCount.terminal_component_count_of_card_eq_sub` | inconditionnel | — | — | — | `PaperC/Combinatorics/TerminalComponentCount.lean:177` |
| `PaperC.TerminalKernelCount.canonicalTerminalKernelTriple_injective_of_ne_zero` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalKernelCount.lean:78` |
| `PaperC.TerminalKernelCount.canonicalTerminalKernelTriple_mem` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalKernelCount.lean:108` |
| `PaperC.TerminalKernelCount.canonicalTerminalKernelTriples_subset` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalKernelCount.lean:155` |
| `PaperC.TerminalKernelCount.card_boundedLargeKernelValues_cast_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalKernelCount.lean:283` |
| `PaperC.TerminalKernelCount.card_boundedLargeKernelValues_cast_le_exp` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalKernelCount.lean:357` |
| `PaperC.TerminalKernelCount.card_boundedLargeKernelValues_cast_le_weight_sums` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalKernelCount.lean:247` |
| `PaperC.TerminalKernelCount.card_boundedLargeKernelValues_le_sqrt_sum` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalKernelCount.lean:181` |
| `PaperC.TerminalKernelCount.card_canonicalTerminalKernelTriples` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalKernelCount.lean:165` |
| `PaperC.TerminalKernelCount.cast_sqrt_div_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalKernelCount.lean:206` |
| `PaperC.TerminalKernelCount.cast_sqrt_div_small_mul_kernel_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalKernelCount.lean:225` |
| `PaperC.TerminalKernelCount.mem_boundedLargeKernelValues` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalKernelCount.lean:47` |
| `PaperC.TerminalMatching.abs_crossDeterminant_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:472` |
| `PaperC.TerminalMatching.abs_crossDeterminant_startCompleteVertexLabel_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:520` |
| `PaperC.TerminalMatching.componentVertices_eq_pair_of_card_eq_two` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:148` |
| `PaperC.TerminalMatching.crossDeterminant_eq_zero_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:54` |
| `PaperC.TerminalMatching.crossDeterminant_ne_zero_of_nonaligned` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:62` |
| `PaperC.TerminalMatching.largeOddKernel_coprime_of_distinct_components` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:341` |
| `PaperC.TerminalMatching.largeOddKernel_eq_of_two_vertex_component` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:230` |
| `PaperC.TerminalMatching.largeOddKernel_eq_one_iff_isDefective` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:268` |
| `PaperC.TerminalMatching.largeOddKernel_product_dvd_crossDeterminant` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:91` |
| `PaperC.TerminalMatching.mem_largeOddPrimeSupport_vertexLabel` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:116` |
| `PaperC.TerminalMatching.mem_primeOccurrences_other_of_two_vertex_component` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:180` |
| `PaperC.TerminalMatching.not_isDefective_of_distinct_mem_component` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:297` |
| `PaperC.TerminalMatching.one_lt_largeOddKernel_of_not_isDefective` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:321` |
| `PaperC.TerminalMatching.product_dvd_crossDeterminant` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:73` |
| `PaperC.TerminalMatching.two_vertex_components_kernel_package` | inconditionnel | — | — | — | `PaperC/Arithmetic/TerminalMatching.lean:385` |
| `PaperC.TerminalPartnerPell.canonicalSquarePart_le_sqrt` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:194` |
| `PaperC.TerminalPartnerPell.canonical_decompositions_give_partner_box` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:344` |
| `PaperC.TerminalPartnerPell.canonical_decompositions_give_pell` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:394` |
| `PaperC.TerminalPartnerPell.canonical_terminal_coefficient_dvd` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:169` |
| `PaperC.TerminalPartnerPell.canonical_terminal_coefficient_le` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:187` |
| `PaperC.TerminalPartnerPell.canonical_terminal_coefficient_ratio_not_isSquare` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:234` |
| `PaperC.TerminalPartnerPell.canonical_terminal_coefficient_squarefree` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:218` |
| `PaperC.TerminalPartnerPell.canonical_terminal_factorization` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:148` |
| `PaperC.TerminalPartnerPell.not_isSquare_ratio_of_squarefree_of_ne` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:62` |
| `PaperC.TerminalPartnerPell.partnerToPell_injective_on` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:419` |
| `PaperC.TerminalPartnerPell.terminalPartnerPolynomialBox_of_generalizedPell` | conditionnel | `PCv07c-L9.2-generalized-Pell` | `internal` | `discharged` | `PaperC/Diophantine/TerminalPartnerPell.lean:519` |
| `PaperC.TerminalPartnerPell.terminalPartnerWitnessBox_atMost` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:450` |
| `PaperC.TerminalPartnerPell.terminalPartnerWitness_maps_to_pell` | inconditionnel | — | — | — | `PaperC/Diophantine/TerminalPartnerPell.lean:373` |
| `PaperC.TerminalPrimeCutoff.badStart_cutoff_comparisons` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:139` |
| `PaperC.TerminalPrimeCutoff.cast_terminalPrimeCutoff_le_scale` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:41` |
| `PaperC.TerminalPrimeCutoff.cutoff_between_linear_and_cubic` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:130` |
| `PaperC.TerminalPrimeCutoff.le_terminalPrimeCutoff` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:66` |
| `PaperC.TerminalPrimeCutoff.terminalPrimeCutoff_le_cube` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:107` |
| `PaperC.TerminalPrimeCutoff.terminalPrimeCutoff_mono` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:178` |
| `PaperC.TerminalPrimeCutoff.terminalPrimeCutoff_one` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:56` |
| `PaperC.TerminalPrimeCutoff.terminalPrimeCutoff_pos` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:96` |
| `PaperC.TerminalPrimeCutoff.terminalPrimeCutoff_zero` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:51` |
| `PaperC.TerminalPrimeCutoff.terminalPrimeScale_lt_cutoff_add_one` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:46` |
| `PaperC.TerminalPrimeCutoff.terminalPrimeScale_mono` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:157` |
| `PaperC.TerminalPrimeCutoff.terminalPrimeScale_nonneg` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:34` |
| `PaperC.TerminalPrimeCutoff.window_succ_le_terminalPrimeCutoff` | inconditionnel | — | — | — | `PaperC/Analysis/TerminalPrimeCutoff.lean:146` |
| `PaperC.TheoremEightAlignedClosure.alignedHammingNumerics_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremEightAlignedClosure.lean:182` |
| `PaperC.TheoremEightAlignedClosure.componentHammingRadius_cast_le_real_log` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremEightAlignedClosure.lean:113` |
| `PaperC.TheoremEightAlignedClosure.no_aligned_deep_core_eventually` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremEightAlignedClosure.lean:260` |
| `PaperC.TheoremEightAlignedClosure.real_log_product_le_dyadic_log_product` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremEightAlignedClosure.lean:39` |
| `PaperC.TheoremEightHammingBudget.componentHammingRadius_cast_le` | inconditionnel | — | — | — | `PaperC/Coding/TheoremEightHammingBudget.lean:137` |
| `PaperC.TheoremEightHammingBudget.componentHammingRadius_conditions` | inconditionnel | — | — | — | `PaperC/Coding/TheoremEightHammingBudget.lean:355` |
| `PaperC.TheoremEightHammingBudget.componentHammingRadius_conditions_of_loglog` | inconditionnel | — | — | — | `PaperC/Coding/TheoremEightHammingBudget.lean:483` |
| `PaperC.TheoremEightHammingBudget.componentHammingRadius_conditions_runLengthWindow_eventually` | inconditionnel | — | — | — | `PaperC/Coding/TheoremEightHammingBudget.lean:504` |
| `PaperC.TheoremEightHammingBudget.exists_nonzero_kernel_word_of_component_density` | inconditionnel | — | — | — | `PaperC/Coding/TheoremEightHammingBudget.lean:559` |
| `PaperC.TheoremEightHammingBudget.log_linear_le_of_loglog` | inconditionnel | — | — | — | `PaperC/Coding/TheoremEightHammingBudget.lean:102` |
| `PaperC.TheoremEightHammingBudget.primeRows_le_radius_mul_loglog` | inconditionnel | — | — | — | `PaperC/Coding/TheoremEightHammingBudget.lean:230` |
| `PaperC.TheoremEightHammingBudget.radius_denominator_le` | inconditionnel | — | — | — | `PaperC/Coding/TheoremEightHammingBudget.lean:60` |
| `PaperC.TheoremEightHammingBudget.radius_mul_log_budget` | inconditionnel | — | — | — | `PaperC/Coding/TheoremEightHammingBudget.lean:290` |
| `PaperC.TheoremEightHammingBudget.sixty_four_le_componentHammingRadius` | inconditionnel | — | — | — | `PaperC/Coding/TheoremEightHammingBudget.lean:190` |
| `PaperC.TheoremSixteenTwo.abs_globalMean_sub_retainedMean_eq_deepMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:792` |
| `PaperC.TheoremSixteenTwo.abs_mass_zero_sub_le_two_mul_natTotalVariation` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:1167` |
| `PaperC.TheoremSixteenTwo.boundedFullStartLaw_eq_retainedStartLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:862` |
| `PaperC.TheoremSixteenTwo.boundedFullStartMean_eq_retainedStartMean` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:884` |
| `PaperC.TheoremSixteenTwo.boundedFullStartRate_eq_retainedStartRate` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:907` |
| `PaperC.TheoremSixteenTwo.boundedRatioBlock_div_eq_retainedStartIndices` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:828` |
| `PaperC.TheoremSixteenTwo.boundedRatioCutoff_le_globalCylinderCutoff` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:836` |
| `PaperC.TheoremSixteenTwo.commonCylinderStartProbability_eq_globalStartProbability` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:746` |
| `PaperC.TheoremSixteenTwo.criticalScale_le_balanceConstant` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:1082` |
| `PaperC.TheoremSixteenTwo.criticalScale_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:1157` |
| `PaperC.TheoremSixteenTwo.disagreementProbability_global_retained_le_discardedMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:360` |
| `PaperC.TheoremSixteenTwo.discardedStartMass_eq_deepStartProbabilityMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:769` |
| `PaperC.TheoremSixteenTwo.discardedStartMass_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:182` |
| `PaperC.TheoremSixteenTwo.discarded_retained_disjoint` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:300` |
| `PaperC.TheoremSixteenTwo.exists_discarded_start_of_counts_ne` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:339` |
| `PaperC.TheoremSixteenTwo.globalStartCount_eq_discarded_add_retained` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:313` |
| `PaperC.TheoremSixteenTwo.globalStartCount_restrictToFinite_eq_infiniteGlobalStartCount` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwoInfiniteModel.lean:53` |
| `PaperC.TheoremSixteenTwo.globalStartIndices_eq_discarded_union_retained` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:282` |
| `PaperC.TheoremSixteenTwo.globalStartLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:196` |
| `PaperC.TheoremSixteenTwo.globalStartMean_eq_discarded_add_retained` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:325` |
| `PaperC.TheoremSixteenTwo.globalStartMean_eq_expectation` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:219` |
| `PaperC.TheoremSixteenTwo.globalStartMean_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:174` |
| `PaperC.TheoremSixteenTwo.infiniteGlobalEmptyProbability_eq_globalEmptyProbability` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwoInfiniteModel.lean:160` |
| `PaperC.TheoremSixteenTwo.infiniteGlobalStartCountEvent_eq_preimage` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwoInfiniteModel.lean:91` |
| `PaperC.TheoremSixteenTwo.infiniteGlobalStartCount_law_eq_globalStartLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwoInfiniteModel.lean:130` |
| `PaperC.TheoremSixteenTwo.lowerBalanceConstant_le_criticalScale` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:1103` |
| `PaperC.TheoremSixteenTwo.lowerBalanceConstant_pos` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:1097` |
| `PaperC.TheoremSixteenTwo.measurableSet_finiteGlobalStartCountEvent` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwoInfiniteModel.lean:107` |
| `PaperC.TheoremSixteenTwo.measurableSet_infiniteGlobalStartCountEvent` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwoInfiniteModel.lean:113` |
| `PaperC.TheoremSixteenTwo.natTotalVariation_global_retained_le_deepMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:782` |
| `PaperC.TheoremSixteenTwo.natTotalVariation_global_retained_le_discardedMass` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:427` |
| `PaperC.TheoremSixteenTwo.poissonPMFReal_zero_eq_exp_neg` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:1205` |
| `PaperC.TheoremSixteenTwo.retainedStartLaw_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:200` |
| `PaperC.TheoremSixteenTwo.retainedStartMean_eq_expectation` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:250` |
| `PaperC.TheoremSixteenTwo.retainedStartMean_nonneg` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:178` |
| `PaperC.TheoremSixteenTwo.retained_window_le_boundedRatioCutoff` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:851` |
| `PaperC.TheoremSixteenTwo.startAt_assemble_iff_local` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:595` |
| `PaperC.TheoremSixteenTwo.startAt_sampleSpaceEquivLocalProd_iff` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:644` |
| `PaperC.TheoremSixteenTwo.summable_globalStartLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:188` |
| `PaperC.TheoremSixteenTwo.summable_retainedStartLaw` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:192` |
| `PaperC.TheoremSixteenTwo.theorem_sixteen_two` | conditionnel | `ADGR07-PNT`, `AGG89-T1-finite-dependency-b3-zero`, `BS93-Theorem-1`, `ES86-T1b-Q-split-n2`, `LS04-Corollary-1`, `PCv07c-L17.26-bounded-ratio-many-defects`, `PCv07c-L17.28-bounded-ratio-nonterminal-sector`, `PCv07c-L17.30-bounded-ratio-terminal-sector`, `PCv07c-L9.2-generalized-Pell` | `external`, `internal` | `discharged`, `open` | `PaperC/Asymptotics/TheoremSixteenTwo.lean:1617` |
| `PaperC.TheoremSixteenTwo.theorem_sixteen_two_canonical` | conditionnel | `ADGR07-PNT`, `AGG89-T1-finite-dependency-b3-zero`, `BS93-Theorem-1`, `ES86-T1b-Q-split-n2`, `LS04-Corollary-1`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/TheoremSixteenTwo.lean:1682` |
| `PaperC.TheoremSixteenTwo.theorem_sixteen_two_infinite_model` | conditionnel | `ADGR07-PNT`, `AGG89-T1-finite-dependency-b3-zero`, `BS93-Theorem-1`, `ES86-T1b-Q-split-n2`, `LS04-Corollary-1`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/TheoremSixteenTwoInfiniteModel.lean:194` |
| `PaperC.TheoremSixteenTwo.two_le_of_mem_retainedStartIndices` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:842` |
| `PaperC.TheoremSixteenTwo.two_pow_le_of_two_le_div` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:1071` |
| `PaperC.TheoremSixteenTwo.uniformEventProbability_startAt_cutoff_invariant` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:707` |
| `PaperC.TheoremSixteenTwo.valueBit_assemble_eq_local` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:557` |
| `PaperC.TheoremSixteenTwo.valueBit_extendSmall_eq_local` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwo.lean:493` |
| `PaperC.TheoremSixteenTwoRecentered.coe_criticalScaleRate` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwoRecentered.lean:35` |
| `PaperC.TheoremSixteenTwoRecentered.globalEmptyProbability_recentered_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwoRecentered.lean:123` |
| `PaperC.TheoremSixteenTwoRecentered.globalStartLaw_recentered_uniformLittleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/TheoremSixteenTwoRecentered.lean:41` |
| `PaperC.TheoremSixteenTwoRecentered.theorem_sixteen_two_recentered_canonical` | conditionnel | `ADGR07-PNT`, `AGG89-T1-finite-dependency-b3-zero`, `BS93-Theorem-1`, `ES86-T1b-Q-split-n2`, `LS04-Corollary-1`, `NR83-T1-divisor-log-bound` | `external` | `open` | `PaperC/Asymptotics/TheoremSixteenTwoRecentered.lean:189` |
| `PaperC.TouchingMass.maxTouchingRho_cast_le` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingMass.lean:103` |
| `PaperC.TouchingMass.touchingLower_mem_dyadicBlock` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingMass.lean:50` |
| `PaperC.TouchingMass.touchingMass_cast_le_two_mul_two_pow_maxTouchingRho` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingMass.lean:92` |
| `PaperC.TouchingMass.touchingMass_le_two_mul_two_pow_maxTouchingRho` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingMass.lean:82` |
| `PaperC.TouchingMass.touchingRho_le_maxTouchingRho` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingMass.lean:63` |
| `PaperC.TouchingMass.touchingWeight_le_two_pow_maxTouchingRho` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingMass.lean:70` |
| `PaperC.TouchingPairs.card_backwardCandidates_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:102` |
| `PaperC.TouchingPairs.card_dyadicBlock` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:123` |
| `PaperC.TouchingPairs.card_forwardCandidates_le` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:98` |
| `PaperC.TouchingPairs.card_touchingPairs_le_two_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:129` |
| `PaperC.TouchingPairs.card_touchingPairs_le_two_mul_card` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:107` |
| `PaperC.TouchingPairs.eq_add_or_eq_add_of_dist_eq` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:46` |
| `PaperC.TouchingPairs.fst_ne_snd_of_mem` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:60` |
| `PaperC.TouchingPairs.mem_touchingPairs` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:35` |
| `PaperC.TouchingPairs.sum_nat_le_card_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:134` |
| `PaperC.TouchingPairs.sum_nat_le_two_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:146` |
| `PaperC.TouchingPairs.sum_real_le_card_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:155` |
| `PaperC.TouchingPairs.sum_real_le_two_mul` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:167` |
| `PaperC.TouchingPairs.touchingPairs_subset_candidates` | inconditionnel | — | — | — | `PaperC/Combinatorics/TouchingPairs.lean:79` |
| `PaperC.TouchingWindow.criticalWindow_eventually` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingWindow.lean:44` |
| `PaperC.TouchingWindow.dyadicBlock_geometry` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingWindow.lean:135` |
| `PaperC.TouchingWindow.dyadicBlock_geometry_eventually` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingWindow.lean:150` |
| `PaperC.TouchingWindow.lowerConstant_lt_upperConstant` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingWindow.lean:32` |
| `PaperC.TouchingWindow.lowerConstant_pos` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingWindow.lean:28` |
| `PaperC.TouchingWindow.pointwise_defects_uniform` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingWindow.lean:168` |
| `PaperC.TouchingWindow.two_mul_runLength_le_eventually` | inconditionnel | — | — | — | `PaperC/Analysis/TouchingWindow.lean:109` |
| `PaperC.TreeBoundary.boundaryMap_bijective_of_isTree` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:404` |
| `PaperC.TreeBoundary.boundaryMap_surjective_of_connected` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:302` |
| `PaperC.TreeBoundary.boundary_empty` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:34` |
| `PaperC.TreeBoundary.boundary_symmDiff` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:127` |
| `PaperC.TreeBoundary.boundary_trailEdges` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:147` |
| `PaperC.TreeBoundary.card_edgeSubset_eq_evenVertexSubset` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:390` |
| `PaperC.TreeBoundary.card_evenVertexSubset` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:382` |
| `PaperC.TreeBoundary.deleteRoot_evenCompletion` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:349` |
| `PaperC.TreeBoundary.edgeFinset_fromEdgeSet_eq` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:39` |
| `PaperC.TreeBoundary.edgeValueFinset_subset_edgeFinset` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:270` |
| `PaperC.TreeBoundary.edgeValueFinset_toEdgeSubset` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:283` |
| `PaperC.TreeBoundary.evenCompletion_deleteRoot` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:357` |
| `PaperC.TreeBoundary.even_card_boundary` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:62` |
| `PaperC.TreeBoundary.even_card_symmDiff` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:118` |
| `PaperC.TreeBoundary.existsUnique_edgeSubset_boundary_eq` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:419` |
| `PaperC.TreeBoundary.exists_edgeSubset_boundary_eq_of_connected` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:166` |
| `PaperC.TreeBoundary.filter_symmDiff` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:77` |
| `PaperC.TreeBoundary.mem_boundary` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:29` |
| `PaperC.TreeBoundary.mem_edgeValueFinset` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:256` |
| `PaperC.TreeBoundary.mem_nonRootValueFinset` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:323` |
| `PaperC.TreeBoundary.nonRootValueFinset_deleteRoot` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:333` |
| `PaperC.TreeBoundary.odd_card_symmDiff_iff` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:87` |
| `PaperC.TreeBoundary.root_not_mem_nonRootValueFinset` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:329` |
| `PaperC.TreeBoundary.trailEdges_subset_edgeFinset` | inconditionnel | — | — | — | `PaperC/Combinatorics/TreeBoundary.lean:136` |
| `PaperC.TwoParityColumnCode.appendTwo_left` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:35` |
| `PaperC.TwoParityColumnCode.appendTwo_right` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:40` |
| `PaperC.TwoParityColumnCode.appendTwo_small` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:29` |
| `PaperC.TwoParityColumnCode.columns_sub_twoAugmentedRows_le_finrank_ker` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:86` |
| `PaperC.TwoParityColumnCode.exists_nonzero_kernel_word_hammingNorm_le` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:152` |
| `PaperC.TwoParityColumnCode.kernel_left_selected_sum_eq_zero` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:121` |
| `PaperC.TwoParityColumnCode.kernel_left_weighted_sum_eq_zero` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:96` |
| `PaperC.TwoParityColumnCode.kernel_right_selected_sum_eq_zero` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:135` |
| `PaperC.TwoParityColumnCode.kernel_right_weighted_sum_eq_zero` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:107` |
| `PaperC.TwoParityColumnCode.twoAugmentedColumnMap_apply_left` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:66` |
| `PaperC.TwoParityColumnCode.twoAugmentedColumnMap_apply_right` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:76` |
| `PaperC.TwoParityColumnCode.twoAugmentedColumnMap_apply_small` | inconditionnel | — | — | — | `PaperC/Coding/TwoParityColumnCode.lean:56` |
| `PaperC.TwoStartLocalRank.jointRho_le_sub_distance_oriented` | inconditionnel | — | — | — | `PaperC/Probability/TwoStartLocalRank.lean:392` |
| `PaperC.TwoStartLocalRank.localTwoStar_connected` | inconditionnel | — | — | — | `PaperC/Probability/TwoStartLocalRank.lean:180` |
| `PaperC.TwoStartLocalRank.localTwoStar_privatePivots` | inconditionnel | — | — | — | `PaperC/Probability/TwoStartLocalRank.lean:283` |
| `PaperC.TwoStartLocalRank.localTwoStar_reachable_from_secondRoot` | inconditionnel | — | — | — | `PaperC/Probability/TwoStartLocalRank.lean:136` |
| `PaperC.TwoStartLocalRank.localTwoStar_reachable_of_le_Q` | inconditionnel | — | — | — | `PaperC/Probability/TwoStartLocalRank.lean:92` |
| `PaperC.TwoStartLocalRank.localVertex_mem_one_runSupport` | inconditionnel | — | — | — | `PaperC/Probability/TwoStartLocalRank.lean:256` |
| `PaperC.TwoStartLocalRank.presentedReachable_trans` | inconditionnel | — | — | — | `PaperC/Probability/TwoStartLocalRank.lean:81` |
| `PaperC.TwoStartLocalRank.twoStartSystem_rowsRepresented` | inconditionnel | — | — | — | `PaperC/Probability/TwoStartLocalRank.lean:217` |
| `PaperC.TwoStartLocalRank.two_mul_lt_terminalPrimeCutoff_succ` | inconditionnel | — | — | — | `PaperC/Probability/TwoStartLocalRank.lean:426` |
| `PaperC.TwoStartLocalRank.valueBit_primeSingle` | inconditionnel | — | — | — | `PaperC/Probability/TwoStartLocalRank.lean:203` |
| `PaperC.UniformHalfPower.const_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/HalfPower.lean:92` |
| `PaperC.UniformHalfPower.mono` | inconditionnel | — | — | — | `PaperC/Asymptotics/HalfPower.lean:73` |
| `PaperC.UniformHalfPower.mul_subpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/LogLogRunWindow.lean:56` |
| `PaperC.UniformHalfPower.of_sqrt_mul_subpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/HalfPower.lean:41` |
| `PaperC.UniformLinear.max_of_nonnegative` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalMobileAssembly.lean:87` |
| `PaperC.UniformLinear.mono` | inconditionnel | — | — | — | `PaperC/Asymptotics/LinearPower.lean:91` |
| `PaperC.UniformLinear.mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/LinearProduct.lean:19` |
| `PaperC.UniformLinear.of_linear_mul_subpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/LinearPower.lean:65` |
| `PaperC.UniformLinear.subpolynomial_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/BoundedRatioNonterminalMobileAssembly.lean:31` |
| `PaperC.UniformNegativeHalfPower.littleOOne` | inconditionnel | — | — | — | `PaperC/Asymptotics/LogLogRunWindow.lean:107` |
| `PaperC.UniformRationalPower.add_fiveThird_threeHalves` | inconditionnel | — | — | — | `PaperC/Asymptotics/RationalPowerClosure.lean:87` |
| `PaperC.UniformRationalPower.add_quadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/QuadraticAndInterpolationClosure.lean:20` |
| `PaperC.UniformRationalPower.add_threeHalves_fiveThird` | inconditionnel | — | — | — | `PaperC/Asymptotics/RationalPowerClosure.lean:197` |
| `PaperC.UniformRationalPower.interpolate_threeHalves_fiveThird` | inconditionnel | — | — | — | `PaperC/Asymptotics/RationalPowerClosure.lean:217` |
| `PaperC.UniformRationalPower.interpolate_threeHalves_nineteenEighths` | inconditionnel | — | — | — | `PaperC/Asymptotics/ShallowCoreRationalClosure.lean:113` |
| `PaperC.UniformRationalPower.interpolate_threeHalves_quadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/QuadraticAndInterpolationClosure.lean:120` |
| `PaperC.UniformRationalPower.littleO_natPower_of_lt` | inconditionnel | — | — | — | `PaperC/Asymptotics/RationalPowerLittleO.lean:30` |
| `PaperC.UniformRationalPower.mono` | inconditionnel | — | — | — | `PaperC/Asymptotics/RationalPowers.lean:93` |
| `PaperC.UniformRationalPower.mul_subpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/RationalPowerClosure.lean:29` |
| `PaperC.UniformRationalPower.natPower_mul` | inconditionnel | — | — | — | `PaperC/Asymptotics/ShallowCoreRationalClosure.lean:29` |
| `PaperC.UniformRationalPower.nineteenTwelfths_littleO_quadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/RationalPowerLittleO.lean:164` |
| `PaperC.UniformRationalPower.of_cube_bound` | inconditionnel | — | — | — | `PaperC/Asymptotics/RationalPowers.lean:56` |
| `PaperC.UniformRationalPower.quadratic_mul_subpolynomial_threeEighths` | inconditionnel | — | — | — | `PaperC/Asymptotics/ShallowCoreRationalClosure.lean:64` |
| `PaperC.UniformRationalPower.quadratic_mul_twoSubpolynomial_threeEighths` | inconditionnel | — | — | — | `PaperC/Asymptotics/ShallowCoreRationalClosure.lean:87` |
| `PaperC.UniformRationalPower.thirtyOneSixteenths_littleO_quadratic` | inconditionnel | — | — | — | `PaperC/Asymptotics/ShallowCoreRationalClosure.lean:218` |
| `PaperC.UniformSubpolynomial.mono` | inconditionnel | — | — | — | `PaperC/Asymptotics/LogLogRunWindow.lean:30` |
| `PaperC.UniformThreeHalves.mono` | inconditionnel | — | — | — | `PaperC/Asymptotics/ThreeHalvesPower.lean:77` |
| `PaperC.UniformThreeHalves.of_linear_sqrt_mul_subpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/ThreeHalvesPower.lean:32` |
| `PaperC.WeightedChannelMassCritical.weightedChannelMass_cast_le_linear_poly` | inconditionnel | — | — | — | `PaperC/Asymptotics/WeightedChannelMassCritical.lean:100` |
| `PaperC.WeightedChannelMassCritical.weightedChannelMass_le_poly_four_pow_half` | inconditionnel | — | — | — | `PaperC/Asymptotics/WeightedChannelMassCritical.lean:22` |
| `PaperC.WeightedChannelMassCritical.weightedChannelMass_uniformLinearSubpolynomial` | inconditionnel | — | — | — | `PaperC/Asymptotics/WeightedChannelMassCritical.lean:137` |
| `PaperC.WeightedDefectCounting.card_positiveDefectValues_cast_le_eulerProduct` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedDefectCounting.lean:173` |
| `PaperC.WeightedDefectCounting.card_positiveDefectValues_le_sqrtDiv_sum` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedDefectCounting.lean:110` |
| `PaperC.WeightedDefectCounting.card_positiveHDefectValues_cast_le_eulerProduct` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedDefectCounting.lean:197` |
| `PaperC.WeightedDefectCounting.card_positiveValuesForSupport_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedDefectCounting.lean:91` |
| `PaperC.WeightedDefectCounting.cast_sqrt_div_prod_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedDefectCounting.lean:146` |
| `PaperC.WeightedDefectCounting.mem_positiveDefectValues_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedDefectCounting.lean:48` |
| `PaperC.WeightedDefectCounting.mem_positiveValuesForSupport_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedDefectCounting.lean:40` |
| `PaperC.WeightedDefectCounting.positiveValuesForSupport_subset_image_Icc` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedDefectCounting.lean:60` |
| `PaperC.WeightedDefectCounting.sqrt_natCast_prod` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedDefectCounting.lean:131` |
| `PaperC.WeightedDefectMass.localCount_positiveDefectValues_eq` | inconditionnel | — | — | — | `PaperC/Analysis/WeightedDefectMass.lean:23` |
| `PaperC.WeightedDefectMass.sum_two_pow_localCount_sub_one_cast_le` | inconditionnel | — | — | — | `PaperC/Analysis/WeightedDefectMass.lean:104` |
| `PaperC.WeightedDefectMass.sum_two_pow_localCount_sub_one_cast_le_of_cappedRadius` | inconditionnel | — | — | — | `PaperC/Analysis/WeightedDefectMass.lean:193` |
| `PaperC.WeightedDefectMass.sum_two_pow_localCount_sub_one_cast_le_of_chebyshev_budget` | inconditionnel | — | — | — | `PaperC/Analysis/WeightedDefectMass.lean:162` |
| `PaperC.WeightedDefectMass.sum_two_pow_localCount_sub_one_le` | inconditionnel | — | — | — | `PaperC/Analysis/WeightedDefectMass.lean:73` |
| `PaperC.abs_channelParameter_lt` | inconditionnel | — | — | — | `PaperC/Arithmetic/CanonicalChannel.lean:138` |
| `PaperC.abs_lt_length_add_one_of_mem_offsetInterval` | inconditionnel | — | — | — | `PaperC/Arithmetic/CanonicalChannel.lean:126` |
| `PaperC.abs_residualChannelExpression_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCells.lean:146` |
| `PaperC.abs_residualChannelExpression_lt_four_mul_max` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCells.lean:216` |
| `PaperC.abs_sub_le_of_mem_offsetInterval` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelGeometry.lean:108` |
| `PaperC.abs_touchingProbability_sub_baseline_le` | inconditionnel | — | — | — | `PaperC/Probability/TouchingProbability.lean:128` |
| `PaperC.add_parityVec_eq_zero_iff_mul_eq_sq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:152` |
| `PaperC.add_parityVec_eq_zero_of_mul_eq_sq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:146` |
| `PaperC.canonicalReducedChannel?_eq_none_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/CanonicalChannel.lean:85` |
| `PaperC.canonicalReducedChannel?_eq_some_of_mem` | inconditionnel | — | — | — | `PaperC/Arithmetic/CanonicalChannel.lean:108` |
| `PaperC.canonicalReducedChannel?_mem` | inconditionnel | — | — | — | `PaperC/Arithmetic/CanonicalChannel.lean:92` |
| `PaperC.card_Ico_modEq_cast_le_div_add_one` | inconditionnel | — | — | — | `PaperC/Arithmetic/IntervalCongruence.lean:54` |
| `PaperC.card_Ico_modEq_le_ceil_length` | inconditionnel | — | — | — | `PaperC/Arithmetic/IntervalCongruence.lean:23` |
| `PaperC.card_cast_le_residual_bound_of_subset` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelSupport.lean:79` |
| `PaperC.card_dyadicBlock_modClass_le_one_add_div` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelStartPairs.lean:174` |
| `PaperC.card_heightTwoBackwardPairs_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/HeightTwoPairCount.lean:163` |
| `PaperC.card_heightTwoBoundaryPairs_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/HeightTwoPairCount.lean:189` |
| `PaperC.card_heightTwoForwardPairs_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/HeightTwoPairCount.lean:141` |
| `PaperC.card_nat_Ico_modEq_cast_le_div_add_one` | inconditionnel | — | — | — | `PaperC/Arithmetic/IntervalCongruence.lean:73` |
| `PaperC.card_offsetInterval_modClass_le_one_add_div` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelMultiplicityBounds.lean:26` |
| `PaperC.card_positiveHDefectValues_cast_le_sqrt_mul_exp` | inconditionnel | — | — | — | `PaperC/Analysis/DefectGlobalBound.lean:21` |
| `PaperC.card_product_Ico_modEq_cast_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/IntervalCongruence.lean:94` |
| `PaperC.card_reducedChannelCandidates_le_one` | inconditionnel | — | — | — | `PaperC/Arithmetic/CanonicalChannel.lean:60` |
| `PaperC.card_reducedRatiosAtHeight_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelEnumeration.lean:85` |
| `PaperC.cauchyBound_map_intCast_le_height_add_one` | inconditionnel | — | — | — | `PaperC/Algebra/IntegerPolynomialRootBound.lean:56` |
| `PaperC.channelCells_card_cast_le_firstStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelCount.lean:110` |
| `PaperC.channelCells_card_cast_le_maxStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelCount.lean:183` |
| `PaperC.channelCells_card_cast_le_secondStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelCount.lean:145` |
| `PaperC.channelCells_card_le_one_add_div_firstStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelMultiplicityBounds.lean:69` |
| `PaperC.channelCells_card_le_one_add_div_maxStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelMultiplicityBounds.lean:124` |
| `PaperC.channelCells_card_le_one_add_div_secondStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelMultiplicityBounds.lean:95` |
| `PaperC.channelCells_nonempty_iff_mem_channelHeights` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelEnumeration.lean:120` |
| `PaperC.channelFirstCoordinates_subset_modClass` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelCount.lean:59` |
| `PaperC.channelHeights_card_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelEnumeration.lean:184` |
| `PaperC.channelHeights_subset_interval` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelEnumeration.lean:143` |
| `PaperC.channelSecondCoordinates_subset_modClass` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelCount.lean:84` |
| `PaperC.channelSigma_eq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelEnumeration.lean:221` |
| `PaperC.channelSigma_le_div_maxStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelMultiplicityBounds.lean:169` |
| `PaperC.channelStartFirstCoordinates_subset_modClass` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelStartPairs.lean:118` |
| `PaperC.channelStartPairs_card_le_one_add_div_firstStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelStartPairs.lean:231` |
| `PaperC.channelStartPairs_card_le_one_add_div_maxStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelStartPairs.lean:285` |
| `PaperC.channelStartPairs_card_le_one_add_div_secondStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelStartPairs.lean:258` |
| `PaperC.channelStartSecondCoordinates_subset_modClass` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelStartPairs.lean:145` |
| `PaperC.channel_coefficients_le_length` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelGeometry.lean:121` |
| `PaperC.channel_coefficients_le_length_of_mem` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelGeometry.lean:173` |
| `PaperC.channel_difference_eq_multiple` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelGeometry.lean:81` |
| `PaperC.channel_difference_identity` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelGeometry.lean:68` |
| `PaperC.channel_max_le_length_of_two_cells` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelSupport.lean:27` |
| `PaperC.channel_mem_reducedCandidates_of_two_units` | inconditionnel | — | — | — | `PaperC/Arithmetic/CanonicalChannel.lean:217` |
| `PaperC.coeff_mul_natAbs_le_degree_mul_height` | inconditionnel | — | — | — | `PaperC/Algebra/PolynomialHeightOperations.lean:25` |
| `PaperC.coeff_natAbs_le_integerPolynomialHeight` | inconditionnel | — | — | — | `PaperC/Algebra/IntegerPolynomialRootBound.lean:37` |
| `PaperC.dist_le_length_of_mem_unit_channel` | inconditionnel | — | — | — | `PaperC/Arithmetic/SeparatedSmallChannels.lean:33` |
| `PaperC.factorialMoment_eq_sum_offDiag` | inconditionnel | — | — | — | `PaperC/Probability/FactorialMoment.lean:26` |
| `PaperC.four_pow_channelSigma_le_div_maxStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelMultiplicityBounds.lean:189` |
| `PaperC.fst_injOn_channelCells` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelCount.lean:24` |
| `PaperC.fst_injOn_channelStartPairs` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelStartPairs.lean:70` |
| `PaperC.heightTwoBackwardPairs_confinement` | inconditionnel | — | — | — | `PaperC/Arithmetic/HeightTwoPairCount.lean:94` |
| `PaperC.heightTwoBackwardPairs_subset_rectangle` | inconditionnel | — | — | — | `PaperC/Arithmetic/HeightTwoPairCount.lean:132` |
| `PaperC.heightTwoForwardPairs_confinement` | inconditionnel | — | — | — | `PaperC/Arithmetic/HeightTwoPairCount.lean:63` |
| `PaperC.heightTwoForwardPairs_subset_rectangle` | inconditionnel | — | — | — | `PaperC/Arithmetic/HeightTwoPairCount.lean:123` |
| `PaperC.height_one_primitive_channel_forces_unit_and_nearby` | inconditionnel | — | — | — | `PaperC/Arithmetic/SeparatedSmallChannels.lean:54` |
| `PaperC.intIndicator_factorialMoment` | inconditionnel | — | — | — | `PaperC/Probability/FactorialMoment.lean:58` |
| `PaperC.integerPolynomialHeight_mul_le` | inconditionnel | — | — | — | `PaperC/Algebra/PolynomialHeightOperations.lean:57` |
| `PaperC.integerPolynomialHeight_sq_le` | inconditionnel | — | — | — | `PaperC/Algebra/PolynomialHeightOperations.lean:78` |
| `PaperC.integerPolynomialHeight_zero` | inconditionnel | — | — | — | `PaperC/Algebra/IntegerPolynomialRootBound.lean:31` |
| `PaperC.integerRoot_abs_le_one_add_height` | inconditionnel | — | — | — | `PaperC/Algebra/IntegerPolynomialRootBound.lean:127` |
| `PaperC.integerRoot_natAbs_le_height` | inconditionnel | — | — | — | `PaperC/Algebra/IntegerPolynomialRootBound.lean:98` |
| `PaperC.integerRoot_natAbs_le_one_add_height` | inconditionnel | — | — | — | `PaperC/Algebra/IntegerPolynomialRootBound.lean:119` |
| `PaperC.inv_sqrt_nat_le_two_mul_sqrt_sub` | inconditionnel | — | — | — | `PaperC/Analysis/ReciprocalSqrtSum.lean:36` |
| `PaperC.maxStep_mul_channelCells_card_sub_one_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelMultiplicityBounds.lean:141` |
| `PaperC.maxStep_mul_channelSigma_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelMultiplicityBounds.lean:160` |
| `PaperC.maxStep_mul_channelStartPairs_card_sub_one_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelStartPairs.lean:300` |
| `PaperC.max_coeff_le_length_of_mem_nontrivialChannelHeights` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedChannelMass.lean:55` |
| `PaperC.mem_channelCells` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelGeometry.lean:59` |
| `PaperC.mem_channelHeights` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelEnumeration.lean:107` |
| `PaperC.mem_channelStartPairs` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelStartPairs.lean:37` |
| `PaperC.mem_heightTwoBackwardPairs` | inconditionnel | — | — | — | `PaperC/Arithmetic/HeightTwoPairCount.lean:42` |
| `PaperC.mem_heightTwoBoundaryPairs` | inconditionnel | — | — | — | `PaperC/Arithmetic/HeightTwoPairCount.lean:50` |
| `PaperC.mem_heightTwoForwardPairs` | inconditionnel | — | — | — | `PaperC/Arithmetic/HeightTwoPairCount.lean:34` |
| `PaperC.mem_nontrivialChannelHeights` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedChannelMass.lean:27` |
| `PaperC.mem_nontrivialChannelHeights_iff_two_le_card` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedChannelMass.lean:39` |
| `PaperC.mem_offsetBox` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelGeometry.lean:52` |
| `PaperC.mem_offsetInterval` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelGeometry.lean:47` |
| `PaperC.mem_reducedChannelCandidates` | inconditionnel | — | — | — | `PaperC/Arithmetic/CanonicalChannel.lean:47` |
| `PaperC.mem_reducedRatiosAtHeight` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelEnumeration.lean:24` |
| `PaperC.mem_residualChannelValues` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCount.lean:29` |
| `PaperC.mem_residualPrimeCells` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCells.lean:51` |
| `PaperC.mem_residualValueEnvelope` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCount.lean:49` |
| `PaperC.mem_residualVertexPrimeCells` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCells.lean:106` |
| `PaperC.mem_residualVertexPrimeCells_iff_offsets_mem` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCells.lean:118` |
| `PaperC.not_onChannel_of_mem_residualPrimeCells` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCells.lean:69` |
| `PaperC.onChannel_neg_of_mem_channelStartPairs` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelStartPairs.lean:48` |
| `PaperC.one_div_two_pow_le_abs_dyadic_sub_integer` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicGap.lean:54` |
| `PaperC.one_div_two_pow_le_abs_integer_sub_dyadic` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicGap.lean:27` |
| `PaperC.one_div_two_pow_le_abs_integer_sub_dyadicPolynomialEval` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicGap.lean:68` |
| `PaperC.one_div_two_pow_le_abs_integer_sub_polynomialEval` | inconditionnel | — | — | — | `PaperC/Arithmetic/DyadicGap.lean:81` |
| `PaperC.pairChannelError_eq_of_exact_unit` | inconditionnel | — | — | — | `PaperC/Arithmetic/CanonicalChannel.lean:202` |
| `PaperC.parityVec_apply` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:24` |
| `PaperC.parityVec_eq_zero_iff_exists_sq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:64` |
| `PaperC.parityVec_eq_zero_iff_isSquare` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:97` |
| `PaperC.parityVec_eq_zero_of_eq_sq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:54` |
| `PaperC.parityVec_mul` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:34` |
| `PaperC.parityVec_mul_self` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:50` |
| `PaperC.parityVec_one` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:30` |
| `PaperC.parityVec_pow_two` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:41` |
| `PaperC.parityVec_prod` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:105` |
| `PaperC.phase_add` | inconditionnel | — | — | — | `PaperC/Model/FiniteRademacher.lean:68` |
| `PaperC.phase_zero` | inconditionnel | — | — | — | `PaperC/Model/FiniteRademacher.lean:65` |
| `PaperC.positive_coprime_pair_of_max_eq_two` | inconditionnel | — | — | — | `PaperC/Arithmetic/SeparatedSmallChannels.lean:75` |
| `PaperC.positive_pair_eq_one_of_max_eq_one` | inconditionnel | — | — | — | `PaperC/Arithmetic/SeparatedSmallChannels.lean:17` |
| `PaperC.prime_lt_four_mul_max_of_mem_residualPrimeCells` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCells.lean:243` |
| `PaperC.prime_lt_four_mul_max_of_mem_residualVertexPrimeCells` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCells.lean:266` |
| `PaperC.prod_one_add_inv_sqrt_le_exp_sum` | inconditionnel | — | — | — | `PaperC/Analysis/SmoothEulerProduct.lean:17` |
| `PaperC.prod_one_add_inv_sqrt_le_exp_two_sqrt` | inconditionnel | — | — | — | `PaperC/Analysis/SmoothEulerProduct.lean:33` |
| `PaperC.prod_one_add_rpow_neg_one_half_le_exp_two_sqrt` | inconditionnel | — | — | — | `PaperC/Analysis/SmoothEulerProduct.lean:43` |
| `PaperC.prod_smallPrimesUpTo_one_add_inv_sqrt_le` | inconditionnel | — | — | — | `PaperC/Analysis/SmoothEulerProduct.lean:62` |
| `PaperC.prod_smallPrimesUpTo_one_add_rpow_neg_one_half_le` | inconditionnel | — | — | — | `PaperC/Analysis/SmoothEulerProduct.lean:69` |
| `PaperC.randomMultiplicativeValue_mul` | inconditionnel | — | — | — | `PaperC/Model/FiniteRademacher.lean:77` |
| `PaperC.ratCast_sum_range_pow_div_factorial_le_exp` | inconditionnel | — | — | — | `PaperC/Analysis/ExponentialSeriesMajorant.lean:28` |
| `PaperC.ratIndicator_factorialMoment` | inconditionnel | — | — | — | `PaperC/Probability/FactorialMoment.lean:71` |
| `PaperC.reducedChannel_unique` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelUniqueness.lean:23` |
| `PaperC.reducedRatiosAtHeight_subset_faces` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelEnumeration.lean:45` |
| `PaperC.residualCertificateChannelEnvelope_uniformLinear` | inconditionnel | — | — | — | `PaperC/Asymptotics/ResidualCertificateMassCritical.lean:30` |
| `PaperC.residualChannelExpression_eq_zero_iff` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCells.lean:61` |
| `PaperC.residualChannelValues_subset_envelope` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCount.lean:60` |
| `PaperC.residualExpression_fiber_card_cast_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCount.lean:122` |
| `PaperC.residualExpression_fiber_subset_channelCells` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCount.lean:107` |
| `PaperC.residualPrimeCells_card_cast_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCount.lean:153` |
| `PaperC.residualPrimeCells_eq_empty_of_cutoff_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelSupport.lean:43` |
| `PaperC.residualPrimeMass_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualPrimeMass.lean:27` |
| `PaperC.residualPrimeMass_natCast_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualPrimeMass.lean:66` |
| `PaperC.residualValueEnvelope_card_cast_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCount.lean:81` |
| `PaperC.residualVertexExpression_apply` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelCells.lean:89` |
| `PaperC.residualVertexPrimeCells_card_eq_residualPrimeCells_card` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualVertexPrimeCellCount.lean:56` |
| `PaperC.residualVertexPrimeCells_eq_empty_of_cutoff_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/ResidualChannelSupport.lean:59` |
| `PaperC.rpow_neg_one_half_eq_inv_sqrt` | inconditionnel | — | — | — | `PaperC/Analysis/ReciprocalSqrtSum.lean:16` |
| `PaperC.snd_injOn_channelCells` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelCount.lean:41` |
| `PaperC.snd_injOn_channelStartPairs` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelStartPairs.lean:91` |
| `PaperC.sqrt_nat_sq_sub_sq_eq_one` | inconditionnel | — | — | — | `PaperC/Analysis/ReciprocalSqrtSum.lean:26` |
| `PaperC.sqrt_nat_sub_one_le` | inconditionnel | — | — | — | `PaperC/Analysis/ReciprocalSqrtSum.lean:21` |
| `PaperC.startEvents_disjoint_of_dist_lt` | inconditionnel | — | — | — | `PaperC/Runs/Starts.lean:97` |
| `PaperC.startEvents_disjoint_of_lt` | inconditionnel | — | — | — | `PaperC/Runs/Starts.lean:77` |
| `PaperC.startProbability_eq_ite` | inconditionnel | — | — | — | `PaperC/Probability/StartProbability.lean:48` |
| `PaperC.startProbability_eq_uniformSolutionProbability` | inconditionnel | — | — | — | `PaperC/Probability/StartProbability.lean:23` |
| `PaperC.startWindow_le_dyadicCutoff` | inconditionnel | — | — | — | `PaperC/Model/FiniteRademacher.lean:97` |
| `PaperC.sum_Icc_inv_sqrt_le` | inconditionnel | — | — | — | `PaperC/Analysis/ReciprocalSqrtSum.lean:95` |
| `PaperC.sum_Icc_rpow_neg_one_half_le` | inconditionnel | — | — | — | `PaperC/Analysis/ReciprocalSqrtSum.lean:68` |
| `PaperC.sum_Ioc_rpow_neg_three_halves_le` | inconditionnel | — | — | — | `PaperC/Analysis/ReciprocalThreeHalvesTail.lean:24` |
| `PaperC.sum_parityVec_eq_zero_iff_prod_eq_sq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:136` |
| `PaperC.sum_parityVec_eq_zero_of_prod_eq_sq` | inconditionnel | — | — | — | `PaperC/Arithmetic/ParityVector.lean:126` |
| `PaperC.sum_range_pow_div_factorial_le_exp` | inconditionnel | — | — | — | `PaperC/Analysis/ExponentialSeriesMajorant.lean:17` |
| `PaperC.sum_weightedChannelMassAtHeight_ge_three_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedChannelMass.lean:203` |
| `PaperC.touchingProbability_eq_eta_mul_two_pow_rho_div` | inconditionnel | — | — | — | `PaperC/Probability/TouchingProbability.lean:61` |
| `PaperC.touchingProbability_eq_uniformSolutionProbability` | inconditionnel | — | — | — | `PaperC/Probability/TouchingProbability.lean:39` |
| `PaperC.two_le_of_mem_dyadicBlock` | inconditionnel | — | — | — | `PaperC/Model/FiniteRademacher.lean:106` |
| `PaperC.two_pow_channelSigma_le_div_maxStep` | inconditionnel | — | — | — | `PaperC/Arithmetic/ChannelMultiplicityBounds.lean:180` |
| `PaperC.uniformExpectation_dyadicCount` | inconditionnel | — | — | — | `PaperC/Probability/FiniteExpectation.lean:35` |
| `PaperC.uniformExpectation_indicator` | inconditionnel | — | — | — | `PaperC/Probability/FiniteExpectation.lean:26` |
| `PaperC.uniformLittleOOn_zero` | inconditionnel | — | — | — | `PaperC/Asymptotics/Uniform.lean:50` |
| `PaperC.valueBit_mul` | inconditionnel | — | — | — | `PaperC/Model/FiniteRademacher.lean:55` |
| `PaperC.valueLinear_apply` | inconditionnel | — | — | — | `PaperC/Model/FiniteRademacher.lean:50` |
| `PaperC.weightedChannelMassAtHeight_ge_three_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedChannelMass.lean:180` |
| `PaperC.weightedChannelMassAtHeight_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedChannelMass.lean:123` |
| `PaperC.weightedChannelMassAtHeight_two_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedChannelMass.lean:173` |
| `PaperC.weightedChannelMassAtPair_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedChannelMass.lean:93` |
| `PaperC.weightedChannelMass_eq_two_add_ge_three` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedChannelMass.lean:230` |
| `PaperC.weightedChannelMass_le_small_add_large` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedChannelMass.lean:248` |
| `PaperC.weightedResidualChannelMass_le` | inconditionnel | — | — | — | `PaperC/Arithmetic/WeightedResidualChannelMass.lean:38` |
<!-- END GENERATED BRIDGE REGISTRY -->

## Catalogue historique documenté

La liste ci-dessous est le catalogue humain des jalons structurants accumulé
avant la v019. `ReviewAxioms.lean` en conserve une sélection exécutable plus
resserrée ; ni ce catalogue ni cette sélection ne sert désormais à produire
l'audit exhaustif, et le vérificateur n'a donc plus à les analyser
automatiquement :

- `parityVec_eq_zero_iff_exists_sq` ;
- `sum_parityVec_eq_zero_iff_prod_eq_sq` ;
- `Affine.card_solution_eq_ite` ;
- `Affine.affineFiber_fourier_identity` ;
- `Affine.relationSignedSum_eq_eta_mul_two_pow_rho` ;
- `Affine.relationCharacter_eq_zero_iff_compatible` ;
- `Affine.affineFiber_normalized_card_identity` ;
- `Affine.abs_eta_mul_two_pow_rho_sub_one_le` ;
- `Affine.startSystem_eq_startRhs_iff` ;
- `startEvents_disjoint_of_dist_lt` ;
- `randomMultiplicativeValue_mul` ;
- `startProbability_eq_ite` ;
- `uniformExpectation_dyadicCount` ;
- `ratIndicator_factorialMoment` ;
- `FinitePMF.tvDist_comm` ;
- `uniformLittleOOn_zero` ;
- `CRT.solutions_modEq` ;
- `CRT.satisfies_iff_modEq_representative` ;
- `CRT.satisfies_iff_intModEq_representative` ;
- `CRT.representative_lt_product` ;
- `card_Ico_modEq_le_ceil_length` ;
- `card_Ico_modEq_cast_le_div_add_one` ;
- `card_nat_Ico_modEq_cast_le_div_add_one` ;
- `card_product_Ico_modEq_cast_le` ;
- `CRT.card_Ico_satisfies_cast_le_div_add_one` ;
- `CRT.card_product_Ico_satisfies_cast_le` ;
- `CRT.card_Ico_satisfies_cast_le_scaled` ;
- `CRT.card_product_Ico_satisfies_cast_le_scaled` ;
- `CRT.modEq_startResidue_iff_dvd_startCompleteVertexLabel` ;
- `CRT.certificateWeightSum_le_pow_sum_div_factorial` ;
- `CRT.certificateCellWeightSum_le` ;
- `CRT.certificatePairCellWeightSum_le` ;
- `CRT.sum_certificateWeightSum_le_exponentialMajorant` ;
- `CRT.admissibleCertificateSolutionMass_le` ;
- `CRT.admissibleCertificatePairSolutionMass_le` ;
- `CRT.sum_labeledCell_admissibleCertificateSolutionMass_le` ;
- `CRT.sum_labeledCell_admissibleCertificatePairSolutionMass_le` ;
- `ratCast_sum_range_pow_div_factorial_le_exp` ;
- `channel_difference_eq_multiple` ;
- `channel_coefficients_le_length` ;
- `channel_coefficients_le_length_of_mem` ;
- `reducedChannel_unique` ;
- `channelCells_card_cast_le_maxStep` ;
- `Affine.range_startCompleteBoundary_eq_ker_startVertexSum` ;
- `Affine.mem_relationSpace_twoStartSystem_iff_boundary_prime_equations` ;
- `Affine.RationalChannelCode.finrank_rationalCode_eq_channelCells_card_sub_one` ;
- `Affine.RationalChannelCode.rationalCode_ne_bot_iff_two_le_channelCells_card` ;
- `Affine.RationalChannelCode.relationCharacter_rationalRelationMap` ;
- `card_reducedChannelCandidates_le_one` ;
- `CanonicalChannelWindow.card_reducedChannelCandidates_le_one_eventually` ;
- `Affine.CanonicalRationalCode.rationalSigma_eq_canonicalMultiplicity_sub_one` ;
- `Affine.CanonicalRationalCode.canonicalRationalCode_eq_of_rationalCode_ne_bot` ;
- `CanonicalRationalCodeWindow.canonicalRationalCode_eq_of_nonzero_eventually` ;
- `RationalMassFinite.rationalMass_le` ;
- `CriticalRationalMass.rationalMass_two_uniformFourThird` ;
- `CriticalRationalMass.rationalMass_four_uniformFiveThird` ;
- `WeightedChannelMassCritical.weightedChannelMass_uniformLinearSubpolynomial` ;
- `LargePrimeOccurrences.card_primeOccurrences_le_two` ;
- `PinnedGraphResolution.pinnedGraphLinearEquiv` ;
- `PinnedGraphResolution.finrank_pinnedGraphSpace` ;
- `PinnedGraphResolution.card_isolated_add_twice_card_nontrivial_le` ;
- `LargePrimeGraph.mem_largePrimeSolution_iff_graph_rules` ;
- `LargePrimeGraph.isDefective_of_not_isPinned_of_isolated` ;
- `LargePrimeGraphResolution.largePrimeSolutionLinearEquiv` ;
- `LargePrimeGraphResolution.finrank_largePrimeSolution_eq_defective_add_components` ;
- `LargePrimeGraphResolution.defectiveVertex_add_twice_nontrivial_le` ;
- `ComponentSquareClass.exists_squarefree_mul_sq` ;
- `ComponentSquareClass.decomposition_unique` ;
- `LargePrimeComponents.component_large_parity_eq_zero` ;
- `LargePrimeComponents.exists_component_square_class` ;
- `ExactUnitLargeKernel.exactUnit_defect_dichotomy` ;
- `ExactUnitLargeKernel.prime_dvd_unique_in_block` ;
- `ExactUnitIsolation.exactUnit_component_card_eq_two` ;
- `ExactUnitIsolation.exactUnit_graph_dichotomy` ;
- `ExactUnitIsolation.channelUnitOccurrencePair_disjoint` ;
- `ExactUnitIsolation.distinct_channelUnits_nondefective_components` ;
- `QuotientParity.finrank_nested_quotient_le_finrank_sub` ;
- `CanonicalResidualQuotient.residualTau_eq_finrank_quotient` ;
- `LargePrimeRelationBoundary.relationBoundaryToLargePrime_injective` ;
- `LargePrimeRelationBoundary.relationRho_le_finrank_largePrimeSolution_sub_one` ;
- `ResidualComponentCounts.residualTau_le_canonicalCorrected_add_residual` ;
- `ResidualComponentCounts.canonicalCorrected_add_twice_residual_le` ;
- `CanonicalResidualComponents.card_canonicalResidualComponents` ;
- `CanonicalResidualComponents.card_canonicalResidualCertificateIndex` ;
- `CanonicalResidualComponents.card_canonicalResidualCertificatePrimes` ;
- `CanonicalResidualComponents.canonicalResidualPrimeProduct_eq_product_certificates` ;
- `CanonicalResidualComponents.canonicalResidualPrimeProduct_dichotomy` ;
- `CanonicalResidualComponents.canonicalResidualFullCertificate_admissible_iff` ;
- `CanonicalResidualComponents.canonicalResidual_pair_mem_fullCertificateSolutions` ;
- `CanonicalResidualComponents.canonicalResidualCertificates_leftOffset_injective` ;
- `CanonicalResidualComponents.canonicalResidualCertificates_rightOffset_injective` ;
- `CanonicalResidualComponents.canonicalResidualCertificates_prime_injective` ;
- `CanonicalResidualComponents.canonicalResidualCertificates_residualExpression_ne_of_choice` ;
- `CanonicalResidualComponents.card_canonicalOneUnitExceptionalComponents_le_two` ;
- `CanonicalResidualComponents.canonicalResidualCertificate_mem_oneUnitExceptionalComponents_of_choice` ;
- `OneUnitResidualExceptions.card_oneUnitExceptionalComponents_le_two` ;
- `OneUnitResidualExceptions.canonicalCertificate_mem_oneUnitExceptionalComponents_of_onChannel` ;
- `DefectiveVertexIntervalBound.canonicalCorrectedDefectCount_le_interval_sum` ;
- `DefectiveVertexIntervalBound.canonicalCorrectedDefectCount_uniform_on_dyadicBlock` ;
- `DefectiveVertexIntervalBound.canonicalCorrectedDefectCount_uniform_B_div_log_B` ;
- `TreeBoundary.edgeFinset_fromEdgeSet_eq` ;
- `TreeBoundary.even_card_boundary` ;
- `TreeBoundary.boundary_symmDiff` ;
- `TreeBoundary.exists_edgeSubset_boundary_eq_of_connected` ;
- `TreeBoundary.boundaryMap_bijective_of_isTree` ;
- `TreeBoundary.existsUnique_edgeSubset_boundary_eq` ;
- `PrivatePivots.linearIndependent_of_private_pivots` ;
- `PrivatePivots.tree_projectedParityEdge_linearIndependent_of_large_odd_primes` ;
- `GraphCycleRank.ker_representedEdgeMap_le_cycleSpace` ;
- `CycleSpaceDimension.finrank_cycleSpace_le_card_edges_sub_nonRoot` ;
- `CycleSpaceDimension.finrank_cycleSpace_le_cyclomaticNumber` ;
- `CycleSpaceDimension.card_vertices_sub_components_le_rank_representedEdgeMap` ;
- `HammingBound.card_ball` ;
- `HammingBound.hamming_bound_sum_choose` ;
- `HammingBound.hamming_bound_submodule_codimension` ;
- `HammingBound.hamming_bound_submodule_of_finrank_ge` ;
- `HammingBound.sum_choose_le_pow_of_finrank_ge` ;
- `RungeTranslation.translatedRungeInput` ;
- `RungeSplitProduct.splitProduct_not_isSquare` ;
- `RungeCoefficients.two_pow_mul_rungeCoefficient_isRatInteger` ;
- `RungeCoefficients.abs_rungeCoefficient_le_eight_mul_pow` ;
- `RungePowerSeries.coeff_rungeProductSeries` ;
- `RungePowerSeries.rungeProductSeries_sq` ;
- `RungeTruncation.map_integralRungeTruncation` ;
- `RungeTruncation.one_div_two_pow_le_abs_integer_sub_rungeTruncation` ;
- `GeometricTail.runge_ratio_tail` ;
- `RungeAnalyticProduct.hasSum_rungeCoefficient_mul_pow_eq_prod_sqrt` ;
- `RungeTailEstimate.rungeCoefficient_pow_mul_abs_tail_le` ;
- `RungeEstimate.abs_natAbs_sub_rungeTruncation_le` ;
- `RungeQPolynomial.natDegree_rungeQ_le_pred` ;
- `RungeQPolynomial.integerPolynomialHeight_rungeQ_explicit` ;
- `RungeBound.quantitative_runge_of_distinct` ;
- `integerRoot_abs_le_one_add_height` ;
- `DefectParitySupport.parityCoverage_of_eq_mul_sq` ;
- `DefectCodeRank.defectCode_finrank_ge` ;
- `DefectCodeRank.defectCode_kernelWord_even` ;
- `DefectCodeRank.square_product_of_mem_ker_augmentedParityMap` ;
- `DefectCodeRunge.kernelWord_support_card_eq_two_mul` ;
- `DefectCodeRunge.kernelWord_translatedRungeInput` ;
- `DefectCodeRepresentation.kernelWord_translatedRungeInput_of_defectRepresentations` ;
- `DefectCodeDistance.minWeightAbove_augmentedParityMap_of_noShortRungeSquare` ;
- `HammingDefectBound.length_lt_of_sum_choose_le_two_pow` ;
- `DefectCodeHamming.defectCode_volume_le_two_pow` ;
- `DefectCodeHamming.defectCode_length_lt` ;
- `DefectCodeProposition.defectCode_length_lt_of_representations` ;
- `RungeDefectApplication.defectCode_length_lt_of_endpoint_growth`.
- `PrimesUpTo.covers_primeDivisors` ;
- `PrimeCountBridge.count_eq_card_smallPrimesUpTo` ;
- `ChebyshevPrimeCount.count_le_seven_mul_div_log` ;
- `RungeLogarithmicGrowth.endpoint_growth_cappedRadius` ;
- `CanonicalDefectCode.length_lt_of_log` ;
- `IntervalDefectBound.card_defectsInInterval_lt_of_log` ;
- `DefectCounting.card_defectValues_le` ;
- `DefectivePredicate.hDefective_iff_exists_HDefectRepresentation` ;
- `WeightedDefectCounting.card_positiveDefectValues_cast_le_eulerProduct` ;
- `prod_smallPrimesUpTo_one_add_inv_sqrt_le` ;
- `card_positiveHDefectValues_cast_le_sqrt_mul_exp` ;
- `IntervalDefectAggregation.sum_two_pow_localCount_sub_one_le` ;
- `WeightedDefectMass.sum_two_pow_localCount_sub_one_cast_le`.
- `DefectPointwiseRate.card_defectsInInterval_cast_lt_log_div` ;
- `CappedRadiusDyadic.uniformSubpolynomialOn_two_cappedRadius` ;
- `ExpSqrtLog.uniformSubpolynomialOn_weighted_defect_factor` ;
- `UniformHalfPower.of_sqrt_mul_subpolynomial` ;
- `CriticalWindowScale.scaled_log_le_eventually` ;
- `CriticalWeightedDefect.dyadicDefectMass_uniformHalfPower_on_window` ;
- `CriticalWeightedDefect.pointwise_uniformBigO_on_window` ;
- `CriticalPointwiseIntervals.pointwise_all_intervals_on_window` ;
- `Affine.StartDefectRank.relationRho_startSystem_le_card_defectsInInterval` ;
- `DefectFirstMoment.abs_dyadicExpectation_sub_baseline_le_globalDefectWeight` ;
- `CriticalFirstMoment.normalized_error_uniformHalfPower` ;
- `CriticalRunWindow.firstMoment_error_uniformNegativeHalfPower` ;
- `Affine.touchingSystem_eq_touchingRhs_iff` ;
- `Affine.TouchingDefectRank.relationRho_touchingSystem_le_card_defectsInInterval` ;
- `TouchingPairs.card_touchingPairs_le_two_mul` ;
- `TouchingMass.touchingMass_le_two_mul_two_pow_maxTouchingRho` ;
- `TouchingWindow.pointwise_defects_uniform` ;
- `ExpSqrtLog.uniformSubpolynomialOn_two_pow_log_div_loglog_eventually` ;
- `UniformLinear.of_linear_mul_subpolynomial` ;
- `CriticalTouchingPairs.touchingMass_uniformLinearSubpolynomial` ;
- `touchingProbability_eq_eta_mul_two_pow_rho_div` ;
- `abs_touchingProbability_sub_baseline_le` ;
- `Affine.twoStartSystem_eq_twoStartRhs_iff` ;
- `Affine.twoStartCompleteBoundary_injective` ;
- `Affine.relationCanonicalSelectedOccurrence_ne_zero` ;
- `Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_left` ;
- `Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_right` ;
- `LargeOddKernel.canonical_largeOddKernel_decomposition` ;
- `LargeKernelAssignments.card_startsForSomeAssignment_cast_le` ;
- `RelationalHosts.card_relationalHosts_cast_le_kernelSumQ` ;
- `LargeKernelWeightedCounting.sum_largeKernelWeight_le_eulerProducts` ;
- `sum_Ioc_rpow_neg_three_halves_le` ;
- `LargeEulerProduct.prod_one_add_mul_rpow_neg_three_halves_le_exp_two_sqrt` ;
- `RelationalHostBound.card_relationalHosts_cast_le_kernelSum` ;
- `RelationalHostBound.sum_largeKernelWeight_le_sqrt_mul_exp` ;
- `RelationalHostBound.card_relationalHosts_cast_le_exp_bound` ;
- `UniformThreeHalves.of_linear_sqrt_mul_subpolynomial` ;
- `RelationalHostsThreeHalves.card_relationalHosts_uniformThreeHalves_inRunLengthWindow` ;
- `RelationalInterpolation.sum_le_sqrt_relationalHosts_bound_mul_sqrt_sqBound` ;
- `RelationalInterpolation.sum_le_rpow_average` ;
- `RelationalInterpolation.sum_le_two_sub_half_delta_add_error` ;
- `RelationalInterpolation.sum_le_two_sub_half_delta_add_error_of_subset` ;
- `RelationalInterpolation.eventually_sum_nonneg_and_le_sqrt_mul_sqrt` ;
- `abs_residualChannelExpression_le` ;
- `prime_lt_four_mul_max_of_mem_residualPrimeCells` ;
- `residualPrimeCells_card_cast_le` ;
- `channel_max_le_length_of_two_cells` ;
- `residualPrimeCells_eq_empty_of_cutoff_le` ;
- `card_cast_le_residual_bound_of_subset` ;
- `residualPrimeMass_natCast_le` ;
- `DyadicPrimeReciprocalSums.sum_inv_dyadicPrimes_le` ;
- `DyadicPrimeReciprocalSums.sum_inv_sq_dyadicPrimes_le` ;
- `DyadicPrimeReciprocalSums.sum_inv_primes_lt_four_mul_le` ;
- `DyadicPrimeReciprocalSums.sum_inv_sq_primes_lt_four_mul_le` ;
- `ResidualChannelLemmaSevenTwo.mem_residualPrimeRange_of_nonempty` ;
- `ResidualChannelLemmaSevenTwo.residualPrimeMass_eq_sum_primesBetween` ;
- `ResidualChannelLemmaSevenTwo.residualPrimeMass_le` ;
- `IntervalDefectBound.card_defectsInInterval_lt_of_cappedRadius` ;
- `WeightedDefectMass.sum_two_pow_localCount_sub_one_cast_le_of_cappedRadius` ;
- `residualVertexPrimeCells_card_eq_residualPrimeCells_card` ;
- `weightedResidualChannelMass_le` ;
- `CRT.card_population_le_sum_admissibleCertificateSolutionCount'` ;
- `CRT.pow_mul_card_population_le_admissibleCertificateSolutionMass'` ;
- `CRT.card_population_le_sum_admissibleCertificatePairSolutionCount'` ;
- `CRT.pow_mul_card_population_le_admissibleCertificatePairSolutionMass'` ;
- `ResidualMasses.pairTau_le_canonicalCorrected_add_residual` ;
- `ResidualMasses.quadraticResidualWeight_le_systematic_mul_corrected_mul_certificate` ;
- `ResidualMasses.smallProductQuadraticResidualMass_eq_sigmaZero_add_positiveSigma` ;
- `ResidualMasses.smallProductLinearResidualMass_cast_le` ;
- `CanonicalResidualComponents.canonicalResidualCertificates_mem_residualVertexPrimeCells_of_choice` ;
- `CanonicalResidualComponents.canonicalResidualCertificates_prime_mem_residualPrimeRange_of_choice` ;
- `CanonicalResidualComponents.canonicalResidualAmbientCertificate_admissible_iff` ;
- `CanonicalResidualComponents.canonicalResidual_pair_mem_ambientCertificatePairSolutions` ;
- `SigmaZeroAmbientCertificate.ambientCertificate_admissible_iff` ;
- `SigmaZeroAmbientCertificate.pair_mem_ambientCertificateSolutions` ;
- `SigmaZeroAmbientCertificate.one_le_ambientCertificate_pairSolutionCount` ;
- `PositiveSigmaFixedChannelCover.four_pow_mul_card_fixedChannelPairs_le_solutionMass` ;
- `PositiveSigmaFixedChannelCover.four_pow_mul_card_fixedChannelPairs_le_effective` ;
- `PositiveSigmaFixedChannelCover.sum_four_pow_mul_card_fixedChannelPairs_cast_le_exp` ;
- `CanonicalResidualComponents.sum_canonicalResidualAmbientCells_card_div_eq_residualPrimeMass` ;
- `CanonicalResidualComponents.canonicalResidualAmbient_admissibleCertificateSolutionMass_le` ;
- `CanonicalResidualComponents.sum_canonicalResidualAmbient_admissibleCertificateSolutionMass_cast_le_exp` ;
- `ExpLogDivLogLog.exp_log_div_loglog_pow_le_nat_eventually` ;
- `ExpLogDivLogLog.criticalRunWindow_exp_height_div_natLog_uniformSubpolynomial` ;
- `UniformLinear.mul` ;
- `residualCertificateChannelEnvelope_uniformLinear` ;
- `CorrectedDefectEnvelope.four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial` ;
- `PropositionSevenThreeSigmaZeroCover.sum_four_pow_mul_card_sigmaZeroSmallProductPairs_le` ;
- `SigmaZeroQuadraticCritical.sigmaZeroQuadraticResidualMass_le_corrected_mul_cover` ;
- `SigmaZeroQuadraticCritical.sum_ambientPrime_inv_sq_le` ;
- `SigmaZeroQuadraticCritical.sigmaZeroQuadraticResidualMass_uniformQuadratic` ;
- `PositiveSigmaGlobalGrouping.existsUnique_key_of_mem_positiveSigmaSmallProductPairs` ;
- `PositiveSigmaGlobalGrouping.positiveSigmaQuadraticResidualMass_le_channelCertificateMass` ;
- `PositiveSigmaKeyMassBound.sum_four_pow_channelSigma_positiveChannelKeys` ;
- `PositiveSigmaKeyMassBound.positiveSigmaChannelCertificateMass_cast_le` ;
- `PositiveSigmaQuadraticCritical.positiveSigmaQuadraticResidualMass_uniformQuadratic` ;
- `UniformRationalPower.add_quadratic` ;
- `UniformRationalPower.interpolate_threeHalves_quadratic` ;
- `PropositionSevenThreeCritical.smallProductQuadraticResidualMassTotal_eq_branches` ;
- `PropositionSevenThreeCritical.smallProductQuadraticResidualMass_uniformQuadratic` ;
- `PropositionSevenThreeCritical.smallProductLinearResidualMass_uniformSevenFourths` ;
- `SmallHeightResidualPrimeSupport.canonicalResidualComponentCount_le_two_add_primeCount_of_choice` ;
- `SmallHeightResidualComponentEnvelope.pairResidualComponentCount_le_envelope_of_mem` ;
- `SmallHeightTauEnvelope.pairTau_le_smallHeightTauEnvelope_of_mem` ;
- `SmallHeightLargeProductMassBound.sum_four_pow_pairSigma_positive_le_two_mul_rationalMass` ;
- `SmallHeightLargeProductMassBound.positiveSigmaQuadraticResidualMass_le_uniform` ;
- `SmallHeightLargeProductMassBound.sigmaZeroQuadraticResidualMass_le_uniform` ;
- `SmallHeightLargeProductMassBound.smallHeightLargeProductQuadraticResidualMass_le_uniform` ;
- `SmallHeightLargeProductMassBound.smallHeightLargeProductLinearResidualMass_cast_le` ;
- `SmallHeightComponentEnvelopeCritical.four_pow_smallHeightResidualComponentEnvelope_uniformSubpolynomial` ;
- `SmallHeightTauEnvelopeCritical.four_pow_smallHeightTauEnvelope_uniformSubpolynomial` ;
- `SmallHeightSigmaZeroCritical.sigmaZeroQuadraticResidualMass_uniformThreeHalves` ;
- `SmallHeightPositiveSigmaCritical.positiveSigmaQuadraticResidualMass_uniformFiveThird` ;
- `UniformRationalPower.add_threeHalves_fiveThird` ;
- `UniformRationalPower.interpolate_threeHalves_fiveThird` ;
- `UniformRationalPower.nineteenTwelfths_littleO_quadratic` ;
- `PropositionSevenFourCritical.smallHeightLargeProductQuadraticResidualMassTotal_eq_branches` ;
- `PropositionSevenFourCritical.smallHeightLargeProductQuadraticResidualMass_uniformFiveThird` ;
- `PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMassTotal_le` ;
- `PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMass_uniformNineteenTwelfths` ;
- `PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMass_uniformLittleOQuadratic` ;
- `ShallowCorePairs.canonicalResidualComponentCount_le_envelope_of_mem` ;
- `ShallowCorePairs.card_shallowCorePairs_le_sq` ;
- `ShallowCorePairs.shallowCoreLinearResidualMass_cast_le` ;
- `ShallowCorePairs.maxShallowCoreSigma_cast_le` ;
- `ShallowCoreMassBound.quadraticResidualWeight_le_shallowCoreEnvelopes_of_mem` ;
- `ShallowCoreMassBound.shallowCoreQuadraticResidualMass_le` ;
- `ShallowCoreSigmaCritical.maxShallowCoreSigma_uniformLittleO` ;
- `ShallowCoreSigmaCritical.four_pow_maxShallowCoreSigma_uniformSubpolynomial` ;
- `ShallowCoreDensityCritical.sixteen_mul_shallowCoreComponentEnvelope_le` ;
- `ShallowCoreDensityCritical.shallowCoreDensity_eighth_cast_le` ;
- `ShallowCoreDensityCritical.four_pow_shallowCoreComponentEnvelope_uniformThreeEighths` ;
- `UniformRationalPower.natPower_mul` ;
- `UniformRationalPower.quadratic_mul_twoSubpolynomial_threeEighths` ;
- `UniformRationalPower.interpolate_threeHalves_nineteenEighths` ;
- `UniformRationalPower.thirtyOneSixteenths_littleO_quadratic` ;
- `PropositionSevenFiveCritical.shallowCoreQuadraticResidualMassTotal_le_envelope` ;
- `PropositionSevenFiveCritical.shallowCoreQuadraticResidualMass_uniformNineteenEighths` ;
- `PropositionSevenFiveCritical.shallowCoreLinearResidualMassTotal_le` ;
- `PropositionSevenFiveCritical.shallowCoreLinearResidualMass_uniformThirtyOneSixteenths` ;
- `PropositionSevenFiveCritical.shallowCoreLinearResidualMass_uniformLittleOQuadratic` ;
- `SectionSevenPartition.sectionSeven_populations_cover` ;
- `SmallComponentExtraction.target_small_components` ;
- `AlignedExactFreeComponents.card_residualComponents_le_card_exactFree_add_two` ;
- `TwoParityColumnCode.exists_nonzero_kernel_word_hammingNorm_le` ;
- `ComponentProductParity.componentVertexProduct_smallPrime_coverage` ;
- `AlignedComponentCode.kernelWord_parity_package` ;
- `AlignedComponentHamming.exists_short_kernelWord_parity_package` ;
- `AlignedRungeBridge.alignedShift_selected_injective` ;
- `AlignedRungeBridge.selected_base_product_square` ;
- `AlignedRungeBridge.quantitative_runge_of_componentWord` ;
- `AlignedRungeBridge.candidate_abs_alignedShift_le` ;
- `AlignedCoreExclusion.no_candidate_aligned_core_of_finite_conditions` ;
- `AlignedDeepCoreExtraction.one_sixteenth_le_card_smallExactFreeResidualComponents_of_candidate` ;
- `TheoremEightHammingBudget.componentHammingRadius_conditions_runLengthWindow_eventually` ;
- `AlignedRungeGrowth.rungeNumerics_eventually` ;
- `TheoremEightAlignedClosure.alignedHammingNumerics_eventually` ;
- `TheoremEightAlignedClosure.no_aligned_deep_core_eventually` ;
- `EvertseSilvermanInput.shiftedSquareEquation_atMost_of_evertseSilverman`.

Pour chacun, la sortie attendue est une sous-liste de la liste blanche :

```text
[propext, Classical.choice, Quot.sound]
```

La plupart utilisent les trois éléments ; certains résultats élémentaires,
comme `RungeTranslation.translatedRungeInput`, en utilisent strictement
moins. La validation exige l'absence de `sorryAx`, de `Lean.ofReduceBool` et
de tout axiome mathématique ajouté pour le papier. Un audit textuel séparé vérifie aussi
l'absence de `sorry`, `axiom`, `admit`, `native_decide`, `unsafe` et
`partial` dans `PaperC/**/*.lean`.

## Portée

Cet audit certifie les théorèmes effectivement présents dans le dépôt,
notamment les conclusions des propositions 7.3, 7.4 et 7.5, leur partition
exhaustive, l'exclusion éventuelle du cœur aligné de densité \(3/16\), et
l'implication conditionnelle du lemme 9.1 ainsi que celle du lemme 9.2 pour
tout exposant réel positif, y compris sa forme source-exacte.
Il ne transforme pas
les ponts enregistrés — externes comme internes — ni les sections encore
absentes en résultats Lean ; leur état est décrit dans
`FORMALIZATION_STATUS.md`.
