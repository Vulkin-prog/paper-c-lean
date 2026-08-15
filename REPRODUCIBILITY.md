# Reproductibilité

## Versions fixées

- paper_c_lean : `0.48.1` candidate (no tag/release yet)
- Lean : `v4.32.2`, commit
  `f3b06c705e6c85f5314019d5d3baab0fec5b580c`
- mathlib : `v4.32.2`, commit
  `905b95818eb32af7874a58b427f50c1711a5e96c`
- Comparator : commit
  `51491237b1d2f96cca203af9c34bced6fe38e0d8`
- lean4export : commit
  `af5aa64bb914c3c2c781f378088dbd38acf4f804`, compilé avec Lean
  `v4.32.2`
- landrun : commit
  `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`
- modèle officiel `formalization.yaml` v0.3 : commit
  `fab03cbbed1a5857de17af32de30421a734c77c6`
- PDF cible anglais (77 pages ; 936767 octets), SHA-256 :
  `ccef4908838fc3b428aed862937a6a3a9129fc6e378fa7368384a9ed45b05189`
- PDF source français synchronisé (79 pages ; 947656 octets), SHA-256 :
  `262ec27afc494fdaf6ad879c44ac553711cc74d9281a4f7ab919a23226281d45`
- racine unique de l’archive : `paper_c_lean/`
- archive de livraison prévue : `paper_c_lean_v0481.zip`


> **Qualification.** Les lignes ci-dessus décrivent le snapshot source. Ses
> métadonnées fixent les définitions et empreintes Comparator sans intégrer de
> verdict produit après le gel. Le résultat de qualification de release est
> donné exclusivement par `release_evidence/v0.48.1/` dans un commit
> d’empaquetage validé, à parent unique, dont le parent est ce commit source
> exact. Le snapshot
> ne prétend donc ni qu’une preuve ultérieure est absente, ni qu’elle a réussi.
> La publication reste soumise aux autres portes de
> [`RELEASE_QUALIFICATION.md`](RELEASE_QUALIFICATION.md).

Le fichier `lean-toolchain` et la révision de `lakefile.toml` rendent ces choix
reproductibles. Il n’existe pas de tag officiel Comparator/lean4export
`v4.32.2` : les commits complets ci-dessus sont donc normatifs. Le binaire
lean4export doit être compilé séparément avec la toolchain Lean de Paper C,
et non remplacé silencieusement par le binaire construit sous la toolchain
plus récente propre à Comparator.

Le candidat courant a recalculé les octets présents dans le dépôt :
`paper_C_complete_v09_en.pdf` est le blob Git
`244d34ed8a5d8b1dfac4619a2d8cee507c94c09f`, mesure 936767 octets et a pour
SHA-256
`ccef4908838fc3b428aed862937a6a3a9129fc6e378fa7368384a9ed45b05189` ;
`paper_C_complete_v09.pdf` est le blob Git
`87f67c04ac86ab3bc357438a44fc25ae83ac5612`, mesure 947656 octets et a pour
SHA-256
`262ec27afc494fdaf6ad879c44ac553711cc74d9281a4f7ab919a23226281d45`.

## Périmètre du correctif 0.48.1

Le candidat v0.48.1 modifie le cœur Lean et l’interface Comparator principale,
en plus des deux PDF. Il construit désormais en Lean la descente de conducteur
par réduction modulo deux : `HK13-QO-conductor-fibres` reste enregistré avec
`kind: external` pour sa provenance historique, mais passe à
`status: discharged` grâce au théorème interne
`PaperC.PellInput.quadraticOrderConductorFiberBound`. Le registre candidat
compte donc treize ponts, dont six `external/open` et sept `discharged`.

Le Théorème 1.1 canonique et la cible Comparator principale ne prennent plus
que trois prémisses ordinaires ouvertes : Arratia--Goldstein--Gordon,
Evertse--Silverman et Nicolas--Robin. Le Théorème 16.2 en prend exactement six :
PNT, Laishram--Shorey, Balasubramanian--Shorey, AGG, Evertse--Silverman et
Nicolas--Robin. Les autres endpoints canoniques concernés ne reçoivent plus
Halter--Koch comme prémisse ouverte.

Le répertoire `literature_certificates/` contient trois certificats actifs
pour les trois prémisses du Théorème 1.1 et une note historique de clôture
Halter--Koch. Les quatre fichiers appartiennent au fileset documentaire haché,
mais seuls les trois premiers comptent comme certificats actifs du théorème.

La preuve Comparator durcie publiée avec v0.48.0 porte exclusivement sur les
anciens octets du cœur et de la cible à quatre prémisses. Elle est historique
et périmée pour ce snapshot. Le schéma 5 sépare désormais explicitement
`source_snapshot_comparator_state: definitions_and_digests_only` de
`release_evidence_state: external_to_source_snapshot`, fixe
`release_evidence_location: release_evidence/v0.48.1/` et exige
`packaging_commit_required: true`. Un verdict courant éventuel doit donc être
lu dans la preuve d’empaquetage liée, jamais inféré du snapshot source. Les
nombres exacts de déclarations et de cibles, ainsi que les digests du cœur, du
fileset Comparator et du fileset documentaire, sont lus dans les artefacts
générés de ce commit.

## Périmètre du jalon 0.48.0 (historique)

La v0.48.0 est additive sur le plan mathématique. Les 382 sources du cœur
(`PaperC.lean` et les 381 fichiers sous `PaperC/`) restent byte-identiques à
la v0.47.0, leurs déclarations et signatures canoniques sont inchangées, les
deux PDF gardent les empreintes consignées dans le tag v0.48.0, et le registre
reste à 13 ponts, dont sept `external/open` et six `discharged`.

La nouvelle frontière humaine comprend :

- `Challenge.lean`, qui importe seulement Mathlib et énonce la forme
  quantitative finite-cylinder du Théorème 1.1, page PDF/imprimée 3 ;
- `Solution.lean`, qui reproduit directement et exactement dans le namespace
  frais `PaperCAudit` la clôture déclarative du Challenge sans l’importer,
  puis se ramène à
  `PaperC.CorollaryThirteenTen.theorem_one_one_uniformBigO_canonical` ;
- `ChallengeTransfer.lean` et `SolutionTransfer.lean`, seconde paire dans
  laquelle la Solution reproduit directement l’interface propre au transfert
  sans importer son Challenge, cible indépendante pour l’identité exacte de
  la loi du modèle produit infini et de la loi du cylindre fini ;
- les configurations `comparator/theorem_one_one.json` et
  `comparator/theorem_one_one_transfer.json`, avec la liste explicite
  `propext`, `Quot.sound`, `Classical.choice` et `enable_nanoda: false`.

Le Théorème 1.1 est énoncé sans condition dans le manuscrit. La cible
Comparator prouve la même conclusion sous quatre propositions ordinaires
entièrement explicitées. Comparator vérifie cette implication ; il ne vérifie
ni que les sources citées impliquent ces propositions, ni à lui seul la
fidélité papier--Challenge. La cible séparée de transfert infini--fini est
inconditionnelle et exacte.

Le premier énoncé consomme exactement quatre hypothèses ordinaires :
Arratia--Goldstein--Gordon
(`AGG89-T1-finite-dependency-b3-zero`), Evertse--Silverman
(`ES86-T1b-Q-split-n2`), Halter--Koch
(`HK13-QO-conductor-fibres`) et Nicolas--Robin
(`NR83-T1-divisor-log-bound`). Elles sont développées dans le Challenge et ne
sont pas des axiomes Lean. Deux traductions non définitionnelles sont rendues
explicites et prouvées dans `Solution.lean` : celle du record de probabilité
finie d’Arratia--Goldstein--Gordon et celle du record de conducteur d’ordre
quadratique de Halter--Koch.

Les écarts de présentation sont explicites : cylindre fini de cutoff
`2*N+L` au lieu du produit infini, transfert exact dans une seconde cible,
distance totale écrite avec la normalisation demi-ℓ1, fenêtre critique
`|L-log N/log 2| ≤ C`, et Big-O uniforme développé en un même seuil et une
même constante pour tous les `L` admissibles. Le Challenge accepte le
renforcement inoffensif `C ≥ 0`, contre `C > 0` dans le papier. Le théorème
global du plus long run est exclu de cette livraison.

`audit_config.json` passe au schéma 2 et constitue l’unique source éditoriale
de la cartographie des items du papier. Le générateur produit
déterministement `audit_manifest.json` et `formalization.yaml` v0.3 ; il
contrôle l’existence et le fichier des déclarations, les identifiants de
ponts, la concordance de la conditionnalité, l’appartenance des cibles
Comparator à `theorem_names` et l’unicité des identifiants d’items. La
complétude éditoriale de la liste ne peut pas être inférée automatiquement et
reste à relire. Le statut de revue déclaré est `agent-reviewed`, non une revue
indépendante. `Challenge.lean` importe uniquement des modules Mathlib et
`ChallengeTransfer.lean` importe exactement `Challenge`. Chaque fichier
Challenge contient exactement un `by sorry`, sur son théorème Comparator
nommé ; l’environnement transitif du transfert contient aussi le placeholder
du premier Challenge. Aucune Solution n’importe un Challenge, et les Solutions
comme le cœur ont un compte de `sorry` nul.

L’ensemble du cœur et le nouvel ensemble Comparator possèdent des digests
séparés : le SHA-256 historique du cœur est
`f6020b0bae9b8c6f22ab6ed0b6c3024a22e0a697ddb5578bb65c5e1f2a56c999`
et celui du fileset Comparator v0.48.0 est
`646e3ba055daf0509ba70237f4e87c59e18fa697b4698a4647ef5f04435757a5`.
Le fileset additif des quatre rapports bibliographiques rc2 a son propre
SHA-256,
`6e4b3e86107bc68911778830c50e66139c6c6d56b037d8143a235d2a8cbd2996` ;
il n’appartient à aucun des deux filesets Lean gelés.
`Challenge.lean` et `ChallengeTransfer.lean` sont exclus de l’audit
« zéro sorry » des preuves mais inclus dans le digest Comparator et les gardes
structurelles. `Solution.lean` et `SolutionTransfer.lean` ne sont jamais
importés simultanément avec leur Challenge homonyme dans `AuditCheck.lean`.

**Statut durci enregistré.** Les deux cibles Paper C ont réussi la procédure
locale durcie au commit Paper C
`27c91f8bdd5c3f4eeda4183eb3bfd7453a14ba07`. Les exécutions ont utilisé
landrun réel sous `systemd-run --user --pty`, un utilisateur non root, des
capacités héritées, effectives, permises et ambiantes nulles, ainsi que
`NoNewPrivileges`. Comparator a construit chaque paire Challenge/Solution
dans un checkout propre distinct ; le noyau Lean par défaut a accepté les deux
solutions avec un code de retour nul.

L’archive publique est
`paper-c-hardened-public-27c91f8.tar.zst`, publiée dans la release `v0.48.0`.
Elle pèse 49 765 octets et son SHA-256 est
`7279ed99e6b1a98b6458fe1f8d95dd1f68af445646ee6a23d0044c7bee94ce50`.
Elle conserve byte-identiques le résumé (SHA-256
`b1d956eeee5451a64dbbdab495fe2f56f22b7ee06e2d65624394b3fee5ca41fb`),
les deux enregistrements de résultat, les 12 fichiers du snapshot source et
l’inventaire brut des empreintes. Le digest du fileset Comparator est
`646e3ba055daf0509ba70237f4e87c59e18fa697b4698a4647ef5f04435757a5`.
`REDACTION_MANIFEST.json` (SHA-256
`01c3619d80786999a323c8b2073c4e674bf97af46f179b7e1434af53f3b6f29b`)
lie par SHA-256 les 17 membres conservés et les 13 membres omis.

L’archive source privée `paper-c-hardened-27c91f8.tar.zst` pèse 98 049
octets et son SHA-256 est
`a4f5469e7c57236dc22f480297591d322eeda0f9d3cf9b7b0a7ff55cb4f6ae89`.
Elle reste locale et n’est pas publiée : les journaux et transcripts omis
contiennent utilisateur, hôte, groupes locaux, HOME/PATH et chemins
temporaires. Les SHA-256 des transcripts bruts principal et transfert restent
liés cryptographiquement :
`fed5cf1fd82037c98c1b3f4c713189958ac92b5ceb58982e0e1093f31ce7599e`
et
`13703cb6794c4102b6d172e6632fddb1df75d6d47dfa32e46f63030adea33076`.
Le paquet public conserve ainsi les liaisons du résultat certifié, mais ne
permet pas une inspection indépendante ligne par ligne de la trace hôte
complète. Le générateur valide les enregistrements minimisés du dépôt et leurs
liaisons aux configurations et au fileset ; il ne télécharge ni ne revalide
l’asset de release GitHub.

Ce résultat historique est limité au noyau Lean : `enable_nanoda` vaut `false`
dans les deux configurations, Nanoda n’a pas été exécuté et aucun résultat à
deux noyaux n’est revendiqué. Le certificat porte sur les octets du fileset
Comparator au commit `27c91f8bdd5c...`. La couche finale de métadonnées
v0.48.0 laisse ce fileset de six fichiers et les deux PDF byte-identiques. Il
ne décharge pas les quatre prémisses ordinaires de littérature et ne certifie
pas à lui seul la fidélité papier--Challenge. Le candidat v0.48.1 ne conserve
ni le cœur Lean ni la cible Comparator principale à l’octet : la preuve
v0.48.0 est donc périmée pour le nouveau théorème à trois prémisses, en plus de
ne pas lier les nouvelles empreintes des manuscrits. Ce passage décrit
uniquement l’historique v0.48.0. Pour v0.48.1, le snapshot source ne porte
volontairement aucun verdict temporel ; la couche d’empaquetage liée porte le
résultat de qualification.

Dans le jalon v0.48.0, les quatre rapports sous
`literature_certificates/` formaient un fileset séparé et haché. Ils
consignaient une contre-expertise par agents, pas une preuve Lean ni une revue
humaine. AGG, Evertse--Silverman et Nicolas--Robin avaient le statut
documentaire `agent_checked_supports`, tandis que Halter--Koch conservait un
gap source→record et un pont Lean ouvert. Dans le candidat actuel, les trois
premiers restent les certificats actifs ; le quatrième fichier est conservé
comme note historique de clôture, incluse avec eux dans le digest documentaire.
Le pont Halter--Koch est maintenant `external/discharged` par la construction
Lean interne modulo deux, indépendamment d’une formalisation des pages citées.

Un probe antérieur de compatibilité de la suite de tests upstream a également
été exécuté sans sandbox avec fake-landrun. Son
transcript est
`comparator/transcripts/toolchain_compatibility_unsandboxed.txt`, SHA-256
`2ee3dcde7fee2dc4a31b1cc4395ea9f5d31f2b2526741f6f18f6463991c25cd5`.
Il n’a chargé aucune configuration Paper C ; il est distinct des deux smoke
tests sémantiques du projet enregistrés ci-dessus.

### Périmètre hérité de la v0.47.0

La v047 conserve Lean/mathlib `v4.32.2`, tout le contenu mathématique de la
v045 et le registre de 13 ponts (sept `external/open`, six `discharged`). Elle
ferme le défaut racine de la v046 : `PaperC.lean`, cible de la bibliothèque
Lake, appartient désormais au digest, au recensement des déclarations, à la
recherche des ponts et à l’import de l’audit. Le manifeste v0.48 expose cet
ensemble historique sous
`core_source_fileset: ["PaperC.lean", "PaperC/**/*.lean"]`, et le générateur
l’énumère avec `fs` sans dépendre de `rg`. Deux gardes automatiques vérifient
le digest et l’inventaire sur ce fichier. La v046 avait rendu le triplet
manuscrits--sources--audit auto-contenu et introduit le hachage des octets
réels des deux PDF. Les comptes de déclarations ci-dessous proviennent du
manifeste v047 régénéré ; les nombres de fichiers et de lignes sont reproduits
par les commandes mécaniques indiquées plus bas.

### Historique v044–v042

La v044 est une re-synchronisation documentaire à contenu Lean gelé. Elle
fait de l’édition anglaise v08 la cible de soumission et enregistre l’édition
française v08 comme source synchronisée. Elle conserve exactement les 3 976
déclarations publiques, leurs signatures, les 3 978 cibles d’audit et le
registre de 13 ponts de la v043. La toolchain reste Lean/mathlib `v4.32.2`.

La v043 avait porté Lean et mathlib de `v4.19.0` à `v4.32.2`, adapté les
imports déplacés ainsi que les alias d’API retirés des corps de preuve, et
conservé à l’identique les déclarations, les signatures publiques et le
registre d’audit de la v042.
Les sept familles d’imports adaptées sont :

- `Data.Complex.ExponentialBounds` vers
  `Analysis.Complex.ExponentialBounds` ;
- `Analysis.SpecialFunctions.Integrals` vers
  `Analysis.SpecialFunctions.Integrals.Basic` ;
- `Algebra.GeomSum` vers `Algebra.Field.GeomSum` ;
- `NumberTheory.ArithmeticFunction` vers
  `NumberTheory.ArithmeticFunction.Misc` ;
- `Combinatorics.SimpleGraph.Path` vers
  `Combinatorics.SimpleGraph.Paths` ;
- `RingTheory.DedekindDomain.Ideal` vers
  `RingTheory.DedekindDomain.Ideal.Lemmas` ;
- `Probability.Distributions.Poisson` vers
  `Probability.Distributions.Poisson.Basic`.

Les deux empreintes du manuscrit se contrôlent par :

```bash
sha256sum paper_C_complete_v09_en.pdf paper_C_complete_v09.pdf
```

La v042 conserve la fermeture du §14 obtenue en v040 sous forme de
caractérisation par fonctionnels de Laplace. Elle conserve le modèle produit
infini, le lemme 14.4, la décomposition exacte et le lemme 14.7, notamment :

- les sommes de Riemann dyadiques et les limites des paramètres aminci
  spatial et marqué ;
- l’amincissement indépendant générique et l’identité exacte
  vide--fonctionnel exponentiel ;
- le graphe de dépendance marqué, les bornes locales de rang, la séparation
  locale/éloignée et les petits-oh canoniques de \(b_1,b_2\) ;
- les identités exactes entre intégrales, PMF finies et loi source infinie ;
- les limites de Laplace des PPP spatial et marqué sous AGG,
  Evertse--Silverman, Halter--Koch et Nicolas--Robin ;
- `FullMarkedLaplaceTransfer`, qui définit la fonctionnelle marquée source
  complète par une somme sur tous les excès et l’identifie exactement,
  point par point puis en espérance, à la version tronquée pour tout test à
  support fini en marques ;
- la tension uniforme des marques, la loi limite du maximum et les
  transferts exacts du vecteur des comptes.

Le changement propre à la v042 est l’ajout de l’unique déclaration publique
`PaperC.SectionTwelveMoments.theorem_one_four_canonical`. Elle raccorde le
noyau fini du §12 directement à la masse mère quantitative et conclut au taux
du premier moment, au petit-oh du second moment factoriel, à
\(R_2(N,L)=o_C(N^2)\) et au petit-oh de la variance. Ses hypothèses sont
exactement `ES86-T1b-Q-split-n2`, `HK13-QO-conductor-fibres` et
`NR83-T1-divisor-log-bound`, sous-ensemble strict des quatre références
externes autorisées. Les 3 975 signatures publiques antérieures et le
registre des 13 ponts sont inchangés.

Le changement propre à la v041 est un nettoyage d’API par suppressions : les
quatre interfaces `internal/open` de 9.9, 9.11, 10.1 et 11.3 et leurs 27
consommateurs publics disparaissent ; douze endpoints recevant directement
Pell ou son ancienne enveloppe et six adaptateurs sectoriels intermédiaires
disparaissent également. Les signatures canoniques sont inchangées. Les six
interfaces `discharged`, ainsi que les deux assemblages génériques directs
de 16.1 et 16.2 qui consomment les trois interfaces sectorielles historiques,
sont conservés.

La convergence PPP est revendiquée exactement par sa famille complète de
fonctionnels de Laplace et, dans le cas marqué, par la tension uniforme.
Le prédicat public marqué est formulé littéralement avec
`infiniteFullMarkedLaplaceExpectation`; le cutoff porté par un test compact
sert uniquement à appliquer l’égalité complète/tronquée et l’argument fini
de Stein--Chen, non à remplacer la fonctionnelle source de l’endpoint.
Le dépôt ne s’appuie pas actuellement sur une API mathlib de mesures
ponctuelles munie de la topologie vague qui permettrait de reformuler cette
même conclusion comme un `Tendsto` de lois. La conversion abstraite des
transformées inverses en masses atomiques est désormais prouvée dans
`DirichletAtomConvergence`, après l’encodage
injectif des vecteurs par `PrimeEncodedCountVector`.
`PrimeEncodedCountLaplace` construit la loi source poussée et l’identifie
aux tests constants \(s\log p_e\), tandis que `PoissonVectorMass` calcule les
transformées de la cible produit--Poisson. Le wrapper canonique du
corollaire 14.8 est donc fermé sans prémisse de convergence supplémentaire.

Les métriques exactes du jalon se reproduisent par :

```bash
{ printf '%s\n' PaperC.lean; find PaperC -name '*.lean' -type f; } | wc -l
{ printf '%s\0' PaperC.lean; find PaperC -name '*.lean' -type f -print0; } | xargs -0 wc -l | tail -n 1
```

La v047 contient **381 modules sous `PaperC/`**, plus le module racine
`PaperC.lean`, soit **382 fichiers sources audités** et **146 391 lignes
Lean**. Le manifeste
recense **4 065 théorèmes** et **5 lemmes**, soit **4 070 déclarations
publiques** et **4 072 cibles d’audit** (les deux cibles supplémentaires sont
les constructions historiques explicitement retenues par la liste blanche).
Le partage est de **3 912 résultats sans prémisse de pont enregistrée** et
**158 résultats conditionnels**. Par rapport à la v044 gelée, 94 noms publics
sont ajoutés, aucun n’est supprimé et aucune signature antérieure n’est
modifiée. Le registre reste exactement à 13 ponts : huit `external`, cinq
`internal`, sept `open` tous `external`, et six `discharged`.

La v044 conserve **373 modules** et **142 840 lignes Lean**. Les **521 lignes**
ajoutées en v043 par rapport à la v042 sont uniquement des adaptations de
corps de preuve à Lean 4.32.2 ; les modules et les signatures publiques sont
inchangés.

Le jalon 0.43 conserve la décharge de l’interface interne de Pell généralisé :

- `GeneralizedPell` traduit les solutions en éléments de `Zsqrtd`, prouve
  que leur idéal principal divise \((M)\), puis transforme l’égalité de deux
  idéaux en une unité de norme un ;
- la coordonnée de cette unité est bornée par \(2H^2\), les puissances d’une
  unité fondamentale croissent au moins comme \(2^n\), et une fibre d’idéal
  contient donc au plus une quantité logarithmique explicite de solutions ;
- `QuadraticIdealDivisors` prouve par factorisation unique que `(M)` possède
  au plus \(\tau(|M|)^2\) diviseurs idéaux dans tout corps quadratique ; le
  compte est alors sommé sur quatre couleurs de conducteur, puis transporté
  du noyau carré-libre à tout \(D>0\) non carré ;
- `PellDivisorEnvelope` part de l’inégalité logarithmique directe de
  Nicolas--Robin et prouve en Lean la substitution polynomiale, les petits
  cas, le carré du facteur divisoriel et l’absorption du compte d’unités dans
  \(\exp(c\log N/\log\log N)\).

À ce jalon historique, les deux seuls faits non formalisés de ce nouveau
module sont enregistrés comme `external/open` :
`HK13-QO-conductor-fibres` pour la comparaison
conducteur 2 entre l’ordre \(\mathbb Z[\sqrt D]\) et l’ordre maximal, et
`NR83-T1-divisor-log-bound` pour l’inégalité logarithmique divisorielle.
L’ancienne enveloppe spécialisée `NR83-T1-divisor-bound` est conservée avec
`status: discharged`.
`PCv07c-L9.2-generalized-Pell` est désormais `discharged`.

À ce même jalon, les théorèmes canoniques de masse mère, 1.4, 13.10, 1.1,
16.1 et 16.2 exposent directement ces entrées externes. Ils ne consomment aucun pont
`internal/open`. La v041 supprime les anciennes signatures directes Pell,
leurs variantes fondées sur l’enveloppe spécialisée et les quatre API legacy
ouvertes. Il ne reste aucun pont `internal/open` dans le registre.

Le jalon 0.43 conserve tous les résultats antérieurs, notamment les deux
dernières estimations sectorielles qualitatives de la section 17 :

- `PrimeFactorsFactorialBound`,
  `BoundedRatioManyDefectsDegreeTwoSum` et
  `BoundedRatioManyDefectsEvertseSum` prouvent uniformément
  \(N^{o(1)}\) les facteurs de diviseurs signés, de Pell et
  d’Evertse--Silverman laissés par les fibres fixées de 17.26 ;
- `BoundedRatioManyDefectsRealFibers`,
  `BoundedRatioManyDefectsDegreeAssembly` et
  `BoundedRatioManyDefectsAssembly` agrègent les degrés \(1,2,\ge3\), les
  bases et les formes, et concluent
  \(N^{3/2+o_{C,\kappa_0}(1)}=o_{C,\kappa_0}(N^2)\) sous
  Evertse--Silverman et l’interface Pell désormais déchargée ;
- `BoundedRatioTwoSingletonHosts` formalise l’injection des paramètres
  \((e,c,u,v)\), la somme harmonique, l’identité
  \(\tau(d)=2^{\omega(d)}\) pour \(d\) carré-libre et le produit
  \(\prod_{p\le B}(1+2/\sqrt p)\) ;
- `BoundedRatioTwoSingletonCritical` transporte ce compte dans la fenêtre
  critique. Le compte global emploie le facteur sûr \(9B^4\), et non le
  facteur source-sharp \(B^2\), puis absorbe cette perte polynomiale dans une
  constante explicite \(C_{\rm term}\) ;
- `BoundedRatioNonterminalHostCounts`,
  `BoundedRatioNonterminalRealHosts` et
  `BoundedRatioNonterminalMobileAssembly` traitent la branche modérée de
  support au plus dix ; `BoundedRatioNonterminalAssembly` combine les deux
  branches et choisit
  \(K=(2C_{\rm term}+1)/\log2\), ce qui ferme 17.28 sous les mêmes entrées.

Il ferme en outre l’interface arithmétique de 9.10 dans sa portée exacte :

- `canonicalCoreBoundaryLinearEquivLargePrime_of_choice_none` montre que,
  lorsque `canonicalReducedCandidate? = none`, les coordonnées canoniques
  \(D^\#+c^\#\) paramètrent tout l’espace des solutions des grands premiers ;
- sous \(x+L\le M\) et \(y+L\le M\),
  `relationToCanonicalArithmeticKernel_of_choice_none` envoie chaque
  relation complète dans le noyau de la matrice concrète des petits premiers
  et des deux lignes de parité ;
- l’injectivité et la surjectivité de ce morphisme donnent
  `relationLinearEquivCanonicalArithmeticKernel_of_choice_none` ;
- le code rationnel canonique est nul dans cette branche, si bien que
  `canonicalArithmeticKernelEquivalence_of_choice_none` construit
  l’équivalence entre le quotient résiduel et ce noyau sans hypothèse
  arithmétique.

Pour une paire à rapport borné, \(L+1\le M_{\rm cut}\) et les deux
couvertures d’extrémités sont déduites de l’appartenance au bloc. Les chemins
canoniques des populations terminales, de la proposition 16.1 et du théorème
16.2 appliquent donc directement cette fermeture.

La géométrie de densité est simultanément paramétrée par des entiers
\(\alpha_{\rm num},\alpha_{\rm den},K\), sous
\(16\alpha_{\rm num}\le3\alpha_{\rm den}\) et
\(2\alpha_{\rm den}<\alpha_{\rm num}(K+1)\). L’instance historique
\(3/16,\ K=10\) reste un corollaire portant les mêmes noms publics.

Les trois interfaces historiques 17.26, 17.28 et 17.30 restent enregistrées
pour les deux assemblages génériques directs avec `status: discharged`; les
six adaptateurs sectoriels intermédiaires de 16.1 et 16.2 sont supprimés.
L’interface historique
de 9.10 porte désormais le même statut, ainsi que l’interface de 9.2. Les API
canoniques de 16.1 et 16.2 n’en consomment aucune. Dans le candidat v0.48.1,
la première reçoit seulement Evertse--Silverman et Nicolas--Robin. La seconde
ne reçoit plus ni \(K\), ni famille terminale, ni estimation de la section 17,
ni hypothèse arithmétique de 9.10, ni prémisse Halter--Koch : ses six seules
prémisses non formalisées sont PNT, Laishram--Shorey,
Balasubramanian--Shorey, AGG, Evertse--Silverman et Nicolas--Robin.

Le jalon conserve aussi la fermeture complète des propositions 7.3, 7.4 et 7.5
et traite le cœur aligné laissé par leur partition. La condition de densité
est encodée sans arrondi par
\[
3B<16c^\#,\qquad B=L+1.
\]
Lean retire les deux exceptions exactes possibles et prouve qu'il reste au
moins \(B/16\) composantes exact-free de taille au plus \(43\). Il construit
la matrice \(\Phi\), ses deux lignes de parité, le mot court et le produit
carré, puis transforme celui-ci en un polynôme de Runge à racines distinctes.
Le rayon entier certifié est
\[
t(B)=\left\lceil
\frac{64B}{\lfloor\log_2B\rfloor
\lfloor\log_2\lfloor\log_2B\rfloor\rfloor}
\right\rceil.
\]
Dans la fenêtre \(\lvert L-\log_2N\rvert\le C\), Lean vérifie uniformément
le budget de Hamming, la borne réelle
\[
t(B)\le
\frac{65B}{\log B\,\log\log B},
\]
la condition \(2(3HB)\le ax\), et pour tout \(1\le k\le43t(B)\),
\[
\bigl(128(2k)(3HB)\bigr)^{4k}<ax.
\]
Le théorème public
`TheoremEightAlignedClosure.no_aligned_deep_core_eventually` assemble ces
résultats et exclut le cœur aligné de densité \(3/16\) pour \(H\le B^A\).

Le jalon 0.22 ajoute cinq modules. `PropositionNineNine` ferme toute la
partie combinatoire et asymptotique de la proposition 9.9 sous le seul compte
d'hôtes enregistré comme dette interne. `CanonicalExactRank` construit les
coordonnées concrètes de cardinal \(D^\#+c^\#\), la matrice finie des petites
lignes et l'identité exacte du lemme 9.10 sous une présentation interne
explicite. `CanonicalTerminalPopulation` raccorde le compte \(B-3s\) aux
composantes résiduelles canoniques, définit un proxy de \(T_K\) à fonction de
rang et budget entiers fournis, puis prouve les décompositions finies et la
borne pondérée de l'étape 4 du théorème 10.1.
`SectionElevenPartition` et `CanonicalSectionElevenPartition` certifient enfin
la partition ordonnée en sept secteurs, sa couverture, sa disjonction, son
unicité et son instanciation par le proxy terminal ; le secteur 7 est
exactement la partie canoniquement non alignée de ce proxy.

Le manifeste de ce jalon historique conserve la distinction indépendante
entre `kind` et `status`.
Les interfaces 9.2 et 9.10 rejoignent 17.26, 17.28 et 17.30 avec
`status: discharged`; seul `status: open` signale une dette actuelle.
Il recense 13 interfaces — huit `external` et cinq `internal` — dont sept
`open`, toutes `external`, et six `discharged`. Il recense en outre **3 971
théorèmes** et **5 lemmes** publics, soit **3 976 déclarations**, **3 978
cibles d’audit**, **3 825 résultats inconditionnels** et **151
conditionnels**. Il ne reste aucune interface `internal/open`.

Le parseur de `scripts/generate_audit.mjs` reconnaît en v035 les déclarations
où `theorem` ou `lemma` est seul sur une ligne et le nom commence sur la
suivante. Un auto-test couvre ce cas ; six cibles, dont trois historiques,
sont ainsi réintégrées rétroactivement dans l’audit exhaustif.

Le jalon 0.19 ajoute l'interface conditionnelle du lemme 9.1. Le résultat
externe d'Evertse--Silverman est un argument explicite du théorème Lean qui
borne par \(7^{4+9|S|}\) les abscisses de la branche \(Z\ne0\). Lean prouve
qu'il y a au plus deux ordonnées par abscisse et en déduit le majorant
\(2\cdot7^{4+9|S|}\) de (9.2). Il ajoute ensuite la branche \(Z=0\), de
cardinal au plus \(d\), et transporte le compte total de
\(Z^2=e\prod_r(X+h_r)\) vers celui de
\(\prod_r(X+h_r)=eY^2\) par l'injection
\((X,Y)\mapsto(X,eY)\). Cette architecture ne certifie pas le résultat
externe ; elle certifie son usage et empêche qu'il soit masqué dans
l'assemblage ultérieur.

Le jalon 0.20 ajoute l'interface conditionnelle du lemme 9.2 pour un exposant
polynomial entier positif. Le pont enregistré contient le compte uniforme du
Pell généralisé. Lean vérifie séparément la réduction
\((z,w)\mapsto(Az,w)\), avec \(D=AC\) et \(M=Ae\), sa non-carréité, les
bornes de hauteur et le transfert du compte. Le jalon 0.34 complète cette
interface pour tout paramètre réel \(K_0>0\), puis établit le prédicat
source-exact \(|z|,|w|\le N^{K_0}\) par le rayon entier
\(\lfloor N^{K_0}\rfloor\).

Le jalon 0.21 ajoute dix modules couvrant les réductions finies des lemmes
9.3--9.8, la formule abstraite de rang du lemme 9.10, le compte terminal de
la proposition 9.11, le paquet arithmétique du lemme 9.12 et plusieurs étapes
du théorème 10.1. Les normalisations, injections, paramétrisations,
factorisations, comptes de composantes, déterminants, doubles comptages et la
borne finie de \(A_{B,T}(X)\) sont vérifiés par Lean. Les appels à
Evertse--Silverman et au Pell généralisé restent des arguments ordinaires
enregistrés ; les sommes asymptotiques non encore raccordées ne sont pas
revendiquées.

## Vérifications attendues

Ces commandes doivent être lancées depuis une extraction neuve de l'archive,
sans répertoire `.lake/build` hérité d'une version antérieure. Après la mise
en place ponctuelle des dépendances (`lake exe cache get`), l’ordre de la CI
et de la validation de release est exactement le suivant :

```bash
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

Cette séquence est exécutable telle quelle dans une extraction neuve du ZIP :
elle ne suppose pas de répertoire `.git`. Le mode `--check` compare les octets
des artefacts générés livrés à leur régénération déterministe. Dans un checkout
Git seulement, on peut ajouter le contrôle complémentaire suivant :

```bash
git diff --exit-code -- AuditCheck.lean audit_manifest.json formalization.yaml AXIOM_AUDIT.md
```

Le premier contrôle ouvre et hache les octets réels des deux PDF ; il échoue
si l’un d’eux manque ou diffère de `audit_config.json`. Le deuxième recalcule
le digest du `core_source_fileset` exact `PaperC.lean` plus
`PaperC/**/*.lean` et le compare au manifeste versionné. Le scan d’hygiène
couvre explicitement ces deux branches ; l’absence de correspondance est le
résultat attendu. Le script `scripts/check_comparator_sources.mjs` contrôle
séparément les imports, les placeholders intentionnels et les tokens interdits
de la frontière Comparator. Les gardes temporaires prouvent qu’une modification
de `PaperC.lean` invalide le digest et qu’un théorème public ajouté à la racine
entre dans l’inventaire et reçoit son `#print axioms`; elles vérifient aussi
qu’un octet modifié dans un rapport bibliographique invalide son digest. Les
gardes d’interface imposent que `Challenge.lean` n’importe que des modules
Mathlib et que `ChallengeTransfer.lean` importe exactement `Challenge`. Chaque
fichier Challenge contient exactement un `by sorry`, sur le théorème
Comparator nommé. Elles interdisent `sorry`, `axiom`, `admit`, `opaque`,
`unsafe`, `partial`, `native_decide` et `definition_names` dans les deux
Solutions et leurs éventuels modules d’appui. Les artefacts générés sont
contrôlés sans réécriture après les
builds ordinaires séparés, puis l’audit exhaustif est exécuté. La sortie de
l’unique exécution Lean
est conservée, puis vérifiée pour l’exhaustivité et la liste blanche. Le
`--check` final hache à nouveau les deux PDF et exige que les quatre artefacts
générés soient exactement à jour. Le workflow public
`.github/workflows/reproducibility.yml` applique cet ordre : le contrôle du
manifeste est la dernière validation, après laquelle `AuditCheck.log` est
archivé. Le générateur ne dépend plus de `rg` ; le workflow installe
néanmoins explicitement `ripgrep` juste avant le scan d’hygiène.

Le scan d’hygiène indépendant ci-dessous ne doit produire aucune ligne :

```bash
rg -n '(^|[[:space:]])(sorry|axiom|admit|native_decide|unsafe|partial)([[:space:]]|$)' --glob '*.lean' PaperC.lean PaperC
```

Pour le candidat 0.48.1, la validation ordinaire doit être rejouée depuis
deux arbres indépendants dépourvus de `.lake/build`, dont une extraction du
ZIP final. Dans chacun, le build doit se terminer par
`Build completed successfully`. L’audit doit produire une sortie pour chaque
théorème ou lemme public et pour les deux constructions porteuses de preuves
conservées de l’audit historique. Toutes les listes doivent rester incluses
dans `[propext, Classical.choice, Quot.sound]`. Le contrôle du générateur doit
retrouver exactement les comptes du manifeste final régénéré et enregistrer
9.2, 9.10, 17.26, 17.28, 17.30 et l’ancienne enveloppe Nicolas--Robin avec
`status: discharged`, ainsi que `HK13-QO-conductor-fibres` avec
`kind: external` et `status: discharged`. Il doit retrouver 13 interfaces —
huit `external`, cinq `internal`, six `open` toutes `external` et sept
`discharged` — et exactement les comptes de déclarations, cibles et résultats
du manifeste candidat régénéré, sans recopier ceux de v0.48.0. Il doit vérifier
que le Théorème 1.1 et la cible Comparator principale consomment trois ponts
ouverts, et que le Théorème 16.2 en consomme six. Il ne doit retrouver aucune
interface `internal/open`. Le scan des constructions interdites doit rester
vide.

Pour inspecter les dépendances logiques d'un théorème particulier :

```lean
#print axioms PaperC.nomDuTheoreme
```

L'audit ne demande pas nécessairement une liste vide : certaines preuves
finies légitimes de mathlib dépendent de `propext`, `Classical.choice` et
`Quot.sound`. La sortie attendue doit rester dans cette liste blanche
fondationnelle et ne doit notamment faire apparaître aucun des éléments
suivants :

- `sorryAx` ;
- `Lean.ofReduceBool` (introduit notamment par `native_decide`) ;
- tout axiome mathématique propre au papier.

Les petits calculs décidables de ce dépôt utilisent donc `decide`, pas
`native_decide`.

`AuditCheck.lean` importe le point d'entrée racine `PaperC` et applique
un `#print axioms` à chaque déclaration publique explicite `theorem` ou
`lemma` sous `PaperC`. Les déclarations `private` et `local` sont exclues :
leurs dépendances remontent transitivement dans les théorèmes publics qui les
utilisent. Deux équivalences linéaires publiques porteuses de preuves, déjà
présentes dans l'audit historique, sont ajoutées explicitement. Les noms
triés, sans doublon, sont reproduits dans `audit_manifest.json`.

`scripts/generate_audit.mjs` énumère nativement l’ensemble exact enregistré
dans `core_source_fileset`, calcule séparément `comparator_fileset`, puis
dérive `AuditCheck.lean`, le schéma versionné de `audit_manifest.json`,
`formalization.yaml` v0.3 et le registre délimité de `AXIOM_AUDIT.md`
directement des sources Lean et de `audit_config.json` schéma 2. Ses modes
`--check-pdfs`, `--check-source-digest` et
`--check-literature-certificates` ferment les préconditions du build et lient
séparément les octets et la cartographie des trois certificats actifs et de la
note historique de clôture Halter--Koch. Les quatre fichiers appartiennent au
digest documentaire, mais seuls les trois certificats actifs justifient les
trois prémisses ouvertes du Théorème 1.1 ;
son mode `--check` les rejoue et échoue si
l'un des quatre artefacts générés est périmé. Le script
`scripts/verify_audit.mjs` peut exécuter l’audit lui-même ou relire le journal
fourni par `--input` ; il exige exactement une sortie par cible du manifeste
et contrôle automatiquement la liste blanche. Le manifeste distingue les
dépendances fondationnelles imprimées par Lean des
hypothèses ordinaires, invisibles à `#print axioms`; il associe donc à chaque
théorème public un statut conditionnel/inconditionnel, la liste des ponts
qu’il prend comme prémisses directes, leur nature `external | internal` et
leur état `open | discharged`. Les comptes historiques v0.48.0 publiés
ci-dessus sont ceux du manifeste de ce jalon ; les comptes candidats doivent
provenir de la nouvelle régénération.
`ReviewAxioms.lean` est conservé comme sélection historique des
résultats structurants, mais n'est plus la liste canonique. Chaque sortie de
l'audit exhaustif doit être une sous-liste de
`[propext, Classical.choice, Quot.sound]`.

## Exécutions Comparator

Le build des trois outils épinglés et leurs chemins complets sont détaillés
dans le README. Comparator au commit
`51491237b1d2f96cca203af9c34bced6fe38e0d8` et lean4export au commit
`af5aa64bb914c3c2c781f378088dbd38acf4f804` sont tous deux construits avec
`ELAN_TOOLCHAIN=leanprover/lean4:v4.32.2`; la toolchain plus récente nommée
dans le checkout source de Comparator n'est pas la combinaison testée ici.
Pour chacun des deux runs Paper C destiné à servir de preuve de publication,
le transcript unique contient le commit du dépôt et de Mathlib, les commits et
SHA-256 des outils effectivement utilisés, les versions, l’empreinte de la
configuration, la commande exacte, toute la sortie et le code de retour. Cette
règle ne décrit pas uniformément tous les journaux historiques du répertoire :
le probe upstream antérieur est un journal de compatibilité plus étroit et ne
constitue pas une preuve d’exécution d’une cible Paper C.

### Smoke test de développement, non sandboxé

Dans un checkout jetable, le shim officiel fake-landrun de Comparator permet
le test sémantique suivant :

```bash
PAPER_C_TOOLS="$(realpath ../paper-c-v048-tools)"
COMPARATOR_LANDRUN="$(realpath "$PAPER_C_TOOLS/comparator/scripts/fake-landrun.sh")" \
COMPARATOR_LEAN4EXPORT="$(realpath "$PAPER_C_TOOLS/lean4export-4.32.2/.lake/build/bin/lean4export")" \
lake env "$(realpath "$PAPER_C_TOOLS/comparator/.lake/build/bin/comparator")" \
  comparator/theorem_one_one.json
```

Pour le transfert, remplacer le dernier argument par
`comparator/theorem_one_one_transfer.json`. Même avec un code de retour nul,
cette commande reste un **unsandboxed Comparator semantic smoke test** : le
script fake-landrun exécute directement la commande et n’offre aucune
isolation. Elle ne peut donc jamais servir de preuve durcie pour la
publication.

### Procédure locale durcie automatisée

La plateforme de référence est Ubuntu 24.04 LTS ou 26.04 LTS standard, sur
`x86_64` ou `arm64`. Ubuntu 22.04 standard n’est pas accepté : son noyau et son
Node.js sont trop anciens pour cette barrière de publication. Le script exige
Linux 6.2 ou ultérieur, afin que Landlock contrôle notamment la troncature, et
Node.js 18 ou ultérieur.

Installer une fois les prérequis Ubuntu :

```bash
sudo apt update
sudo apt install --yes \
  bash bsdutils build-essential ca-certificates coreutils curl \
  dbus-user-session findutils git grep nodejs sed systemd tar util-linux zstd
```

Si Elan n’est pas déjà installé dans `$HOME/.elan`, installer sa distribution
officielle pour l’utilisateur courant, puis charger son environnement :

```bash
curl --proto '=https' --tlsv1.2 -sSf \
  https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
source "$HOME/.elan/env"
```

Après l’installation de `dbus-user-session`, se déconnecter puis se reconnecter
si `systemctl --user show-environment` ne répond pas. Il ne faut jamais lancer
le vérificateur avec `sudo`. Il est inutile d’installer Go : le script
télécharge Go 1.24.13 et contrôle son SHA-256 officiel. Si la toolchain Lean
épinglée est déjà installée, l’interface idempotente `run --install` d’Elan la
réutilise ; sinon elle l’installe. Une invocation indépendante analyse ensuite
l’unique ligne de version Lean et exige l’égalité avec le commit épinglé avant
de poursuivre.

Depuis le commit exact à certifier, le checkout doit être entièrement propre,
y compris les fichiers non suivis. Lancer ensuite :

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

La première commande ne doit rien afficher. Le `setpriv` extérieur retire
notamment `CAP_WAKE_ALARM`, que `pam_systemd` peut placer dans la session Ubuntu
appelante, et le `PATH` restreint empêche qu’un outil utilisateur masque les
binaires Ubuntu et Elan audités. Un terminal `tmux` convient, mais
le script refuse `sudo`, les pipes, `nohup`, les tâches d’IDE, les conteneurs et
les descripteurs standard redirigés. Il construit les outils aux commits
épinglés, prépare chacun des deux checkouts immédiatement avant sa cible et
utilise l’enveloppe `systemd-run --user --pty` prescrite par Comparator autour
de landrun réel. Avant chaque cible, les contrôles négatifs exigent que la
politique exacte à racine en lecture seule interdise la création, la
troncature, la suppression et le renommage de fichiers.

Sur Ubuntu 26.04, certains chemins `/usr/bin` sont officiellement des liens
vers le fournisseur Rust coreutils ou vers des binaires GNU préfixés. Le
lanceur conserve les chemins d’appel fixes `/usr/bin`, contrôle que leurs
cibles résolues appartiennent à root et ne sont modifiables ni par le groupe
ni par les autres utilisateurs, applique le même contrôle à leurs répertoires
parents canoniques, puis consigne ces cibles dans les preuves. Le lanceur et
chaque unité Comparator transitoire doivent en outre constater quatre jeux de
capabilities nuls et `NoNewPrivs=1`. Le gestionnaire `systemd --user` étant
indépendant du shell appelant, il peut conserver `CAP_WAKE_ALARM` après le
nettoyage extérieur. Le lanceur audite donc également `/usr/bin/setpriv`, le
consigne avec son SHA-256 et l’exécute à l’intérieur de chacun des quatre
payloads transitoires, sans retirer la propriété systemd
`NoNewPrivileges=yes`. Le validateur exige les deux marqueurs transitoires et
la méthode de retrait interne enregistrée. Si le premier probe systemd échoue,
un diagnostic borné est affiché avant l’arrêt.

Systemd 259 décore par défaut le premier octet du payload PTY interactif avec
un titre de fenêtre OSC. Le lanceur refuse toute valeur héritée de
`SYSTEMD_ADJUST_TERMINAL_TITLE` dans l’appelant comme dans le gestionnaire
utilisateur, fixe ensuite sa valeur documentée à `0` avant chaque
`systemd-run` avec PTY, puis la consigne dans les preuves durcies. Les marqueurs
de sécurité restent ainsi des lignes exactes : le vérificateur ne les assouplit
pas en supprimant arbitrairement des contrôles de terminal. Le préflight peu
coûteux vérifie désormais cette propriété de ligne exacte avant tout
téléchargement ou build.

Les contrôles des marqueurs PTY bruts lisent directement le fichier de
transcript et n'acceptent qu'un enregistrement exact avec au plus un CR final.
Ils n'utilisent ni filtre permissif des contrôles de terminal, ni pipeline avec
`grep -q` à arrêt précoce : sous `pipefail`, ce dernier peut transformer une
correspondance valide au début d'un long transcript en échec `SIGPIPE` du
producteur.

La phase Comparator peut rester silencieuse : son flux PTY brut est conservé
dans les preuves, sans être rejoué dans le terminal appelant, afin qu’une
Solution non fiable ne puisse y injecter des séquences de contrôle. Un échec
préserve les diagnostics sans créer de marqueur `SUCCESS`. Après validation
des deux résultats par `scripts/assemble_comparator_evidence.mjs`, le script
produit un répertoire de preuves, une archive sœur `.tar.zst` et son fichier
`.tar.zst.sha256` prêt à transmettre.

Les répertoires `*.partial` et arbres de travail temporaires conservés servent
uniquement au diagnostic : ils ne doivent être ni renommés, ni promus, ni
réutilisés. Après tout échec, la production de preuves exige un nouveau run
complet depuis un `HEAD` propre et commité.

Le résultat attendu certifie une exécution Comparator sandboxée et non root,
acceptée par le noyau Lean par défaut. Il ne s’agit pas d’un résultat à deux
noyaux : `enable_nanoda` reste à `false`. La base de confiance inclut encore
Ubuntu/systemd enregistrés dans la trace, les sources épinglées des outils,
Lean et le cache OLean Mathlib téléchargé. Les sondes prouvent les restrictions
testées, pas toutes les propriétés de sécurité possibles de l’hôte.

<details>
<summary>Ancienne esquisse manuelle, conservée uniquement pour comparaison</summary>

Ne pas employer le bloc ci-dessous comme preuve de release : il précède le
lanceur atomique à deux cibles, les quatre contrôles négatifs, la capture PTY
sûre et la validation finale machine-lisible.

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

Le lanceur automatisé exécute toujours la cible principale et la cible de
transfert infini-vers-fini dans deux checkouts distincts. Un succès de la cible
principale ne donne aucune couverture implicite du modèle infini. Dans tous
les cas, Comparator construit lui-même Challenge et Solution ; aucun `.olean`
de Solution préexistant n’est accepté.

Si landrun, `systemd-run --user` ou un transport approuvé pour l'enveloppe
prescrite `--pty` n'est pas disponible sur un runner, l'étape d'exécution et
son transcript doivent être nommés explicitement « unsandboxed Comparator
semantic smoke test ». Après le blocage réellement observé des deux cibles sur
le runner hébergé, la CI considère par politique conservatrice que ses flux
capturés non-TTY ne suffisent pas à établir l'utilisabilité de ce transport.
Ce n'est pas une affirmation que `systemd-run --pty` exige intrinsèquement des
descripteurs de terminal préexistants. Ce fallback ne remplace pas le run
local durci. Le transcript de release doit contenir le commit du dépôt, les
octets ou l’empreinte de la configuration JSON, les versions Lean et Mathlib,
les commits et SHA-256 des outils, la commande exacte, toute la sortie et le
code de retour.

Le workflow distingue désormais ces deux usages par l'entrée manuelle
`require_hardened`. À `true`, l'indisponibilité de landrun réel ou d'un
transport approuvé pour `systemd-run --user --pty` fait échouer le job avec le
code 92 et interdit le fallback. Sur le transport hébergé actuel, ce mode est
donc destiné à échouer fermé ; la certification de release reste la procédure
locale durcie. À `false` (push/PR), le fallback reste un smoke test
explicitement non certifiant. Chaque étape d'exécution Comparator est limitée
à 60 minutes. Après chaque succès, les trois journaux d'environnement, de
sonde et d'exécution sont assemblés en un transcript atomique ;
`scripts/assemble_comparator_evidence.mjs` recalcule les empreintes et produit
un `result-*.json` machine-lisible avant l'archivage GitHub Actions. Avec les
scripts rc2, ce résultat contient aussi les SHA-256 de Challenge et Solution,
la liste exacte des théorèmes et axiomes permis, les deux SHA-256 des
manuscrits et les cinq commits d'outils. Le résumé agrégé répète les identités
d'outils et de manuscrits communes aux deux cibles. Ces champs sont présents
dans le paquet final v0.48.0.

Le succès de la sonde négative et de l'enveloppe documente les restrictions
effectivement testées. Il ne constitue pas, à lui seul, une certification
générale de tous les mécanismes d’isolation de l’hôte ; aucune isolation
sandbox n’est revendiquée avant une exécution réelle réussie et publiée dans
ces conditions.

Les deux runs durcis de référence ont réussi au commit `27c91f8bdd5c...` et
qualifient seulement le fileset historique v0.48.0. Le cœur et la cible
principale ayant changé, ils sont périmés pour v0.48.1. L’état généré du
snapshot v0.48.1 ne dit pas si l’exécution postérieure a eu lieu : il fixe les
octets auxquels une éventuelle preuve sous `release_evidence/v0.48.1/` doit se
lier. Les runs CI non sandboxés restent de simples smoke tests. Le suffixe d’un
ancien artefact CI peut être le SHA d’événement GitHub et ne doit pas être
confondu avec `paper_c_commit` ni avec le commit de l’outil Comparator. Nanoda
n’a pas été exécuté : les deux JSON ont `enable_nanoda: false`, et aucun
résultat de second noyau n’est revendiqué.

## Reproduction de l'archive

L'archive doit être construite depuis le répertoire parent du projet afin de
conserver l'unique racine `paper_c_lean/`. Après création, les contrôles
suivants sont requis :

```bash
unzip -t paper_c_lean_v0481.zip
unzip -Z1 paper_c_lean_v0481.zip | rg -v '^paper_c_lean/'
zip_check_dir="$(mktemp -d)"
unzip -q paper_c_lean_v0481.zip -d "$zip_check_dir"
(cd "$zip_check_dir/paper_c_lean" && \
  node scripts/check_comparator_sources.mjs && \
  node scripts/generate_audit.mjs --check)
```

La seconde commande ne doit produire aucune ligne. Le contrôle du générateur
est volontairement exécuté sans `git diff`, puisque le ZIP ne contient aucun
historique Git ; il compare directement les artefacts livrés à leur production
déterministe. L'archive ne doit contenir
ni `.lake`, ni `.git`, ni un second répertoire `paper_c_lean/` imbriqué. Elle
doit en revanche contenir à sa racine les deux PDF certifiés, afin que les
contrôles d’empreinte soient exécutables hors ligne.

## Limite de cette vérification

Compiler un énoncé admis comme argument ordinaire ne prouve pas cet énoncé et
`#print axioms` ne le signale pas. Le registre généré de
`audit_manifest.json` et `AXIOM_AUDIT.md` constitue donc un second audit,
séparé de la liste blanche fondationnelle. Le théorème principal ne devra être
annoncé comme certifié qu'une fois vide la liste des ponts `status: open`
propagés jusqu’à son assemblage. Les entrées `discharged` restent
volontairement dans l’inventaire historique sans constituer une dette.

Comparator ajoute une garantie différente : identité de l’énoncé et de sa
clôture déclarative entre Challenge et Solution, respect de la liste d’axiomes
fondationnels autorisés, puis acceptation par le noyau Lean. Il ne démontre
pas les trois hypothèses de littérature passées comme arguments ordinaires.
Même après un run Comparator réussi, le résultat restera donc correctement
décrit comme conditionnel à AGG, Evertse--Silverman et Nicolas--Robin.
Halter--Koch n’est plus une prémisse : sa compatibilité de conducteur est
déchargée par le théorème Lean interne modulo deux. La cible principale seule
porte sur le cylindre fini ; seule
la cible de transfert peut établir la couverture exacte du modèle infini.
