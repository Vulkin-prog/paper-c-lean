# Reproductibilité

## Versions fixées

- paper_c_lean : `0.47.0`
- Lean : `v4.32.2`
- mathlib : `v4.32.2`
- PDF cible anglais (71 pages dans le fichier portant cette empreinte), SHA-256 :
  `2f7c7b9fe3522059f0eb5fb7bf7871f0c3247e30aec534b1caa63abff5c8c927`
- PDF source français synchronisé (72 pages), SHA-256 :
  `c53b66ad467b2637d764124c20b9d788f1489b91cd90f3d907bf1eb814a17bc5`
- racine unique de l’archive : `paper_c_lean/`
- archive de livraison : `paper_c_lean_v047.zip`

Le fichier `lean-toolchain` et la révision de `lakefile.toml` rendent ces choix
reproductibles.

## Périmètre du jalon 0.47

La v047 conserve Lean/mathlib `v4.32.2`, tout le contenu mathématique de la
v045 et le registre de 13 ponts (sept `external/open`, six `discharged`). Elle
ferme le défaut racine de la v046 : `PaperC.lean`, cible de la bibliothèque
Lake, appartient désormais au digest, au recensement des déclarations, à la
recherche des ponts et à l’import de l’audit. Le manifeste expose l’ensemble
exact `source_fileset: ["PaperC.lean", "PaperC/**/*.lean"]`, et le générateur
l’énumère avec `fs` sans dépendre de `rg`. Deux gardes automatiques vérifient
le digest et l’inventaire sur ce fichier. La v046 avait rendu le triplet
manuscrits--sources--audit auto-contenu et introduit le hachage des octets
réels des deux PDF. Les comptes de déclarations ci-dessous proviennent du
manifeste v047 régénéré ; les nombres de fichiers et de lignes sont reproduits
par les commandes mécaniques indiquées plus bas.

### Historique v044–v043

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
sha256sum paper_C_complete_v08_en.pdf paper_C_complete_v08.pdf
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

Les deux seuls faits non formalisés de ce nouveau module sont enregistrés
comme `external/open` : `HK13-QO-conductor-fibres` pour la comparaison
conducteur 2 entre l’ordre \(\mathbb Z[\sqrt D]\) et l’ordre maximal, et
`NR83-T1-divisor-log-bound` pour l’inégalité logarithmique divisorielle.
L’ancienne enveloppe spécialisée `NR83-T1-divisor-bound` est conservée avec
`status: discharged`.
`PCv07c-L9.2-generalized-Pell` est désormais `discharged`.

Les théorèmes canoniques de masse mère, 1.4, 13.10, 1.1, 16.1 et 16.2 exposent
directement ces entrées externes. Ils ne consomment aucun pont
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
canoniques de 16.1 et 16.2 n’en consomment aucune. La première reçoit
seulement Evertse--Silverman, Halter--Koch et Nicolas--Robin. La seconde ne
reçoit plus ni \(K\), ni famille terminale, ni estimation
de la section 17, ni hypothèse arithmétique de 9.10 : ses seules prémisses
non formalisées sont PNT, Laishram--Shorey, Balasubramanian--Shorey, AGG,
Evertse--Silverman, Halter--Koch et Nicolas--Robin.

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

Le manifeste conserve la distinction indépendante entre `kind` et `status`.
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
rg -n '(^|[[:space:]])(sorry|axiom|admit|native_decide|unsafe|partial)([[:space:]]|$)' --glob '*.lean' PaperC.lean PaperC
node scripts/test_audit_root_guards.mjs
lake build
node scripts/generate_audit.mjs
mkdir -p ci-logs
lake env lean AuditCheck.lean 2>&1 | tee ci-logs/AuditCheck.log
node scripts/verify_audit.mjs --input ci-logs/AuditCheck.log
node scripts/generate_audit.mjs --check
```

Le premier contrôle ouvre et hache les octets réels des deux PDF ; il échoue
si l’un d’eux manque ou diffère de `audit_config.json`. Le deuxième recalcule
le digest de l’ensemble exact `PaperC.lean` plus `PaperC/**/*.lean` et le
compare au manifeste versionné. Le scan d’hygiène couvre explicitement ces
deux branches ; l’absence de correspondance est le résultat attendu. Les deux
gardes travaillent sur des copies temporaires et prouvent qu’une modification
de `PaperC.lean` invalide le digest et qu’un théorème public ajouté à la racine
entre dans l’inventaire et reçoit son `#print axioms`. La génération de
l’audit vient seulement après le build. La sortie de l’unique exécution Lean
est conservée, puis vérifiée pour l’exhaustivité et la liste blanche. Le
`--check` final hache à nouveau les deux PDF et exige que les trois artefacts
générés soient exactement à jour. Le workflow public
`.github/workflows/reproducibility.yml` applique cet ordre : le contrôle du
manifeste est la dernière validation, après laquelle `AuditCheck.log` est
archivé. Le générateur ne dépend plus de `rg` ; le workflow installe
néanmoins explicitement `ripgrep` juste avant le scan d’hygiène.

Le scan d’hygiène indépendant ci-dessous ne doit produire aucune ligne :

```bash
rg -n '(^|[[:space:]])(sorry|axiom|admit|native_decide|unsafe|partial)([[:space:]]|$)' --glob '*.lean' PaperC.lean PaperC
```

Pour la livraison 0.47, la validation de publication doit être rejouée depuis
deux arbres indépendants dépourvus de `.lake/build`, dont une extraction du
ZIP final. Dans chacun, le build doit se terminer par
`Build completed successfully`. L’audit doit produire une sortie pour chaque
théorème ou lemme public et pour les deux constructions porteuses de preuves
conservées de l’audit historique. Toutes les listes doivent rester incluses
dans `[propext, Classical.choice, Quot.sound]`. Le contrôle du générateur doit
retrouver exactement les comptes du manifeste final régénéré et enregistrer
9.2, 9.10, 17.26, 17.28, 17.30 et l’ancienne enveloppe Nicolas--Robin avec
`status: discharged`. Il doit retrouver 13 interfaces — huit `external`,
cinq `internal`, sept `open` toutes `external` et six `discharged` — ainsi
que 4 065 théorèmes et 5 lemmes publics, 4 072 cibles, 3 912 résultats
inconditionnels et 158 conditionnels. Il ne doit retrouver aucune interface
`internal/open`. Le scan des constructions interdites doit rester vide.

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
dans `source_fileset`, puis dérive `AuditCheck.lean`, le schéma versionné de
`audit_manifest.json` et le registre délimité de `AXIOM_AUDIT.md` directement
des sources Lean. Ses modes `--check-pdfs` et `--check-source-digest` ferment
les deux préconditions du build ; son mode `--check` les rejoue et échoue si
l'un des trois artefacts générés est périmé. Le script
`scripts/verify_audit.mjs` peut exécuter l’audit lui-même ou relire le journal
fourni par `--input` ; il exige exactement une sortie par cible du manifeste
et contrôle automatiquement la liste blanche. Le manifeste distingue les
dépendances fondationnelles imprimées par Lean des
hypothèses ordinaires, invisibles à `#print axioms`; il associe donc à chaque
théorème public un statut conditionnel/inconditionnel, la liste des ponts
qu’il prend comme prémisses directes, leur nature `external | internal` et
leur état `open | discharged`. Les comptes v047 publiés ci-dessus sont ceux
du manifeste régénéré.
`ReviewAxioms.lean` est conservé comme sélection historique des
résultats structurants, mais n'est plus la liste canonique. Chaque sortie de
l'audit exhaustif doit être une sous-liste de
`[propext, Classical.choice, Quot.sound]`.

## Reproduction de l'archive

L'archive doit être construite depuis le répertoire parent du projet afin de
conserver l'unique racine `paper_c_lean/`. Après création, les contrôles
suivants sont requis :

```bash
unzip -t paper_c_lean_v047.zip
unzip -Z1 paper_c_lean_v047.zip | rg -v '^paper_c_lean/'
```

La seconde commande ne doit produire aucune ligne. L'archive ne doit contenir
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
