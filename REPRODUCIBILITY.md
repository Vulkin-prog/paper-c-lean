# Reproductibilité

## Versions fixées

- paper_c_lean : `0.40.0`
- Lean : `v4.19.0`
- mathlib : `v4.19.0`
- PDF cible, SHA-256 :
  `23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336`
- racine unique de l’archive : `paper_c_lean/`

Le fichier `lean-toolchain` et la révision de `lakefile.toml` rendent ces choix
reproductibles.

## Périmètre du jalon 0.40

La v040 ferme le §14 sous forme de caractérisation par fonctionnels de
Laplace. Elle conserve le modèle produit infini, le lemme 14.4, la
décomposition exacte et le lemme 14.7 de la v039, puis ajoute :

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

La convergence PPP est revendiquée exactement par sa famille complète de
fonctionnels de Laplace et, dans le cas marqué, par la tension uniforme.
Le prédicat public marqué est formulé littéralement avec
`infiniteFullMarkedLaplaceExpectation`; le cutoff porté par un test compact
sert uniquement à appliquer l’égalité complète/tronquée et l’argument fini
de Stein--Chen, non à remplacer la fonctionnelle source de l’endpoint.
Mathlib `v4.19.0` ne possède pas l’API de mesures ponctuelles/topologie vague
qui permettrait de reformuler cette même conclusion comme un `Tendsto` de
lois. La conversion abstraite des transformées inverses en masses atomiques
est désormais prouvée dans `DirichletAtomConvergence`, après l’encodage
injectif des vecteurs par `PrimeEncodedCountVector`.
`PrimeEncodedCountLaplace` construit la loi source poussée et l’identifie
aux tests constants \(s\log p_e\), tandis que `PoissonVectorMass` calcule les
transformées de la cible produit--Poisson. Le wrapper canonique du
corollaire 14.8 est donc fermé sans prémisse de convergence supplémentaire.

Les métriques exactes du jalon se reproduisent par :

```bash
find PaperC -name '*.lean' -type f | wc -l
find PaperC -name '*.lean' -type f -print0 | xargs -0 wc -l | tail -n 1
```

La v040 contient **372 modules** et **143 797 lignes Lean**.

Le jalon 0.40 conserve la décharge de l’interface interne de Pell généralisé :

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

Les théorèmes canoniques de masse mère, 13.10, 1.1, 16.1 et 16.2 exposent
directement ces entrées externes. Ils ne consomment aucun pont
`internal/open`; leurs anciennes signatures directes restent disponibles
sous les suffixes `_of_generalizedPell` et `_of_pellEnvelope`. C11.3, P9.9,
P9.11 et T10.1 sont conservés comme API legacy ouvertes mais non bloquantes.

Le jalon 0.40 conserve tous les résultats de la v039, notamment les deux
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
pour les API génériques avec `status: discharged`; l’interface historique
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
Il recense 17 interfaces — huit `external` et neuf `internal` — dont onze
`open` et six `discharged`, ainsi que **4 020 théorèmes ou lemmes
publics**, **4 022 cibles d’audit**, **3 825 résultats inconditionnels** et
**195 conditionnels**.

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
sans répertoire `.lake` hérité d'une version antérieure :

```bash
lake build
node scripts/generate_audit.mjs --check
lake env lean AuditCheck.lean
node scripts/verify_audit.mjs
rg -n '(^|[[:space:]])(sorry|axiom|admit|native_decide|unsafe|partial)([[:space:]]|$)' --glob '*.lean' .
```

Les quatre premières commandes doivent réussir. La dernière ne doit produire
aucune ligne.

Pour la livraison 0.40, la validation de publication doit être rejouée depuis
deux arbres indépendants dépourvus de `.lake/build`, dont une extraction du
ZIP final. Dans chacun, le build doit se terminer par
`Build completed successfully`. L’audit doit produire une sortie pour chaque
théorème ou lemme public et pour les deux constructions porteuses de preuves
conservées de l’audit historique. Toutes les listes doivent rester incluses
dans `[propext, Classical.choice, Quot.sound]`. Le contrôle du générateur doit
retrouver exactement les comptes du manifeste final régénéré et enregistrer
9.2, 9.10, 17.26, 17.28, 17.30 et l’ancienne enveloppe Nicolas--Robin avec
`status: discharged`. Il doit retrouver 17 interfaces — huit `external`,
neuf `internal`, onze `open` et six `discharged` — ainsi que 4 020
déclarations publiques, 4 022 cibles, 3 825 résultats inconditionnels et
195 conditionnels. Le scan des constructions interdites doit rester vide.

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

`AuditCheck.lean` importe le point d'entrée public `PaperC.Main` et applique
un `#print axioms` à chaque déclaration publique explicite `theorem` ou
`lemma` sous `PaperC`. Les déclarations `private` et `local` sont exclues :
leurs dépendances remontent transitivement dans les théorèmes publics qui les
utilisent. Deux équivalences linéaires publiques porteuses de preuves, déjà
présentes dans l'audit historique, sont ajoutées explicitement. Les noms
triés, sans doublon, sont reproduits dans `audit_manifest.json`.

`scripts/generate_audit.mjs` dérive `AuditCheck.lean`, le schéma versionné de
`audit_manifest.json` et le registre délimité de `AXIOM_AUDIT.md` directement
des sources Lean. Son mode `--check` échoue si l'un des trois est périmé. Le
script `scripts/verify_audit.mjs` exécute l’audit, exige exactement une sortie
par cible du manifeste et contrôle automatiquement la liste blanche. Le
manifeste distingue les dépendances fondationnelles imprimées par Lean des
hypothèses ordinaires, invisibles à `#print axioms`; il associe donc à chaque
théorème public un statut conditionnel/inconditionnel, la liste des ponts
qu’il prend comme prémisses directes, leur nature `external | internal` et
leur état `open | discharged`. La v040 doit reporter les comptes exacts des
ponts et des théorèmes conditionnels depuis le manifeste régénéré ; les
placeholders visibles de ce document doivent être remplacés seulement après
cette étape.
`ReviewAxioms.lean` est conservé comme sélection historique des
résultats structurants, mais n'est plus la liste canonique. Chaque sortie de
l'audit exhaustif doit être une sous-liste de
`[propext, Classical.choice, Quot.sound]`.

## Reproduction de l'archive

L'archive doit être construite depuis le répertoire parent du projet afin de
conserver l'unique racine `paper_c_lean/`. Après création, les contrôles
suivants sont requis :

```bash
unzip -t paper_c_lean_v040.zip
unzip -Z1 paper_c_lean_v040.zip | rg -v '^paper_c_lean/'
```

La seconde commande ne doit produire aucune ligne. L'archive ne doit contenir
ni `.lake`, ni `.git`, ni un second répertoire `paper_c_lean/` imbriqué.

## Limite de cette vérification

Compiler un énoncé admis comme argument ordinaire ne prouve pas cet énoncé et
`#print axioms` ne le signale pas. Le registre généré de
`audit_manifest.json` et `AXIOM_AUDIT.md` constitue donc un second audit,
séparé de la liste blanche fondationnelle. Le théorème principal ne devra être
annoncé comme certifié qu'une fois vide la liste des ponts `status: open`
propagés jusqu’à son assemblage. Les entrées `discharged` restent
volontairement dans l’inventaire historique sans constituer une dette.
