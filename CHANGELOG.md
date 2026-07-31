# Journal des versions

## 0.41.0

- Nettoyage strict de l’API publique legacy, sans changement des signatures
  canoniques. Les quatre interfaces `internal/open` C11.3, P9.9, P9.11 et
  T10.1, ainsi que leurs 27 consommateurs publics, sont supprimées. Le
  registre ne contient désormais aucun pont `internal/open`.
- Les douze endpoints prenant directement l’ancien paquet Pell ou son
  enveloppe spécialisée (`_of_generalizedPell` et `_of_pellEnvelope`) sont
  supprimés au profit de leurs endpoints canoniques. Les six adaptateurs
  sectoriels intermédiaires de la proposition 16.1 et du théorème 16.2
  (`_of_sector_estimates`, `_of_manyDefectsEstimate(s)` et
  `_of_nonterminalEstimate(s)`) sont supprimés eux aussi.
- Les six entrées `discharged` sont conservées avec leurs théorèmes de
  décharge : l’ancienne enveloppe Nicolas--Robin, Pell généralisé, 9.10,
  17.26, 17.28 et 17.30. Les assemblages génériques directs
  `proposition_sixteen_one` et `theorem_sixteen_two` restent disponibles et
  assurent notamment la traçabilité des trois interfaces sectorielles
  déchargées.
- Lean et mathlib restent gelés en `v4.19.0`. La v041 contient 372 modules et
  142 015 lignes Lean. Le manifeste final recense 3 970 théorèmes et 5
  lemmes publics, soit 3 975 déclarations, 3 977 cibles d’audit et 13 ponts —
  huit `external`, cinq `internal`, sept `open` tous `external` et six
  `discharged` — soit 3 825 résultats inconditionnels et 150 conditionnels.

## 0.40.0

- La proposition 14.2 emprunte désormais la même masse mère quantitative
  canonique que le théorème 1.1. Son endpoint
  `maskedPoissonTotalVariation_uniformLittleOOne` n’expose que
  Arratia--Goldstein--Gordon, Evertse--Silverman, Halter--Koch et
  Nicolas--Robin. Les interfaces internes historiques C11.3, P9.9 et T10.1
  ne remontent plus au théorème 1.2(i).
- `SpatialRiemannSums` prouve la limite de la somme de Riemann dyadique
  littérale. `SpatialMarkedParameters` en déduit les limites exactes des
  paramètres spatial et marqué, au facteur critique
  \(\lambda_N=N2^{-L}\), ainsi que la loi géométrique
  \(\nu(\{e\})=2^{-(e+1)}\).
- L’amincissement indépendant est formalisé au niveau d’une famille finie
  munie d’un graphe de dépendance exact. L’événement de vide est identifié
  exactement au fonctionnel exponentiel, et l’application d’AGG donne une
  erreur au plus \(4(b_1+b_2)\). Les intégrales sur les cylindres finis, les
  espérances sous PMF et les espérances sous la loi produit infinie sont
  reliées par des identités exactes.
- La chaîne spatiale du §14.2 assemble la suppression puis la réintégration
  des mauvais starts, les deux termes de Stein--Chen, le paramètre aminci et
  la limite de Riemann. Elle conclut, sous les quatre seules entrées de
  littérature précédentes, à la convergence du fonctionnel de Laplace
  source vers celui de \(\operatorname{PPP}(\lambda\,dt)\).
- Pour le §14.4, Lean construit le graphe de dépendance marqué sur les
  indices \((x,e)\), prouve les marginales conditionnelles, les annulations
  même-start/chevauchement et le rang local des deux arbres. La séparation
  locale/éloignée ramène le terme \(b_2\) à une population
  \(O_E(N(L+E))\), au compte d’arêtes et à la masse homogène en longueur
  \(Q=L+E+1\). La route quantitative \(κ\) rend ainsi \(b_1,b_2=o_{C,E}(1)\)
  sans nouveau pont interne.
- Le fonctionnel marqué tronqué à cutoff fixé est comparé au fonctionnel
  retenu par la masse exacte du lemme 14.7 ; leurs paramètres diffèrent
  d’au plus
  \((E+1)2^E\,\#D(Q)/2^Q=o_{C,E}(1)\). Pour tout test continu positif dont
  le support en marques est contenu dans \(\{0,\ldots,E\}\),
  `FullMarkedLaplaceTransfer` définit en outre la fonctionnelle source
  littéralement complète, avec somme sur tous les excès, et prouve son
  égalité point par point puis en espérance avec la fonctionnelle tronquée.
  L’endpoint public porte donc bien sur l’espérance de cette fonctionnelle
  source complète et converge vers le fonctionnel de
  \(\operatorname{PPP}(\lambda\,dt\otimes\nu)\).
- La dé-troncation finale est explicite : la probabilité de voir une marque
  \(>E\) a un `limsup` au plus
  \(\lambda2^{-(E+1)}\), puis tend uniformément vers zéro quand \(E\to\infty\).
  La partie maximum du corollaire 14.8 est fermée canoniquement :
  \(\mathbb P(M_{N,L}\le m)\to
  \exp(-\lambda2^{-(m+1)})\). Le transfert exact du vecteur des comptes est
  également formalisé. `PrimeEncodedCountVector` encode injectivement un
  vecteur par les puissances des premiers et `DirichletAtomConvergence`
  prouve, par extraction inductive et contrôle géométrique de la queue, que
  la convergence de toutes les transformées inverses implique celle de
  chaque atome. `PrimeEncodedCountLaplace` identifie exactement la loi
  source poussée et les tests constants \(s\log p_e\) ;
  `PoissonVectorMass` identifie la cible produit--Poisson. Le théorème
  `corollary_fourteen_eight_counts` conclut donc la convergence de chaque
  atome du vecteur sous les quatre entrées canoniques de littérature, sans
  prémisse de loi retenue ni pont supplémentaire.
- L’endpoint formel de convergence PPP est donc, honnêtement, la famille
  complète des fonctionnels de Laplace avec tension uniforme des marques.
  Aucun espace de mesures ponctuelles ni topologie vague fictifs ne sont
  introduits. `SectionFourteenClosure` expose directement
  `theorem_one_two_ii_laplace` et
  `theorem_one_two_iii_laplace_and_tightness`; ce dernier est formulé avec
  `infiniteFullMarkedLaplaceExpectation`. Pour un test muni d’un témoin de
  support fini, la fonctionnelle source complète y est identifiée exactement
  à sa version tronquée et la somme finie de la cible à la série complète
  sur \(\mathbb N_0\).
- Lean et mathlib restent gelés en `v4.19.0`. La v040 contient 372 modules
  et 143 797 lignes Lean. Le manifeste recense 4 020 théorèmes ou lemmes
  publics, 4 022 cibles d’audit et 17 ponts — huit `external`, neuf
  `internal`, onze `open` et six `discharged` — soit 3 825 résultats
  inconditionnels et 195 conditionnels.

## 0.39.0

- Le modèle de Rademacher étendu sur tous les premiers est construit dans
  `PaperC.Model.InfiniteRademacher` comme mesure produit infinie de bits
  uniformes. Les cylindres imposant \(N\) coordonnées ont masse exactement
  \(2^{-N}\), une queue prescrite a mesure nulle, et le lemme 14.4 est prouvé
  dans sa forme source simultanée : presque sûrement, pour tout \(x\ge2\),
  une valeur ultérieure diffère de \(f(x)\).
- `InfiniteCylinderTransfer` identifie exactement toute projection finie de
  cette loi au modèle uniforme déjà utilisé par le dépôt. Les bits et les
  valeurs multiplicatives coïncident sous la restriction pour tout entier
  couvert par le cutoff ; les masses ponctuelles valent
  \(2^{-\pi(M)}\).
- `InfiniteExactLengthProbabilityTransfer` effectue aussi ce raccord au
  niveau des événements de longueur exacte : l’événement infini est la
  préimage mesurable de son cylindre dès que celui-ci couvre son dernier
  sommet, et sa mesure est exactement l’image réelle de la probabilité
  rationnelle finie. L’identité est sommée sans perte sur tous les
  \(e\le E\) et tous les starts retirés.
- `ExactLengthDecomposition` et
  `InfiniteExactLengthDecomposition` ferment le raccord placé immédiatement
  après le lemme 14.4. Presque sûrement, un start de longueur \(L\) possède
  un unique excès \(e\), et l’ensemble des indicatrices exactes actives a
  cardinal \(1\) sur l’événement de start et \(0\) sur son complément.
  L’inclusion de dé-troncation \(e>E\Rightarrow J_{x,L+E+1}=1\) est aussi
  prouvée.
- Le lemme 14.7 est fermé sous la vraie loi infinie.
  `ExactLengthBadStartMass` sépare exactement les starts dont le support
  court contient déjà un défaut et les starts de rang plein, puis somme les
  masses sur \(e\le E\). La variante directe sur les sommets non-racines
  perd un facteur \(2\) par rapport à la constante affichée dans le papier,
  sans modifier le petit-oh. Le module
  `ExactLengthBadStartMassCritical` transporte les deux estimations communes
  de la fenêtre \(L\) à \(Q=L+E+1\). Son théorème
  `lemma_fourteen_seven_finiteCylinder` établit d’abord l’estimation
  rationnelle sur le cylindre adéquat ; l’identité de mesure précédente
  permet ensuite à `lemma_fourteen_seven` de prouver littéralement
  \[
    \sum_{e=0}^{E}\sum_{x\in D(Q)}
      \mathbb P_\infty(K_{x,e}=1)=o_{C,E}(1).
  \]
- `MarkedLocalGeometry` prouve les annulations déterministes utiles au
  processus marqué : deux marques distinctes au même start sont
  incompatibles, un chevauchement strict a masse jointe nulle, et les deux
  offsets locaux compatibles ont respectivement une intersection de support
  de deux sommets et d’un sommet. Une marque \(e>E\) force le start plus
  long utilisé pour la tension des marques.
- `PellDivisorEnvelope` resserre la dernière frontière Nicolas--Robin du
  lemme 9.2. L’hypothèse canonique est maintenant l’inégalité logarithmique
  directe sur \(d(n)\) au-dessus de \(64\). Lean effectue la substitution
  polynomiale, traite les petits entiers, élève le compte de diviseurs au
  carré, borne le facteur des orbites d’unités et l’absorbe dans
  \(\exp(c\log N/\log\log N)\). L’ancienne enveloppe Pell spécialisée
  `NR83-T1-divisor-bound` est `discharged`; les cinq endpoints canoniques
  utilisent `NR83-T1-divisor-log-bound`.
- Le statut global reste volontairement plus faible que « tout le papier est
  formalisé ». Après cette version, les principaux travaux internes du
  §14 restant sont l’assemblage Stein--Chen marqué, les limites de Riemann,
  la convergence PPP/Laplace et la dé-troncation probabiliste finale. Les
  quatre interfaces internes ouvertes C11.3, P9.9, P9.11 et T10.1 restent
  uniquement des API legacy et ne remontent à aucun endpoint canonique.
- Lean et mathlib restent gelés en `v4.19.0`. La v039 contient 342 modules
  et 131 715 lignes Lean. Le manifeste recense 3 681 théorèmes ou lemmes
  publics, 3 683 cibles d’audit et 17 ponts — huit `external`, neuf
  `internal`, onze `open` et six `discharged` — soit 3 521 résultats
  inconditionnels et 160 conditionnels.

## 0.38.0

- Le pont interne de Pell généralisé du lemme 9.2 est déchargé.
  `PaperC.Diophantine.GeneralizedPell` formalise l’encodage
  \(x+y\sqrt D\), le diviseur idéal principal de \((M)\), le passage d’une
  même fibre d’idéal à une unité de Pell, la borne
  \(|u_y|\le2H^2\), la croissance exponentielle des unités fondamentales,
  le compte logarithmique d’une orbite et la réduction au noyau carré-libre.
  `QuadraticIdealDivisors` prouve séparément et sans pont que le nombre
  d’idéaux de l’ordre maximal divisant \((M)\) est au plus
  \(\tau(|M|)^2\), par
  factorisation unique des idéaux, indices de ramification et degrés
  d’inertie. Une partition finie par quatre couleurs de conducteur donne
  ensuite le facteur \(4\tau(|M|)^2\).
- Deux entrées `external/open` étroites remplacent l’ancienne dette interne :
  `HK13-QO-conductor-fibres` isole seulement la comparaison conducteur 2
  entre \(\mathbb Z[\sqrt D]\) et l’ordre maximal, et
  `NR83-T1-divisor-bound` isole la spécialisation éventuelle de la borne de
  Nicolas–Robin. Le théorème
  `generalizedPellPolynomialBox_of_quadraticOrder_nicolasRobin` prouve
  exactement `GeneralizedPellPolynomialBoxStatement`; l’entrée historique
  `PCv07c-L9.2-generalized-Pell` passe à `status: discharged`.
- Les cinq endpoints canoniques
  `homogeneousMass_uniformBigO`,
  `corollary_thirteen_ten_uniformBigO_canonical`,
  `theorem_one_one_uniformBigO_canonical`,
  `proposition_sixteen_one_canonical` et
  `theorem_sixteen_two_canonical` ne prennent plus Pell comme pont interne.
  Leurs signatures exposent directement les entrées de littérature ; aucun
  pont `internal/open` ne remonte donc aux théorèmes principaux canoniques.
  Les anciennes signatures restent disponibles sous le suffixe
  `_of_generalizedPell`.
- C11.3, P9.9, P9.11 et T10.1 restent `internal/open` uniquement comme API
  legacy génériques. Leur métadonnée précise désormais qu’elles sont
  non bloquantes pour les chemins canoniques ; aucune décharge plus forte
  que les instances effectivement prouvées n’est revendiquée.
- Lean et mathlib restent gelés en `v4.19.0`, le SHA-256 du PDF cible reste
  `23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336`
  et la racine d’archive demeure `paper_c_lean/`. Le manifeste v038 recense
  16 interfaces — sept `external` et neuf `internal` — dont onze `open` et
  cinq `discharged`, 3 579 théorèmes ou lemmes publics, 3 581 cibles
  d’audit, 3 426 résultats inconditionnels et 153 conditionnels.

## 0.37.0

- La masse mère dyadique est raccordée exactement aux preuves à rapport
  borné. `DyadicKappaTransport` établit
  \(R_2(N,L)=R_{2,\kappa}(N,2N,L)\) pour tout \(N,L\), avec un traitement
  explicite et sans hypothèse du cas \(N<2\).
- Les taux sources sont préservés jusqu’à cette spécialisation.
  `BoundedRatioElementaryQuantitative` fournit les taux \(3/2\), \(7/4\) et
  \(31/16\) des masses systématique, petit produit, petite hauteur, cœur peu
  profond et secteur terminal, ainsi que l’annulation éventuelle du secteur
  aligné. La chaîne many-defects conserve désormais conjointement son taux
  \(N^{3/2+o(1)}\) et son ancienne conclusion qualitative.
- `BoundedRatioDenseQuantitative` compare explicitement
  \(\sqrt{\log N}/\log\log N\) à
  \(\sqrt{L+1}/\log(L+1)\) dans la fenêtre critique et transporte le gain de
  rang dense vers l’échelle quantitative homogène. La branche modérée garde
  son taux \(N^{5/3+o(1)}\).
- `DyadicKappaQuantitative` choisit en interne
  \(K=(2C_{\rm term}+1)/\log2\), construit les enveloppes de tailles deux et
  dix, traite les sept secteurs littéraux, les somme avec la masse
  systématique, puis prouve
  \(R_2=O_C(N^2/(\log\log N)^2)\) sous Evertse--Silverman et Pell.
- `CorollaryThirteenTen` expose les nouvelles entrées
  `corollary_thirteen_ten_uniformBigO_canonical` et
  `theorem_one_one_uniformBigO_canonical`. Leur signature contient
  exactement AGG, Evertse--Silverman et Pell : C11.3, P9.9 et T10.1 ne sont
  plus des prémisses du théorème principal canonique. Les anciennes
  signatures sectorielles restent disponibles pour la compatibilité et
  leurs ponts historiques restent audités.
- Lean et mathlib restent gelés en `v4.19.0`, le SHA-256 du PDF cible reste
  `23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336`
  et la racine d’archive demeure `paper_c_lean/`. Le manifeste v037 recense
  14 interfaces, dont dix `open` et quatre `discharged`, 3 528 théorèmes ou
  lemmes publics, 3 530 cibles d’audit, 3 382 résultats inconditionnels et
  146 conditionnels.

## 0.36.0

- L’interface arithmétique du lemme 9.10 est déchargée dans sa portée
  exacte du manuscrit. Dans la branche non alignée
  `canonicalReducedCandidate? = none`, le code rationnel canonique est nul.
  Sous les couvertures de frontières \(x+L\le M\), \(y+L\le M\) et
  \(L+1\le M\), Lean montre que les coordonnées canoniques
  \(D^\#+c^\#\) paramètrent tout l’espace des solutions des grands premiers.
  La frontière d’une relation complète fournit alors un morphisme vers le
  noyau de la matrice arithmétique concrète ; son injectivité et sa
  surjectivité sont prouvées séparément, puis assemblées en une équivalence
  linéaire relations--noyau. Comme le quotient par le code rationnel nul est
  le plein espace des relations, Lean construit sans pont l’équivalence
  quotient résiduel--noyau et la formule de rang de 9.10.
- Les bornes de couverture requises par cet argument sont déduites
  automatiquement pour toute paire à rapport borné. Les populations
  terminales canoniques utilisent directement le théorème non aligné, et
  l’hypothèse fonctionnelle de 9.10 est retirée des chemins canoniques de la
  sommation terminale, de la proposition 16.1 et du théorème 16.2. Les
  wrappers génériques restent disponibles ; l’entrée auditée de 9.10 est
  conservée avec `status: discharged` pour la traçabilité historique.
- Les fermetures de 17.26 et 17.28 introduites en v035 sont conservées
  intégralement. Les sommes subpolynomiales des diviseurs signés, de Pell et
  d’Evertse--Silverman, l’assemblage des degrés \(1,2,\ge3\), les comptes
  directs d’hôtes mobiles et de deux singletons, ainsi que le choix
  \(K=(2C_{\rm term}+1)/\log2\), restent prouvés sous les seuls ponts
  Evertse--Silverman (`external`) et Pell (`internal`). Aucun nouveau pont
  n’est introduit.
- Lean et mathlib restent gelés en `v4.19.0`, le SHA-256 du PDF cible reste
  `23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336`
  et la racine d’archive demeure `paper_c_lean/`. Le manifeste v036 recense
  14 interfaces, dont dix `open` et quatre `discharged`, 3 477 théorèmes ou
  lemmes publics, 3 479 cibles d’audit, 3 345 résultats inconditionnels et
  132 conditionnels.

## 0.35.0

- Le lemme 17.26 est fermé jusqu’au petit-oh sectoriel, sans nouvelle
  interface. `BoundedRatioManyDefectsDegreeTwoSum` absorbe uniformément les
  diviseurs signés et le Pell généralisé du degré deux ;
  `BoundedRatioManyDefectsEvertseSum` transforme le compte
  Evertse--Silverman du degré au moins trois en une enveloppe commune
  \(N^{o(1)}\). `BoundedRatioManyDefectsDegreeAssembly` agrège les degrés
  \(1,2,\ge3\), puis `BoundedRatioManyDefectsAssembly` somme les bases et les
  formes et établit
  \(N^{3/2+o_{C,\kappa_0}(1)}=o_{C,\kappa_0}(N^2)\). Les seules prémisses
  non formalisées de cette fermeture sont le pont `external`
  Evertse--Silverman et le pont `internal` de Pell déjà enregistrés.
- Le lemme 17.28 est lui aussi fermé sous ces deux mêmes ponts.
  `BoundedRatioTwoSingletonHosts` construit la paramétrisation injective des
  deux singletons, sa somme harmonique et son produit eulérien ;
  `BoundedRatioTwoSingletonCritical` en déduit l’enveloppe
  \(N\exp(C_{\rm term}\sqrt B/\log B)\). Pour le compte global de support
  deux, l’union sur les formes emploie le majorant sûr \(9B^4\), plus faible
  que le facteur \(B^2\) affiné de la preuve source ; cette perte
  polynomiale est explicitement absorbée dans \(C_{\rm term}\).
  `BoundedRatioNonterminalMobileAssembly` traite la branche modérée de
  support au plus dix, et `BoundedRatioNonterminalAssembly` choisit
  \[
    K=\frac{2C_{\rm term}+1}{\log2}
  \]
  pour vérifier \(2C_{\rm term}<K\log2\) et conclure la stabilité du sixième
  secteur. Aucun pont propre à 17.28 n’est nécessaire dans cette chaîne.
- La géométrie de densité n’est plus figée à \(3/16\) :
  `PropositionNineNineHostGeometry` et
  `BoundedRatioManyDefectsReduction` transportent toute densité rationnelle
  \(\alpha_{\rm num}/\alpha_{\rm den}\le3/16\) et tout cutoff \(K\)
  satisfaisant
  \(2\alpha_{\rm den}<\alpha_{\rm num}(K+1)\). L’instance historique
  \(3/16,\ K=10\) reste disponible avec les mêmes noms publics.
- L’API canonique de la proposition 16.1 ne prend plus aucune estimation
  sectorielle de 17.26 ou 17.28 : elle construit les trois secteurs profonds
  depuis Evertse--Silverman, Pell et l’équivalence arithmétique de 9.10.
  L’API canonique principale du théorème 16.2 ne prend plus ni seuil \(K\)
  ni hypothèse de la section 17 ; ses seules entrées sont PNT,
  Laishram--Shorey, Pell, Balasubramanian--Shorey, AGG,
  Evertse--Silverman et 9.10. Les anciennes signatures restent accessibles
  sous les suffixes `_of_sector_estimates`, `_of_manyDefectsEstimate(s)` et
  `_of_nonterminalEstimate(s)`.
- Le générateur d’audit reconnaît désormais une déclaration dont le mot-clé
  `theorem` ou `lemma` est seul sur une ligne et dont le nom commence sur la
  suivante. Son auto-test couvre ce format et six cibles, dont trois
  historiques, sont réintégrées rétroactivement au manifeste exhaustif. Le
  registre sépare maintenant la provenance `kind: external | internal` de
  l’état `status: open | discharged` : les interfaces historiques 17.26,
  17.28 et 17.30 sont `discharged`, les onze autres restent `open`. Une
  entrée `internal` n’est donc plus assimilée automatiquement à une dette
  restante. Les comptes finaux sont repris exclusivement du manifeste
  régénéré après les builds propres. Lean et mathlib restent gelés en
  `v4.19.0`, le
  SHA-256 du PDF cible reste
  `23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336`
  et la racine d’archive demeure `paper_c_lean/`.

## 0.34.0

- `PellRealExponent` ferme l’écart d’interface laissé au lemme 9.2 et dans
  son emploi au lemme 17.19. À partir du même pont interne de Pell
  généralisé, Lean passe de l’exposant naturel à tout
  \(K_0\in\mathbb R_{>0}\) par \(J=\lceil K_0\rceil\), puis choisit
  \(H=\lfloor N^{K_0}\rfloor\) pour obtenir le prédicat source-exact
  \(|z|,|w|\le N^{K_0}\). Aucun nouveau pont n’est introduit.
- `BoundedRatioManyDefectsFixedFibers` désintègre les fibres restantes de
  17.26 par coefficient \(d\) carré-libre et lisse. La branche mobile de
  degré un est entièrement dominée par une enveloppe
  \(N^{1/2+o(1)}\), et la branche de degré au moins trois est raccordée à
  l’interface Evertse–Silverman avec sa somme finie explicite. Pour le degré
  deux, Lean construit la boîte de Pell de hauteur
  \(2(Y+L+1)^2\) ; lorsque le coefficient normalisé vaut \(1\), il remplace
  Pell par une injection exacte dans les paires de diviseurs signées de
  \(\Delta^2\). Pour tout \(E\ge4\) avec \(2K\le E\), les trois bornes
  polynomiales requises sur le coefficient, \(\Delta^2\) et cette hauteur
  sont déduites automatiquement de toute fibre non vide. Restent le contrôle
  \(N^{o(1)}\) des sommes explicites de diviseurs et d’Evertse–Silverman,
  puis l’agrégation des degrés.
- `BoundedRatioNonterminalCardinality` suit désormais exactement la
  dichotomie du lemme 17.28. Dans la branche
  \(3c^\#\le2B\), la masse est fermée en
  \(N^{1+o(1)}N^{2/3+o(1)}=N^{5/3+o(1)}\) depuis un compte direct des hôtes
  de taille au plus 10. Dans la branche \(2B<3c^\#\), Lean extrait une
  composante de taille deux, traite le plancher de \(R_K(B)\) et obtient le
  petit-oh sous \(2C_{\rm term}<K\log2\) depuis le compte direct
  \(N\exp(C_{\rm term}\sqrt B/\log B)\). L’ancien critère global par
  cardinalité effective est conservé, mais explicitement marqué comme
  suffisant plus fort que la preuve source.
- `BoundedRatioTerminalSummation` ferme la dette propre du lemme 17.30 :
  désintégration par premier start, sommation uniforme des fibres sous Pell,
  remplacement des petites parties par l’enveloppe de Chebyshev, facteur de
  partenaire \(N^{o(1)}\), cardinal
  \(N^{3/4+o(1)}\) et masse \(N^{7/4+o(1)}=o(N^2)\).
  Les deux exposants sont des API publiques distinctes ; le transfert de la
  population rangée vers le classifieur intrinsèque est exact sous le pont
  amont déjà enregistré du lemme 9.10.
- Les API canoniques de la proposition 16.1 et du théorème 16.2 construisent
  désormais elles-mêmes le septième secteur à partir de Pell et du
  fournisseur universel de 9.10 ; leur signature principale ne prend plus
  le pont grossier 17.30. Les anciens wrappers restent disponibles sous le
  suffixe `_of_sector_estimates`, et les assemblages génériques conservent
  l’interface historique pour les classifieurs terminaux arbitraires.
- L’audit déterministe recense 3 328 théorèmes ou lemmes publics, 3 330
  cibles, 3 204 résultats sans pont enregistré et 124 conditionnels. Le
  registre reste à 14 interfaces, cinq `external` et neuf `internal`, avec
  le SHA-256 du PDF cible inchangé et Lean/mathlib gelés en `v4.19.0`.

## 0.33.0

- Le nouveau module `BoundedRatioManyDefectsFibers` raccorde la population
  littérale du cinquième secteur aux bases \(x-1\) de fenêtres contenant
  deux défauts et aux formes finies de composantes. Dans la zone haute, la
  branche à noyaux égaux disparaît ; la branche à noyaux distincts est
  comptée sous Pell, puis toutes les bases et toutes les formes sont sommées
  avec un facteur polynomial explicite. Le lemme 17.26 est ainsi ramené à
  l’unique estimation uniforme
  \(N^{1/2+o_{C,\kappa_0}(1)}\) des fibres à base de fenêtre et forme fixées.
- `BoundedRatioNonterminalClosure` somme l’économie ponctuelle de 17.28,
  extrait exactement le facteur \(2^{R_K(B)+1}\) et transporte l’enveloppe
  obtenue dans la fenêtre critique. Tout le calcul des poids est désormais
  fermé : l’obligation restante est précisément
  \[
    \#\mathcal N_{N,M,L}/2^{R_K(B)+1}=o_{C,\kappa_0}(N).
  \]
  Ce transport n’utilise directement ni Evertse–Silverman ni Pell ; le pont
  17.28 reste enregistré tant que cette estimation de cardinalité n’est pas
  prouvée.
- `BoundedRatioTerminalPartnerClosure` traite la population terminale de rang
  `boundedRankTerminalPairs`. Pour un premier start, quatre offsets et deux
  petites parties impaires fixés, la fibre de partenaires s’injecte dans une
  boîte de Pell ; la réunion finie porte le facteur exact
  \((L+1)^4(\#\text{petites parties})^2\). Lean prouve aussi l’unicité de
  l’éventuelle composante exceptionnelle, l’incidence des noyaux bornés et
  les deux conditions de marge du budget de rang dans la fenêtre critique.
  Restent le transport vers la population terminale canonique intrinsèque,
  la sommation uniforme des partenaires et le passage final à la masse
  \(o(N^2)\) de 17.30.
- Aucun pont n’est ajouté ni supprimé : le registre conserve 14 interfaces,
  cinq `external` et neuf `internal`. Le générateur déterministe de l’audit
  est corrigé pour ne compter que les ponts présents dans les prémisses :
  conclure un énoncé-pont ne crée plus une fausse dépendance à ce pont. Les
  comptes exacts régénérés sont 3 213 théorèmes ou lemmes publics,
  3 215 cibles d’audit, 3 114 résultats inconditionnels et 99 conditionnels.
  `scripts/verify_audit.mjs` rejoue les 3 215 commandes et refuse
  automatiquement tout axiome hors de la liste blanche fondationnelle.
- Lean et mathlib restent gelés en `v4.19.0`. Le SHA-256 du PDF cible reste
  `23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336`
  et l’archive conserve l’unique racine `paper_c_lean/`.

## 0.32.0

- Fixation de la population terminale canonique du manuscrit. Lean définit
  \(R_K(B)=\lfloor K\sqrt B/\log B\rfloor\), encode littéralement
  \(T_K=\{s+\widetilde k\le R_K(B)\}\), puis prouve son équivalence, sous
  l’interface déjà enregistrée du lemme 9.10, avec le test intrinsèque
  \(B+D^\#\le\tau+R_K(B)\). Les secteurs six et sept de la proposition 16.1
  ne dépendent donc plus d’une partition terminale arbitraire dans les
  nouveaux wrappers publics canoniques.
- Formalisation des étapes finies des lemmes 17.27–17.28 : décomposition
  terminal/non-terminal exacte, annulation de \(\sigma\) sur le sixième
  secteur et économie ponctuelle
  \[
    (2^\tau-1)\,2^{R_K(B)+1}\le4\,2^B.
  \]
  La réduction asymptotique globale de 17.28 reste l’interface interne
  auditée existante.
- Réduction détaillée de 17.18–17.26 à un unique invariant de comptage
  d’hôtes orientés. Lean extrait un défaut double dans une petite composante,
  construit la couverture finie correspondante et transfère toute enveloppe
  \(N^{1/2+o(1)}\) vers la masse
  \(N^{3/2+o(1)}=o(N^2)\). Dans la population auxiliaire des bases de
  défauts, le cas à noyaux carrés-libres égaux est factorisé et devient vide
  dès que \(B^2+1<N\); le cas distinct est séparé et muni de ses premières
  enveloppes lisses. Leur raccord aux hôtes orientés littéraux reste à faire.
- Normalisation composante par composante :
  \(P\,Q=d z^2\), puis \(Q=e v^2\), avec positivité, \(d\) carré-libre
  \(B\)-friable, \(e\) carré-libre, et bornes de hauteur explicites en
  \((M+L)^K\). Les ensembles d’offsets et leurs produits décalés canoniques
  donnent la forme exacte consommable par les futurs comptes
  Evertse–Silverman/Pell.
- Réductions génériques pour la fermeture terminale 17.29–17.30 : borne
  uniforme du déterminant, unicité d’un éventuel noyau exceptionnel, compte
  \(N^{3/4+o(1)}\) des valeurs de noyau possibles, désintégration exacte de
  \(T_K\) en fibres de partenaires et transfert générique
  « cardinal terminal \(\Rightarrow o(N^2)\) ». Les certificats des
  composantes de taille deux sont injectifs et leurs déterminants sont
  non nuls. Restent à raccorder ces résultats à la population terminale
  effective : incidence des premiers départs, choix des fibres de partenaires,
  application de Pell et sommation uniforme.
- L’interface terminale profonde est resserrée : le lemme 17.30 ne prend
  plus Evertse–Silverman, absent de sa preuve manuscrite, mais seulement le
  Pell généralisé. Aucun nouveau pont n’est ajouté et aucun pont existant
  n’est masqué ; les trois obligations globales 17.26, 17.28 et 17.30
  restent inscrites au registre.
- Lean et mathlib restent gelés en `v4.19.0`, le SHA-256 du PDF cible est
  inchangé et la racine d’archive demeure l’unique dossier
  `paper_c_lean/`.

## 0.31.0

- Fermeture sans pont des lemmes 17.14–17.16 sur l’intervalle exact
  \(U(N,M)=[N,M)\), uniformément pour
  \(2N\le M\le\kappa_0N\). Les trois anciens
  `AUDIT_BRIDGE` sectoriels sont supprimés.
- Ajout du compte direct des hôtes relationnels au cutoff \(M+L\), sans
  couverture par sous-blocs dyadiques. L’enveloppe obtenue est
  \(N^{3/2+o_{C,\kappa_0}(1)}\). Les nouveaux modules de masses résiduelles,
  de défaut corrigé et de fermeture sectorielle formalisent aussi
  l’injection des couples actifs et l’interpolation de Cauchy–Schwarz.
- Pour les secteurs petit produit et petite hauteur, Lean sépare exactement
  \(\sigma=0\) et \(\sigma>0\), obtient
  \(Q_{\rm res}\le N^{2+o(1)}\), puis
  \(R_{\rm res}\le N^{7/4+o(1)}=o(N^2)\). Pour le cœur peu profond, les
  exposants certifiés sont \(19/8\) et \(31/16\), conformément au
  lemme 17.16.
- Scission de `PropositionSixteenOne` en un noyau fini
  `PropositionSixteenOneCore` et un wrapper d’assemblage, sans cycle
  d’import. La proposition 16.1 et le théorème 16.2 ne dépendent plus que
  des trois secteurs profonds 17.26, 17.28 et 17.30, avec
  Evertse–Silverman et Pell toujours explicites.
- Ajout du lemme général qui transporte un big-O uniforme à l’échelle
  quantitative du corollaire 11.3 vers le petit-oh quadratique de la
  proposition 9.11. La signature conserve les deux interfaces déjà
  enregistrées et n’introduit aucun pont invisible.
- Le registre passe de 17 à 14 interfaces : cinq `external` et neuf
  `internal`. L’audit, le SHA-256 du PDF cible, la racine unique
  `paper_c_lean/` et la toolchain Lean/mathlib `v4.19.0` restent inchangés.

## 0.30.0

- Fermeture des bornes de mauvais départs des lemmes 17.33–17.34 sur
  \(U(N,M)=[N,M)\). `BoundedRatioBadStarts` injecte les incidences terminales
  et prouve uniformément
  \(\#D_Y=N^{1/2+o_{C,\kappa_0}(1)}=o_{C,\kappa_0}(N)\).
  `BoundedRatioWeightedDefect` applique directement la proposition 3.2 à
  l’intervalle à rapport borné et obtient la même borne pour la masse
  pondérée, puis une masse probabiliste \(o_{C,\kappa_0}(1)\).
- Ajout de `FiniteCylinderCountTransport`. Une décomposition explicite des
  coordonnées premières transporte exactement événements, comptes et lois
  entre deux cutoffs adéquats. Lean en déduit le couplage entre compte des
  bons départs et compte complet par la masse des mauvais départs, ainsi que
  l’identité exacte de la moyenne complète.
- Fermeture des deux termes de Stein–Chen de 17.37.
  `BoundedRatioSteinChenRates` déduit \(b_1=o_{C,\kappa_0}(1)\) de l’identité
  finie et du compte d’arêtes de 17.36, uniformément dans l’affectation des
  petits premiers. `BoundedRatioSteinChenSecondTerm` identifie la moyenne
  conditionnelle de \(b_2\), partitionne exactement les arêtes en
  chevauchement, contact et séparation, annule le chevauchement et domine la
  séparation par \(R_{2,\kappa}\). La fermeture asymptotique est assemblée
  dans `BoundedRatioSteinChenSecondTermCritical`.
- `BoundedRatioPoissonAssembly` combine AGG, la loi totale finie, les deux
  termes de Stein–Chen, la masse des mauvais départs et le déplacement du
  paramètre. `BoundedRatioFixedJBadStarts` spécialise les estimations à
  \([M/2^j,M)\), tandis que `BoundedRatioRetainedTransport` identifie
  exactement la loi et la moyenne locales au compte retenu et contrôle
  l’arrondi du bord. Les lemmes nécessaires sont aussi intégrés directement
  dans `TheoremSixteenTwo`, ce qui ferme son entrée à rapport borné sans
  cycle d’import.
- Suppression de `BoundedRangePoissonApproximation` et de son
  `AUDIT_BRIDGE`. Le théorème 16.2 final ne possède plus de dette
  probabiliste agrégée : il dépend directement des cinq ponts `external`
  existants, des six ponts sectoriels `internal` de la proposition 16.1 et
  du Pell généralisé `internal`. Le registre attendu contient donc
  17 interfaces, cinq `external` et douze `internal`; les comptes de
  théorèmes et de cibles sont laissés au générateur déterministe.
- Lean et mathlib restent gelés en `v4.19.0`, le SHA-256 du PDF cible est
  inchangé et la racine d’archive demeure l’unique dossier
  `paper_c_lean/`.

## 0.29.0

- Fermeture sans pont de l’instance \(\alpha=3/16\) du lemme 17.17
  effectivement consommée par la proposition 16.1. Le nouveau module
  `BoundedRatioSectorAligned` renforce l’exclusion alignée pour deux starts
  ayant seulement un minorant commun \(N\) ; il couvre ainsi les paires qui
  croisent deux sous-blocs dyadiques. La quatrième fibre est éventuellement
  vide et son petit-oh uniforme est déduit dans Lean. La proposition 16.1 ne
  dépend plus que de six transports sectoriels internes.
- Suppression du pont de compatibilité de marginale du théorème 16.2.
  Lean décompose explicitement le grand cylindre premier en cylindre local
  et coordonnées supplémentaires, transporte l’événement de start par des
  équivalences finies et prouve l’invariance de sa probabilité uniforme.
  L’argument `GlobalMarginalAgreement` disparaît de toute la chaîne publique,
  dont le théorème final garde l’hypothèse source \(C>0\).
- Ajout de `BoundedRatioSteinChen`. Sur \(U=[N,M)\), Lean construit les bons
  starts, le graphe conditionnel et la loi uniforme, puis prouve les
  marginales \(2^{-L}\), le graphe de dépendance exact, l’identité exacte de
  \(b_1\), le paramètre et sa correction par \(\#D_Y2^{-L}\). L’application
  ponctuelle est prouvée sous l’interface externe AGG. Le comptage par premier
  témoin donne
  \(E_{Y,U}=o_{C,\kappa_0}(N^2)\) sous les quantificateurs exacts
  \(2N\le M\le\kappa_0N\), ainsi que la spécialisation
  \(E_{Y,[M/2^j,M)}=o_C(M^2)\) pour tout \(j\) fixé. Ces paquets certifiés
  sont maintenant des antécédents explicites du pont d’assemblage restant ;
  l’estimation d’arêtes y est fournie pour toute constante décalée \(C'>0\).
  Celui-ci prend aussi la proposition 16.1 pour toute constante de fenêtre
  \(C'>0\) et tout \(\kappa_0\ge2\), ce qui couvre le décalage produit par
  \(N=M/2^{j_0}\). La population terminale commune peut dépendre de ces deux
  paramètres, conformément à l’ordre de choix de \(K\), et le raccord
  plancher/plafond au bord reste explicitement dans la dette. Le théorème
  16.2 construit cette entrée depuis les six interfaces sectorielles, qui
  apparaissent donc directement dans sa signature auditée. Le pont isole
  encore les bornes asymptotiques de mauvais starts, le petit-oh de \(b_1\),
  le mélange/couplage, la moyenne de \(b_2\) et la moyenne retenue de
  17.34–17.37.
- Resserrement du pont `HostCountStatement` de la proposition 9.9. Les
  paires avec \(\tau=0\) sont supprimées sans changer la masse ; chaque hôte
  actif possède une composante canonique de support entre 2 et 10 et l’un
  des deux blocs porte au moins deux défauts concrets. La population est
  couverte par deux branches orientées, seules désormais soumises au compte
  \(N^{1/2+o_C(1)}\).
- Nettoyage du registre de 9.10 : l’ancienne interface existentielle large,
  déjà impliquée par `CanonicalArithmeticKernelStatement`, est supprimée.
  Avec 17.17 et la marginale globale, trois interfaces internes disparaissent
  au total. Le point d’entrée importe directement les trois nouveaux modules,
  l’audit est régénéré déterministiquement et Lean/mathlib restent gelés en
  `v4.19.0`; la racine d’archive reste `paper_c_lean/`.

## 0.28.0

- Formalisation de la proposition 16.1 sur l’intervalle entier littéral
  \(U(N,M)=[N,M)\), avec \(2N\le M\le\kappa_0N\). Lean définit la somme
  \(R_{2,\kappa}\), prouve l’identité exacte
  \(2^\rho-1=(2^\sigma-1)+2^\sigma(2^\tau-1)\), construit la partition
  ordonnée en sept secteurs et assemble leur petit-oh uniforme. La
  conclusion est conditionnelle aux sept transports internes précisément
  sourcés des lemmes 17.14–17.17, 17.26, 17.28 et 17.30 ; les entrées
  Evertse–Silverman (`external`) et Pell (`internal`) restent des arguments
  explicites des trois secteurs diophantiens (5)–(7).
- Fermeture sans pont du site nouveau de la proposition 16.1. Le module de
  géométrie à rapport borné prouve les cardinaux d’intervalles, la
  couverture dyadique finie, les comptes de classes résiduelles, le
  paramètre de translation d’un canal et les couvertures \(q=2\) et
  \(q\ge3\). Il en déduit la borne finie
  \[
    \sum(2^\sigma-1)
      \le 16(\kappa_0+1)(L+1)^4N\,2^{\lfloor L/2\rfloor},
  \]
  puis \(N^{3/2+o_{C,\kappa_0}(1)}=o_{C,\kappa_0}(N^2)\). Le pont initial
  envisagé pour le lemme 17.5 est ainsi supprimé. La somme purement
  géométrique du lemme 17.6 est inchangée et sa borne déjà certifiée est
  réexportée.
- Formalisation de tout le passage analytique du théorème 16.2. Le compte
  global \(Z_M\), le compte retenu, leurs lois et leurs espérances sont
  définis sur un cylindre fini commun. Lean prouve le couplage de
  troncature, le déplacement du paramètre de Poisson, l’ordre exact du
  double passage \(j_0\) puis \(M\), l’asymptotique relative
  \(\Lambda_M\sim M2^{-L}\) et
  \(\mathbb P(Z_M=0)=e^{-\Lambda_M}+o_C(1)\). Deux dettes internes restent
  enregistrées : l’identité de marginale lors du changement de cylindre et
  la fermeture fixe-ratio des lemmes 17.35–17.37. Cette dernière prend
  explicitement AGG, Evertse–Silverman et Pell en antécédents.
- Le théorème public final assemble directement la proposition 15.5 à
  partir de PNT, Laishram–Shorey, Pell et Balasubramanian–Shorey, de sorte
  qu’aucune hypothèse dérivée n’échappe au registre. Lean et mathlib restent
  gelés en `v4.19.0`; la racine d’archive reste `paper_c_lean/`.

## 0.27.0

- Fermeture conditionnelle du corollaire 13.10 et de sa reformulation
  introductive, le théorème 1.1, dans le cylindre fini. Lean spécialise la
  borne harmonique des arêtes au cutoff terminal, obtient les taux
  quantitatifs de \(b_1\) et \(\mathbb E b_2\), applique AGG et assemble
  \[
    d_{\rm TV}\!\left(\mathcal L(Z_{N,L}),
      \operatorname{Pois}(N2^{-L})\right)
      =O((\log\log N)^{-2})
  \]
  uniformément dans \(\lvert L-\log_2N\rvert\le C\). Les ponts enregistrés
  restent exactement AGG (`external`) et les trois interfaces
  `HostCountStatement`, `NonterminalSectorQuantitativeStatement`,
  `TerminalSectorMassStatement` (`internal`) ; aucun pont n'est ajouté.
- Fermeture du lemme 15.3 dans sa plage littérale. Sous PNT (`external`) et
  le Pell généralisé (`internal`), une même constante et un même seuil
  bornent par \(\exp(K_CL/\log L)\) toutes les populations à deux défauts
  des blocs \(2L^2\le N\le M\), lorsque \(L\) est critique pour \(M\).
  La comparaison monotone de \(\log(3N)/\log\log(3N)\) à l'échelle de
  \(M\) est prouvée dans Lean.
- Fermeture conditionnelle de la proposition 15.5. La masse littérale
  \(\sum_{2\le x<M/2^{j_0}}\mathbb P(J_{x,L}=1)\) et l'ordre exact de sa
  double limite sont encodés. Lean couvre la plage \(x\le2L^2\) par les
  lemmes 15.1–15.2, insère 15.3–15.4 dans chaque bloc supérieur, prouve
  \[
    L\,e^{KL/\log L}\,2^{1-g_L}\longrightarrow0
  \]
  ainsi que la queue géométrique finie \(O(2^{-j_0})\). La partition
  dyadique globale est construite dans Lean depuis \(2L^2+1\), sans trou ni
  recouvrement, avec au plus \(2L\) blocs et un contrôle du dernier bloc.
  La borne \(o_M(1)+D2^{-j_0}\) ferme alors la double limite exacte. Les
  seuls ponts enregistrés sont PNT, Laishram--Shorey et
  Balasubramanian--Shorey (`external`) et le Pell généralisé (`internal`).
- Le point d'entrée public importe les nouveaux modules et l'audit
  déterministe est régénéré sans modifier le registre des douze ponts.
  Lean et mathlib restent gelés en `v4.19.0`. Le jalon compte 272 modules et
  85 110 lignes Lean ; l'audit exhaustif couvre 2 501 théorèmes/lemmes
  publics et 2 503 cibles, dont 75 résultats conditionnels.

## 0.26.0

- Formalisation conditionnelle du corollaire 11.3 à son taux littéral
  \[
    R_2(N,L)\ll_C N^2
      \exp\!\left(-c\frac{\sqrt{\log N}}{\log\log N}\right).
  \]
  Les secteurs déjà munis d'une économie de puissance sont transportés vers
  cette échelle en Lean. La seule nouvelle dette est un pont `internal`
  limité au sixième secteur non terminal ; les interfaces antérieures de
  9.9 et 10.1 restent visibles.
- Composants quantitatifs du corollaire 13.10. Lean prouve
  \(e^{-c\sqrt{\log N}/\log\log N}
  =O_c((\log\log N)^{-2})\), transporte le terme arithmétique
  \(2^{-2L}R_2(N,L)\) vers ce taux, puis établit le même taux pour le
  cardinal normalisé des mauvais starts, la contribution pondérée des
  défauts terminaux et leur masse de probabilité. Le majorant fini du terme
  d'arêtes est amélioré par la somme harmonique, mais son taux critique, les
  termes de Stein–Chen et l'assemblage final en variation totale ne sont pas
  encore revendiqués.
- Fermeture conditionnelle de la proposition 14.2, uniformément sur tous les
  masques déterministes \(A_N\subseteq I_N\). Le graphe non masqué reste un
  graphe de dépendance exact après annulation des indicatrices hors masque ;
  les termes \(b_1,b_2\), la masse retirée et le déplacement du paramètre sont
  dominés par les termes complets. Sous AGG et les trois ponts internes de
  11.2, Lean obtient
  \[
    d_{\rm TV}\!\left(\mathcal L(Z_{N,L}(A_N)),
      \operatorname{Pois}(|A_N|2^{-L})\right)=o_C(1).
  \]
- Ajout de l'amincissement auxiliaire fini de la section 14.2 : loi produit
  de Bernoulli, identité exacte de la probabilité de vide et forme de Laplace
  \(\exp(-\sum_{x:J_x=1}g_x)\), plus domination des sommes amincies. Le
  passage aux sommes de Riemann et la convergence PPP restent séparés.
- Fermeture du lemme 15.2 sous les ponts `external` Laishram–Shorey et PNT.
  Le rang exact est minoré éventuellement par \(4\log_2L\), l'enveloppe
  sommée est \(O(L^{-2})\), et Lean prouve que la masse de toute la bande
  littérale \(L+2<x\le2L^2\) tend vers zéro.
- Avancée du lemme 15.3. Les noyaux carrés-libres \(B\)-friables sont
  comptés par \(2^{\pi(B)}\), puis par \(\exp(O(B/\log B))\) sous PNT. Lean
  construit les paramètres canoniques de deux sommets défectueux, exclut les
  noyaux égaux dans la zone haute, couvre les fenêtres réelles par l'union
  finie de Pell et obtient, sous le pont interne de Pell, le produit fini
  « noyaux² × offsets² × borne de Pell ». L'assemblage asymptotique uniforme
  complet du lemme reste à faire.
- Enregistrement du théorème 1 de Balasubramanian–Shorey comme pont
  `external` source-vérifié. Lean transforme canoniquement le produit des
  sommets défectueux en \(by^2\), prouve \(P^+(b)\le B\), puis déduit pour
  \(B\) assez grand et \(x>B^2+2\) la forme littérale du lemme 15.4
  \(m_x\le B-g_B\), avec \(g_B=B-\mu_B(\theta_0)\).
- Le point d'entrée public et la sélection historique `ReviewAxioms.lean`
  importent les nouveaux modules. Lean et mathlib restent gelés en
  `v4.19.0`. Le jalon compte 266 modules et 81 242 lignes Lean ; l'audit
  exhaustif couvre 2 433 théorèmes/lemmes publics et 2 435 cibles. Le
  registre généré contient douze ponts — cinq `external`, sept `internal` —
  et trace 60 théorèmes conditionnels.

## 0.25.0

- Raccord complet du graphe conditionnel du lemme 13.5 à l’interface finie
  d’Arratia–Goldstein–Gordon. La loi uniforme du cylindre des grands
  premiers est construite comme `FinitePMF`; Lean prouve la marginale
  exacte \(2^{-L}\) et, surtout, la factorisation pour **tout motif
  booléen** sur une famille arbitraire de non-voisins. Le prédicat
  `HasExactDependencyGraph` est ainsi instancié sans nouvelle hypothèse, et
  le pont externe AGG s’applique directement aux bonnes indicatrices
  conditionnelles.
- Formalisation du calcul fini de variation totale nécessaire au corollaire
  13.9 : symétrie, inégalité triangulaire, convexité par mélange uniforme et
  inégalité de couplage pour deux lois naturelles finies. Lean assemble un
  majorant explicite du corollaire à partir de la masse pondérée des mauvais
  starts, de leur cardinal et des termes \(b_1,b_2\). La décomposition
  bijective du cylindre en petites et grandes coordonnées fournit en outre
  la loi totale uniforme ; les moyennes conditionnelles de \(b_1\) et
  \(b_2\) sont identifiées exactement aux termes finis du lemme 13.8, sans
  nouveau pont. Au cutoff terminal littéral, leur petit-oh ferme ensuite
  uniformément la variation totale conditionnelle moyenne sous AGG et les
  trois ponts internes déjà exposés par la proposition 11.2.
- Fermeture du corollaire 13.9. Lean identifie le mélange conditionnel à la
  loi du bon compte sur le cylindre complet, couple ce compte au compte
  dyadique entier par la masse des mauvais starts, prouve
  \(d_{\rm TV}(\mathrm{Pois}(r),\mathrm{Pois}(s))\le|r-s|\), puis identifie
  la différence de paramètres à \(\#D_Y2^{-L}\). Le triangle fini et les
  trois petits-oh donnent uniformément
  \(d_{\rm TV}(\mathcal L(Z_{N,L}),\mathrm{Pois}(N2^{-L}))=o_C(1)\), sans
  nouveau pont.
- Fermeture de la proposition 14.1 dans sa fenêtre littérale
  \[
    \lvert L-\log_2N\rvert\le C_\star\log\log N .
  \]
  L’enveloppe du premier moment masqué est
  \(N^{-1/2+o(1)}\), uniformément sur tous les masques déterministes, puis
  uniformément \(o(1)\). Aucun pont n’est requis.
- Ajout du noyau fini masqué de la proposition 14.2. Les bons starts, arêtes
  de dépendance et voisinages fermés sont restreints par intersection ; les
  deux termes de Stein–Chen masqués sont dominés par leurs versions
  complètes. La perte de paramètre de Poisson est identifiée exactement à
  \(\lvert A_N\cap D_Y\rvert2^{-L}\), puis majorée par
  \(\lvert D_Y\rvert2^{-L}\).
- Fermeture du lemme 14.5 dans le cylindre fini. Pour les longueurs exactes
  \(q_e=L+e+1\) et \(q_f=L+f+1\), la fibre affine mixte donne exactement
  \(2^{-q_e-q_f}\eta_{e,f}2^{\rho_{e,f}}\). Si \(e,f\le E\), une extension
  par zéro injective des coefficients de lignes prouve
  \(\rho_{e,f}\le\rho_{L+E+1}\), sans pont.
- Formalisation du noyau fini du lemme 14.7. Après conditionnement sur les
  petits premiers, les probabilités exactes sont normalisées par
  \(\eta2^\rho/2^m\). La réalisation des lignes par un graphe, les pivots
  privés et l’espace cyclique donnent la marginale \(2^{-q}\) dans le cas
  forêt et la borne locale \(2^{1-q-r}\) lorsque le nombre cyclomatique est
  au plus un, sans nouveau pont.
- La dette interne du « square gap » du lemme 15.1 est supprimée. Lean
  déduit éventuellement
  \(2\lfloor\sqrt{x-1}\rfloor+1\le L\) de
  \(x\le L^{2-\varepsilon}\), et prouve séparément la décroissance
  exponentielle de l’enveloppe. Le pont externe est simultanément resserré à
  l’énoncé source \(\pi(t)\log t/t\to1\). Lean en déduit lui-même,
  uniformément sur la zone basse, la minoration
  \(3\log_2L\le\pi(L)-\pi(\sqrt{x+L})\). Les deux anciennes interfaces plus
  larges disparaissent donc du registre au profit d’un unique pont PNT
  directement contrôlable par citation.
- Enregistrement source-fidèle du corollaire 1 de Laishram–Shorey comme
  pont `external` du lemme 15.2. Lean formalise ensuite toute la chaîne
  finie : premiers \(>B\), sommet divisible unique, au plus trois exceptions
  dont le carré divise un sommet, au plus deux grands premiers simples par
  sommet, minorant exact des sommets non \(B\)-défectueux, spécialisation à
  \(B=L+1,\ L+2<x\le2L^2\), puis borne ponctuelle issue de (15.1). Le PNT
  source fournit en outre le minorant de rang avec la constante explicite
  \(c_3=1/32\).
- Lean et mathlib restent gelés en `v4.19.0`. L’archive conserve la racine
  unique `paper_c_lean/`; le manifeste et `AuditCheck.lean` sont régénérés
  déterministiquement après un build complet depuis un arbre sans
  `.lake/build` hérité.
- Le générateur d’audit reconnaît désormais aussi les attributs Lean placés
  sur la même ligne qu’une déclaration, par exemple `@[simp] theorem`. Cette
  correction réintègre deux théorèmes qui échappaient au parseur : l’audit
  exhaustif couvre 2 322 théorèmes/lemmes publics et deux constructions
  historiques, soit 2 324 cibles. Le registre contient dix ponts, répartis
  en quatre `external` et six `internal`, et trace 39 théorèmes conditionnels.
- La validation de publication est effectuée deux fois sans `.lake/build`
  hérité, d’abord depuis une copie propre des sources, puis depuis une
  extraction du ZIP final. Les deux builds complets et les deux audits
  exhaustifs réussissent avec la liste blanche fondationnelle
  `[propext, Classical.choice, Quot.sound]`.

## 0.24.0

- Fermeture des lemmes 13.3 et 13.4 dans la fenêtre critique littérale.
  Lean déduit de l'enveloppe finie au cutoff
  \(Y=\lfloor B^2\log B\rfloor\) que
  \(\#D_Y=N^{1/2+o_C(1)}\), puis \(\#D_Y=o_C(N)\) et
  \(2^{-L}\#D_Y=o_C(1)\). Le raccord exact
  `terminalDefectWeightMass` vers la masse de défauts de la proposition 3.2
  ferme simultanément
  \(\sum_{x\in D_Y}\mathbb P(J_{x,L}=1)=o_C(1)\), sans nouveau pont.
- Formalisation du graphe de dépendance conditionnel du lemme 13.5 dans le
  cylindre fini. Les événements dépendent extensionnellement des seules
  coordonnées \(\Pi_x(Y)\). Lean prouve la factorisation d'un bon start
  contre une famille arbitraire de non-voisins, puis la surjectivité du
  système joint et la probabilité exacte \(2^{-L\#s}\) de toute famille
  finie sans arête.
- Ajout de l'interface externe explicite du théorème
  d'Arratia–Goldstein–Gordon. L'espace probabilisé fini, les indicatrices,
  \(b_1,b_2\), la loi de leur somme, la loi de Poisson et la variation
  totale demi-\(\ell^1\) sont définis. La conséquence
  \(d_{\rm TV}\le2(b_1+b_2)\) reste un argument ordinaire
  `ArratiaGoldsteinGordonStatement`, enregistré `kind: external`.
- Formalisation des termes de Stein–Chen du lemme 13.8. Le premier terme
  possède son identité cardinale et vérifie inconditionnellement
  \(b_1=o_C(1)\). Le second terme moyen est partitionné exactement en
  chevauchement, contact et séparation ; son majorant fini puis
  \(\mathbb E b_2=o_C(1)\) sont prouvés sous les trois mêmes ponts internes
  que la proposition 11.2.
- Fermeture uniforme du premier moment masqué de la proposition 14.1 pour
  la fenêtre fixe \(\lvert L-\log_2N\rvert\le C\), simultanément pour tous
  les masques \(A_N\subseteq I_N\). La fenêtre plus large
  \(C_\star\log\log N\) du manuscrit reste à traiter.
- Formalisation du noyau fini du lemme 15.1 : premiers intermédiaires,
  supports disjoints, carré hors supports, indépendance des formes sur
  l'hyperplan pair, rang et borne
  \(\mathbb P(J_{x,L}=1)\le2^{-r(x)}\). La conclusion sommée \(o(1)\) est
  assemblée conditionnellement sous deux entrées séparées et auditées :
  le passage interne de \(x\le L^{2-\varepsilon}\) au gap entier, et la
  spécialisation externe du théorème des nombres premiers.
- Le registre contient désormais dix ponts, dont trois `external` et sept
  `internal`. L'audit déterministe couvre 2 136 théorèmes/lemmes publics et
  deux constructions historiques, soit 2 138 cibles. Lean et mathlib
  restent gelés en `v4.19.0`; le SHA du PDF cible et la racine d'archive
  `paper_c_lean/` sont inchangés.
- Validation depuis un arbre sans `.lake/build` hérité : le build complet
  termine avec succès après l'index `[2740/2741]`; les 2 138 sorties
  `#print axioms` sont présentes, dont 2 136 avec dépendances et deux sans
  axiome, et leur union est exactement
  `[propext, Classical.choice, Quot.sound]`. Le scan des constructions
  interdites est vide.

## 0.23.0

- Formalisation conditionnelle de la proposition 11.2. Lean prouve
  l'identité exacte
  \(2^\rho-1=(2^\sigma-1)+2^\sigma(2^\tau-1)\), la somme sur les couples
  ordonnés séparés, la désintégration dans les sept secteurs du lemme 11.1
  et les raccords aux secteurs 1–5. Deux ponts internes distincts, sourcés
  mot pour mot, isolent désormais exactement la masse hors \(T_K\) de la
  proposition 9.11 et la masse terminale \(N^{7/4+o_C(1)}\) du théorème
  10.1. La conclusion homogène \(o_C(N^2)\) expose aussi directement le
  pont d'hôtes de la proposition 9.9.
- Fermeture conditionnelle de la déduction des moments du §12 dans le
  cylindre fini. Les couples hors diagonale sont partitionnés exactement en
  chevauchement strict, contact et séparation ; Lean prouve l'identité du
  second moment factoriel, l'erreur
  \(\mathbb E[(Z)_{2}]-(N)_2 2^{-2L}=o_C(1)\), son transport vers
  \(\lambda_N^2\), puis
  \(\operatorname{Var}(Z)-\lambda_N=o_C(1)\). Les trois ponts réels de la
  proposition 11.2 restent visibles dans chaque signature publique ; aucun
  pont agrégé opaque n'est ajouté.
- Réduction substantielle de la dette interne du lemme 9.10. La matrice des
  petites lignes est maintenant canonique, avec
  \(\pi(L+1)+2\) lignes : premiers \(p\le L+1\) et deux parités de blocs.
  Ses colonnes proviennent des vraies composantes corrigées, leur synthèse
  est injective dans l'espace des solutions des grands premiers, et, sous
  \(L+1\le M\), son noyau est identifié exactement aux frontières uniques de
  relations. La
  seule dette raffinée restante est l'équivalence entre le quotient
  résiduel par le code rationnel et ce noyau concret ; elle implique
  l'ancienne interface de présentation.
- Formalisation du cœur fini des lemmes 13.3–13.4. Les mauvais starts
  \(D_B\) sont couverts par les incidences \((x,j)\), puis injectés par
  \((x,j)\mapsto(x+j,j)\), ce qui donne
  \[
  \#D_B\le
  L\,\#A_{B,1}(2N+L)
  \le2L\sqrt{2N+L}\prod_{p\le B}(1+p^{-1/2}).
  \]
  Lean prouve aussi l'inclusion \(D_B\subseteq D_Y\), le rang plein et la
  probabilité exacte \(2^{-L}\) hors \(D_B\), puis l'assemblage
  \[
  \sum_{x\in D_Y}\mathbb P(J_{x,L}=1)
  \le 2^{1-L}M_B+2^{-L}\#D_Y.
  \]
  Le cutoff est désormais littéralement
  \(Y=\lfloor B^2\log B\rfloor\), avec \(B\le Y\le B^3\) pour \(B\ge2\).
  Une décomposition
  dyadique fondée sur la borne de Chebyshev certifiée ferme l'étape
  première :
  \[
  \sum_{p\le H}p^{-1/2}\le
  2\sqrt{\operatorname{rootCutoff}(H)}
  +\frac{56\sqrt{2H}}{\lfloor\log_2H\rfloor/2},
  \qquad \operatorname{rootCutoff}(H)^2\le H .
  \]
  Pour \(N\ge1,B\ge16\), elle est composée avec le compte des incidences au
  cutoff \(Y\), donnant une enveloppe finie explicite de \(\#D_Y\) sans pont
  externe. Le passage final à \(N^{1/2+o_C(1)}\) dans la fenêtre critique
  n'est pas sur-revendiqué. De même, la conclusion \(o_C(1)\) de 13.4 attend
  encore le raccord de `terminalDefectWeightMass` à la masse déjà contrôlée
  par la proposition 3.2.
- Fermeture exacte du corollaire 13.2 dans le cylindre fini. Les coordonnées
  premières sont scindées en \(p\le Y\) et \(p>Y\) ; après fixation arbitraire
  des petites coordonnées, Lean traduit le second membre, prouve par pivots
  privés la surjectivité du système sur les grandes coordonnées hors \(D_Y\),
  puis obtient
  \[
  \#\mathrm{solutions}\,2^L=\#\mathrm{affectations\ grandes},
  \qquad
  \mathbb P(J_{x,L}=1\mid\text{petites coordonnées fixées})=2^{-L}.
  \]
  Le conditionnement est représenté extensionnellement par la loi uniforme
  finie sur les coordonnées restantes.
- Formalisation du noyau combinatoire des lemmes 13.5–13.6 : supports
  \(U_x,V_x\), ensembles \(\Pi_x(Y)\), graphe simple des bons starts,
  arêtes locales, couverture par le premier premier partagé, et majorant
  fini
  \[
  E_Y\le(L+1)^2
    \sum_{\substack{Y<p\le3N\\p\ {\rm premier}}}(N/p+1)^2.
  \]
  Une première fermeture analytique certifiée donne la variante explicite
  \[
  E_Y\le(L+1)^2\!\left(
    \frac{28N^2}{Y\lfloor\log_2Y\rfloor}
    +\frac{6N^2}{Y}+3N\right).
  \]
  Au cutoff littéral \(Y=\lfloor(L+1)^2\log(L+1)\rfloor\), Lean établit
  ensuite \(E_Y\le37N^2/m\) pour tout paramètre admissible \(m\), puis
  **\(E_Y=o_C(N^2)\)** uniformément dans la fenêtre critique, sans pont.
  L'indépendance conditionnelle, qui exige encore son interface probabiliste,
  n'est pas revendiquée.
- Premier jalon de la proposition 14.1 : pour tout masque déterministe
  \(A_N\subseteq I_N\), l'erreur exacte de premier moment est dominée par
  la même masse pondérée de défauts du bloc complet.
- Lean et mathlib restent gelés en `v4.19.0`. Le registre distingue toujours
  les ponts `external` et `internal`, conserve l'empreinte du PDF et signale
  explicitement que la nouvelle interface raffinée 9.10 implique
  l'ancienne interface historique.
- Validation finale depuis un arbre sans `.lake/build` hérité :
  2 730/2 730 tâches, audit exhaustif de 2 032 cibles limité à
  `[propext, Classical.choice, Quot.sound]`, et scan des constructions
  interdites vide.

## 0.22.0

- Formalisation de la proposition 9.9 jusqu'à une unique dette interne
  nommée : la population exacte du cœur profond avec \(\sigma=0\) et
  \(D^\#\ge3\), les enveloppes finies de poids et de masse, puis le calcul
  uniforme
  \(N^{1/2+o_C(1)}N^{1+o_C(1)}=N^{3/2+o_C(1)}\) sont certifiés. Le compte
  \(N^{1/2+o_C(1)}\) des hôtes, qui assemble les lemmes 9.4 et 9.8, reste un
  pont interne explicite.
- Raccord du lemme 9.10 aux objets canoniques : Lean construit la famille
  corrigée de cardinal \(D^\#\), l'ajoute aux \(c^\#\) composantes
  résiduelles, encode les petites lignes par une matrice finie sur
  \(\mathbf F_2\), puis prouve
  \(\tau+\widetilde k=D^\#+c^\#\). La présentation arithmétique exacte des
  petites lignes reste isolée comme pont interne.
- Raccord de la proposition 9.11 à la famille canonique : pour
  \(s=B-c^\#\), au plus \(2s\) composantes ont taille au moins trois et au
  moins \(B-3s\) ont taille deux. Un proxy entier explicite de \(T_K\)
  est défini avec une fonction de rang et un budget fournis, et Lean y prouve
  \(\tau\le B+2\).
- Nouvelles étapes concrètes du théorème 10.1 : désintégration exacte de
  \(T_K\) en fibres de partenaires, majoration par
  « premiers départs × partenaires », et borne pondérée finie
  \(\mathrm{masse}(T_K)\le\#T_K\,4\,2^B\).
- Formalisation du lemme 11.1 par six tests ordonnés : les sept secteurs
  couvrent exactement toutes les paires séparées, sont deux à deux disjoints
  et chaque paire appartient à un secteur unique. Les trois premiers
  secteurs coïncident avec les populations de la section 7 et les quatre
  derniers ont pour union exacte le cœur profond. Le test terminal est
  ensuite instancié par le proxy à budget entier ; le secteur 7 est
  exactement sa partie canoniquement non alignée.
- Le manifeste d'audit passe au schéma 3. Chaque pont porte désormais
  `kind: external | internal`; le rapport donne les comptes par nature et
  propage ces natures à tous les théorèmes conditionnels. Evertse--Silverman
  est `external`, tandis que le Pell généralisé et les dettes d'assemblage
  du manuscrit sont `internal`.
- Lean et mathlib restent gelés en `v4.19.0`; le point d'entrée public,
  l'audit exhaustif et l'archive à racine unique restent les contrôles de
  publication. La livraison a été reconstruite sans `.lake/build`
  préexistant : 2 717/2 717 tâches, puis audit propre des 1 783 cibles.

## 0.21.0

- Formalisation du lemme 9.3 par un noyau sans carré canonique :
  \(P Q=d z^2\) implique
  \(Q=\operatorname{sqfree}(dP)\,v^2\), avec unicité, divisibilité,
  \(e\le dP\) et transfert exact des bornes polynomiales.
- Formalisation des trois réductions du lemme 9.4 : compte élémentaire du
  degré un, complétion du carré et injection vers Pell au degré deux
  (y compris la factorisation de la branche \(e=1\)), puis normalisation
  Evertse--Silverman aux degrés au moins trois. Les deux entrées enregistrées
  — externe pour Evertse--Silverman, interne pour Pell — restent des
  hypothèses explicites.
- Paramétrisation canonique complète du lemme 9.5 :
  \(X=ecu^2\), \(Y=(d/e)cv^2\), avec \(e\mid d\),
  \(c\) carré-libre, \((c,d)=1\), unicité, réciproque et bornes des
  paramètres utiles au comptage.
- Extraction structurelle des lemmes 9.6--9.7 : une densité linéaire de
  composantes sous un budget total \(2B\) force l'existence d'une composante
  de taille uniformément bornée, y compris pour les composantes résiduelles
  concrètes.
- Réduction du lemme 9.8 à Pell pour deux défauts de classes distinctes,
  injection exacte des témoins de starts, et factorisation élémentaire de
  la branche de classes égales.
- Rang--nullité exact du lemme 9.10 dans un modèle explicite de coordonnées
  résiduelles, avec définition de \(\widetilde k\) et transport séparé par
  l'équivalence des composantes du lemme 6.1.
- Formalisation du noyau combinatoire de la proposition 9.11 : au plus
  \(2s\) composantes de taille \(>2\), donc au moins \(B-3s\) composantes
  de taille deux.
- Formalisation arithmétique du lemme 9.12 : égalité et non-trivialité des
  noyaux dans une composante de taille deux, coprimalité entre composantes,
  divisibilité du déterminant, non-nullité sous non-alignement et borne
  explicite \(|\Delta|\le6N(L+1)\).
- Formalisation des étapes finies de la fermeture terminale : unicité du
  noyau au-dessus du seuil, double comptage d'incidences, sommation pondérée,
  réduction injective du compte des partenaires à une boîte de Pell
  généralisée sous l'hypothèse-pont enregistrée,
  et borne
  \[
  \#A_{B,T}(X)\le
  2\sqrt X\sqrt T\prod_{p\le B}(1+p^{-1/2})
  \le2\sqrt X\sqrt T\,e^{2\sqrt B}.
  \]
- Lean et mathlib restent gelés en `v4.19.0`; le registre des ponts et
  l'audit exhaustif sont régénérés depuis les sources.

## 0.20.0

- Correction de `toSplitQuadratic_injective` : les deux projections de
  l'égalité sont désormais typées avant réduction, puis la paire est
  reconstruite avec `Prod.ext_iff`.
- Formalisation conditionnelle du lemme 9.2, dans sa variante à exposant
  polynomial entier positif, dans `PaperC.Diophantine.PellInput`.
- Lean prouve la réduction injective
  \((z,w)\mapsto(Az,w)\), avec \(D=AC\), \(M=Ae\), la non-carréité, les
  bornes de hauteur et le transfert de cardinal. Le compte uniforme de Pell
  généralisé reste l'unique hypothèse non prouvée de ce résultat ; le schéma
  3 le classe rétrospectivement comme pont interne.
- Passage du manifeste d'audit au schéma 2 : SHA-256 du PDF cible, registre
  sourcé des ponts, empreinte exacte de leurs énoncés, et statut
  conditionnel/inconditionnel des 1 560 théorèmes publics.
- `AXIOM_AUDIT.md` contient désormais le registre généré exhaustif ; le mode
  `--check` vérifie simultanément ce fichier, `AuditCheck.lean` et
  `audit_manifest.json`.
- Lean et mathlib restent gelés en `v4.19.0`; le manifeste de dépendances
  n'est pas modifié.

## 0.19.0

- Formalisation conditionnelle du lemme 9.1 dans
  `PaperC.Diophantine.EvertseSilvermanInput`.
- Le compte d'abscisses issu d'Evertse--Silverman reste une hypothèse
  explicite ; Lean en déduit le facteur deux de (9.2), puis prouve le compte
  des solutions nulles et le transfert injectif
  \((X,Y)\mapsto(X,eY)\).
- Ajout de `AuditCheck.lean` et `audit_manifest.json` : 1 559 théorèmes ou
  lemmes publics et deux constructions publiques porteuses de preuves.
- Ajout du générateur déterministe `scripts/generate_audit.mjs`.
- Import explicite dans `PaperC.Main` du module auparavant orphelin
  `SmallHeightPositiveSigmaSystematicBound`.
- Restauration et gel de la racine d'archive `paper_c_lean/`.
- Lean et mathlib restent gelés en `v4.19.0`; aucun changement du manifeste
  de dépendances.

## 0.18.0

- Fermeture de l'instance \(\alpha=3/16\) du théorème 8.1.
- Exclusion uniforme du cœur aligné restant après la partition de la
  section 7.
