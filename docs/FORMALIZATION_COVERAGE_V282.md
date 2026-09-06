# Couverture indépendante du papier C v2.8.2 et du compagnon — lot 10

**Environ 65 % de l’effort total de formalisation est acquis ; une fourchette prudente est 60–75 %. Il reste donc environ 25–40 % de l’effort.** Le périmètre est l’article entier et son compagnon, avec leurs modèles, leurs preuves et leurs raccords. Cette estimation conserve exactement les **19 blocs et 105 unités relatives** du lot 9. Elle ne résulte ni du nombre de théorèmes Lean, ni des lignes écrites, ni des heures écoulées.

Le comptage strict passe de **25 à 27 énoncés complets sur 61 dans l’article, soit 44,3 %** : 4.1 et 4.2 s’ajoutent aux résultats déjà acquis. Le compagnon passe de **1 à 3 énoncés nommés complets sur 8**, grâce à B.1 et B.2. B.1 développe 4.2 ; ces deux crédits ne représentent pas deux travaux indépendants et leurs pourcentages ne s’additionnent pas.

« Complet » conserve ici la convention du bilan précédent : les conclusions sont formalisées relativement aux entrées de littérature explicitement énoncées et à leurs représentations documentées. Le lot 10 ne démontre pas intérieurement le théorème des nombres premiers, l’existence classique des solutions de Stein avec leurs facteurs, ou le théorème AGG de processus. Ces trois frontières sont décrites plus bas.

Le bilan compare les preuves à la base publiée du lot 9, **24ea13304f5919ae2c1fa202cd9e2685727f2193**. La compilation globale a réussi (4 360 étapes), ainsi que l’audit exhaustif des 1 379 déclarations et les huit tests du garde d’audit. Le commit publié et les contrôles distants sont consignés dans le rapport de validation séparé. Ce bilan n’annonce aucune nouvelle qualification Palomar.

## Conclusions du lot 10

| Résultat | Page | Statut strict | Portée maintenant acquise |
|---|---:|---|---|
| Théorème 4.1 | Article 27–28 | Complet, avec entrées explicites | Transfert masqué scalaire et vectoriel, vraie source infinie, moyenne conditionnelle sur F_Y pour tous Y admissibles, puis loi inconditionnelle par mélange. |
| Proposition 4.2 | Article 28–29 | Complet, sous PNT pour la suppression | Vraie coupure libre, mauvais départs, arêtes et degré de tous les sites, deux selles uniques et constantes de second ordre. |
| Proposition B.1 | Compagnon 7–8 | Complet, sous PNT | Calcul de Rankin et sommes d’Euler uniformes avant la coupure libre, puis toutes les conclusions de 4.2. |
| Lemme B.2 | Compagnon 8 | Complet, avec facteurs de Stein explicites | Rétention des indicateurs exceptionnels, deux facteurs d’intensité, cas zéro et moyenne dans un environnement probabilisé arbitraire représenté par ses lois conditionnelles finies mesurables. |
| Théorème 4.3 | Article 29–30 | Partiel | Les briques du transfert dur/doux sont acquises ; les taux optimisés (4.8)–(4.10) et leurs cas d’intensité restent à assembler. |

Pour **4.1**, le masque reste le masque demandé. Le coût de suppression porte sur sa propre masse de défauts et sur ses mauvais départs effectifs, racine x−1 comprise. Avec p=2^−L, le terme prouvé est p(M_B(A)+2|D_Y(A)|). Le facteur scalaire dépend de la moyenne retenue µ_A=|A∩G_Y|p ; une intensité ambiante ne lui est pas substituée. Le champ vectoriel garde sa cible produit de Poisson indépendante, avec le facteur de processus adapté.

Le conditionnement utilise le cylindre max(coupure des événements,Y). Les atomes ont une masse strictement positive, sont équiprobables et leur partition engendre exactement F_Y. Le cas Y supérieur à la coupure des événements est traité par la suppression complète ; il ne crée donc pas de restriction cachée Y≤coupure. Les identités de cylindre puis de mélange portent sur les vraies lois du compteur et du vecteur de la source infinie. Les masses conditionnelles du champ somment bien à un.

Les endpoints principaux sont `MaskedScalarFullConditioning.theorem_four_one_scalar_full_FY`, `InfiniteMaskedScalarTransfer.theorem_four_one_scalar_infinite`, `InfiniteFieldTransfer.theorem_four_one_field_full_FY` et `InfiniteFieldTransfer.theorem_four_one_field_unconditional`.

Pour **4.2/B.1**, fixer c,C,β et ε précède le seuil N₀, puis viennent N, la coupure libre w, la longueur L et le masque. Toute la bande c√(log N·log log N)≤w≤C√(log N·log log N) est couverte. Les deux erreurs signées de la somme sur les premiers et du logarithme du produit d’Euler sont ≤ε(log N/w). Elles sont déduites de la sommation d’Abel et du PNT ordinaire, sans supposer leur propre terme principal pondéré.

`BadStartRankinFreeCutoff.normalized_fullBadMask_free_cutoff_le_eventually` donne exp(−D(log N/w)+ε log N/w) pour les vrais mauvais départs. `CutoffGraphFreeCutoff.normalized_degree_and_edges_free_cutoff_le_eventually` donne exp(−w+ε log N/w) pour le degré divisé par N et les arêtes ordonnées divisées par N², y compris les sites mauvais. Cette dernière estimation est sans prémisse PNT et absorbe, sur la bande considérée, le terme supplémentaire N^−1+o(1) du texte. Les développements des selles, leur rapport √2 et log log N=o(ν_N) sont des théorèmes internes séparés. Trois équivalents auxiliaires affichés au cours de la preuve de B.1 ne sont pas isolés comme endpoints ; cela ne laisse aucune conclusion de la proposition en prémisse.

## Relecture indépendante de la chaîne Stein

La lecture ciblée des onze modules demandés n’a révélé **aucun défaut matériel**. L’indépendance utilisée porte sur le motif complet des indicateurs hors voisinage ; une indépendance seulement deux à deux ne lui est pas substituée. Les marginales variables et les zéros hors masque sont conservés. La normalisation de la variation totale est la moitié de la somme des différences absolues, et son passage aux ensembles tests est prouvé.

Dans B.2, les voisins exceptionnels gardent leurs vraies marginales, puis leur moyenne est prise. La partie bonne utilise le facteur min(1,1/λ), la partie exceptionnelle min(1,1/√λ), avec la convention un à λ=0. Ce cas zéro est prouvé séparément. L’inégalité locale, le télescopage, la sommation, le passage à la variation totale et l’intégration sont internes : aucun endpoint arithmétique à démontrer n’est posé comme hypothèse.

`SoftMeasureAverage.lemma_b_two_integral` travaille sur un environnement probabilisé arbitraire. Ses lois conditionnelles jointes sont des PMF sur un espace fini, dépendant mesurablement de l’environnement ; graphe exact et marginales bonnes ne sont requis que presque partout. La mesurabilité et l’intégrabilité de la distance sont démontrées. Il ne construit pas automatiquement un noyau conditionnel régulier à partir de tout espace probabilisé initial ; cette limite de représentation n’est pas un manque de l’inégalité B.4 dans le modèle fourni.

Une précision de portée subsiste pour `SoftConditionalPoisson.weighted_environment_restriction_le` : son dénominateur positif générique n’est pas automatiquement identifié à la probabilité de l’événement d’environnement. L’inégalité est valide ; elle ne doit pas être présentée seule comme un théorème complet de conditionnement sur événement. Aucun crédit supplémentaire n’est attribué pour cette raison au §6.

La suggestion V3-S008 de localiser le budget de suppression au masque est confirmée. C’est un renforcement pour les masques clairsemés, et non une erreur du budget global imprimé. Les PDF v2.8.2 restent les seules sources du présent bilan.

## Les trois entrées de littérature

| Entrée explicite | Ce qu’elle fournit | Ce qui est prouvé à partir d’elle |
|---|---|---|
| `PrimeEulerPNT.PrimeNumberTheoremRemainder` | Pour tout η>0, l’erreur absolue π(⌊t⌋)−Ei(log t) est ≤ηt/log t à partir d’un seuil. | Sommes pondérées et produits d’Euler, coupure libre et mauvais départs réels. Les graphes, les selles et leurs développements sont internes. |
| `ScalarSteinInput.ScalarSteinFactorsStatement` | Solutions de l’équation de Stein pour toute intensité positive et tout ensemble test, avec bornes classiques de norme et de différence. | Cas zéro, télescopage, transfert scalaire masqué, rétention douce et moyenne mesurable B.4. |
| `ProcessAGGInput.ProcessAGGStatement` | Comparaison AGG de processus avec le produit de lois de Poisson, distincte du résultat scalaire. | Coûts arithmétiques, suppression, déplacement de cible et véritable champ infini conditionnel/inconditionnel. |

Ces entrées ne sont ni cachées dans un import ni annoncées comme démontrées intérieurement. Le pourcentage adopte la même frontière de littérature que les bilans précédents. Exiger aussi la formalisation intégrale de toutes les preuves externes changerait l’objectif et son dénominateur ; ce bilan ne donne pas de pourcentage pour cet objectif élargi.

## Comptage strict des énoncés

Le dénominateur de l’article reste ses **61 énoncés numérotés des §§2–7**. Les reformulations introductives 1.1–1.3 ne sont pas comptées une seconde fois. Définitions, preuves non numérotées, discussions et développements du compagnon sont pris en compte dans l’effort nécessaire, sans créer artificiellement des énoncés supplémentaires.

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifié |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 3 | 1 | 0 | 0 |
| §5 | 10 | 0 | 1 | 4 | 5 |
| §6 | 4 | 0 | 0 | 0 | 4 |
| §7 | 10 | 0 | 5 | 1 | 4 |
| Compagnon | 8 | 3 | 4 | 0 | 1 |

Le JSON associé conserve les **69 lignes documentaires**, avec pages, statut, preuves précises et reste. Elles ne constituent pas 69 résultats indépendants : A.1, A.2 et B.1 recouvrent directement 2.3, 3.13 et 4.2. Hors 4.1, 4.2, B.1 et B.2, aucun résultat précédemment partiel ou non raccordé ne reçoit de crédit complet par simple transitivité supposée des nouveaux outils.

## Effort total : dénominateur inchangé

Seuls les blocs « deux coupures » et « transfert TV » reçoivent du crédit nouveau. L’estimation passe de **56,25–68,42 à 63,60–74,37 unités acquises sur 105**, soit environ **61–71 %** selon le calcul interne. La présentation **60–75 %**, avec un repère central à 65 %, arrondit vers l’extérieur. Il s’agit d’un jugement sur la difficulté du travail restant, et non d’une mesure statistique. Les nouveaux raccords et les bibliothèques génériques réduisent déjà le reste ; ils ne sont pas crédités à nouveau dans chaque chapitre futur.

| Bloc mathématique | Poids | Acquis après lot 9 | Acquis après lot 10 |
|---|---:|---:|---:|
| Modèle, Fourier, arbres et pivots | 6 | 90–98 % | 90–98 % |
| Runge croissant et défauts | 8 | 95–100 % | 95–100 % |
| Probabilités ponctuelles et moments à une fenêtre | 4 | 100 % | 100 % |
| Canal canonique, résolution, quotient et cellules | 6 | 90–100 % | 90–100 % |
| Hôtes globaux, masse rationnelle et CRT | 5 | 85–95 % | 85–95 % |
| Secteurs 1–7 et hôtes de composantes | 8 | 90–98 % | 90–98 % |
| Pell et split-products, y compris taux précis | 4 | 55–75 % | 55–75 % |
| Secteur terminal, énergie, profils globaux et minorants | 8 | 95–100 % | 95–100 % |
| Deux coupures et calcul uniforme des selles | 7 | 20–40 % | 95–100 % |
| Transfert TV, rétention douce et moments | 7 | 50–65 % | 80–90 % |
| Dictionnaires, recouvrements et constructions | 5 | 10–20 % | 10–20 % |
| Marques, signes, comparaison agrégée et clusters | 7 | 35–50 % | 35–50 % |
| Niveaux croissants et limite Poisson–Gauss | 5 | 10–20 % | 10–20 % |
| Conditionnement, chemins et contrôle presque sûr | 5 | 5–15 % | 5–15 % |
| Frontière microscopique et rang d’incidence | 6 | 20–35 % | 20–35 % |
| Départs intermédiaires et mésoscopiques | 3 | 35–55 % | 35–55 % |
| Préfixe global et enveloppes presque sûres | 3 | 30–55 % | 30–55 % |
| Transport macroscopique et noyau signé relatif | 3 | 20–40 % | 20–40 % |
| Mélange des deux sources et horloges affines | 5 | 5–15 % | 5–15 % |

## Reste prioritaire

**4.3 est la prochaine conclusion structurante.** Les erreurs dures et douces doivent encore être assemblées sur toute la bande logarithmique, avec les vraies contributions arithmétiques du masque et les facteurs sensibles à λ. Le cas λ<1 de la branche douce doit conserver le conditionnement à sa propre coupure douce ; un résultat seulement à la coupure dure ne suffirait pas. Il reste aussi le minimum avec un, le domaine non trivial d’intensité croissante et l’absorption rigoureuse des restes polynomiaux au taux N^−1/3+ε. B.2 et les deux selles, même complets séparément, ne remplacent pas cette preuve.

Viennent ensuite les dictionnaires du §5 : recouvrements dirigés, constructions et dictionnaires croissants, puis marques exactes et signées. Le modèle infini, les lois finies/infinies, les graphes conditionnels, les couplages et les marques historiques sont de vraies briques réutilisables. Ils ne donnent pas encore les pertes uniformes en nombre de marques, la comparaison agrégée de C.1 ni la limite Poisson–Gauss. Les chapitres sur les chemins conditionnels, le presque sûr, la frontière microscopique et le mélange de deux sources conservent leurs obligations propres.

Les limites arithmétiques antérieures ne sont pas effacées : la proposition 3.19 reste partielle pour tout α>0 général ; les taux précis exp(O(log M/log log M)) de 3.13, 3.14 et A.2 dépassent les comptes M^ε actuellement prouvés ; le raffinement exp(O(√B/log B)) de 3.17 et de la seconde clause de 3.18 reste ouvert. Les wrappers de Fourier pour un tuple arbitraire et la dimension cyclomatique générale restent également à raccorder. Leur travail est déjà inclus dans les 105 unités.

## Provenance et validation

Les textes restent ceux remis par l’utilisateur : article v2.8.2 de 52 pages et compagnon de 23 pages. Le cœur conservé est `b3cf107d2df629453a5da8e84f2bad29eea0bf94`, Lean `leanprover/lean4:v4.32.0`, mathlib `v4.32.0`, révision `81a5d257c8e410db227a6665ed08f64fea08e997`. Aucun changement de version ou nouvelle qualification Palomar n’est crédité.

| PDF | SHA-256 |
|---|---|
| Article | `263682a1f2aa8301f06bf811fea1f81f42cd4493ccc4e1b94242a66cacfbd623` |
| Compagnon | `60d6f110aa057ebd9b1c79eaa291bc42759b5f021ef03807d9405a7ec473b094` |

Bilan indépendant établi le 6 septembre 2026, à partir des textes extraits, des signatures et des dernières compilations confirmées. Les 830 déclarations auditées et les 4 270 étapes de compilation du rapport précédent décrivent le lot 9, pas le lot 10. La tâche principale consigne séparément les nouveaux comptes, le contrôle global et le commit de publication. Le présent document reste utilisable sans anticiper ces résultats.

## Validation locale coordonnée

Compilation globale réussie sous Lean 4.32.0 et mathlib v4.32.0 ; audit de 1 379 déclarations réussi, limité aux trois axiomes usuels autorisés. Les trois propositions de littérature restent des hypothèses explicites. Une alerte de dépréciation non bloquante concerne le pont vers le nom Poisson historique ; le cœur conservé et les versions n’ont pas été modifiés. La relecture complémentaire des quatre modules de coupure libre confirme les seuils uniformes et les crédits 4.2/B.1.
