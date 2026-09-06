# Couverture du papier C v2.8.2 et du compagnon — lot 11

**Environ 68 % de l'effort total est acquis, avec une fourchette prudente de 60–75 %.** L'estimation porte sur l'article entier et son compagnon, selon les mêmes **19 blocs et 105 unités relatives** que les lots 9 et 10. Elle ne provient ni du nombre de déclarations Lean, ni des lignes de code, ni des heures écoulées.

Le comptage strict atteint **28 résultats complets sur 61 dans l'article (45,9 %)**, contre 27 au lot 10. Le théorème 4.3 est le nouveau résultat numéroté complet ; les quatre résultats du §4 sont maintenant couverts. Le compagnon reste à **3/8** : B.3 est une sous-section d'application, pas un énoncé nommé supplémentaire. Les fractions article/compagnon ne s'additionnent pas, car plusieurs résultats se recouvrent.

« Complet » conserve la frontière bibliographique des bilans précédents : les conclusions sont formalisées relativement aux propositions externes explicitement déclarées. Le dépôt ne prouve pas intérieurement le PNT ordinaire, l'existence classique des solutions de Stein avec leurs facteurs, ou le théorème AGG de processus. Les nouveaux taux scalaires n'utilisent que les deux premières propositions ; aucun nouvel input externe n'est ajouté. Voir les [hypothèses bibliographiques](../PaperCV282/LITERATURE_INPUTS.md).

## Ce que le lot ferme

| Résultat | Portée établie |
|---|---|
| Théorème 4.3, (4.8) et (4.9) | Vraie loi du compte et moyenne conditionnelle aux seuils hard et soft ; toute bande logarithmique fixée, toutes intensités, minimum avec un, constantes explicites 20 et 6. |
| Équation (4.10) | Seuil premier libre dans toute bande fixée c√(H log H)≤w≤C√(H log H), pour λ≥1 et log λ≤Aw ; coefficients 2, 3 et 6, reste polynomial absorbé, tout ε>0. |
| Régimes de convergence | Intensité bornée au hard, marge soft positive, et ancien seuil hard inclus dans la plage soft ; vraies lois et moyennes conditionnelles. |
| Événements arithmétiques | Loi exactement P(Z=k et E)/P(E), événement positif mesurable dans le F_Y choisi, coût inverse réel, puis convergence sous 2I+log⁺λ≤Vsoft−cνsoft avec I=−log P(E). |

Les seuils en N sont choisis avant L, et avant w pour la coupure libre. Les coûts sont les vraies masses de défauts, mauvais départs, degrés et arêtes de tous les sites, paires touchantes et relations séparées. Les voisins mauvais gardent leurs probabilités réelles dans le calcul soft. La preuve démontre que chaque coupure entière floor(exp V) représente **tout F_Y**, puis identifie les lois conditionnelles aux rapports de mesures des atomes de la source infinie.

La preuve soft traite aussi λ<1 au même seuil soft. La simplification correspondante est proposée en V3-S009 ; elle ne signale pas une erreur du papier. Les PDF restent inchangés. Les déclarations précises figurent dans le [registre des résultats](../PaperCV282/ENDPOINTS.md).

## Conditionnement : limite du crédit

Le dénominateur générique des premières briques est maintenant raccordé à la véritable probabilité P(E). La loi restreinte est normalisée et son mélange sur les atomes choisis est prouvé. Le seuil de la borne rare précède à la fois la longueur et l'événement ; sous la marge annoncée, l'erreur est au plus 6(exp(−cνsoft/4)+N^(−1/6)), ce qui établit la convergence pour des suites d'événements.

Le **lemme 6.1 reste partiel** : son relèvement produit conjoint avec une variable enregistrée arbitraire dans un espace standard borélien n'est pas encore démontré. La restriction scalaire à un événement F_Y ne donne pas le conditionnement résolu sur un compte observé rare, les chemins complets, ni le presque sûr. Les équations (6.1)–(6.2) n'ajoutent pas deux résultats au dénominateur des 61 énoncés. Aucun crédit complet supplémentaire n'est attribué au §6.

La convergence obtenue est celle de distances en variation totale et de moyennes conditionnelles. Elle ne signifie pas une convergence presque sûre des noyaux. Aucune convergence à la frontière soft exacte log λ=Vsoft, ni optimalité du seuil, n'est revendiquée.

## Comptage strict

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifié |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 4 | 0 | 0 | 0 |
| §5 | 10 | 0 | 1 | 4 | 5 |
| §6 | 4 | 0 | 1 | 0 | 3 |
| §7 | 10 | 0 | 5 | 1 | 4 |
| Compagnon | 8 | 3 | 4 | 0 | 1 |

La [matrice JSON](FORMALIZATION_COVERAGE_V282.json) conserve les 69 lignes documentaires avec preuves, pages et obligations restantes. Les reprises introductives 1.1–1.3 ne sont pas recomptées. Les 69 lignes ne sont pas 69 résultats indépendants : notamment A.1, A.2 et B.1 développent des résultats de l'article.

## Estimation de l'effort

Seuls le transfert de Poisson et le conditionnement reçoivent du crédit nouveau. Le calcul passe de **63,60–74,37** à **65,75–76,07 unités sur 105**, soit **62,6–72,4 %**. Le milieu est à 67,5 %, communiqué comme « environ 68 % », avec la fourchette extérieure 60–75 %. La hausse reste modérée parce que les briques de 4.3 étaient déjà largement créditées au lot 10. Le volume de nouveaux théorèmes n'altère pas les poids.

| Bloc mathématique | Poids | Acquis après lot 10 | Acquis après lot 11 |
|---|---:|---:|---:|
| Modèle, Fourier, arbres et pivots | 6 | 90–98 % | 90–98 % |
| Runge croissant et défauts | 8 | 95–100 % | 95–100 % |
| Probabilités ponctuelles et moments à une fenêtre | 4 | 100 % | 100 % |
| Canal canonique, résolution, quotient et cellules | 6 | 90–100 % | 90–100 % |
| Hôtes globaux, masse rationnelle et CRT | 5 | 85–95 % | 85–95 % |
| Secteurs 1–7 et hôtes de composantes | 8 | 90–98 % | 90–98 % |
| Pell et split-products, y compris taux précis | 4 | 55–75 % | 55–75 % |
| Secteur terminal, énergie, profils globaux et minorants | 8 | 95–100 % | 95–100 % |
| Deux coupures et calcul uniforme des selles | 7 | 95–100 % | 95–100 % |
| Transfert TV, rétention douce et moments | 7 | 80–90 % | 100 % |
| Dictionnaires, recouvrements et constructions | 5 | 10–20 % | 10–20 % |
| Marques, signes, comparaison agrégée et clusters | 7 | 35–50 % | 35–50 % |
| Niveaux croissants et limite Poisson–Gauss | 5 | 10–20 % | 10–20 % |
| Conditionnement, chemins et contrôle presque sûr | 5 | 5–15 % | 20–35 % |
| Frontière microscopique et rang d’incidence | 6 | 20–35 % | 20–35 % |
| Départs intermédiaires et mésoscopiques | 3 | 35–55 % | 35–55 % |
| Préfixe global et enveloppes presque sûres | 3 | 30–55 % | 30–55 % |
| Transport macroscopique et noyau signé relatif | 3 | 20–40 % | 20–40 % |
| Mélange des deux sources et horloges affines | 5 | 5–15 % | 5–15 % |

## Reste prioritaire

Les prochains endpoints sont les dictionnaires du §5 : champ site×mot, recouvrements dirigés, constructions et uniformité en cardinal. Viennent ensuite les marques exactes signées et la comparaison agrégée de C.1, puis les niveaux croissants et la limite conjointe Poisson–Gauss. Un transfert de champ ne fournit pas automatiquement le gain après agrégation.

Restent également le relèvement produit de 6.1, le conditionnement sharp, les trajectoires résolues et le presque sûr ; puis la frontière microscopique et le mélange de deux sources du §7 et des annexes D/E. Leurs obligations propres ne sont pas créditées par simple réemploi présumé des nouveaux outils.

Les limites arithmétiques antérieures sont conservées : tout α>0 général de 3.19, taux précis exp(O(log M/log log M)) de 3.13/3.14/A.2, refinements 3.17/3.18, Fourier arbitraire et rang cyclomatique. Les taux M^ε et spécialisations déjà démontrés restent acquis.

## Provenance et validation

La base de comparaison est le commit du lot 10 `9ffa501681b0baf1da8d88c4bb069a9c0004aa55`. Le cœur historique, les PDF anglais v2.8.2 et les versions restent inchangés : Lean 4.32.0, mathlib v4.32.0, révision `81a5d257c8e410db227a6665ed08f64fea08e997`. Les identités des documents figurent dans le [manifeste](../PaperCV282/source_manifest.json).

La relecture indépendante a examiné les signatures, les calculs et leur correspondance avec le papier. La compilation globale du lot 11 a réussi (4 381 étapes), ainsi que l'audit des 1 552 déclarations et les huit tests du garde d'audit. Aucun avertissement ne concerne les 21 nouveaux modules ; un ancien pont Poisson de l'overlay conserve son avertissement de dépréciation. Le commit publié et ses contrôles distants sont consignés dans la validation séparée. Les 17 contrôles réussis de la base du lot 10 ne remplacent pas ceux du nouveau commit. Aucune nouvelle qualification Palomar n'est annoncée.
