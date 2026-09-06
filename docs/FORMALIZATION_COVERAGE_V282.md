# Couverture du papier C v2.8.2 et du compagnon — lot 16

**Environ 78 % de l'effort total est acquis, avec une fourchette prudente de 70–85 %.** La grille conserve les mêmes 19 blocs et 105 unités. Le comptage strict atteint **38 résultats complets sur 61 dans l'article (62,3 %)** et reste, séparément, à **3/8 dans le compagnon**. Les deux fractions ne s'additionnent pas.

Ce lot complète les **théorèmes 5.8 et 5.10 et le corollaire 5.9** : comparaison agrégée sous le budget de conditionnement à un facteur d'intensité, version signée, puis véritable limite faible Poisson–Gauss des compteurs arithmétiques conditionnés. Le théorème introductif 1.1 et les parties étiquetées acquises au lot 15 restent acquis. Les reprises introductives 1.1–1.3 sont toujours exclues du dénominateur 61.

La comparaison directionnelle nécessaire est démontrée à partir d'une nouvelle **entrée bibliographique explicite sur la solution de Stein multivariée et deux bornes quadratiques du Hessien**. Elle porte le total à quatre entrées : PNT, Stein scalaire, AGG de processus et Stein multivarié directionnel. Les conclusions nouvelles agrégées et le transfert de 5.10 utilisent seulement les arguments directionnel et PNT ; la convergence gaussienne de la cible n'ajoute aucune prémisse de CLT. Ces arguments bibliographiques ne sont ni des axiomes Lean nouveaux ni des théorèmes démontrés par l'audit : voir les [hypothèses déclarées](../PaperCV282/LITERATURE_INPUTS.md).

## Résultats nouveaux

| Résultat | Portée démontrée |
|---|---|
| Comparaison agrégée signée | Vrai vecteur de comptes, suppression des mauvais sites et remplissage indépendant de Poisson. Les taux de la cible complète sont préservés, même lorsque tous les sites sont supprimés. La somme des poids directionnels ne dépend pas du nombre de marques. |
| Théorème 5.8(ii), (5.21)–(5.22) | Sous `I+logΛ≤V−cν`, vraie variation totale signée et non signée au plus `2 exp(−c′ν)+N^(−1/3+ε)`, pour tout `0<c′<c` et `ε>0`. Le seuil précède la longueur et l'événement positif de tout `F_Yhard` ; tous les excès sont retenus. La convergence utilise `ε<1/3`. |
| Corollaire 5.9 | Les deux signes sont conservés dans le calcul joint et la cible indépendante. Le changement exact `r=e−d` donne l'intensité signée `2^(phase−r−2)`. Les distances agrégées sont préservées, ainsi que celle du chemin entier des seuils. |
| Théorème 5.10 | Pour tout segment fini `0≤j≤J` et tout ensemble fini de niveaux critiques entiers, vraie convergence faible conjointe sous le conditionnement du papier. Les tailles peuvent suivre une sous-suite quelconque, avec `d→∞`, `d/logN→0` et convergence de la phase dyadique. Le centrage et l'échelle utilisent la véritable intensité `Λ_N`. |
| Cible Poisson–Gauss | Covariance gaussienne `2^(−max(j,k))`, moyennes critiques Poisson `2^(θ−r−1)` et indépendance des deux blocs dans la limite. Cette indépendance est déduite de la même configuration de Poisson sous-jacente ; elle n'est pas supposée pour les observables à taille finie. |
| Description AR(1) | Après standardisation, covariance `2^(−|j−k|/2)`, innovations normales indépendantes et récurrence de coefficient `1/√2` sur chaque segment fini. Aucune convergence de trajectoires gaussiennes infinies n'est annoncée par ces seuls résultats. |

Les raccords principaux sont [SignedAggregateHardBudget.lean](../PaperCV282/SignedAggregateHardBudget.lean), [AggregateMovingCoordinates.lean](../PaperCV282/AggregateMovingCoordinates.lean) et [PoissonGaussianTheorem.lean](../PaperCV282/PoissonGaussianTheorem.lean). Le dernier démontre l'erreur de comparaison de la source avant de transférer la limite ; il ne prend pas cette erreur tendant vers zéro comme hypothèse finale.

**C.1 reste partiel au sens strict.** L'analogue signé effectivement démontré utilise la masse des relations complètes de valeurs à longueur `Q=L+E+1` et la condition `2*(Q+1)≤Y`. L'équation (C.5) imprimée, non signée, utilise la masse relative `R2(N,Q)` et `2Q<Y`. Aucun raccord exact entre ces deux formules n'est revendiqué. L'enveloppe signée suffit aux preuves achevées de 5.8–5.10 ; cela ne justifie pas de changer les quantités de l'énoncé C.1. Le [ledger exact](../PaperCV282/SignedAggregateRates.lean) et sa [comparaison réelle](../PaperCV282/SignedAggregateComparison.lean) rendent cette distinction vérifiable.

## Comptage strict

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifié |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 4 | 0 | 0 | 0 |
| §5 | 10 | 10 | 0 | 0 | 0 |
| §6 | 4 | 0 | 1 | 0 | 3 |
| §7 | 10 | 0 | 5 | 1 | 4 |
| Compagnon | 8 | 3 | 4 | 0 | 1 |

La [matrice JSON](FORMALIZATION_COVERAGE_V282.json) conserve ses 69 lignes documentaires. Les résultats 5.8 et 5.9 passent de « partiel » à « complet », et 5.10 de « à établir / non identifié » à « complet ». Les dix résultats numérotés du §5 sont ainsi couverts ; les arguments non numérotés plus précis du compagnon conservent leur propre réserve. Aucun nouveau crédit strict n'est attribué au compagnon dans ce lot.

## Estimation de l'effort

Le bloc des marques (7 unités) passe de **75–85 % à 85–95 %**, soit +0,70 unité aux deux bornes. Le bloc des niveaux croissants et de la limite Poisson–Gauss (5 unités) passe de **30–40 % à 65–80 %**, soit +1,75/+2,00 unités. Les 17 autres blocs restent inchangés. La réserve sur C.1 ne retire pas le travail réel de son analogue signé ; les outils génériques, le CLT et l'égalité des distances des chemins ne reçoivent pas de second crédit dans les chapitres suivants.

Le total passe de **74,05–83,52 à 76,50–86,22 unités sur 105**, soit **72,86–82,11 %**. Le milieu est **77,49 %**, communiqué comme « environ 78 % », avec une fourchette prudente de **70–85 %**. Ce jugement d'effort ne mesure ni le nombre de déclarations Lean, ni les lignes, ni la durée du lot.

| Bloc mathématique | Poids | Acquis après lot 15 | Acquis après lot 16 |
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
| Transfert TV, rétention douce et moments | 7 | 100 % | 100 % |
| Dictionnaires, recouvrements et constructions | 5 | 100 % | 100 % |
| Marques, signes, comparaison agrégée et clusters | 7 | 75–85 % | 85–95 % |
| Niveaux croissants et limite Poisson–Gauss | 5 | 30–40 % | 65–80 % |
| Conditionnement, chemins et contrôle presque sûr | 5 | 20–35 % | 20–35 % |
| Frontière microscopique et rang d'incidence | 6 | 20–35 % | 20–35 % |
| Départs intermédiaires et mésoscopiques | 3 | 35–55 % | 35–55 % |
| Préfixe global et enveloppes presque sûres | 3 | 30–55 % | 30–55 % |
| Transport macroscopique et noyau signé relatif | 3 | 20–40 % | 20–40 % |
| Mélange des deux sources et horloges affines | 5 | 5–15 % | 5–15 % |

## Reste à établir

Le raccord littéral à (C.5), les taux de **Berry–Esseen, les estimations locales et les déviations modérées de D.1** restent ouverts. La limite faible de 5.10 ne démontre pas ces taux. Les raffinements de trajectoires de D.2–D.4, le relèvement produit général 6.1 avec environnement enregistré, les conditionnements précis et le presque sûr, la frontière microscopique, les transports macroscopiques et le mélange de deux sources restent distincts des acquis de ce lot.

Les réserves arithmétiques antérieures sont conservées : tout `α>0` en 3.19, taux précis `exp(O(logM/loglogM))` en 3.13/3.14/A.2, raffinements 3.17/3.18, Fourier arbitraire et rang cyclomatique. Aucun crédit nouveau n'est attribué à ces obligations.

## Sources et validation

Base publiée du lot 15 : `a6bafe2027ec6c9fa53ea41db01e0cee7edee27c`. **Lean 4.32.0 et mathlib v4.32.0** restent ceux de la formalisation historique v0.9. Le cœur historique et les deux PDF conservent leurs identités dans le [manifeste](../PaperCV282/source_manifest.json).

Le [journal V3](PAPER_V3_REVISION_LOG.md) précise la frontière directionnelle Röllin/Barbour et distingue la formule C.1 imprimée de l'analogue signé démontré. Aucune nouvelle erreur du manuscrit n'est confirmée. Le registre contient **une correction confirmée et onze suggestions**. Les [déclarations](../PaperCV282/ENDPOINTS.md), les relectures et la validation séparée documentent les preuves vérifiées ; aucune validation distante ni nouvel enregistrement Palomar n'est présumé par cette évaluation.
