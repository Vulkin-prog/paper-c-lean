# Couverture finale du papier C v2.8.2 et du compagnon — lot24

**La formalisation mathématique est complète relativement aux sept
propositions bibliographiques explicites.** La grille conserve 19 blocs et
105 unités, tous clos : 100% du périmètre mathématique. Ce pourcentage
ne mesure ni une probabilité de justesse ni le nombre de déclarations Lean.

Le comptage strict est **61/61 dans l'article** et, séparément, **8/8 dans
le compagnon**. Les reprises introductives1.1–1.3 sont exclues des 61.
Les deux fractions ne s'additionnent pas. Les conclusions non numérotées
sont comprises dans les blocs d'effort et ont fait l'objet d'une dernière
relecture transversale.

## Ce que ferme le dernier lot

Fourier pour des tuples arbitraires, rang cyclomatique, sommation CRT,
taux précis de Pell et produits scindés, raffinements d'Euler et exclusion
pour toute densité positive complètent les neuf derniers énoncés de
l'article et A.2. Les estimations gaussiennes quantitatives, les queues
modérées et leurs vrais transferts conditionnels ferment D.1.

Le contrôle presque sûr du champ spatial et de toutes les longueurs de la
bande logarithmique est raccordé à des couplages maximaux construits.
D.4 contient le processus entier, sa mesure ponctuelle localement finie
de masse totale infinie, ses restrictions aux demi-droites, ses lois après
conditionnement par le compte, ses fonctionnelles de Laplace et ses extrêmes.
Les petits raccords non numérotés de B.1, C.4, E.3/E.4 et de l'article
font également partie de la clôture.

## Périmètre exact

Les sept [entrées bibliographiques](../PaperCV282/LITERATURE_INPUTS.md)
restent non démontrées dans Lean. Elles sont des arguments explicites des
théorèmes, pas de nouveaux axiomes Lean. L'audit du noyau ne les démontre
pas. Les représentations équivalentes et l'ordre des quantificateurs sont
consignés dans les [déclarations](../PaperCV282/ENDPOINTS.md).

B.2 utilise des lois jointes conditionnelles finies mesurables sur un
environnement probabilisé ; il ne construit pas automatiquement un noyau
conditionnel depuis toute présentation de l'espace d'origine. Les segments
inverses sont ceux à borne inférieure fixée du texte. Les couplages maximaux
sont établis à chaque échelle, sans assertion supplémentaire de cohérence
conjointe entre toutes les échelles.

| Bloc conservé | Poids | Couverture relative |
|---|---:|---:|
| Modèle, Fourier, arbres et pivots | 6 | 100 % |
| Runge croissant et défauts | 8 | 100 % |
| Probabilités ponctuelles et moments à une fenêtre | 4 | 100 % |
| Canal canonique, résolution, quotient et cellules | 6 | 100 % |
| Hôtes globaux, masse rationnelle et CRT | 5 | 100 % |
| Secteurs 1–7 et hôtes de composantes | 8 | 100 % |
| Pell et split-products, y compris taux précis | 4 | 100 % |
| Secteur terminal, énergie, profils globaux et minorants | 8 | 100 % |
| Deux coupures et calcul uniforme des selles | 7 | 100 % |
| Transfert TV, rétention douce et moments | 7 | 100 % |
| Dictionnaires, recouvrements et constructions | 5 | 100 % |
| Marques, signes, comparaison agrégée et clusters | 7 | 100 % |
| Niveaux croissants et limite Poisson–Gauss | 5 | 100 % |
| Conditionnement, chemins et contrôle presque sûr | 5 | 100 % |
| Frontière microscopique et rang d’incidence | 6 | 100 % |
| Départs intermédiaires et mésoscopiques | 3 | 100 % |
| Préfixe global et enveloppes presque sûres | 3 | 100 % |
| Transport macroscopique et noyau signé relatif | 3 | 100 % |
| Mélange des deux sources et horloges affines | 5 | 100 % |

## Validation et suite éditoriale

L'inventaire contient **752 modules mathématiques et
6082 déclarations nommées**, dont 4530 théorèmes.
Les 638 modules mathématiques antérieurs sont conservés. Lean 4.32.0 et
mathlib v4.32.0 restent ceux de la formalisation v0.9. Les PDF sont inchangés.
Les relectures, la compilation globale, l'audit exhaustif et les contrôles
du commit publié sont consignés séparément, avec leurs empreintes.

Le [journal V3](PAPER_V3_REVISION_LOG.md) conserve une correction confirmée
et seize suggestions. Il reste la révision par l'auteur, l'intégration des
sources de la future V3 et la préparation d'une éventuelle qualification
Palomar. Ce sont des étapes éditoriales et de publication, pas des preuves
mathématiques encore ouvertes dans le périmètre annoncé.
