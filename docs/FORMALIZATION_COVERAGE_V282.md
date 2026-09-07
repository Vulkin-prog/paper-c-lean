# Couverture du papier C v2.8.2 et du compagnon — lot 23

**Environ 94 % de l'effort total est acquis, avec une fourchette prudente de 88–99 %.**
La grille conserve 19 blocs et 105 unités. Le comptage strict atteint
**52/61 résultats complets dans l'article**, et séparément **7/8 dans le
compagnon**. Les deux fractions ne s'additionnent pas ; les reprises
introductives1.1–1.3 restent exclues des 61.

Ce lot complète le théorème7.10. Les dix résultats numérotés de la section7
sont désormais formalisés sous les propositions bibliographiques explicites
déjà utilisées. Tous les acquis antérieurs sont conservés.

## Nouveaux acquis

La masse du bord après conditionnement affine est exactement2^(-d), avec
d=pi(L)−dim(rowG∩U_L). Le budget de rang permet de démontrer la vraie queue
rare, la concentration microscopique sur le bord et la loi du premier départ
conditionnée par A∩hit. Les phases réelles et les deux phases infinies sont
couvertes, y compris la version qui conserve la source et ses échelles L²/M.

La formule du signe positif au premier départ est également prouvée sans
neutralité future. La variante censurée à droite conserve la même cible
marquée complète sous la condition future, avec un coût additionnel
d'au plus1/card(bulk).

Ces conclusions de queue et de localisation ne demandent aucune neutralité sur les premiers futurs.
Le maintien de leur horloge géométrique exige la condition distincte du
papier, éventuellement pour chaque K fixé. Sous cette condition, la vraie
loi marquée converge en variation totale vers le mélange aux poids mobiles,
sans convergence de phase requise. Le cas général conserve la formule de
queue avec test de compatibilité et déficit de rang.

Les [déclarations précises](../PaperCV282/ENDPOINTS.md) distinguent le
résultat fini de rang, le régime asymptotique et la condition sur la marque
future. Les erreurs sont estimées avant leur amplification par exp(I), puis
normalisées par les probabilités des vrais événements. La convergence faible
de la grille vers Lebesgue est séparée de la comparaison en variation totale.

Les sept [propositions bibliographiques](../PaperCV282/LITERATURE_INPUTS.md)
restent inchangées. La chaîne affine utilise cinq arguments déjà actifs :
AGG de processus, PNT, LS uniforme, Shorey carré et Nicolas–Robin. L'audit
Lean ne démontre pas ces propositions. Aucun résultat de convergence
souhaité n'est ajouté comme entrée bibliographique.

## Comptage strict

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé |
|---|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 |
| §3 | 25 | 19 | 6 | 0 |
| §4 | 4 | 4 | 0 | 0 |
| §5 | 10 | 10 | 0 | 0 |
| §6 | 4 | 4 | 0 | 0 |
| §7 | 10 | 10 | 0 | 0 |
| Compagnon | 8 | 7 | 1 | 0 |

La [matrice JSON](FORMALIZATION_COVERAGE_V282.json) conserve 69 lignes et les
motifs de chaque statut. Les sections non numérotées du compagnon n'augmentent
pas son dénominateur 8. Un seul nouvel énoncé numéroté reçoit le crédit complet
dans ce lot ; ses nombreuses preuves intermédiaires ne sont pas comptées
comme autant de résultats du papier.

## Estimation de l'effort

Seul le bloc crossover change ; les 18 autres restent identiques au lot22.
Les bornes passent de 94,10–101,22 à **95,60–101,97 unités sur 105**, soit
91.05–97.11 %, milieu 94.08 %.
La communication arrondit à 94 %, avec prudence 88–99 %. Le nombre de lignes,
de déclarations ou d'heures ne détermine pas cette estimation. Les derniers
énoncés peuvent demander une part de travail disproportionnée.

| Bloc mathématique | Poids | Acquis après lot22 | Acquis après lot23 |
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
| Marques, signes, comparaison agrégée et clusters | 7 | 95–100 % | 95–100 % |
| Niveaux croissants et limite Poisson–Gauss | 5 | 70–85 % | 70–85 % |
| Conditionnement, chemins et contrôle presque sûr | 5 | 75–85 % | 75–85 % |
| Frontière microscopique et rang d’incidence | 6 | 95–100 % | 95–100 % |
| Départs intermédiaires et mésoscopiques | 3 | 90–100 % | 90–100 % |
| Préfixe global et enveloppes presque sûres | 3 | 100 % | 100 % |
| Transport macroscopique et noyau signé relatif | 3 | 100 % | 100 % |
| Mélange des deux sources et horloges affines | 5 | 70–85 % | 100 % |

## Reste à établir

Restent Berry–Esseen, les déviations modérées, le transfert local central pour
le taux doux et les conséquences de processus ouvertes dans D.4. D.1 reste
partiel. Les extensions non numérotées après6.4 restent distinctes : champ
étiqueté, contrôle scalaire simultané sur O(logN) longueurs et couplages
maximaux. Aucune trajectoire inverse infinie n'est revendiquée.

Les réserves arithmétiques antérieures demeurent : tout alpha>0 en3.19,
énoncés précis complets3.13/3.14/A.2, raffinements3.17/3.18, Fourier
arbitraire et rang cyclomatique. La clôture de7.10 ne les résout pas.

## Sources et validation

Base publiée du lot22 : `fa5200762f90bcb06ecd65ef82425b93d08a40a0`. **Lean 4.32.0 et mathlib v4.32.0** restent
ceux de la v0.9. Les 595 modules mathématiques antérieurs, le cœur historique,
les configurations et les deux PDF conservent leurs identités. L'inventaire
courant comprend 638 modules et 5386 déclarations.

Le [journal V3](PAPER_V3_REVISION_LOG.md) contient **une correction confirmée
et seize suggestions**. V3-S016 propose un rappel du régime rare et des
quantificateurs futurs ; aucune nouvelle erreur du papier n'est identifiée.
Compilation globale, audit exhaustif, relectures et contrôles du commit publié
sont consignés séparément. Aucun nouvel enregistrement Palomar n'est annoncé.
