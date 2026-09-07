# Couverture du papier C v2.8.2 et du compagnon — lot 22

**Environ 93 % de l’effort total est acquis, avec une fourchette prudente de 87–98 %.** La grille conserve 19 blocs et 105 unités. Le comptage strict est **51/61 résultats complets dans l’article**, et séparément **7/8 dans le compagnon**. Les deux fractions ne s’additionnent pas ; les reprises introductives1.1–1.3 restent exclues des 61.

Ce lot complète les théorèmes7.6,7.8 et7.9. Les objets formalisés sont le vrai champ macroscopique à base contenue et le premier départ réel d’un run contenu, avec ses deux sources et ses marques. La version conditionnée par une information affine7.10 reste partielle. Tous les acquis antérieurs sont conservés.

## Nouveaux acquis

| Résultat | Portée démontrée |
|---|---|
| 7.6 | Champ complet à positions et niveaux littéraux, taux quantitatif(7.14), budgets étiquetés dur et mobile, budget agrégé à un facteur d’intensité. Cibles de Poisson exactes, marques non censurées, statistiques et chemin entier des seuils sur la population de base. |
| 7.8 | Vraie queue rare, loi conditionnelle du premier départ, phase réelle et deux limites dégénérées. Version avec labels de source et échelles L² ou M conservés. Passage faible de la grille uniforme à la vraie mesure de Lebesgue. |
| 7.9 | Vraie loi marquée conditionnelle en variation totale vers le mélange aux poids mobiles, sans hypothèse de convergence de ces poids. Horloge première au bord et excès entier bulk distincts, signe exact, variante censurée vers la même cible. |

Les [déclarations précises](../PaperCV282/ENDPOINTS.md) distinguent l’intensité ambiante M·2^(-L), l’intensité de la population contenue (M−L)·2^(-L) et l’intensité bulk. Une base contenue n’implique pas la censure de sa marque exacte. L’agrégation perd les positions ; la comparaison étiquetée les conserve.

Les sept [propositions bibliographiques explicites](../PaperCV282/LITERATURE_INPUTS.md) sont inchangées. Les branches étiquetées et les théorèmes7.8–7.9 utilisent AGG de processus, PNT, LS uniforme, Shorey carré et Nicolas–Robin. La branche agrégée7.6 utilise Stein directionnel à la place d’AGG de processus. L’audit Lean ne démontre pas ces propositions. Aucun nouveau résultat probabiliste souhaité n’est introduit en hypothèse.

## Comptage strict

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifié |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 4 | 0 | 0 | 0 |
| §5 | 10 | 10 | 0 | 0 | 0 |
| §6 | 4 | 4 | 0 | 0 | 0 |
| §7 | 10 | 9 | 1 | 0 | 0 |
| Compagnon | 8 | 7 | 1 | 0 | 0 |

La [matrice JSON](FORMALIZATION_COVERAGE_V282.json) conserve 69 lignes et les motifs de chaque statut. La section7 atteint 9 résultats complets sur10 ; le seul résultat encore partiel dans cette section est7.10. Les sections non numérotées du compagnon n’augmentent pas son dénominateur8.

## Estimation de l’effort

Seuls les blocs transport macroscopique et crossover changent. Les 17 autres restent identiques au lot21. Les bornes passent de 90,95–98,52 à **94.10–101.22 unités sur 105**, soit 89.62–96.40 %, milieu 93.01 %. La communication arrondit à 93 %, avec prudence 87–98 %. Le nombre de lignes, de déclarations ou d’heures ne détermine pas cette estimation. Le travail restant peut être disproportionné par rapport au nombre d’énoncés ouverts.

| Bloc mathématique | Poids | Acquis après lot21 | Acquis après lot22 |
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
| Transport macroscopique et noyau signé relatif | 3 | 70–85 % | 100 % |
| Mélange des deux sources et horloges affines | 5 | 25–40 % | 70–85 % |

## Reste à établir

La priorité est le théorème7.10 complet : queue rare et loi de localisation/marques après conditionnement par une information affine, sous son budget de rang. Les identités affines de bord et des premiers futurs sont déjà prouvées ; elles ne fournissent pas encore le contrôle relatif de la loi conditionnelle complète.

Restent aussi Berry–Esseen, les déviations modérées, le transfert local central pour le taux doux et les conséquences de processus ouvertes dans D.4. D.1 n’est pas complet. Le paragraphe suivant6.4 conserve ses réserves : champ étiqueté, contrôle scalaire simultané sur O(logN) longueurs et couplages maximaux. Aucune trajectoire inverse infinie n’est revendiquée.

Les réserves arithmétiques antérieures demeurent : tout alpha>0 en3.19, énoncés précis complets3.13/3.14/A.2, raffinements3.17/3.18, Fourier arbitraire et rang cyclomatique. Le taux précis raccordé aux deux-défauts intermédiaires ne clôt pas automatiquement toutes ces formulations.

## Sources et validation

Base publiée du lot21 : `7e6eeae0992cddcc4c0649362fba14841842c941`. **Lean 4.32.0 et mathlib v4.32.0** restent ceux de la v0.9. Les 511 modules mathématiques antérieurs, le cœur historique et les deux PDF conservent leurs identités. L’inventaire courant comprend 595 modules et 5103 déclarations.

Le [journal V3](PAPER_V3_REVISION_LOG.md) contient **une correction confirmée et quinze suggestions**. V3-S015 clarifie la normalisation du mélange marqué et sa preuve par troncature du seul indice premier. Aucune nouvelle erreur du papier n’est identifiée. Compilation globale, audit exhaustif, relectures et contrôles du commit publié sont consignés séparément. Aucun nouvel enregistrement Palomar n’est annoncé.
