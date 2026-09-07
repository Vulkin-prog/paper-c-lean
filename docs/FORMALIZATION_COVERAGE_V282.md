# Couverture du papier C v2.8.2 et du compagnon — lot 21

**Environ 90 % de l’effort total est acquis, avec une fourchette prudente de 84–96 %.** La grille conserve 19 blocs et 105 unités. Le comptage strict est **48/61 résultats complets dans l’article**, et séparément **7/8 dans le compagnon**. Les deux fractions ne s’additionnent pas ; les reprises introductives1.1–1.3 restent exclues des 61.

Ce lot complète le théorème7.4, le corollaire7.5 et le théorème7.7. Les vrais objets du papier sont raccordés : compteur de préfixe contenu, plus long run, champ signé avec toutes ses marques, positions x/M et enregistrement microscopique B_L. Les résultats antérieurs sont conservés.

## Nouveaux acquis

| Résultat | Portée démontrée |
|---|---|
| 7.4 | Taux quantitatif pour le préfixe ouvert dans toute bande logarithmique ; vrai préfixe contenu avec correction de bord et de dépassement ; approximation uniforme de la loi de vide aux longueurs critiques. |
| 7.5 | Deux enveloppes asymétriques presque sûres pour tous les M assez grands ; sommabilité des vrais termes d’erreur, premier Borel–Cantelli et interpolation monotone. Aucune indépendance entre échelles. |
| 7.7 | Vraie moyenne conditionnelle pour le champ premier complet, toutes marques et deux signes, taux relatif67λ(exp(-V+ην)+M^(-1/3+ε)). Agrégation puis factorisation avec B_L à erreur o(λ), donc o(q_L+λ). |
| Positions | Vraies sommes de Dirac à x/M ; cibles de Poisson aux mêmes sites et mêmes moyennes. Le masque est exactement[ceil(M^δ),M−L+1]. |

Les [déclarations précises](../PaperCV282/ENDPOINTS.md) distinguent les masques, les moyennes et les hypothèses. L’équation(7.7) de la proposition7.3 et le théorème7.7 sont deux objets distincts ; tous deux sont désormais raccordés. Les sections non numérotées du compagnon ne créent pas de résultats supplémentaires dans le dénominateur8.

Les sept [propositions bibliographiques explicites](../PaperCV282/LITERATURE_INPUTS.md) sont inchangées. Les résultats7.4–7.5 utilisent Stein scalaire, LS uniforme, Shorey carré, PNT et Nicolas–Robin ;7.7 utilise AGG de processus et PNT. L’audit Lean ne démontre pas ces propositions. Aucun nouvel axiome ou résultat probabiliste souhaité n’est supposé.

## Comptage strict

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifié |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 4 | 0 | 0 | 0 |
| §5 | 10 | 10 | 0 | 0 | 0 |
| §6 | 4 | 4 | 0 | 0 | 0 |
| §7 | 10 | 6 | 2 | 0 | 2 |
| Compagnon | 8 | 7 | 1 | 0 | 0 |

La [matrice JSON](FORMALIZATION_COVERAGE_V282.json) conserve 69 lignes et les motifs de chaque statut.

## Estimation de l’effort

Seuls les blocs préfixe, transport macroscopique et crossover changent. Les 16 autres restent identiques au lot20. Les bornes passent de 87,10–95,57 à **90.95–98.52 unités sur 105**, soit 86.62–93.83 %, milieu 90.22 %. La communication arrondit à 90 %, avec prudence 84–96 %. Le nombre de lignes, de déclarations ou d’heures ne détermine pas cette estimation.

| Bloc mathématique | Poids | Acquis après lot20 | Acquis après lot21 |
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
| Préfixe global et enveloppes presque sûres | 3 | 30–55 % | 100 % |
| Transport macroscopique et noyau signé relatif | 3 | 20–40 % | 70–85 % |
| Mélange des deux sources et horloges affines | 5 | 20–35 % | 25–40 % |

## Reste à établir

La suite porte sur le transport macroscopique complet7.6 : niveaux croissants, événements conditionnants, budgets dur et mobile, comparaison agrégée. Le champ rare7.7 et la nouvelle géométrie de masques en fournissent des composantes, sans établir ces clauses à toutes intensités. Les mélanges7.8–7.10 restent ouverts ; la factorisation microscopique/bulk et les identités affines de bord ne suffisent pas à leurs conclusions complètes.

Restent aussi Berry–Esseen, les déviations modérées, le transfert local central pour le taux doux et les conséquences de processus ouvertes dans D.4. D.1 n’est pas complet. Le paragraphe suivant6.4 conserve ses réserves : champ étiqueté, contrôle scalaire simultané sur O(logN) longueurs et couplages maximaux. Aucune trajectoire inverse infinie n’est revendiquée.

Les réserves arithmétiques antérieures demeurent : tout α>0 en3.19, énoncés précis complets3.13/3.14/A.2, raffinements3.17/3.18, Fourier arbitraire et rang cyclomatique. Le taux précis raccordé aux deux-défauts intermédiaires ne clôt pas automatiquement toutes ces formulations.

## Sources et validation

Base publiée du lot20 : `ecd19a340d74e4a892f899a23ccf3b2490c18e95`. **Lean 4.32.0 et mathlib v4.32.0** restent ceux de la v0.9. Les 455 modules mathématiques antérieurs, le cœur historique et les deux PDF conservent leurs identités. L’inventaire courant comprend 511 modules et 4382 déclarations.

Le [journal V3](PAPER_V3_REVISION_LOG.md) contient **une correction confirmée et quatorze suggestions**. V3-S014 simplifie la correction des départs exclus à droite du préfixe ; aucune nouvelle erreur du papier n’est identifiée. Compilation globale, audit exhaustif, relectures et contrôles du commit publié sont consignés séparément. Aucun nouvel enregistrement Palomar n’est annoncé.
