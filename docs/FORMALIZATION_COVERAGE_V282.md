# Couverture du papier C v2.8.2 et du compagnon — lot 20

**Environ 87 % de l’effort total est acquis, avec une fourchette prudente de 80–93 %.** La grille conserve 19 blocs et 105 unités. Le comptage strict est **45/61 résultats complets dans l’article**, et séparément **7/8 dans le compagnon**. Les deux fractions ne s’additionnent pas ; les reprises introductives 1.1–1.3 restent exclues des 61.

Ce lot complète le théorème7.1, le lemme7.2, la proposition 7.3 et les lemmes E.1–E.3. Les preuves utilisent les vrais rangs, défauts et événements de départ. La stabilité des configurations conditionnées à coupure variable est incluse. Les acquis des lots précédents, notamment le §6 et le budget central avec coefficient3/2, sont conservés.

## Nouveaux acquis

| Résultat | Portée démontrée |
|---|---|
| 7.1 | Masse intérieure≤2^−((1+δ)πL) pour tout 0<δ<28271/332640 ; q_L/2^−πL→1 et localisation conditionnelle au bord. Le choix δ=1/12 est explicite. |
| 7.2 | Vrais deux-défauts, toute hauteur intermédiaire, taux exp(C logM/loglogM), seuil avant L et X. |
| 7.3 | Somme de préfixe(7.7), départs profonds(7.8), coupure libre(7.9), négligeabilité relative et comparaison TV des vraies configurations prolongées par zéro. |
| E.1 | Mineur identité dans les trois fenêtres de transition et perte de rang d’au plus un. |
| E.2 | Vrai lemme de rang d’incidence, quotient des lignes privées, exception des carrés≤854 et optimum global K=11. |
| E.3 | Borne uniforme des défauts postquadratiques, gap/π(B)→∞ et vraie probabilité de départ. |
| Horloges et affine | Loi géométrique exacte sous le bord, limite TV sous non-vacance microscopique, queue du dépassement entier et non-tension ; masse affine et queues des prochains premiers. Le théorème 7.10 reste partiel. |

Les [déclarations précises](../PaperCV282/ENDPOINTS.md) détaillent les interfaces. L’équation(7.7) appartient à la proposition 7.3 ; elle ne désigne pas le théorème 7.7, encore non raccordé. Les sections non numérotées E.4–E.7 ne créent pas de résultats supplémentaires dans le dénominateur 8.

Sept [propositions bibliographiques](../PaperCV282/LITERATURE_INPUTS.md) sont désormais actives : les quatre antérieures, LS uniforme, Shorey carré et Nicolas–Robin. Les nouvelles preuves de rang et de probabilité les prennent comme arguments explicites. Elles n’ajoutent aucun axiome Lean ; l’audit ne démontre pas ces propositions.

## Comptage strict

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifié |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 4 | 0 | 0 | 0 |
| §5 | 10 | 10 | 0 | 0 | 0 |
| §6 | 4 | 4 | 0 | 0 | 0 |
| §7 | 10 | 3 | 3 | 1 | 3 |
| Compagnon | 8 | 7 | 1 | 0 | 0 |

La [matrice JSON](FORMALIZATION_COVERAGE_V282.json) conserve 69 lignes et les motifs de chaque statut.

## Estimation de l’effort

Seuls les blocs microscopique, intermédiaire et crossover changent. Les 16 autres restent identiques au lot 19. Les bornes passent de 80,20–89,32 à **87,10–95,57 unités sur 105**, soit 82,95–91,02 %, milieu 86,99 %. La communication arrondit à 87 %, avec prudence 80–93 %. Le nombre de lignes et de déclarations ne détermine pas cette estimation.

| Bloc mathématique | Poids | Acquis après lot 19 | Acquis après lot 20 |
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
| Frontière microscopique et rang d’incidence | 6 | 20–35 % | 95–100 % |
| Départs intermédiaires et mésoscopiques | 3 | 35–55 % | 90–100 % |
| Préfixe global et enveloppes presque sûres | 3 | 30–55 % | 30–55 % |
| Transport macroscopique et noyau signé relatif | 3 | 20–40 % | 20–40 % |
| Mélange des deux sources et horloges affines | 5 | 5–15 % | 20–35 % |

## Reste à établir

La suite porte sur le préfixe global 7.4, les enveloppes presque sûres 7.5, les transports macroscopiques 7.6–7.7 et les mélanges 7.8–7.10. Les seules identités affines de bord et d’horloge ne suffisent pas au crossover complet.

Restent aussi Berry–Esseen, les déviations modérées, le transfert local central pour le taux doux et les conséquences de processus ouvertes dans D.4. D.1 n’est pas complet. Le paragraphe suivant 6.4 conserve ses réserves : champ étiqueté, contrôle scalaire simultané sur O(logN) longueurs et couplages maximaux. Aucune trajectoire inverse infinie n’est revendiquée.

Les réserves arithmétiques antérieures demeurent : tout α>0 en 3.19, énoncés précis complets 3.13/3.14/A.2, raffinements 3.17/3.18, Fourier arbitraire et rang cyclomatique. Le taux précis est maintenant raccordé aux deux-défauts intermédiaires ; cela ne clôt pas automatiquement toutes ces formulations.

## Sources et validation

Base publiée du lot 19 : `455f35f6c188da67fdef6994b2a7d6a1c3bf8a9a`. **Lean 4.32.0 et mathlib v4.32.0** restent ceux de la v0.9. Le cœur historique et les deux PDF conservent leurs identités dans le [manifeste](../PaperCV282/source_manifest.json).

Le [journal V3](PAPER_V3_REVISION_LOG.md) contient **une correction confirmée et treize suggestions**. V3-S013 propose une simplification du comptage profond ; aucune nouvelle erreur du papier n’est identifiée. Compilation globale, audit exhaustif, relectures et contrôles du commit publié sont consignés séparément. Aucun nouvel enregistrement Palomar n’est annoncé.
