# Couverture du papier C v2.8.2 et du compagnon — lot 19

**Environ 81 % de l'effort total est acquis, avec une fourchette prudente de 75–88 %.** La même grille de 19 blocs et 105 unités donne **42/61 résultats numérotés complets dans l'article**, et séparément **4/8 dans le compagnon**. Ces fractions ne s'additionnent pas ; les reprises introductives 1.1–1.3 restent exclues du dénominateur 61.

Ce petit lot démontre **le budget central avec coefficient 3/2** après (6.7). Pour `λ→∞`, `n=λ+t√λ+O(1)` et `t=o(λ^(1/6))`, les deux erreurs `log n−log λ` et `λh(n/λ)−t²/2` tendent vers zéro. Le budget `I+(3/2)log λ+t²/2≤V−cν` contrôle donc le vrai futur après résolution, avec toute marge `0<c'<c`. La bande logarithmique et la positivité de l'événement résolu sont déduites. Aucun résultat numéroté n'est recompté ; l'estimation reste à 81 %.

L’équation (6.3), relative aux probabilités conditionnelles à petite intensité, demeure acquise depuis le lot 18.

Le lot 17 a complété les **lemmes 6.1 et 6.2, le théorème 6.3, le corollaire 6.4 et le théorème C.1**. Il a aussi prouvé le taux agrégé à toute intensité positive (6.5), une estimation locale de Poisson effective et le budget de résolution (6.7) sur une bande logarithmique explicite.

## Acquis du lot 17 conservés

| Résultat | Portée démontrée |
|---|---|
| C.1 / (C.5) exact | Vrais comptes non signés, profil relatif `R2(N,Q)` pour `Q=L+E+1`, seul seuil `2Q<Y`, cas `E=0` inclus. La moyenne sur tout `F_Y` et la restriction aux événements positifs sont identifiées. |
| Lemme 6.1 | Vrai noyau conditionnel pour une observation standard borélienne, sur un espace source arbitraire. Toute variable enregistrée mesurable pour la sous-tribu peut être retenue. La restriction à un événement positif coûte une seule division par sa probabilité. |
| Lemme 6.2 | Borne exacte `ε/max(p,q)≤ε/p` pour des lois générales ; la positivité de l'événement source est démontrée dès que `ε<p`. |
| Théorème 6.3 | Vraie loi de tout le futur sous `C∩{Z=n}`, cible de `n` durées géométriques indépendantes. Un segment inférieur fini conserve les incréments de Poisson indépendants, conjointement avec le futur entier. |
| Taux (6.5) | Erreur agrégée au plus `40 exp(I)λ(1+log⁺(2λ))exp(−V+ην)+N^(−1/3+ε)`, sans hypothèse `λ≥1`, sous une enveloppe `I+log⁺λ≤A V`. Le seuil précède la longueur et l'événement. |
| Estimation locale et (6.7) | Pour `n≥1`, la correction multiplicative de Stirling vaut `exp(−δ_n)`, avec `0≤δ_n≤1/(12n)`, uniformément en `λ>0`. Sous (6.7), l'erreur divisée par la vraie masse de Poisson est au plus `40 C exp(−cν/2)+N^(−1/6)→0`, où `C=√(2π)exp(1/12)`. La vraie loi résolue satisfait cette même borne. |
| Corollaire 6.4 | Vraie TV conditionnelle de toute la configuration agrégée et de tout l'escalier, au plus `exp(−βν)` finalement presque sûrement sur les tailles géométriques. Le budget entraîne la condition sur la profondeur ; aucune indépendance entre échelles n'est supposée. |

Les [déclarations précises](../PaperCV282/ENDPOINTS.md) donnent les interfaces vérifiées. La correspondance entre les atomes premiers et le véritable noyau conditionnel est démontrée dans [PrimeEnvironmentStableLift.lean](../PaperCV282/PrimeEnvironmentStableLift.lean). C.1 est maintenant complet au sens strict ; la réserve du lot 16 sur `Q` et `2Q<Y` est levée.

Les quatre [propositions bibliographiques](../PaperCV282/LITERATURE_INPUTS.md) sont inchangées. C.1 utilise l'entrée directionnelle de Stein ; les nouveaux taux arithmétiques ajoutent PNT. Les noyaux, le conditionnement précis, les cibles géométriques, Stirling et Borel–Cantelli ne requièrent aucune nouvelle prémisse. L'audit des axiomes ne démontre pas les hypothèses bibliographiques.

## Comptage strict

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifié |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 4 | 0 | 0 | 0 |
| §5 | 10 | 10 | 0 | 0 | 0 |
| §6 | 4 | 4 | 0 | 0 | 0 |
| §7 | 10 | 0 | 5 | 1 | 4 |
| Compagnon | 8 | 4 | 3 | 0 | 1 |

La [matrice JSON](FORMALIZATION_COVERAGE_V282.json) conserve ses 69 lignes. Les quatre résultats numérotés du §6 sont couverts. Les paragraphes non numérotés et les raffinements du compagnon conservent leurs réserves propres.

## Estimation de l'effort

Le petit ajout de ce lot est absorbé dans la fourchette existante du bloc de conditionnement. Les 19 blocs conservent leurs valeurs du lot 18 : **80,20–89,32 unités sur 105**, soit **76,38–85,07 %**, milieu **80,72 %**. La communication arrondit à **81 %**, avec prudence **75–88 %**. Le nombre de déclarations, les lignes et les outils génériques ne déterminent pas cette estimation.

| Bloc mathématique | Poids | Acquis après lot 18 | Acquis après lot 19 |
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
| Frontière microscopique et rang d’incidence | 6 | 20–35 % | 20–35 % |
| Départs intermédiaires et mésoscopiques | 3 | 35–55 % | 35–55 % |
| Préfixe global et enveloppes presque sûres | 3 | 30–55 % | 30–55 % |
| Transport macroscopique et noyau signé relatif | 3 | 20–40 % | 20–40 % |
| Mélange des deux sources et horloges affines | 5 | 5–15 % | 5–15 % |

## Reste à établir

La priorité suivante porte sur la frontière microscopique puis les régimes du §7 et le mélange des deux sources. Restent aussi Berry–Esseen, les déviations modérées, le transfert local central pour le taux doux, et les conséquences de processus encore ouvertes dans D.4. La formule locale de Poisson est acquise ; cela ne ferme pas D.1 en entier.

Le paragraphe suivant 6.4, concernant le champ étiqueté, les noyaux scalaires simultanés sur `O(log N)` longueurs et les couplages maximaux, n'est pas annoncé complet. Aucun couplage canonique de toutes les échelles ni toute la trajectoire inverse infinie n'est revendiqué.

Les réserves arithmétiques antérieures demeurent : tout `α>0` en 3.19, taux précis de Pell et split-products en 3.13/3.14/A.2, raffinements 3.17/3.18, Fourier arbitraire et rang cyclomatique.

## Sources et validation

Base publiée du lot 18 : `90fc3c5b40a5d3441a9c1b407f19f244b6eeb728`. **Lean 4.32.0 et mathlib v4.32.0** restent ceux de la v0.9. Le cœur historique et les deux PDF conservent leurs identités dans le [manifeste](../PaperCV282/source_manifest.json).

Le [journal V3](PAPER_V3_REVISION_LOG.md) contient **une correction confirmée et douze suggestions**, dont la borne effective de Stirling proposée au lot 17. Aucune nouvelle erreur du papier n'est confirmée. Compilation, audit exhaustif, relectures et contrôles du commit publié sont consignés séparément ; aucun nouvel enregistrement Palomar n'est annoncé.
