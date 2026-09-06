# Couverture du papier C v2.8.2 et du compagnon — lot 13

**Environ 72 % de l'effort total est acquis, avec une fourchette prudente de 65–80 %.** La grille conserve les mêmes 19 blocs et 105 unités. Le comptage strict atteint **33 résultats complets sur 61 dans l'article (54,1 %)**, contre 30 au lot 12. Le compagnon reste à **3/8**. Ces deux fractions ne s'additionnent pas.

Les corollaires **5.2, 5.3 et 5.5** sont désormais formalisés avec leurs objets probabilistes effectifs et leurs clauses supplémentaires. Ils complètent le bloc 5.1–5.5, dont le théorème 5.1 et le corollaire 5.4 étaient acquis au lot 12. « Complet » conserve les entrées bibliographiques explicitement déclarées : AGG de processus et PNT pour les bornes arithmétiques, sans nouvelle prémisse. La combinatoire, les lois produit et leurs agrégations sont démontrées. L'audit des axiomes ne démontre pas les hypothèses prises comme arguments ; voir les [hypothèses bibliographiques](../PaperCV282/LITERATURE_INPUTS.md).

## Résultats nouveaux

| Résultat | Portée démontrée |
|---|---|
| Corollaire 5.2 | Vraie suite infinie de signes indépendants, graphe des seuls recouvrements, loi de son champ et comparaison triangulaire avec le champ multiplicatif. |
| Clause des compteurs de 5.2 | Loi produit indépendante des compteurs par mot, de moyenne N2^(-B), obtenue par une identité exacte de regroupement des coordonnées Poisson. Le nombre de mots peut croître. |
| Corollaire 5.3, (5.8) | Tirage uniforme des véritables m-sous-ensembles, comptes sans remise et espérance exacte EΩ=m(B−1)/2^B, plus forte que la borne imprimée. |
| Fraction exceptionnelle de 5.3 | Probabilité réelle Ω>N^(-1/2) majorée par O(logN/√N), seuil avant B,m ; tout dictionnaire restant reçoit la borne du vrai champ. |
| Corollaire 5.5, (5.9)–(5.10) | Dictionnaire {a,−a}, identité Ω=Θ, vraie occurrence à un signe commun près, taux uniforme et cible exacte card(A)2^(-L) pour tout masque déterministe. |
| Fin de 5.5 | Majorant Θ≤2^(1−d*) et convergence si le premier recouvrement s'éloigne ; mot de départ dont seul le déplacement L est compatible. |

Les coordonnées iid sont les bits directs du produit infini ; les valeurs multiplicatives sont toujours calculées à partir des coordonnées premières. Aucun théorème ne suppose l'indépendance des valeurs multiplicatives. Le graphe iid donne l'indépendance par rapport au motif extérieur entier, et ses coûts sont démontrés : b1≤2NBa², b2≤2ΛΩ, puis distance≤4(ΛΩ+Λ²B/N).

La cible vectorielle est un vrai produit de mesures de Poisson sur un espace dénombrable. La réorganisation des coordonnées en colonnes et la somme de chaque colonne sont prouvées comme des identités de lois ; l'indépendance des compteurs cibles n'est pas supposée après agrégation. Pour les mots à un signe commun près, le complément binaire est1+a dansF₂. Les deux événements sont disjoints, leur somme est une indicatrice et leurs taux s'ajoutent. La fenêtre est littéralement|L−log₂N|≤C et le taux polynomial resteN^(-1/3+ε).

Les bornes de 5.5 et du dictionnaire non exceptionnel portent aussi sur la moyenne des distances conditionnelles des vrais atomes des petits premiers. Les constantes et seuils précèdent les mots et les masques. Le reste exponentiel est quantifié pour chaque η>0. Aucune convergence presque sûre d'un noyau conditionnel n'est revendiquée.

## Comptage strict

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifié |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 4 | 0 | 0 | 0 |
| §5 | 10 | 5 | 1 | 3 | 1 |
| §6 | 4 | 0 | 1 | 0 | 3 |
| §7 | 10 | 0 | 5 | 1 | 4 |
| Compagnon | 8 | 3 | 4 | 0 | 1 |

La [matrice JSON](FORMALIZATION_COVERAGE_V282.json) conserve les69 lignes documentaires, leurs preuves et leurs obligations. Les reprises introductives 1.1–1.3 ne sont pas recomptées. B.3 est une sous-section et non un neuvième résultat du compagnon. Les identités intermédiaires et les équations ne créent pas de résultats supplémentaires dans le dénominateur61.

## Estimation de l'effort

Seul le bloc « Dictionnaires, recouvrements et constructions », correspondant à5.1–5.5, passe de 70–85 % à 100 %. Le total acquis passe de 68,75–79,32 à **70,25–80,07 unités sur 105**, soit **66,90–76,26 %**. Son milieu 71,58 % est communiqué comme « environ 72 % », avec une fourchette extérieure 65–80 %. Cette estimation d'effort comporte un jugement ; elle ne mesure ni le temps passé ni le nombre de théorèmes Lean.

| Bloc mathématique | Poids | Acquis après lot 12 | Acquis après lot 13 |
|---|---:|---:|---:|
| Modèle, Fourier, arbres et pivots | 6 | 90 %–98 % | 90 %–98 % |
| Runge croissant et défauts | 8 | 95 %–100 % | 95 %–100 % |
| Probabilités ponctuelles et moments à une fenêtre | 4 | 100 % | 100 % |
| Canal canonique, résolution, quotient et cellules | 6 | 90 %–100 % | 90 %–100 % |
| Hôtes globaux, masse rationnelle et CRT | 5 | 85 %–95 % | 85 %–95 % |
| Secteurs 1–7 et hôtes de composantes | 8 | 90 %–98 % | 90 %–98 % |
| Pell et split-products, y compris taux précis | 4 | 55 %–75 % | 55 %–75 % |
| Secteur terminal, énergie, profils globaux et minorants | 8 | 95 %–100 % | 95 %–100 % |
| Deux coupures et calcul uniforme des selles | 7 | 95 %–100 % | 95 %–100 % |
| Transfert TV, rétention douce et moments | 7 | 100 % | 100 % |
| Dictionnaires, recouvrements et constructions | 5 | 70 %–85 % | 100 % |
| Marques, signes, comparaison agrégée et clusters | 7 | 35 %–50 % | 35 %–50 % |
| Niveaux croissants et limite Poisson–Gauss | 5 | 10 %–20 % | 10 %–20 % |
| Conditionnement, chemins et contrôle presque sûr | 5 | 20 %–35 % | 20 %–35 % |
| Frontière microscopique et rang d’incidence | 6 | 20 %–35 % | 20 %–35 % |
| Départs intermédiaires et mésoscopiques | 3 | 35 %–55 % | 35 %–55 % |
| Préfixe global et enveloppes presque sûres | 3 | 30 %–55 % | 30 %–55 % |
| Transport macroscopique et noyau signé relatif | 3 | 20 %–40 % | 20 %–40 % |
| Mélange des deux sources et horloges affines | 5 | 5 %–15 % | 5 %–15 % |

## Reste à établir

Les prochaines étapes sont les marques exactes signées et la loi composée de Poisson 5.6–5.7, puis les niveaux croissants, les champs signés et la limite Poisson–Gauss 5.8–5.10. L'agrégation des mots d'une même longueur ne démontre pas ces lois à plusieurs longueurs. Aucun crédit nouveau n'est attribué à ces blocs, aux chapitres 6–7 ou au compagnon.

Restent les obligations précédentes : relèvement produit général 6.1 avec environnement enregistré, conditionnement sharp, trajectoires et presque sûr, frontière microscopique et mélange de deux sources ; tout α>0 de 3.19, taux précis exp(O(logM/loglogM)) de 3.13/3.14/A.2, raffinements 3.17/3.18, Fourier arbitraire et rang cyclomatique.

## Sources et validation

Base du lot 12 : `b5e2baec0dc20b1490a6f58940c76d4c5efa6a79`. Lean 4.32.0 et mathlib v4.32.0 restent ceux de la formalisation historique v0.9. Le cœur historique et les deux PDF anglais restent inchangés ; leurs identités figurent dans le [manifeste](../PaperCV282/source_manifest.json).

Le [journal V3](PAPER_V3_REVISION_LOG.md) ajoute la suggestion V3-S010 d'une espérance exacte en (5.8), sans erreur attribuée à la borne publiée. Il conserve une correction confirmée et comporte désormais dix suggestions. Les [déclarations précises](../PaperCV282/ENDPOINTS.md), les relectures et la validation séparée documentent la portée réellement vérifiée. Une compilation réussie ou les contrôles GitHub ne constituent pas un nouvel enregistrement Palomar.
