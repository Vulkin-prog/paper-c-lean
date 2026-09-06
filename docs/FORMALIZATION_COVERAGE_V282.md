# Couverture du papier C v2.8.2 et du compagnon — lot 15

**Environ 75 % de l'effort total est acquis, avec une fourchette prudente de 65–80 %.** La grille conserve les mêmes 19 blocs et 105 unités. Le comptage strict reste **35 résultats complets sur 61 dans l'article (57,4 %)** et, séparément, **3/8 dans le compagnon**. Les deux fractions ne s'additionnent pas.

Ce lot ferme le **théorème introductif 1.1**, avec le champ spatial à toutes marques, le coefficient exponentiel imprimé, sa conséquence scalaire et la vraie limite diffuse. Il ferme aussi toute la **partie étiquetée 5.8(i)**, avec ses deux budgets de conditionnement et la borne mobile (5.20), ainsi que sa version signée en **5.9**. Les parties agrégées de 5.8–5.9 restent ouvertes. La convention de comptage exclut depuis l'origine les reprises introductives 1.1–1.3 ; 1.1 n'ajoute donc pas une unité au dénominateur 61.

« Formalisé » conserve la frontière bibliographique déclarée : les conclusions arithmétiques utilisent AGG de processus et PNT comme arguments explicites. Les constructions probabilistes, les cibles, leur indépendance, la topologie et le transfert de limite faible sont prouvés sans nouvelle entrée. L'audit des axiomes ne démontre pas ces arguments bibliographiques : voir les [hypothèses](../PaperCV282/LITERATURE_INPUTS.md).

## Résultats nouveaux

| Résultat | Portée démontrée |
|---|---|
| Champ complet | Véritable configuration à support fini sur site × excès naturel × signe ; projections égales aux vrais champs finis, terminaison des runs presque sûre, queues source et cible prouvées séparément. |
| Théorème 1.1, (1.3) | Pour chaque a<1/√2, un seuil uniforme avant L donne TV≤exp(−a√(logN·loglogN)) sur toute la fenêtre critique. Toutes les marques et les deux signes sont conservés. Le vrai compteur de départs hérite de la même borne. |
| Limite diffuse de 1.1 | Vraie convergence faible des lois des mesures de points à positions x/N vers un nombre de Poisson de marques indépendantes, positions uniformes sur [1,2], excès géométriques et signes équiprobables. Sous-suites de tailles quelconques tendant vers l'infini et λ_N→λ admises. |
| Cible spatiale | Projections finies Poisson indépendantes, identité avec le tirage global marqué, somme totale Poisson et somme pondérée géométrique composée ; intégrale de Laplace du champ complet. |
| Budget hard, (5.18) | Pour d=o(logN), vrai événement positif de tout F_Yhard et I+logΛ+log(1+Λ)≤V−cν : variation totale du champ spatial signé complet vers zéro. |
| Budget mobile, (5.19)–(5.20) | Conditionnement par tout F_Ysoft ; budget I+logΛ≤Vsoft/2−cνsoft. Borne explicite64 exp(I)[Λexp(−Vsoft/2+ηνsoft)+Λ²exp(−Vsoft+ηνsoft)+Λ(1+Λ)N^(−1/3+ε)], pour chaque 0<ε<1/3 et η>0, sans queue restante. |
| Niveaux et trajectoires | Reparamétrage exact r=e−d et intensités avec la phase dyadique. Bijection mesurable entre comptes exacts à masse finie et tous leurs seuils ; égalité exacte des distances, y compris sous le vrai conditionnement. |

La cible diffuse est construite sur un vrai produit : un nombre de Poisson, une suite indépendante de positions uniformes, d'excès géométriques et de signes. Le couplage par cellules uniformes identifie exactement la cible de grille ; la limite porte sur la topologie faible des mesures finies et celle des lois de probabilité, via les véritables intégrales de tests continus bornés. La structure mesurable de cette topologie est explicite. Les mesures obtenues n'ont aucune masse hors [1,2]. Il n'est pas affirmé de convergence en variation totale vers la cible diffuse.

Les pertes de queue sont enlevées avec E=3⌈V/log2⌉ ou son analogue mobile. Le coût de la queue source est divisé par la vraie probabilité de l'événement conditionnant ; la queue cible indépendante ne l'est pas. Les seuils finis précèdent L et l'événement. Le papier peut ainsi conserver ses paramètres mobiles, sans supposer à tort une limite d'intensité sur toutes les tailles entières consécutives.

## Comptage strict

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifié |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 4 | 0 | 0 | 0 |
| §5 | 10 | 7 | 2 | 0 | 1 |
| §6 | 4 | 0 | 1 | 0 | 3 |
| §7 | 10 | 0 | 5 | 1 | 4 |
| Compagnon | 8 | 3 | 4 | 0 | 1 |

La [matrice JSON](FORMALIZATION_COVERAGE_V282.json) conserve ses 69 lignes documentaires. Les résultats 5.8 et 5.9 passent de « réemploi non raccordé » à « partiel ». Aucun ne reçoit de crédit complet tant que sa comparaison agrégée reste ouverte. La clôture de 1.1 est consignée séparément, sans recomptage des reprises introductives.

## Estimation de l'effort

Le bloc des marques (7 unités) passe de 70–80 % à **75–85 %**, soit +0,35 unité. Le bloc des niveaux croissants et de la limite Poisson–Gauss (5 unités) passe de 10–20 % à **30–40 %**, soit +1 unité ; ce crédit porte uniquement sur les comparaisons étiquetées démontrées. Les 17 autres blocs restent inchangés. Les outils génériques et l'égalité des distances des trajectoires ne reçoivent pas un second crédit dans les chapitres suivants.

Le total passe de 72,70–82,17 à **74,05–83,52 unités sur 105**, soit **70,52–79,54 %**. Le milieu 75,03 % est communiqué comme « environ 75 % », avec la même fourchette prudente 65–80 %. Ce jugement d'effort tient compte du travail antérieurement acquis ; il ne mesure ni le nombre de théorèmes Lean, ni les lignes, ni la durée du lot.

| Bloc mathématique | Poids | Acquis après lot 14 | Acquis après lot 15 |
|---|---:|---:|---:|
| Modèle, Fourier, arbres et pivots | 6 | 90–98 % | 90–98 % |
| Runge croissant et défauts | 8 | 95–100 % | 95–100 % |
| Probabilités ponctuelles et moments à une fenêtre | 4 | 100–100 % | 100–100 % |
| Canal canonique, résolution, quotient et cellules | 6 | 90–100 % | 90–100 % |
| Hôtes globaux, masse rationnelle et CRT | 5 | 85–95 % | 85–95 % |
| Secteurs 1–7 et hôtes de composantes | 8 | 90–98 % | 90–98 % |
| Pell et split-products, y compris taux précis | 4 | 55–75 % | 55–75 % |
| Secteur terminal, énergie, profils globaux et minorants | 8 | 95–100 % | 95–100 % |
| Deux coupures et calcul uniforme des selles | 7 | 95–100 % | 95–100 % |
| Transfert TV, rétention douce et moments | 7 | 100–100 % | 100–100 % |
| Dictionnaires, recouvrements et constructions | 5 | 100–100 % | 100–100 % |
| Marques, signes, comparaison agrégée et clusters | 7 | 70–80 % | 75–85 % |
| Niveaux croissants et limite Poisson–Gauss | 5 | 10–20 % | 30–40 % |
| Conditionnement, chemins et contrôle presque sûr | 5 | 20–35 % | 20–35 % |
| Frontière microscopique et rang d’incidence | 6 | 20–35 % | 20–35 % |
| Départs intermédiaires et mésoscopiques | 3 | 35–55 % | 35–55 % |
| Préfixe global et enveloppes presque sûres | 3 | 30–55 % | 30–55 % |
| Transport macroscopique et noyau signé relatif | 3 | 20–40 % | 20–40 % |
| Mélange des deux sources et horloges affines | 5 | 5–15 % | 5–15 % |

## Reste à établir

La priorité est la comparaison **agrégée directionnelle C.1**, qui doit fournir la plage à un facteur en (5.21)–(5.22), sa version signée et la limite **Poisson–Gauss 5.10**. L'égalité entre distances de niveaux et de seuils ne remplace pas cette estimation. Le relèvement produit général 6.1 avec environnement enregistré, les conditionnements précis, les trajectoires et le presque sûr, la frontière microscopique et le mélange de deux sources restent ouverts.

Les réserves arithmétiques antérieures sont conservées : tout α>0 en 3.19, taux précis exp(O(logM/loglogM)) en 3.13/3.14/A.2, raffinements 3.17/3.18, Fourier arbitraire et rang cyclomatique. Aucun crédit nouveau n'est attribué à ces obligations.

## Sources et validation

Base du lot 14 : `0af618dd8924e38d60a2b2332c74acd1bfbbd706`. **Lean 4.32.0 et mathlib v4.32.0** restent ceux de la formalisation historique v0.9. Le cœur historique et les deux PDF restent inchangés ; leurs identités figurent dans le [manifeste](../PaperCV282/source_manifest.json).

Le [journal V3](PAPER_V3_REVISION_LOG.md) décrit ces nouveaux acquis et les limites restantes. Aucune nouvelle erreur du manuscrit n'a été confirmée ; le registre conserve une correction et dix suggestions. Les [déclarations](../PaperCV282/ENDPOINTS.md), les relectures et la validation séparée documentent les preuves vérifiées. Aucun nouvel enregistrement Palomar n'est annoncé.
