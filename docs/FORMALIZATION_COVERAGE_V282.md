# Couverture du papier C v2.8.2 et du compagnon — lot 14

**Environ 74 % de l'effort total est acquis, avec une fourchette prudente de 65–80 %.** La grille conserve les mêmes 19 blocs et 105 unités. Le comptage strict atteint **35 résultats complets sur 61 dans l'article (57,4 %)**, contre 33 au lot 13. Le compagnon reste à **3/8**. Ces fractions ne s'additionnent pas.

Le **théorème 5.6** et le **corollaire 5.7** sont désormais formalisés sur leurs véritables objets probabilistes. « Complet » conserve la frontière bibliographique déclarée : AGG de processus pour la comparaison finie, AGG et PNT pour les taux arithmétiques et le corollaire asymptotique. Les identités locales, les lois de Poisson composées, leur indépendance et leurs fonctions génératrices sont démontrées sans nouvelle entrée. L'audit des axiomes ne démontre pas les arguments bibliographiques : voir les [hypothèses](../PaperCV282/LITERATURE_INPUTS.md).

## Résultats nouveaux

| Résultat | Portée démontrée |
|---|---|
| Théorème 5.6, (5.13) | Champs complets site × excès, avec ou sans signe ; vrais rapports conditionnels et lois inconditionnelles, cibles Poisson indépendantes exactes. Constante absolue explicite 40 sur les cinq termes imprimés. |
| Taux (5.14) | Un même seuil avant L et E sur la bande βmin logN≤L+1 et L+E+2≤βmax logN ; borne 32λ(1+λ)[exp(−V+ην)+N^(−1/3+ε)] pour chaque ε,η>0. |
| Cas locaux signés | Incompatibilité, deux sommets communs, un sommet commun, supports disjoints : probabilités 0, 4pe,s pf,t, 2pe,s pf,t et pe,s pf,t avec les conditions exactes sur les signes. |
| Suppression et paires | Somme des alternatives avant estimation : défaut et R2 à la longueur de base L, défauts supprimés et arêtes au support maximal Q=L+E+1. Aucun facteur polynomial en E. |
| Corollaire 5.7 | Vrai compteur des fenêtres constantes sans maximalité gauche, approché en TV par Σi<P H_i, P∼Pois(λ), H_i indépendantes de masse 2^(−h), h≥1. |
| Cible et queues | PGF exp[λ(z/(2−z)−1)] pour 0≤z≤1 ; identité de la cible pondérée finie et de la vraie loi composée tronquée ; queue cible ≤λ2^(−E−1), queue source ≤λ2^(−E−1)(1+N^(−1/2+ε)). |
| Bords du bloc | Identité déterministe hors des fenêtres constantes commençant à N ou 2N−1, vraie borne ponctuelle et disparition de cette erreur au critique. |

Le cylindre premier C reste libre. Il couvre le champ lorsque C≥dyadicCutoff(N,Q), et représente tout F_Y lorsque C≥Y. Le choix C=max(Y,dyadicCutoff(N,Q)) garantit ces deux propriétés ; aucune indépendance de valeurs multiplicatives n'est supposée. L'indépendance du graphe concerne tout le motif extérieur, avec chaque marque et chaque signe conservés.

La cible composée est construite à partir d'un vrai nombre de Poisson et d'une vraie suite indépendante de marques géométriques positives. Son identité avec la somme pondérée du produit Poisson est démontrée par les lois et leurs transformées. La convergence de 5.7 enlève les queues après la limite pour chaque troncature fixe. Elle ne repose pas sur une convergence de moments.

Une configuration cible dénombrable **agrégée par excès**, à support fini dans ℕ→₀ℕ, est également construite ; chacune de ses projections finies possède la vraie loi produit indépendante, et sa somme pondérée a la loi composée. Cela ne ferme pas le **champ spatial dénombrable** ni sa limite diffuse en 1.1. Ces obligations, les champs croissants de 5.9 et le résultat agrégé C.1 du compagnon ne reçoivent aucun crédit complet supplémentaire.

## Comptage strict

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifié |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 4 | 0 | 0 | 0 |
| §5 | 10 | 7 | 0 | 2 | 1 |
| §6 | 4 | 0 | 1 | 0 | 3 |
| §7 | 10 | 0 | 5 | 1 | 4 |
| Compagnon | 8 | 3 | 4 | 0 | 1 |

La [matrice JSON](FORMALIZATION_COVERAGE_V282.json) conserve les 69 lignes documentaires. Les reprises introductives 1.1–1.3 ne sont pas recomptées, et B.3 n'est pas un neuvième résultat du compagnon. Des identités intermédiaires ne créent pas de résultats supplémentaires dans le dénominateur 61.

## Estimation de l'effort

Seul le bloc « Marques, signes, comparaison agrégée et clusters » (7 unités) passe de 35–50 % à 70–80 %. Il contient aussi 5.9 et C.1, qui restent ouverts. Le total acquis passe de 70,25–80,07 à **72,70–82,17 unités sur 105**, soit **69,24–78,26 %**. Le milieu 73,75 % est communiqué comme « environ 74 % », avec une fourchette extérieure 65–80 %. C'est une estimation d'effort, distincte des comptes de déclarations et du temps passé.

| Bloc mathématique | Poids | Acquis après lot 13 | Acquis après lot 14 |
|---|---:|---:|---:|
| Modèle, Fourier, arbres et pivots | 6 | 90 %–98 % | 90 %–98 % |
| Runge croissant et défauts | 8 | 95 %–100 % | 95 %–100 % |
| Probabilités ponctuelles et moments à une fenêtre | 4 | 100 %–100 % | 100 %–100 % |
| Canal canonique, résolution, quotient et cellules | 6 | 90 %–100 % | 90 %–100 % |
| Hôtes globaux, masse rationnelle et CRT | 5 | 85 %–95 % | 85 %–95 % |
| Secteurs 1–7 et hôtes de composantes | 8 | 90 %–98 % | 90 %–98 % |
| Pell et split-products, y compris taux précis | 4 | 55 %–75 % | 55 %–75 % |
| Secteur terminal, énergie, profils globaux et minorants | 8 | 95 %–100 % | 95 %–100 % |
| Deux coupures et calcul uniforme des selles | 7 | 95 %–100 % | 95 %–100 % |
| Transfert TV, rétention douce et moments | 7 | 100 %–100 % | 100 %–100 % |
| Dictionnaires, recouvrements et constructions | 5 | 100 %–100 % | 100 %–100 % |
| Marques, signes, comparaison agrégée et clusters | 7 | 35 %–50 % | 70 %–80 % |
| Niveaux croissants et limite Poisson–Gauss | 5 | 10 %–20 % | 10 %–20 % |
| Conditionnement, chemins et contrôle presque sûr | 5 | 20 %–35 % | 20 %–35 % |
| Frontière microscopique et rang d’incidence | 6 | 20 %–35 % | 20 %–35 % |
| Départs intermédiaires et mésoscopiques | 3 | 35 %–55 % | 35 %–55 % |
| Préfixe global et enveloppes presque sûres | 3 | 30 %–55 % | 30 %–55 % |
| Transport macroscopique et noyau signé relatif | 3 | 20 %–40 % | 20 %–40 % |
| Mélange des deux sources et horloges affines | 5 | 5 %–15 % | 5 %–15 % |

## Reste à établir

La suite porte sur le champ spatial à toutes marques et sa limite diffuse, puis les niveaux croissants, la comparaison agrégée et la limite Poisson–Gauss 5.8–5.10. Le relèvement produit général 6.1 avec environnement enregistré, les conditionnements précis, les trajectoires et le presque sûr, la frontière microscopique et le mélange de deux sources restent ouverts.

Les raffinements antérieurs conservent leur portée : tout α>0 en 3.19, taux précis exp(O(logM/loglogM)) en 3.13/3.14/A.2, raffinements 3.17/3.18, Fourier arbitraire et rang cyclomatique. Aucun crédit nouveau n'est attribué à ces obligations.

## Sources et validation

Base du lot 13 : `e8bb75fa629a1f414fb1c5dc99a704a0f7b2af0a`. Lean 4.32.0 et mathlib v4.32.0 restent ceux de la formalisation historique v0.9. Le cœur historique et les deux PDF anglais restent inchangés ; leurs identités figurent dans le [manifeste](../PaperCV282/source_manifest.json).

Le [journal V3](PAPER_V3_REVISION_LOG.md) consigne la portée acquise de 5.6–5.7. Aucun nouveau défaut du texte n'a été confirmé dans ce lot : le registre conserve une correction et dix suggestions. Les [déclarations](../PaperCV282/ENDPOINTS.md), les relectures et la validation séparée documentent les preuves réellement vérifiées. Aucun nouvel enregistrement Palomar n'est annoncé.
